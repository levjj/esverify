import { stringifyAssertion, stringifyExpression } from './codegen';
import { Syntax, TestCode, Visitor, id, isValidAssignmentTarget, nullLoc, removeTestCodePrefix,
         replaceVarAssertion as replaceJSVarAssertion, replaceVarFunction as replaceJSVarFunction,
         replaceVarBlock as replaceJSVarBlock, uniqueIdentifier, eqSourceLocation,
         compEndPosition } from './javascript';
import { A, Classes, FreeVars, Heap, Locs, P, Vars, and, eq, falsy, fls, heapEq, heapStore, implies, not, or,
         removePrefix, replaceResultWithCall, replaceVar, transformClassInvariant, transformEveryInvariant,
         transformSpec, tru, truthy, und, Syntax as Logic, compareType } from './logic';
import { eraseTriggersProp } from './qi';
import { isMutable } from './scopes';
import { flatMap } from './util';
import VerificationCondition, { Assumption } from './verification';
import { generatePreamble } from './preamble';

export type BreakCondition = P;
export type AccessTriggers = Array<Logic.AccessTrigger>;

export class VCGenerator extends Visitor<[A, AccessTriggers, Syntax.Expression],
                                         [P, AccessTriggers, Syntax.Expression, TestCode],
                                         [A, Syntax.Expression],
                                         BreakCondition> {

  classes: Classes;
  oldHeap: Heap;
  heap: Heap;
  locs: Locs;
  vars: Vars;
  prop: P;
  vcs: Array<VerificationCondition>;
  resVar: string | null;
  freeVars: FreeVars;
  testBody: TestCode;
  assertionPolarity: boolean;
  simpleAssertion: boolean;
  assumptions: Array<string>;
  heapHints: Array<[Syntax.SourceLocation, Heap]>;

  constructor (classes: Classes, oldHeap: Heap, heap: Heap, locs: Locs, vars: Vars, assumptions: Array<string>,
               heapHints: Array<[Syntax.SourceLocation, Heap]>, prop: P = tru) {
    super();
    this.classes = classes;
    this.oldHeap = oldHeap;
    this.heap = heap;
    this.locs = locs;
    this.vars = vars;
    this.prop = prop;
    this.vcs = [];
    this.resVar = null;
    this.freeVars = [];
    this.testBody = [];
    this.assertionPolarity = true;
    this.simpleAssertion = true;
    this.assumptions = assumptions;
    this.heapHints = heapHints;
  }

  have (p: P, t: TestCode = []): void {
    this.prop = and(this.prop, p);
    this.testBody = this.testBody.concat(t);
  }

  check (assertion: Syntax.Expression): Syntax.Statement {
    return {
      type: 'ExpressionStatement',
      expression: {
        type: 'CallExpression',
        callee: id('assert'),
        args: [assertion],
        loc: assertion.loc
      },
      loc: assertion.loc
    };
  }

  visitComplexAssertion (assertion: Syntax.Assertion): [P, AccessTriggers, Syntax.Expression] {
    const origSimpleAssertion = this.simpleAssertion;
    try {
      this.simpleAssertion = false;
      const [p, triggers, e, t] = this.visitAssertion(assertion);
      if (t.length > 0) throw new Error('specs in in complex assertions not supported yet');
      return [p, triggers, e];
    } finally {
      this.simpleAssertion = origSimpleAssertion;
    }
  }

  assert (assertion: Syntax.Assertion, oldHeap: Heap = this.oldHeap, heap: Heap = this.heap):
          [P, AccessTriggers, TestCode] {
    const origOldHeap = this.oldHeap;
    const origHeap = this.heap;
    const origSimpleAssertion = this.simpleAssertion;
    try {
      this.oldHeap = oldHeap;
      this.heap = heap;
      this.simpleAssertion = true;
      const [assertP, assertTriggers, assertE, assertT] = this.visitAssertion(assertion);
      const checkT: Array<Syntax.Statement> = [];
      if (this.assertionPolarity && (assertE.type !== 'Literal' || assertE.value !== true)) {
        checkT.push(this.check(assertE));
      }
      return [assertP, assertTriggers, checkT.concat(assertT)];
    } finally {
      this.heap = origHeap;
      this.oldHeap = origOldHeap;
      this.simpleAssertion = origSimpleAssertion;
    }
  }

  assume (assertion: Syntax.Assertion, oldHeap: Heap = this.oldHeap, heap: Heap = this.heap):
         [P, AccessTriggers, TestCode] {
    try {
      this.assertionPolarity = !this.assertionPolarity;
      return this.assert(assertion, oldHeap, heap);
    } finally {
      this.assertionPolarity = !this.assertionPolarity;
    }
  }

  tryPre<T> (pre: P, fn: () => T): [Heap, P, TestCode, T] {
    const origPre = this.prop;
    const origHeap = this.heap;
    const origBody = this.testBody;
    try {
      this.have(pre);
      const r = fn();
      return [this.heap, removePrefix(and(origPre, pre), this.prop), removeTestCodePrefix(origBody, this.testBody), r];
    } finally {
      this.prop = origPre;
      this.heap = origHeap;
      this.testBody = origBody;
    }
  }

  tryExpression (pre: P, expr: Syntax.Expression): [Heap, P, A, Syntax.Expression] {
    const [heap, p, tc, [a, e]] = this.tryPre(pre, () => {
      return this.visitExpression(expr);
    });
    if (tc.length > 0) throw new Error('expected no new test statements');
    return [heap, p, a, e];
  }

  freshVar (): string {
    let i = 0;
    while (this.vars.has(`_tmp_${i}`)) i++;
    this.vars.add(`_tmp_${i}`);
    return `_tmp_${i}`;
  }

  freshThisVar (): string {
    let i = 0;
    while (this.vars.has(`_this_${i}`)) i++;
    this.vars.add(`_this_${i}`);
    return `_this_${i}`;
  }

  testVar (loc: Syntax.SourceLocation): string {
    return `_tmp_${uniqueIdentifier(loc)}`;
  }

  smtPlaceholder (name: string) {
    return id(`__free__${name}`);
  }

  freeVar (name: string) {
    this.freeVars.push(name);
    this.testBody = this.testBody.concat([{
      type: 'VariableDeclaration',
      id: id(name),
      init: this.smtPlaceholder(name),
      kind: 'let',
      loc: nullLoc()
    }, {
      type: 'VariableDeclaration',
      id: id(`old_${name}`),
      init: id(name),
      kind: 'const',
      loc: nullLoc()
    }]);
  }

  freeLoc (name: string) {
    this.freeVars.push({ name, heap: this.heap });
    this.testBody = this.testBody.concat([{
      type: 'ExpressionStatement',
      expression: {
        type: 'AssignmentExpression',
        left: id(name),
        right: this.smtPlaceholder(name),
        loc: nullLoc()
      },
      loc: nullLoc()
    }, {
      type: 'VariableDeclaration',
      id: id(`old_${name}`),
      init: id(name),
      kind: 'const',
      loc: nullLoc()
    }]);
  }

  verify (vc: P, testBody: TestCode, loc: Syntax.SourceLocation, desc: string,
          aliases: { [from: string]: string } = {}) {
    const assumptions: Array<Assumption> = this.assumptions.map((src: string): [string, P] => [src, tru]);
    this.vcs.push(new VerificationCondition(this.classes, this.heap, this.locs, this.vars, this.prop, assumptions,
                                            vc, loc, desc, this.freeVars, this.testBody, testBody,
                                            this.heapHints, aliases));
  }

  compareType (expr: Syntax.Expression, type: 'boolean' | 'number' | 'string'): Syntax.Expression {
    return {
      type: 'BinaryExpression',
      operator: '===',
      left: {
        type: 'UnaryExpression',
        operator: 'typeof',
        argument: expr,
        loc: expr.loc
      },
      right: {
        type: 'Literal',
        value: type,
        loc: expr.loc
      },
      loc: expr.loc
    };
  }

  compareTypePropAndTest (exprA: A, exprE: Syntax.Expression,
                          type: 'boolean' | 'number' | 'string' | 'number or string' | 'int'):
             [P, Syntax.Expression] {
    switch (type) {
      case 'boolean':
        return [
          compareType(exprA, 'boolean'),
          this.compareType(exprE, 'boolean')
        ];
      case 'number':
        return [
          compareType(exprA, 'number'),
          this.compareType(exprE, 'number')
        ];
      case 'string':
        return [
          compareType(exprA, 'string'),
          this.compareType(exprE, 'string')
        ];
      case 'number or string':
        return [
          or(compareType(exprA, 'number'), compareType(exprA, 'string')),
          {
            type: 'LogicalExpression',
            operator: '||',
            left: this.compareType(exprE, 'number'),
            right: this.compareType(exprE, 'string'),
            loc: exprE.loc
          }
        ];
      case 'int':
        return [truthy({
          type: 'IsIntegerExpression',
          expression: exprA
        }), {
          type: 'CallExpression',
          callee: {
            type: 'MemberExpression',
            object: id('Number', exprE.loc),
            property: { type: 'Literal', value: 'isInteger', loc: exprE.loc },
            loc: exprE.loc
          },
          args: [exprE],
          loc: exprE.loc
        }];
    }
  }

  verifyType (expr: Syntax.Expression, exprA: A, exprE: Syntax.Expression, op: string,
              type: 'boolean' | 'number' | 'string' | 'number or string' | 'int') {
    const [prop, test] = this.compareTypePropAndTest(exprA, exprE, type);
    const msg = op === 'if' ? 'if condition' : `operator ${op}`;
    this.verify(prop, [this.check(test)], exprE.loc, `${msg} requires ${type}: ${stringifyExpression(expr)}`);
  }

  heapHint (loc: Syntax.SourceLocation): void {
    // find index of heap hint
    const idx = this.heapHints.findIndex(([loc2]) => eqSourceLocation(loc, loc2));
    if (idx >= 0) {
      this.heapHints[idx][1] = this.heap;
    } else {
      // no such hint yet
      // find index of first heap hint that is not earlier
      const idx = this.heapHints.findIndex(([loc2]) => !compEndPosition(loc, loc2));
      if (idx >= 0) {
        this.heapHints.splice(idx, 0, [loc, this.heap]);
      } else {
        // no heap hint found that is later, so append
        this.heapHints.push([loc, this.heap]);
      }
    }
  }

  visitTerm (term: Syntax.Term): [A, AccessTriggers, Syntax.Expression] {
    try {
      return super.visitTerm(term);
    } finally {
      this.heapHint(term.loc);
    }
  }

  visitIdentifierTerm (term: Syntax.Identifier): [A, AccessTriggers, Syntax.Expression] {
    if (isMutable(term)) {
      return [{ type: 'HeapReference', heap: this.heap, loc: term.name }, [], term];
    } else {
      return [term.name, [], term];
    }
  }

  visitOldIdentifierTerm (term: Syntax.OldIdentifier): [A, AccessTriggers, Syntax.Expression] {
    if (!isMutable(term.id)) { throw new Error('not mutable'); }
    return [
      { type: 'HeapReference', heap: this.oldHeap, loc: term.id.name },
      [],
      id(`old_${term.id.name}`, term.loc)
    ];
  }

  visitLiteralTerm (term: Syntax.Literal): [A, AccessTriggers, Syntax.Expression] {
    return [term, [], term];
  }

  visitUnaryTerm (term: Syntax.UnaryTerm): [A, AccessTriggers, Syntax.Expression] {
    const [argumentA, argumentTriggers, argumentE] = this.visitTerm(term.argument);
    return [
      { type: 'UnaryExpression', operator: term.operator, argument: argumentA },
      argumentTriggers,
      { type: 'UnaryExpression', operator: term.operator, argument: argumentE, loc: term.loc }
    ];
  }

  visitBinaryTerm (term: Syntax.BinaryTerm): [A, AccessTriggers, Syntax.Expression] {
    const [leftA, leftTriggers, leftE] = this.visitTerm(term.left);
    const [rightA, rightTriggers, rightE] = this.visitTerm(term.right);
    return [
      { type: 'BinaryExpression', operator: term.operator, left: leftA, right: rightA },
      leftTriggers.concat(rightTriggers),
      { type: 'BinaryExpression', operator: term.operator, left: leftE, right: rightE, loc: term.loc }
    ];
  }

  visitLogicalTerm (term: Syntax.LogicalTerm): [A, AccessTriggers, Syntax.Expression] {
    const [leftA, leftTriggers, leftE] = this.visitTerm(term.left);
    const [rightA, rightTriggers, rightE] = this.visitTerm(term.right);
    switch (term.operator) {
      case '&&':
        return [
          { type: 'ConditionalExpression', test: truthy(leftA), consequent: rightA, alternate: leftA },
          leftTriggers.concat(rightTriggers),
          { type: 'LogicalExpression', operator: '&&', left: leftE, right: rightE, loc: term.loc }
        ];
      case '||':
        return [
          { type: 'ConditionalExpression', test: truthy(leftA), consequent: leftA, alternate: rightA },
          leftTriggers.concat(rightTriggers),
          { type: 'LogicalExpression', operator: '||', left: leftE, right: rightE, loc: term.loc }
        ];
    }
  }

  visitConditionalTerm (term: Syntax.ConditionalTerm): [A, AccessTriggers, Syntax.Expression] {
    const [testA, testTriggers, testE] = this.visitTerm(term.test);
    const [consequentA, consequentTriggers, consequentE] = this.visitTerm(term.consequent);
    const [alternateA, alternateTriggers, alternateE] = this.visitTerm(term.alternate);
    return [
      { type: 'ConditionalExpression', test: truthy(testA), consequent: consequentA, alternate: alternateA },
      [...testTriggers, ...consequentTriggers, ...alternateTriggers],
      { type: 'ConditionalExpression', test: testE, consequent: consequentE, alternate: alternateE, loc: term.loc }
    ];
  }

  visitCallTerm (term: Syntax.CallTerm): [A, AccessTriggers, Syntax.Expression] {
    const [calleeA, calleeTriggers, calleeE] = this.visitTerm(term.callee);
    const args = term.args.map(a => this.visitTerm(a));
    let thisArg: A = (typeof calleeA !== 'string' && calleeA.type === 'MemberExpression') ? calleeA.object : und;
    return [
      {
        type: 'CallExpression',
        callee: calleeA,
        heap: this.heap,
        thisArg,
        args: args.map(([argA]) => argA)
      },
      calleeTriggers.concat(flatMap(args, ([, argTriggers]) => argTriggers)),
      {
        type: 'CallExpression',
        callee: calleeE,
        args: args.map(([, , argE]) => argE),
        loc: term.loc
      }
    ];
  }

  visitMemberTerm (term: Syntax.MemberTerm): [A, AccessTriggers, Syntax.Expression] {
    const [objectA, objectTriggers, objectE] = this.visitTerm(term.object);
    const [propertyA, propertyTriggers, propertyE] = this.visitTerm(term.property);
    return [
      {
        type: 'MemberExpression',
        object: objectA,
        property: propertyA
      },
      objectTriggers.concat(propertyTriggers, [{
        type: 'AccessTrigger',
        object: objectA,
        property: propertyA,
        heap: this.heap,
        fuel: 1
      }]),
      {
        type: 'MemberExpression',
        object: objectE,
        property: propertyE,
        loc: term.loc
      }
    ];
  }

  visitIsIntegerTerm (term: Syntax.IsIntegerTerm): [A, AccessTriggers, Syntax.Expression] {
    const [termA, termTriggers, termE] = this.visitTerm(term.term);
    return [{
      type: 'IsIntegerExpression',
      expression: termA
    }, termTriggers, {
      type: 'CallExpression',
      callee: {
        type: 'MemberExpression',
        object: id('Number', term.loc),
        property: { type: 'Literal', value: 'isInteger', loc: term.loc },
        loc: term.loc
      },
      args: [termE],
      loc: term.loc
    }];
  }

  visitToIntegerTerm (term: Syntax.ToIntegerTerm): [A, AccessTriggers, Syntax.Expression] {
    const [termA, termTriggers, termE] = this.visitTerm(term.term);
    return [{
      type: 'ToIntegerExpression',
      expression: termA
    }, termTriggers, {
      type: 'CallExpression',
      callee: {
        type: 'MemberExpression',
        object: id('Math', term.loc),
        property: { type: 'Literal', value: 'trunc', loc: term.loc },
        loc: term.loc
      },
      args: [termE],
      loc: term.loc
    }];
  }

  visitAssertion (assertion: Syntax.Assertion): [P, AccessTriggers, Syntax.Expression, TestCode] {
    try {
      return super.visitAssertion(assertion);
    } finally {
      this.heapHint(assertion.loc);
    }
  }

  visitTermAssertion (term: Syntax.Term): [P, AccessTriggers, Syntax.Expression, TestCode] {
    const [termA, termTriggers, termE] = this.visitTerm(term);
    return [truthy(termA), termTriggers, termE, []];
  }

  visitPureAssertion (assertion: Syntax.PureAssertion): [P, AccessTriggers, Syntax.Expression, TestCode] {
    const tru: Syntax.Expression = { type: 'Literal', value: true, loc: assertion.loc };
    return [heapEq(this.heap, this.oldHeap), [], tru, []];
  }

  insertWrapper (callee: Syntax.Expression, loc: Syntax.SourceLocation, args: Array<Syntax.Identifier>, rT: TestCode,
                 retName: Syntax.Identifier, sT: TestCode): Syntax.Expression {
    return {
      type: 'CallExpression',
      callee: id('spec'),
      args: [
        callee,
        { type: 'Literal', value: uniqueIdentifier(callee.loc), loc },
        {
          type: 'FunctionExpression',
          id: null,
          params: args,
          requires: [],
          ensures: [],
          body: {
            type: 'BlockStatement',
            body: rT.concat({
              type: 'ReturnStatement',
              argument: {
                type: 'ArrayExpression',
                elements: args,
                loc
              },
              loc
            }),
            loc
          },
          freeVars: [],
          loc
        }, {
          type: 'FunctionExpression',
          id: null,
          params: args.concat(retName),
          requires: [],
          ensures: [],
          body: {
            type: 'BlockStatement',
            body: sT.concat({
              type: 'ReturnStatement',
              argument: retName,
              loc
            }),
            loc
          },
          freeVars: [],
          loc
        }
      ],
      loc
    };
  }

  visitSpecAssertion (assertion: Syntax.SpecAssertion): [P, AccessTriggers, Syntax.Expression, TestCode] {
    const [calleeA,, calleeE] = this.visitTerm(assertion.callee);
    // reserve fresh name for 'this'
    const thisArg = this.freshThisVar();
    // translate pre and post
    const [rP,, rT] = this.assume(assertion.pre, this.heap + 1, this.heap + 1);
    const [sP,, sT] = this.assert(assertion.post.expression, this.heap + 1, this.heap + 2);
    // remove 'this' name from scope again
    this.vars.delete(thisArg);
    // rename 'this' to the name reserved above in the generated propositions
    const rP2 = assertion.hasThis ? replaceVar('this', thisArg, rP) : rP;
    const sP2 = assertion.hasThis ? replaceVar('this', thisArg, sP) : sP;
    const sP3 = replaceResultWithCall(calleeA, this.heap + 1, thisArg, assertion.args,
                                      assertion.post.argument && assertion.post.argument.name, sP2);
    const specP = transformSpec(calleeA, thisArg, assertion.args, rP2, sP3, this.heap + 1);
    const retName = assertion.post.argument === null
      ? id(`_res_${uniqueIdentifier(assertion.loc)}`)
      : assertion.post.argument;
    const specE: Syntax.Expression = {
      type: 'BinaryExpression',
      operator: '===',
      left: {
        type: 'UnaryExpression',
        operator: 'typeof',
        argument: calleeE,
        loc: assertion.loc
      },
      right: {
        type: 'Literal',
        value: 'function',
        loc: assertion.loc
      },
      loc: assertion.loc
    };
    const specT: Array<Syntax.Statement> = [];
    if (this.simpleAssertion && isValidAssignmentTarget(calleeE)) {
      if (rT.length + sT.length > 0) {
        specT.push({
          type: 'ExpressionStatement',
          expression: {
            type: 'AssignmentExpression',
            left: calleeE,
            right: this.insertWrapper(calleeE, assertion.loc, assertion.args.map(a => id(a)), rT, retName, sT),
            loc: assertion.loc
          },
          loc: assertion.loc
        });
      }
      if (this.assertionPolarity) {
        if (specP.type !== 'And' || specP.clauses.length !== 2) {
          throw new Error('expected spec to translate to [fnCheck, forAll]');
        }
        const forAllP: P = specP.clauses[1];
        if (forAllP.type !== 'ForAllCalls') {
          throw new Error('expected spec to translate to [fnCheck, forAll]');
        }
        const callStmt: Syntax.ExpressionStatement = {
          type: 'ExpressionStatement',
          expression: calleeE,
          loc: assertion.loc
        };
        let lifted = false;
        forAllP.liftCallback = (renamedThis: string, renamedArgs: Array<string>) => {
          if (lifted) return;
          lifted = true;
          if (assertion.hasThis) {
            callStmt.expression = {
              type: 'CallExpression',
              callee: {
                type: 'MemberExpression',
                object: callStmt.expression,
                property: { type: 'Literal', value: 'call', loc: assertion.loc },
                loc: assertion.loc
              },
              args: [id(renamedThis)].concat(renamedArgs.map(arg => this.smtPlaceholder(arg))),
              loc: assertion.loc
            };
          } else {
            callStmt.expression = {
              type: 'CallExpression',
              callee: callStmt.expression,
              args: renamedArgs.map(arg => this.smtPlaceholder(arg)),
              loc: assertion.loc
            };
          }
        };
        specT.push(callStmt);
      }
    }
    return [specP, [], specE, specT];
  }

  visitEveryAssertion (assertion: Syntax.EveryAssertion): [P, AccessTriggers, Syntax.Expression, TestCode] {
    const [arrayA,, arrayE] = this.visitTerm(assertion.array);
    this.heap++;
    const [invP,, invE] = this.visitComplexAssertion(assertion.expression);
    this.heap--;
    const index = assertion.indexArgument !== null ? assertion.indexArgument.name : null;
    const everyP = transformEveryInvariant(arrayA, assertion.argument.name, index, invP, this.heap + 1);
    const everyE: Syntax.Expression = {
      type: 'LogicalExpression',
      operator: '&&',
      left: {
        type: 'InstanceOfExpression',
        left: arrayE,
        right: id('Array'),
        loc: assertion.loc
      },
      right: {
        type: 'CallExpression',
        callee: {
          type: 'MemberExpression',
          object: arrayE,
          property: { type: 'Literal', value: 'every', loc: assertion.loc },
          loc: assertion.loc
        },
        args: [{
          type: 'FunctionExpression',
          id: null,
          params: assertion.indexArgument !== null
            ? [assertion.argument, assertion.indexArgument]
            : [assertion.argument],
          requires: [],
          ensures: [],
          body: {
            type: 'BlockStatement',
            body: [{
              type: 'ReturnStatement',
              argument: invE,
              loc: assertion.expression.loc
            }],
            loc: assertion.expression.loc
          },
          freeVars: [],
          loc: assertion.expression.loc
        }],
        loc: assertion.loc
      },
      loc: assertion.loc
    };
    return [everyP, [], everyE, []];
  }

  visitInstanceOfAssertion (assertion: Syntax.InstanceOfAssertion): [P, AccessTriggers, Syntax.Expression, TestCode] {
    const [leftA, leftTriggers, leftE] = this.visitTerm(assertion.left);
    return [
      { type: 'InstanceOf', left: leftA, right: assertion.right.name },
      leftTriggers,
      { type: 'InstanceOfExpression', left: leftE, right: assertion.right, loc: assertion.loc },
      []
    ];
  }

  visitInAssertion (assertion: Syntax.InAssertion): [P, AccessTriggers, Syntax.Expression, TestCode] {
    const [objectA, objectTriggers, objectE] = this.visitTerm(assertion.object);
    const [propertyA, propertyTriggers, propertyE] = this.visitTerm(assertion.property);
    return [
      { type: 'HasProperty', object: objectA, property: propertyA },
      objectTriggers.concat(propertyTriggers),
      { type: 'InExpression', property: propertyE, object: objectE, loc: assertion.loc },
      []
    ];
  }

  visitUnaryAssertion (assertion: Syntax.UnaryAssertion): [P, AccessTriggers, Syntax.Expression, TestCode] {
    const [argP, argTriggers, argE] = this.visitComplexAssertion(assertion.argument);
    let retE: Syntax.Expression;
    if (argE.type === 'Literal' && argE.value === true) {
      retE = { type: 'Literal', value: false, loc: assertion.loc };
    } else if (argE.type === 'Literal' && argE.value === false) {
      retE = { type: 'Literal', value: true, loc: assertion.loc };
    } else {
      retE = { type: 'UnaryExpression', argument: argE, operator: '!', loc: assertion.loc };
    }
    return [not(argP), argTriggers, retE, []];
  }

  visitBinaryAssertion (assertion: Syntax.BinaryAssertion): [P, AccessTriggers, Syntax.Expression, TestCode] {
    switch (assertion.operator) {
      case '&&': {
        const [leftP, leftTriggers, leftE, leftT] = this.visitAssertion(assertion.left);
        const [rightP, rightTriggers, rightE, rightT] = this.visitAssertion(assertion.right);
        let retE: Syntax.Expression;
        if (leftE.type === 'Literal' && leftE.value === true) {
          retE = rightE;
        } else if (rightE.type === 'Literal' && rightE.value === true) {
          retE = leftE;
        } else {
          retE = { type: 'LogicalExpression', operator: '&&', left: leftE, right: rightE, loc: assertion.loc };
        }
        return [and(leftP, rightP), leftTriggers.concat(rightTriggers), retE, leftT.concat(rightT)];
      }
      case '||': {
        const [leftP, leftTriggers, leftE] = this.visitComplexAssertion(assertion.left);
        const [rightP, rightTriggers, rightE] = this.visitComplexAssertion(assertion.right);
        let retE: Syntax.Expression;
        if (leftE.type === 'Literal' && leftE.value === false) {
          retE = rightE;
        } else if (rightE.type === 'Literal' && rightE.value === false) {
          retE = leftE;
        } else {
          retE = { type: 'LogicalExpression', operator: '||', left: leftE, right: rightE, loc: assertion.loc };
        }
        return [or(leftP, rightP), leftTriggers.concat(rightTriggers), retE, []];
      }
    }
  }

  visitExpression (expr: Syntax.Expression): [A, Syntax.Expression] {
    try {
      return super.visitExpression(expr);
    } finally {
      this.heapHint(expr.loc);
    }
  }

  visitIdentifier (expr: Syntax.Identifier): [A, Syntax.Expression] {
    if (isMutable(expr)) {
      return [{ type: 'HeapReference', heap: this.heap, loc: expr.name }, expr];
    } else {
      return [expr.name, expr];
    }
  }

  visitLiteral (expr: Syntax.Literal): [A, Syntax.Expression] {
    return [expr, expr];
  }

  visitUnaryExpression (expr: Syntax.UnaryExpression): [A, Syntax.Expression] {
    const [argumentA, argumentE] = this.visitExpression(expr.argument);
    switch (expr.operator) {
      case '-':
        this.verifyType(expr, argumentA, argumentE, '-', 'number');
        break;
      case '+':
        this.verifyType(expr, argumentA, argumentE, '+', 'number');
        break;
      case '!':
        this.verifyType(expr, argumentA, argumentE, '!', 'boolean');
        break;
      case '~':
        this.verifyType(expr, argumentA, argumentE, '~', 'number');
        break;
    }
    return [
      { type: 'UnaryExpression', operator: expr.operator, argument: argumentA },
      { type: 'UnaryExpression', operator: expr.operator, argument: argumentE, loc: expr.loc }];
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): [A, Syntax.Expression] {
    const [leftA, leftE] = this.visitExpression(expr.left);
    const [rightA, rightE] = this.visitExpression(expr.right);
    switch (expr.operator) {
      case '<':
        this.verifyType(expr, leftA, leftE, '<', 'number or string');
        this.verifyType(expr, rightA, rightE, '<', 'number or string');
        break;
      case '<=':
        this.verifyType(expr, leftA, leftE, '<=', 'number or string');
        this.verifyType(expr, rightA, rightE, '<=', 'number or string');
        break;
      case '>':
        this.verifyType(expr, leftA, leftE, '>', 'number or string');
        this.verifyType(expr, rightA, rightE, '>', 'number or string');
        break;
      case '>=':
        this.verifyType(expr, leftA, leftE, '>=', 'number or string');
        this.verifyType(expr, rightA, rightE, '>=', 'number or string');
        break;
      case '<<':
        this.verifyType(expr, leftA, leftE, '<<', 'int');
        this.verifyType(expr, rightA, rightE, '<<', 'int');
        break;
      case '>>':
        this.verifyType(expr, leftA, leftE, '>>', 'int');
        this.verifyType(expr, rightA, rightE, '>>', 'int');
        break;
      case '>>>':
        this.verifyType(expr, leftA, leftE, '>>>', 'int');
        this.verifyType(expr, rightA, rightE, '>>>', 'int');
        break;
      case '+':
        this.verifyType(expr, leftA, leftE, '+', 'number or string');
        this.verifyType(expr, rightA, rightE, '+', 'number or string');
        break;
      case '-':
        this.verifyType(expr, leftA, leftE, '-', 'number');
        this.verifyType(expr, rightA, rightE, '-', 'number');
        break;
      case '*':
        this.verifyType(expr, leftA, leftE, '*', 'number');
        this.verifyType(expr, rightA, rightE, '*', 'number');
        break;
      case '/':
        this.verifyType(expr, leftA, leftE, '/', 'number');
        this.verifyType(expr, rightA, rightE, '/', 'number');
        break;
      case '%':
        this.verifyType(expr, leftA, leftE, '%', 'int');
        this.verifyType(expr, rightA, rightE, '%', 'int');
        break;
      case '|':
        this.verifyType(expr, leftA, leftE, '|', 'int');
        this.verifyType(expr, rightA, rightE, '|', 'int');
        break;
      case '^':
        this.verifyType(expr, leftA, leftE, '^', 'int');
        this.verifyType(expr, rightA, rightE, '^', 'int');
        break;
      case '&':
        this.verifyType(expr, leftA, leftE, '&', 'int');
        this.verifyType(expr, rightA, rightE, '&', 'int');
        break;
    }
    return [
      { type: 'BinaryExpression', operator: expr.operator, left: leftA, right: rightA },
      { type: 'BinaryExpression', operator: expr.operator, left: leftE, right: rightE, loc: expr.loc }];
  }

  visitLogicalExpression (expr: Syntax.LogicalExpression): [A, Syntax.Expression] {
    const [leftA, leftE] = this.visitExpression(expr.left);
    if (expr.operator === '&&') {
      const [rightHeap, rightPost, rightA, rightE] = this.tryExpression(truthy(leftA), expr.right);
      this.have(implies(truthy(leftA), rightPost));
      this.have(implies(falsy(leftA), heapEq(rightHeap, this.heap)));
      this.heap = rightHeap;
      return [
        { type: 'ConditionalExpression', test: truthy(leftA), consequent: rightA, alternate: leftA },
        { type: 'LogicalExpression', operator: expr.operator, left: leftE, right: rightE, loc: expr.loc }];
    } else {
      const [rightHeap, rightPost, rightA, rightE] = this.tryExpression(falsy(leftA), expr.right);
      this.have(implies(falsy(leftA), rightPost));
      this.have(implies(truthy(leftA), heapEq(rightHeap, this.heap)));
      this.heap = rightHeap;
      return [
        { type: 'ConditionalExpression', test: falsy(leftA), consequent: rightA, alternate: leftA },
        { type: 'LogicalExpression', operator: expr.operator, left: leftE, right: rightE, loc: expr.loc }];
    }
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): [A, Syntax.Expression] {
    const [testA, testE] = this.visitExpression(expr.test);
    const [lHeap, lPost, lVal, lExpr] = this.tryExpression(truthy(testA), expr.consequent);
    const [rHeap, rPost, rVal, rExpr] = this.tryExpression(falsy(testA), expr.alternate);
    const newHeap = Math.max(lHeap, rHeap);
    this.have(implies(truthy(testA), and(lPost, heapEq(newHeap, lHeap))));
    this.have(implies(falsy(testA), and(rPost, heapEq(newHeap, rHeap))));
    this.heap = newHeap;
    return [
      { type: 'ConditionalExpression', test: truthy(testA), consequent: lVal, alternate: rVal },
      { type: 'ConditionalExpression', test: testE, consequent: lExpr, alternate: rExpr, loc: expr.loc }];
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression): [A, Syntax.Expression] {
    if (expr.left.type !== 'Identifier') throw new Error('unsupported');
    const [rightA, rightE] = this.visitExpression(expr.right);
    this.have(heapStore(this.heap++, expr.left.name, rightA));
    return [rightA, { type: 'AssignmentExpression', left: expr.left, right: rightE, loc: expr.loc }];
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression): [A, Syntax.Expression] {
    let val = und;
    const seqExpr: Syntax.SequenceExpression = { type: 'SequenceExpression', expressions: [], loc: expr.loc };
    for (const e of expr.expressions) {
      const [exprA, exprE] = this.visitExpression(e);
      val = exprA;
      seqExpr.expressions.push(exprE);
    }
    return [val, seqExpr];
  }

  visitCallExpression (expr: Syntax.CallExpression): [A, Syntax.Expression] {
    // evaluate callee
    const [callee, calleeE] = this.visitExpression(expr.callee);

    // determine this argument
    let thisArg: A = (typeof callee !== 'string' && callee.type === 'MemberExpression') ? callee.object : und;

    // evaluate arguments
    const argsAE: Array<[A, Syntax.Expression]> = expr.args.map(e => this.visitExpression(e));
    const args: Array<A> = argsAE.map(([a]) => a);
    const argsE: Array<Syntax.Expression> = argsAE.map(([, e]) => e);

    const heap = this.heap;

    // apply call trigger
    this.have({ type: 'CallTrigger', callee, heap, thisArg, args, fuel: 1 });

    // verify precondition
    const pre: P = { type: 'Precondition', callee, heap, thisArg, args };
    const callExpr: Syntax.Expression = { type: 'CallExpression', callee: calleeE, args: argsE, loc: expr.loc };
    const callStmt: TestCode = [{ type: 'ExpressionStatement', expression: callExpr, loc: expr.loc }];
    this.verify(pre, callStmt, expr.loc, `precondition ${stringifyExpression(expr)}`);

    // assume postcondition
    this.have({ type: 'Postcondition', callee, heap, thisArg, args });

    // function call effect
    this.have(heapEq(this.heap + 1, { type: 'HeapEffect', callee, heap, thisArg, args }));
    this.heap++;
    return [{ type: 'CallExpression', callee, heap, thisArg, args }, callExpr];
  }

  visitNewExpression (expr: Syntax.NewExpression): [A, Syntax.Expression] {
    const argsAE: Array<[A, Syntax.Expression]> = expr.args.map(e => this.visitExpression(e));
    const args: Array<A> = argsAE.map(([a]) => a);
    const argsE: Array<Syntax.Expression> = argsAE.map(([, e]) => e);
    if (expr.callee.decl.type !== 'Class') throw new Error('Class not resolved');
    const clz: Syntax.ClassDeclaration = expr.callee.decl.decl;
    const object: A = { type: 'NewExpression', className: clz.id.name, args };
    const [invP] = this.assert(clz.invariant, this.heap, this.heap);
    const newCode: Syntax.Expression = { type: 'NewExpression', callee: expr.callee, args: argsE, loc: expr.loc };
    const testCode: TestCode = [{
      type: 'ExpressionStatement',
      expression: {
        type: 'CallExpression',
        callee: {
          type: 'MemberExpression',
          object: newCode,
          property: { type: 'Literal', value: 'checkInvariant', loc: expr.loc },
          loc: expr.loc
        },
        args: [],
        loc: expr.loc
      },
      loc: expr.loc
    }];
    this.verify(replaceVar('this', object, invP), testCode, expr.loc, `class invariant ${clz.id.name}`);
    return [object, newCode];
  }

  visitArrayExpression (expr: Syntax.ArrayExpression): [A, Syntax.Expression] {
    const elemsAE: Array<[A, Syntax.Expression]> = expr.elements.map(e => this.visitExpression(e));
    const elems: Array<A> = elemsAE.map(([a]) => a);
    const elemsE: Array<Syntax.Expression> = elemsAE.map(([, e]) => e);

    const object = this.freshVar();
    this.have({ type: 'InstanceOf', left: object, right: 'Array' });
    const lengthProp: A = { type: 'Literal', value: 'length' };
    const lengthVal: A = { type: 'Literal', value: elems.length };
    this.have(eq({ type: 'MemberExpression', object, property: lengthProp }, lengthVal));
    elems.forEach((property, idx) => {
      this.have(eq({ type: 'ArrayIndexExpression', array: object, index: { type: 'Literal', value: idx } },
                   elems[idx]));
    });
    return [object, { type: 'ArrayExpression', elements: elemsE, loc: expr.loc }];
  }

  visitObjectExpression (expr: Syntax.ObjectExpression): [A, Syntax.Expression] {
    const valuesAE: Array<[A, Syntax.Expression]> = expr.properties.map(({ value }) => this.visitExpression(value));
    const values: Array<A> = valuesAE.map(([a]) => a);
    const valuesE: Array<Syntax.Expression> = valuesAE.map(([, e]) => e);

    const object = this.freshVar();
    this.have({ type: 'InstanceOf', left: object, right: 'ObjectLiteral' });
    this.have({ type: 'HasProperties', object, properties: expr.properties.map(({ key }) => key) });
    expr.properties.forEach(({ key }, idx) => {
      this.have(eq({ type: 'MemberExpression', object, property: { type: 'Literal', value: key } },
                   values[idx]));
    });
    return [
      object,
      {
        type: 'ObjectExpression',
        properties: expr.properties.map(({ key }, idx) => ({ key, value: valuesE[idx] })),
        loc: expr.loc
      }
    ];
  }

  visitInstanceOfExpression (expr: Syntax.InstanceOfExpression): [A, Syntax.Expression] {
    const [leftA, leftE] = this.visitExpression(expr.left);
    const test: P = { type: 'InstanceOf', left: leftA, right: expr.right.name };
    const consequent: A = { type: 'Literal', value: true };
    const alternate: A = { type: 'Literal', value: false };
    return [
      { type: 'ConditionalExpression', test, consequent, alternate },
      { type: 'InstanceOfExpression', left: leftE, right: expr.right, loc: expr.loc }];
  }

  visitInExpression (expr: Syntax.InExpression): [A, Syntax.Expression] {
    const [objectA, objectE] = this.visitExpression(expr.object);
    const [propertyA, propertyE] = this.visitExpression(expr.property);
    const test: P = { type: 'HasProperty', object: objectA, property: propertyA };
    const consequent: A = { type: 'Literal', value: true };
    const alternate: A = { type: 'Literal', value: false };
    return [
      { type: 'ConditionalExpression', test, consequent, alternate },
      { type: 'InExpression', object: objectE, property: propertyE, loc: expr.loc }];
  }

  visitMemberExpression (expr: Syntax.MemberExpression): [A, Syntax.Expression] {
    const [objectA, objectE] = this.visitExpression(expr.object);
    const [propertyA, propertyE] = this.visitExpression(expr.property);
    this.have({ type: 'AccessTrigger', heap: this.heap, object: objectA, property: propertyA, fuel: 1 });
    this.verify(
      { type: 'HasProperty', object: objectA, property: propertyA },
      [this.check({ type: 'InExpression', object: objectE, property: propertyE, loc: expr.loc })],
      expr.loc,
      `${stringifyExpression(expr.object)} has property ${stringifyExpression(expr.property)}`);
    return [
      { type: 'MemberExpression', object: objectA, property: propertyA },
      { type: 'MemberExpression', object: objectE, property: propertyE, loc: expr.loc }];
  }

  visitFunctionExpression (expr: Syntax.FunctionExpression): [A, Syntax.Expression] {
    const callee = expr.id ? expr.id.name : this.freshVar();
    const [preTestCode, postTestCode, testBody, inlinedSpec, retVar] = this.visitFunction(expr, callee);
    this.have(inlinedSpec);
    const testFuncExpr: Syntax.Expression = {
      type: 'FunctionExpression',
      id: expr.id,
      params: expr.params,
      requires: [],
      ensures: [],
      body: testBody,
      freeVars: expr.freeVars,
      loc: expr.loc
    };
    if (preTestCode.length + postTestCode.length > 0) {
      return [callee, this.insertWrapper(testFuncExpr, expr.loc, expr.params, preTestCode, retVar, postTestCode)];
    } {
      return [callee, testFuncExpr];
    }
  }

  visitStatement (stmt: Syntax.Statement): BreakCondition {
    try {
      return super.visitStatement(stmt);
    } finally {
      this.heapHint(stmt.loc);
    }
  }

  tryStatement (pre: P, stmt: Syntax.Statement): [Heap, P, TestCode, BreakCondition] {
    return this.tryPre(pre, () => {
      return this.visitStatement(stmt);
    });
  }

  tryBlockStatement (pre: P, stmt: Syntax.BlockStatement): [Heap, P, Syntax.BlockStatement, BreakCondition] {
    const [heap, p, testCode, bc] = this.tryStatement(pre, stmt);
    if (testCode.length !== 1) throw new Error('expected single block statement');
    const blockStmt = testCode[0];
    if (blockStmt.type !== 'BlockStatement') throw new Error('expected single block statement');
    return [heap, p, blockStmt, bc];
  }

  visitVariableDeclaration (stmt: Syntax.VariableDeclaration): BreakCondition {
    const [initA, initE] = this.visitExpression(stmt.init);
    const testCode: TestCode = [{
      type: 'VariableDeclaration',
      id: stmt.id,
      init: initE,
      kind: 'let',
      loc: stmt.loc
    }];
    if (stmt.kind === 'const') {
      this.vars.add(stmt.id.name);
      this.have(eq(stmt.id.name, initA), testCode);
    } else {
      this.locs.add(stmt.id.name);
      this.have(heapStore(this.heap, stmt.id.name, initA), testCode);
      this.heap++;
    }
    this.heapHint(stmt.id.loc);
    return fls;
  }

  visitBlockStatement (stmt: Syntax.BlockStatement): BreakCondition {
    let bc = fls;
    const origBody = this.testBody;
    for (const s of stmt.body) {
      const [tHeap, tProp, tTC, tBC] = this.tryStatement(not(bc), s);
      this.have(implies(bc, heapEq(tHeap, this.heap)));
      this.have(implies(not(bc), tProp), tTC);
      this.heap = tHeap;
      bc = or(bc, tBC);
    }
    const newStatements = removeTestCodePrefix(origBody, this.testBody);
    this.testBody = origBody.concat({ type: 'BlockStatement', body: [...newStatements], loc: stmt.loc });
    return bc;
  }

  visitExpressionStatement (stmt: Syntax.ExpressionStatement): BreakCondition {
    const [, exprE] = this.visitExpression(stmt.expression);
    this.testBody = this.testBody.concat({ type: 'ExpressionStatement', expression: exprE, loc: stmt.loc });
    return fls;
  }

  visitAssertStatement (stmt: Syntax.AssertStatement): BreakCondition {
    const [assertP, assertTriggers, assertT] = this.assert(stmt.expression);
    this.tryPre(and(...assertTriggers), () => {
      this.verify(assertP, assertT, stmt.expression.loc, 'assert: ' + stringifyAssertion(stmt.expression));
    });
    const [assumeP,, assumeT] = this.assume(stmt.expression);
    this.assumptions.push(stringifyAssertion(stmt.expression));
    this.have(assumeP, assumeT);
    return fls;
  }

  visitIfStatement (stmt: Syntax.IfStatement): BreakCondition {
    const origBody = this.testBody;
    const [testA, testE] = this.visitExpression(stmt.test);
    this.verifyType(stmt.test, testA, testE, 'if', 'boolean');
    this.testBody = this.testBody.concat({ type: 'ExpressionStatement', expression: testE, loc: stmt.test.loc });
    const [lHeap, lProp, lTC, lBC] = this.tryBlockStatement(truthy(testA), stmt.consequent);
    const [rHeap, rProp, rTC, rBC] = this.tryBlockStatement(falsy(testA), stmt.alternate);
    const newHeap = Math.max(lHeap, rHeap);
    this.have(implies(truthy(testA), and(lProp, heapEq(newHeap, lHeap))));
    this.have(implies(falsy(testA), and(rProp, heapEq(newHeap, rHeap))));
    this.heap = newHeap;
    this.testBody = origBody.concat({
      type: 'IfStatement',
      test: testE,
      consequent: lTC,
      alternate: rTC,
      loc: stmt.loc
    });
    return or(and(truthy(testA), lBC), and(falsy(testA), rBC));
  }

  visitReturnStatement (stmt: Syntax.ReturnStatement): BreakCondition {
    const [argA, argE] = this.visitExpression(stmt.argument);
    if (!this.resVar) throw new Error('return outside function');
    this.have(eq(this.resVar, argA), [{ type: 'ReturnStatement', argument: argE, loc: stmt.loc }]);
    return tru;
  }

  visitWhileStatement (stmt: Syntax.WhileStatement): BreakCondition {
    // verify invariants on entry
    for (const inv of stmt.invariants) {
      const [invP, invTriggers, invT] = this.assert(inv, this.heap, this.heap);
      this.tryPre(and(...invTriggers), () => {
        this.verify(invP, invT, inv.loc, 'invariant on entry: ' + stringifyAssertion(inv));
      });
    }

    // havoc heap
    this.heap++;

    const startBody = this.testBody;

    // free mutable variables within the loop
    for (const fv of stmt.freeVars) {
      this.freeLoc(fv);
    }

    const startHeap = this.heap;
    const startProp = this.prop;

    // assume loop condition true and invariants true
    for (const inv of stmt.invariants) {
      const [invP,, invT] = this.assume(inv, this.heap, this.heap);
      this.have(invP, invT);
      this.assumptions.push(stringifyAssertion(inv));
    }
    let [testEnterA, testEnterE] = this.visitExpression(stmt.test);
    this.have(truthy(testEnterA), [{ type: 'ExpressionStatement', expression: testEnterE, loc: stmt.test.loc }]);

    // internal verification conditions
    const bcBody = this.visitStatement(stmt.body);

    // ensure invariants maintained
    for (const inv of stmt.invariants) {
      const [invP, invTriggers, invT] = this.assert(inv, this.heap, this.heap);
      this.tryPre(and(...invTriggers), () => {
        this.verify(invP, invT, inv.loc, 'invariant maintained: ' + stringifyAssertion(inv));
      });
    }

    // we are going to use the returned verification conditions and break condition
    // but we will ignore its effects
    this.heap = startHeap;
    this.prop = startProp;
    const whileBody = this.testBody[this.testBody.length - 1];
    if (whileBody.type !== 'BlockStatement') {
      throw new Error('expected while body to be single block statement');
    }
    this.testBody = startBody.concat([{
      type: 'WhileStatement',
      test: testEnterE,
      body: whileBody,
      invariants: stmt.invariants,
      freeVars: stmt.freeVars,
      loc: stmt.loc
    }]);

    for (const inv of stmt.invariants) {
      const [invP,, invT] = this.assume(inv, this.heap, this.heap);
      this.have(invP, invT);
    }
    // assume loop condition false and invariants true
    const [testExitA, testExitE] = this.visitExpression(stmt.test);
    this.have(falsy(testExitA), [{ type: 'ExpressionStatement', expression: testExitE, loc: stmt.test.loc }]);
    return and(truthy(testEnterA), bcBody);
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement): BreakCondition {
    this.testBody = this.testBody.concat({ type: 'DebuggerStatement', loc: stmt.loc });
    return fls;
  }

  functionAsSpec (f: Syntax.Function): Syntax.SpecAssertion {
    if (f.id === null) throw new Error('can only create specs for named functions');

    const pre: Syntax.Assertion = f.requires.reduceRight(
      (prev, req) => ({ type: 'BinaryAssertion', operator: '&&', left: req, right: prev, loc: req.loc }),
      { type: 'Literal', value: true, loc: f.loc });

    const retName = id(`_res_${uniqueIdentifier(f.loc)}`);

    const post: Syntax.Assertion = f.ensures.reduceRight(
      (prev: Syntax.Assertion, ens): Syntax.Assertion => ({
        type: 'BinaryAssertion',
        operator: '&&',
        left: ens.argument !== null
          ? replaceJSVarAssertion(ens.argument.name, retName, retName, ens.expression)
          : ens.expression,
        right: prev,
        loc: ens.loc
      }),
      { type: 'Literal', value: true, loc: f.loc });
    return {
      type: 'SpecAssertion',
      callee: f.id,
      hasThis: f.type === 'MethodDeclaration',
      args: f.params.map(param => param.name),
      pre,
      post: { argument: retName, expression: post, loc: f.loc },
      loc: f.loc
    };
  }

  visitFunctionBody (f: Syntax.Function, funcName: string, thisArg: string): [P, Syntax.BlockStatement] {

    // add "this" argument
    this.vars.add(thisArg);
    this.freeVar(thisArg);

    // add arguments to scope
    const args: Array<A> = [];
    for (const p of f.params) {
      args.push(p.name);
      this.vars.add(p.name);
      this.freeVar(p.name);
      this.heapHint(p.loc);
    }
    for (const fv of f.freeVars) {
      this.freeLoc(fv);
    }

    // add special result variable
    this.resVar = this.freshVar();

    let startBody = this.testBody;
    const startHeap = this.heap;
    this.oldHeap = this.heap;

    // assume non-rec spec if named function
    if (f.type !== 'MethodDeclaration' && f.id !== null) {
      const [fP,, fT] = this.assume(this.functionAsSpec(f));
      const funDecl: TestCode = [{
        type: 'FunctionDeclaration',
        id: f.id,
        params: f.params,
        requires: [],
        ensures: [],
        body: f.body,
        freeVars: f.freeVars,
        loc: f.loc
      }];
      this.have(fP, funDecl.concat(fT));
    }

    // assume preconditions
    for (const r of f.requires) {
      const [rP,, rT] = this.assume(r);
      startBody = startBody.concat(rT);
      this.have(rP, rT);
      this.assumptions.push(stringifyAssertion(r));
    }

    const preBodyCode = this.testBody;
    const preBodyProp = this.prop;

    // internal verification conditions
    this.visitBlockStatement(f.body);

    const blockBody = removeTestCodePrefix(preBodyCode, this.testBody);
    if (blockBody.length !== 1) throw new Error('expected single block statement');
    const blockStmt = blockBody[0];
    if (blockStmt.type !== 'BlockStatement') throw new Error('expected single block statement');

    this.have(eq(this.resVar, { type: 'CallExpression', callee: funcName, heap: startHeap, thisArg, args }));

    // assume function body and call
    if (f.type === 'MethodDeclaration') {
      this.testBody = startBody.concat([{
        type: 'VariableDeclaration',
        id: id(this.resVar, f.loc),
        init: {
          type: 'CallExpression',
          callee: {
            type: 'MemberExpression',
            object: id(thisArg),
            property: { type: 'Literal', value: f.id.name, loc: f.loc },
            loc: f.loc
          },
          args: f.params,
          loc: f.loc
        },
        kind: 'let',
        loc: f.loc
      }]);
    } else {
      this.testBody = startBody.concat([{
        type: 'FunctionDeclaration',
        id: id(funcName),
        params: f.params,
        requires: [],
        ensures: [],
        body: f.body,
        freeVars: f.freeVars,
        loc: f.loc
      }, {
        type: 'VariableDeclaration',
        id: id(this.resVar),
        init: {
          type: 'CallExpression',
          callee: id(funcName),
          args: f.params,
          loc: f.loc
        },
        kind: 'let',
        loc: f.loc
      }]);
    }

    // ensure post conditions
    for (const ens of f.ensures) {
      const ens2 = ens.argument !== null
          ? replaceJSVarAssertion(ens.argument.name, id(this.resVar), id(this.resVar), ens.expression)
          : ens.expression;
      const aliases: { [from: string]: string } = ens.argument !== null ? { [ens.argument.name]: this.resVar } : {};
      const [ensP, ensTriggers, ensT] = this.assert(ens2);
      this.tryPre(and(...ensTriggers), () => {
        this.verify(ensP, ensT, ens.loc, stringifyAssertion(ens.expression), aliases);
      });
    }
    this.vcs.forEach(vc => {
      vc.setDescription((f.id ? f.id.name : 'func') + ': ' + vc.getDescription());
    });

    // remove context and preconditions from prop for purpose of inlining
    return [removePrefix(preBodyProp, this.prop), blockStmt];
  }

  createFunctionBodyInliner (): VCGenerator {
    return new VCGenerator(this.classes,
                           this.heap + 1,
                           this.heap + 1,
                           new Set([...this.locs]),
                           new Set([...this.vars]),
                           [...this.assumptions],
                           this.heapHints,
                           this.prop);
  }

  visitFunction (fun: Syntax.Function, funcName: string):
                [TestCode, TestCode, Syntax.BlockStatement, P, Syntax.Identifier] {
    if (fun.type !== 'MethodDeclaration') {
      this.vars.add(funcName);
    }
    const inliner = this.createFunctionBodyInliner();
    inliner.testBody = this.testBody;
    const thisArg = this.freshThisVar();
    const renamedFunc = replaceJSVarFunction('this', id(thisArg), id(thisArg), fun);
    let [inlinedP, inlinedBlock] = inliner.visitFunctionBody(renamedFunc, funcName, thisArg);
    inlinedBlock = replaceJSVarBlock(thisArg, id('this'), id('this'), inlinedBlock);
    inliner.vcs.forEach(vc => vc.setDescription(vc.getDescription().replace(thisArg, 'this')));
    this.vcs = this.vcs.concat(inliner.vcs);
    const existsLocs = new Set([...inliner.locs].filter(l => !this.locs.has(l)));
    const existsVars = new Set([...inliner.vars].filter(v => {
      return !this.vars.has(v) && !fun.params.some(n => n.name === v);
    }));

    const pre: Array<[P, AccessTriggers, TestCode]> = fun.requires.map(req =>
      this.assert(req, this.heap + 1, this.heap + 1));
    const retVar = this.testVar(fun.loc);
    const post: Array<[P, AccessTriggers, TestCode]> = fun.ensures.map(ens => {
      let ens2 = ens.expression;
      if (ens.argument !== null) {
        ens2 = replaceJSVarAssertion(ens.argument.name,
                                     id(retVar, ens.argument.loc), id(retVar, ens.argument.loc), ens2);
      }
      return this.assume(ens2, this.heap + 1, inliner.heap);
    });

    const args: Array<string> = fun.params.map(p => p.name);
    const preP = pre.reduceRight((prev, [p]) => and(prev, replaceVar('this', thisArg, p)), tru);
    const postP = post.reduceRight((post, [p]) => {
      const p2 = replaceVar('this', thisArg, p);
      return and(post, replaceResultWithCall(funcName, this.heap + 1, thisArg, args, retVar, p2));
    }, eraseTriggersProp(inlinedP));
    const inlinedSpec = transformSpec(funcName, thisArg, args, preP, postP,
                                      this.heap + 1, inliner.heap, existsLocs, existsVars);

    return [flatMap(pre, ([,,c]) => c), flatMap(post, ([,,c]) => c), inlinedBlock, inlinedSpec, id(retVar)];
  }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration): BreakCondition {
    const [preTestCode, postTestCode, blockStmt, inlinedSpec, retVar] = this.visitFunction(stmt, stmt.id.name);
    const testCode: Array<Syntax.Statement> = [{
      type: 'FunctionDeclaration',
      id: stmt.id,
      params: stmt.params,
      requires: [],
      ensures: [],
      body: blockStmt,
      freeVars: stmt.freeVars,
      loc: stmt.loc
    }];
    if (preTestCode.length + postTestCode.length > 0) {
      testCode.push({
        type: 'ExpressionStatement',
        expression: {
          type: 'AssignmentExpression',
          left: stmt.id,
          right: this.insertWrapper(stmt.id, stmt.loc, stmt.params, preTestCode, retVar, postTestCode),
          loc: stmt.loc
        },
        loc: stmt.loc
      });
    }
    this.have(inlinedSpec, testCode);
    return fls;
  }

  visitClassDeclaration (stmt: Syntax.ClassDeclaration): BreakCondition {
    const startProp = this.prop;
    const startBody = this.testBody;

    // first assume non-recursive specs of methods
    const methodNames: Array<string> = [];
    const methodSpecs: Array<P> = [];
    const methodTestBodies: Array<Syntax.MethodDeclaration> = [];
    for (const method of stmt.methods) {
      method.requires.push({
        type: 'InstanceOfAssertion',
        left: id('this', stmt.id.loc),
        right: stmt.id,
        loc: method.loc
      });
      const globalMethodName = `${stmt.id.name}.${method.id.name}`;
      methodNames.push(method.id.name);
      const [fP,, fT] = this.assume(this.functionAsSpec(method));
      methodSpecs.push(replaceVar(method.id.name, globalMethodName, fP));
      methodTestBodies.push({
        type: 'MethodDeclaration',
        id: method.id,
        params: method.params,
        requires: [],
        ensures: [],
        body: {
          type: 'BlockStatement',
          body: [{
            type: 'FunctionDeclaration',
            id: method.id,
            params: method.params,
            requires: [],
            ensures: [],
            body: method.body,
            freeVars: method.freeVars,
            loc: method.loc
          }, ...fT, {
            type: 'ReturnStatement',
            argument: {
              type: 'CallExpression',
              callee: {
                type: 'MemberExpression',
                object: method.id,
                property: { type: 'Literal', value: 'call', loc: method.loc },
                loc: method.loc
              },
              args: [id('this'), ...method.params],
              loc: method.loc
            },
            loc: method.loc
          }],
          loc: method.loc
        },
        freeVars: method.freeVars,
        className: stmt.id.name,
        loc: method.loc
      });
    }
    const [invP,, invT] = this.assert(stmt.invariant, this.heap, this.heap);
    this.classes.add({ cls: stmt.id.name, fields: stmt.fields, methods: methodNames });
    this.have(and(...methodSpecs), this.classDeclarationCode(stmt, methodTestBodies, invT));
    this.have(transformClassInvariant(stmt.id.name, 'this', stmt.fields, invP, this.heap));

    // verify inidivual function bodies

    const preMethodProp = this.prop;
    const preMethodBody = this.testBody;

    const inlinedMethodSpecs: Array<P> = [];
    const inlinedMethodTestBodies: Array<Syntax.MethodDeclaration> = [];
    for (const method of stmt.methods) {
      const globalMethodName = `${stmt.id.name}.${method.id.name}`;
      this.prop = preMethodProp;
      this.testBody = preMethodBody;

      const [preTestCode, postTestCode, blockStmt, inlinedSpec, retVar] = this.visitFunction(method, globalMethodName);

      inlinedMethodSpecs.push(inlinedSpec);
      inlinedMethodTestBodies.push({
        type: 'MethodDeclaration',
        id: method.id,
        params: method.params,
        requires: [],
        ensures: [],
        body: preTestCode.length + postTestCode.length === 0 ? blockStmt : {
          type: 'BlockStatement',
          body: [{
            type: 'FunctionDeclaration',
            id: method.id,
            params: method.params,
            requires: [],
            ensures: [],
            body: blockStmt,
            freeVars: method.freeVars,
            loc: method.loc
          }, {
            type: 'ExpressionStatement',
            expression: {
              type: 'AssignmentExpression',
              left: method.id,
              right: this.insertWrapper(method.id, method.loc, method.params, preTestCode, retVar, postTestCode),
              loc: stmt.loc
            },
            loc: stmt.loc
          }, {
            type: 'ReturnStatement',
            argument: {
              type: 'CallExpression',
              callee: {
                type: 'MemberExpression',
                object: method.id,
                property: { type: 'Literal', value: 'call', loc: method.loc },
                loc: method.loc
              },
              args: [id('this'), ...method.params],
              loc: method.loc
            },
            loc: method.loc
          }],
          loc: method.loc
        },
        freeVars: method.freeVars,
        className: stmt.id.name,
        loc: method.loc
      });
    }

    // now use rewritten function bodies and assume inlined specs for methods
    this.prop = startProp;
    this.testBody = startBody;

    this.have(and(...inlinedMethodSpecs), this.classDeclarationCode(stmt, inlinedMethodTestBodies, invT));
    this.have(transformClassInvariant(stmt.id.name, 'this', stmt.fields, invP, this.heap));

    return fls;
  }

  classDeclarationCode (clsDef: Syntax.ClassDeclaration, methods: Array<Syntax.MethodDeclaration>,
                        invT: TestCode): TestCode {
    const checkInvariant: Array<Syntax.MethodDeclaration> = [{
      type: 'MethodDeclaration',
      id: id('checkInvariant', clsDef.invariant.loc),
      params: [],
      requires: [],
      ensures: [],
      body: {
        type: 'BlockStatement',
        body: [...invT],
        loc: clsDef.invariant.loc
      },
      freeVars: [],
      className: clsDef.id.name,
      loc: clsDef.invariant.loc
    }];
    return [{
      type: 'ClassDeclaration',
      id: clsDef.id,
      fields: clsDef.fields,
      invariant: { type: 'Literal', value: true, loc: clsDef.invariant.loc },
      methods: checkInvariant.concat(methods),
      loc: clsDef.loc
    }];
  }

  visitProgram (prog: Syntax.Program): BreakCondition {

    // go through all statements
    for (const stmt of prog.body) {
      if (stmt.type === 'FunctionDeclaration') {
        // function should maintain invariants
        prog.invariants.forEach(inv => {
          stmt.requires.push(inv);
          stmt.ensures.push({ argument: null, expression: inv, loc: inv.loc });
        });
      }
      this.visitStatement(stmt);
    }

    // main program body needs to establish invariants
    for (const inv of prog.invariants) {
      const [assertP, assertTriggers, assertT] = this.assert(inv);
      this.tryPre(and(...assertTriggers), () => {
        this.verify(assertP, assertT, inv.loc, 'initially: ' + stringifyAssertion(inv));
      });
      const [assumeP,, assumeT] = this.assume(inv);
      this.have(assumeP, assumeT);
      this.assumptions.push(stringifyAssertion(inv));
    }
    return fls;
  }
}

export function vcgenProgram (prog: Syntax.Program): Array<VerificationCondition> {
  const { classes, heap, locs, vars, prop } = generatePreamble();
  const vcgen = new VCGenerator(classes, heap, heap, locs, vars, [], [], prop);
  vcgen.visitProgram(prog);
  return vcgen.vcs;
}
