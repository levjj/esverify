import VerificationCondition from './verification';
import { Syntax, Visitor, stringifyExpr, loopTestingCode, checkPreconditions, isMutable,
         replaceVar as replaceJSVar, nullLoc } from './javascript';
import { A, P, Classes, Vars, FreeVars, Locs, Heap, transformSpec, und, tru, fls, truthy, falsy,
         implies, and, or, eq, not, heapEq, heapStore, removePrefix, replaceVar,
         replaceResultWithCall, transformClassInvariant } from './logic';
import { translateExpression } from './assertions';
import { eraseTriggersProp } from './qi';

type BreakCondition = P;

class VCGenerator extends Visitor<A, BreakCondition> {
  classes: Classes;
  oldHeap: Heap;
  heap: Heap;
  locs: Locs;
  vars: Vars;
  prop: P;
  vcs: Array<VerificationCondition>;
  resVar: string | null;
  freeVars: FreeVars;
  testBody: ReadonlyArray<Syntax.Statement>;

  constructor (classes: Classes, oldHeap: Heap, heap: Heap, locs: Locs, vars: Vars, prop: P = tru) {
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
  }

  have (p: P): void {
    this.prop = and(this.prop, p);
  }

  tryPre<T> (pre: P, fn: () => T): [Heap, P, T] {
    const origPre = this.prop;
    const origHeap = this.heap;
    const origBody = this.testBody;
    try {
      this.have(pre);
      const r = fn();
      return [this.heap, removePrefix(and(origPre, pre), this.prop), r];
    } finally {
      this.prop = origPre;
      this.heap = origHeap;
      this.testBody = origBody;
    }
  }

  tryExpression (pre: P, expr: Syntax.Expression): [Heap, P, A] {
    return this.tryPre(pre, () => {
      return this.visitExpression(expr);
    });
  }

  freshVar (): string {
    let i = 0;
    while (this.vars.has(`_tmp_${i}`)) i++;
    this.vars.add(`_tmp_${i}`);
    return `_tmp_${i}`;
  }

  freeVar (name: string) {
    this.freeVars.push(name);
    this.testBody = this.testBody.concat([{
      type: 'VariableDeclaration',
      id: {
        type: 'Identifier',
        name,
        decl: { type: 'Unresolved' },
        loc: nullLoc(),
        refs: [],
        isWrittenTo: false
      },
      init: {
        type: 'Identifier',
        name: `__free__${name}`,
        decl: { type: 'Unresolved' },
        loc: nullLoc(),
        refs: [],
        isWrittenTo: false
      },
      kind: 'const',
      loc: nullLoc()
    }, {
      type: 'VariableDeclaration',
      id: {
        type: 'Identifier',
        name: `old_${name}`,
        decl: { type: 'Unresolved' },
        loc: nullLoc(),
        refs: [],
        isWrittenTo: false
      },
      init: {
        type: 'Identifier',
        name,
        decl: { type: 'Unresolved' },
        loc: nullLoc(),
        refs: [],
        isWrittenTo: false
      },
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
        left: {
          type: 'Identifier',
          name,
          decl: { type: 'Unresolved' },
          loc: nullLoc(),
          refs: [],
          isWrittenTo: false
        },
        right: {
          type: 'Identifier',
          name: `__free__${name}`,
          decl: { type: 'Unresolved' },
          loc: nullLoc(),
          refs: [],
          isWrittenTo: false
        },
        loc: nullLoc()
      },
      loc: nullLoc()
    }, {
      type: 'VariableDeclaration',
      id: {
        type: 'Identifier',
        name: `old_${name}`,
        decl: { type: 'Unresolved' },
        loc: nullLoc(),
        refs: [],
        isWrittenTo: false
      },
      init: {
        type: 'Identifier',
        name,
        decl: { type: 'Unresolved' },
        loc: nullLoc(),
        refs: [],
        isWrittenTo: false
      },
      kind: 'const',
      loc: nullLoc()
    }]);
  }

  verify (vc: P, loc: Syntax.SourceLocation, desc: string, testBody: Array<Syntax.Statement> = []) {
    this.vcs.push(new VerificationCondition(this.classes, this.heap, this.locs, this.vars, and(this.prop, not(vc)),
                                            loc, desc, this.freeVars, this.testBody.concat(testBody)));
  }

  visitIdentifier (expr: Syntax.Identifier): A {
    if (isMutable(expr)) {
      return { type: 'HeapReference', heap: this.heap, loc: expr.name };
    } else {
      return expr.name;
    }
  }

  visitLiteral (expr: Syntax.Literal): A {
    return expr;
  }

  visitUnaryExpression (expr: Syntax.UnaryExpression): A {
    return { type: 'UnaryExpression', operator: expr.operator, argument: this.visitExpression(expr) };
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): A {
    return {
      type: 'BinaryExpression',
      operator: expr.operator,
      left: this.visitExpression(expr.left),
      right:  this.visitExpression(expr.right)
    };
  }

  visitLogicalExpression (expr: Syntax.LogicalExpression): A {
    const l = this.visitExpression(expr.left);
    if (expr.operator === '&&') {
      const [rHeap, rPost, rVal] = this.tryExpression(truthy(l), expr.right);
      this.have(implies(truthy(l), rPost));
      this.have(implies(falsy(l), heapEq(rHeap, this.heap)));
      this.heap = rHeap;
      return { type: 'ConditionalExpression', test: truthy(l), consequent: rVal, alternate: l };
    } else {
      const [rHeap, rPost, rVal] = this.tryExpression(falsy(l), expr.right);
      this.have(implies(falsy(l), rPost));
      this.have(implies(truthy(l), heapEq(rHeap, this.heap)));
      this.heap = rHeap;
      return { type: 'ConditionalExpression', test: falsy(l), consequent: rVal, alternate: l };
    }
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): A {
    const t = this.visitExpression(expr.test);
    const [lHeap, lPost, lVal] = this.tryExpression(truthy(t), expr.consequent);
    const [rHeap, rPost, rVal] = this.tryExpression(falsy(t), expr.alternate);
    const newHeap = Math.max(lHeap, rHeap);
    this.have(implies(truthy(t), and(lPost, heapEq(newHeap, lHeap))));
    this.have(implies(falsy(t), and(rPost, heapEq(newHeap, rHeap))));
    this.heap = newHeap;
    return { type: 'ConditionalExpression', test: truthy(t), consequent: lVal, alternate: rVal };
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression): A {
    const t = this.visitExpression(expr.right);
    this.have(heapStore(this.heap++, expr.left.name, t));
    return t;
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression): A {
    let val = und;
    for (const e of expr.expressions) {
      val = this.visitExpression(e);
    }
    return val;
  }

  visitCallExpression (expr: Syntax.CallExpression): A {
    // evaluate callee
    const callee = this.visitExpression(expr.callee);

    // evaluate arguments
    const args: Array<A> = expr.args.map(e => this.visitExpression(e));
    const heap = this.heap;

    // apply call trigger
    this.have({ type: 'CallTrigger', callee, heap, args, fuel: 1 });

    // verify precondition
    const pre: P = { type: 'Precondition', callee, heap, args };
    this.verify(pre, expr.loc, `precondition ${stringifyExpr(expr)}`);

    // assume postcondition
    this.have({ type: 'Postcondition', callee, heap, args });

    // function call effect
    this.have(heapEq(this.heap + 1, { type: 'HeapEffect', callee, heap, args }));

    return { type: 'CallExpression', callee, heap: this.heap++, args };
  }

  visitOldIdentifier (expr: Syntax.OldIdentifier): A {
    throw new Error('Only possible in assertion context');
  }

  visitSpecExpression (expr: Syntax.SpecExpression): A {
    throw new Error('Only possible in assertion context');
  }

  visitPureExpression (expr: Syntax.PureExpression): A {
    throw new Error('Only possible in assertion context');
  }

  visitNewExpression (expr: Syntax.NewExpression): A {
    const args: Array<A> = expr.args.map(e => this.visitExpression(e));

    if (expr.callee.decl.type !== 'Class') throw new Error('Class not resolved');
    const clz: Syntax.ClassDeclaration = expr.callee.decl.decl;
    const object: A = { type: 'NewExpression', className: clz.id.name, args };
    const inv: P = translateExpression(this.heap, this.heap, clz.invariant);
    this.verify(replaceVar('this', object, inv), expr.loc, `class invariant ${clz.id.name}`);
    return object;
  }

  visitInstanceOfExpression (expr: Syntax.InstanceOfExpression): A {
    const test: P = { type: 'InstanceOf', left: this.visitExpression(expr.left), right: expr.right.name };
    const consequent: A = { type: 'Literal', value: true };
    const alternate: A = { type: 'Literal', value: false };
    return { type: 'ConditionalExpression', test, consequent, alternate };
  }

  visitInExpression (expr: Syntax.InExpression): A {
    const object = this.visitExpression(expr.object);
    const property = this.visitExpression(expr.property);
    const test: P = { type: 'HasProperty', object, property };
    const consequent: A = { type: 'Literal', value: true };
    const alternate: A = { type: 'Literal', value: false };
    return { type: 'ConditionalExpression', test, consequent, alternate };
  }

  visitMemberExpression (expr: Syntax.MemberExpression): A {
    const object = this.visitExpression(expr.object);
    const property = this.visitExpression(expr.property);
    this.have({ type: 'AccessTrigger', heap: this.heap, object: object, fuel: 1 });
    this.verify(
      { type: 'HasProperty', object, property }, expr.loc,
      `${stringifyExpr(expr.object)} has property ${stringifyExpr(expr.property)}`,
      [{
        type: 'AssertStatement',
        loc: expr.loc,
        expression: { type: 'InExpression', object: expr.object, property: expr.property, loc: expr.loc }
      }]);
    return { type: 'MemberExpression', object, property };
  }

  visitFunctionExpression (expr: Syntax.FunctionExpression): A {
    const callee = expr.id ? expr.id.name : this.freshVar();
    this.visitFunction(expr, callee);
    return callee;
  }

  tryStatement (pre: P, stmt: Syntax.Statement): [Heap, P, BreakCondition] {
    return this.tryPre(pre, () => {
      return this.visitStatement(stmt);
    });
  }

  transformDef (f: Syntax.Function, callee: string, heap: number, toHeap: number = heap + 1,
                existsLocs: Locs = new Set(), existsVars: Vars = new Set(), q: P = tru): P {
    const args: Array<string> = f.params.map(p => p.name);
    let req = tru;
    for (const r of f.requires) {
      req = and(req, translateExpression(heap, heap, r));
    }
    let ens = q;
    for (const s of f.ensures) {
      const s2: P = translateExpression(heap, toHeap, s.expression);
      ens = and(ens, replaceResultWithCall(callee, heap, args, s.argument, s2));
    }
    return transformSpec(callee, args, req, ens, heap, toHeap, existsLocs, existsVars, q);
  }

  visitFunctionBody (f: Syntax.Function, callee: string) {

    // add function name to scope
    this.vars.add(callee);

    // add arguments to scope
    const args: Array<A> = [];
    for (const p of f.params) {
      args.push(p.name);
      this.vars.add(p.name);
      this.freeVar(p.name);
    }
    for (const fv of f.freeVars) {
      this.freeLoc(fv);
    }

    // add special result variable
    this.resVar = this.freshVar();

    // assume preconditions
    for (const r of f.requires) {
      const tr = translateExpression(this.heap, this.heap, r);
      this.prop = and(this.prop, tr);
    }

    // assume non-rec spec
    this.prop = and(this.prop, this.transformDef(f, callee, this.heap + 1));
    const pre = this.prop;

    const startHeap = this.heap;
    const startBody = this.testBody;

    // internal verification conditions
    const res = this.visitStatement(f.body);

    this.testBody = startBody.concat([{
      type: 'VariableDeclaration',
      id: {
        type: 'Identifier',
        name: this.resVar,
        decl: { type: 'Unresolved' },
        loc: f.loc,
        refs: [],
        isWrittenTo: false
      },
      init: {
        type: 'CallExpression',
        callee: f.type === 'FunctionExpression' ? f : f.id,
        args: f.params,
        loc: f.loc
      },
      kind: 'const',
      loc: f.loc
    }]);

    // ensure post conditions
    this.have(eq(this.resVar, { type: 'CallExpression', callee, heap: startHeap, args }));

    for (const ens of f.ensures) {
      const ens2 = ens.argument ? replaceJSVar(ens.argument.name, this.resVar, ens.expression) : ens.expression;
      const ti = translateExpression(startHeap, this.heap, ens2);
      this.verify(ti, ens.loc, stringifyExpr(ens.expression),
                  [{ type: 'AssertStatement', loc: ens.loc, expression: ens2 }]);
    }
    this.vcs.forEach(vc => {
      vc.description = (f.id ? f.id.name : 'func') + ': ' + vc.description;
    });

    // remove preconditions from prop for purpose of inlining
    this.prop = removePrefix(pre, this.prop);
    return res;
  }

  visitVariableDeclaration (stmt: Syntax.VariableDeclaration): BreakCondition {
    const origBody = this.testBody;
    this.testBody = this.testBody.concat({ type: 'ExpressionStatement', expression: stmt.init, loc: stmt.init.loc });
    const t = this.visitExpression(stmt.init);
    if (stmt.kind === 'const') {
      this.vars.add(stmt.id.name);
      this.have(eq(stmt.id.name, t));
      this.testBody = origBody.concat([stmt]);
    } else {
      this.locs.add(stmt.id.name);
      this.have(heapStore(this.heap, stmt.id.name, t));
      this.heap++;
      this.testBody = origBody.concat(stmt);
    }
    return fls;
  }

  visitBlockStatement (stmt: Syntax.BlockStatement): BreakCondition {
    let bc = fls;
    const origBody = this.testBody;
    for (const s of stmt.body) {
      const [tHeap, tProp, tBC] = this.tryStatement(not(bc), s);
      this.testBody = this.testBody.concat(s);
      this.have(implies(bc, heapEq(tHeap, this.heap)));
      this.have(implies(not(bc), tProp));
      this.heap = tHeap;
      bc = or(bc, tBC);
    }
    this.testBody = origBody.concat(stmt);
    return bc;
  }

  visitExpressionStatement (stmt: Syntax.ExpressionStatement): BreakCondition {
    this.testBody = this.testBody.concat(stmt);
    this.visitExpression(stmt.expression);
    return fls;
  }

  visitAssertStatement (stmt: Syntax.AssertStatement): BreakCondition {
    const a = translateExpression(this.oldHeap, this.heap, stmt.expression);
    this.verify(a, stmt.loc, 'assert: ' + stringifyExpr(stmt.expression), [stmt]);
    this.have(a);
    return fls;
  }

  visitIfStatement (stmt: Syntax.IfStatement): BreakCondition {
    const origBody = this.testBody;
    this.testBody = this.testBody.concat({ type: 'ExpressionStatement', expression: stmt.test, loc: stmt.test.loc });
    const t = this.visitExpression(stmt.test);
    const [lHeap, lProp, lBC] = this.tryStatement(truthy(t), stmt.consequent);
    const [rHeap, rProp, rBC] = this.tryStatement(falsy(t), stmt.alternate);
    const newHeap = Math.max(lHeap, rHeap);
    this.have(implies(truthy(t), and(lProp, heapEq(newHeap, lHeap))));
    this.have(implies(falsy(t), and(rProp, heapEq(newHeap, rHeap))));
    this.heap = newHeap;
    this.testBody = origBody.concat(stmt);
    return or(and(truthy(t), lBC), and(falsy(t), rBC));
  }

  visitReturnStatement (stmt: Syntax.ReturnStatement): BreakCondition {
    const origBody = this.testBody;
    this.testBody = this.testBody.concat({
      type: 'ExpressionStatement',
      expression: stmt.argument,
      loc: stmt.argument.loc });
    const t = this.visitExpression(stmt.argument);
    if (!this.resVar) throw new Error('return outside function');
    this.have(eq(this.resVar, t));
    this.testBody = origBody.concat(stmt);
    return tru;
  }

  visitWhileStatement (stmt: Syntax.WhileStatement): BreakCondition {
    // verify invariants on entry
    for (const inv of stmt.invariants) {
      const t = translateExpression(this.oldHeap, this.heap, inv);
      this.verify(t, inv.loc, 'invariant on entry: ' + stringifyExpr(inv),
                  [{ type: 'AssertStatement', loc: inv.loc, expression: inv }]);
    }

    // havoc heap
    this.heap++;

    const startHeap = this.heap;
    const startProp = this.prop;
    const startBody = this.testBody;

    // assume loop condition true and invariants true
    this.testBody = this.testBody.concat({ type: 'ExpressionStatement', expression: stmt.test, loc: stmt.test.loc });

    let testEnter = this.visitExpression(stmt.test);
    this.have(truthy(testEnter));
    for (const inv of stmt.invariants) {
      this.have(translateExpression(startHeap, this.heap, inv)); // TODO old() for previous iteration
    }

    // internal verification conditions
    const bcBody = this.visitStatement(stmt.body);

    // ensure invariants maintained
    for (const inv of stmt.invariants) {
      const ti = translateExpression(startHeap, this.heap, inv);
      const assertCode: Syntax.Statement = { type: 'AssertStatement', loc: inv.loc, expression: inv };
      this.verify(ti, inv.loc, 'invariant maintained: ' + stringifyExpr(inv),
                  loopTestingCode(stmt).concat([assertCode]));
    }

    // we are going to use the returned verification conditions and break condition
    // but we will ignore its effects
    this.heap = startHeap;
    this.prop = startProp;
    this.testBody = startBody.concat(stmt);

    // assume loop condition false and invariants true
    const testExit = this.visitExpression(stmt.test);
    this.have(falsy(testExit));
    for (const inv of stmt.invariants) {
      this.have(translateExpression(this.oldHeap, this.heap, inv));
    }
    return and(truthy(testEnter), bcBody);
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement): BreakCondition {
    return fls;
  }

  visitFunction (fun: Syntax.Function, callee: string): void {
    this.vars.add(callee);
    const inliner = new VCGenerator(this.classes, this.heap + 1, this.heap + 1,
                                    new Set([...this.locs]),
                                    new Set([...this.vars]), this.prop);
    inliner.testBody = this.testBody;
    inliner.visitFunctionBody(fun, callee);
    this.vcs = this.vcs.concat(inliner.vcs);
    const existsLocs = new Set([...inliner.locs].filter(l => !this.locs.has(l)));
    const existsVars = new Set([...inliner.vars].filter(v => {
      return !this.vars.has(v) && !fun.params.some(n => n.name === v);
    }));
    const inlinedP: P = eraseTriggersProp(inliner.prop);
    const inlinedSpec: P = this.transformDef(fun, callee, this.heap + 1, inliner.heap,
                                             existsLocs, existsVars, inlinedP);
    this.have(inlinedSpec);
  }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration): BreakCondition {
    this.testBody = this.testBody.concat([checkPreconditions(stmt)]);
    this.visitFunction(stmt, stmt.id.name);
    return fls;
  }

  visitClassDeclaration (stmt: Syntax.ClassDeclaration): BreakCondition {
    this.classes.add({ cls: stmt.id.name, fields: stmt.fields });
    this.testBody = this.testBody.concat([stmt]);
    const inv: P = translateExpression(this.heap, this.heap, stmt.invariant);
    this.have(transformClassInvariant(stmt.id.name, stmt.fields, inv, this.heap));
    return fls;
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
      const ti = translateExpression(this.heap, this.heap, inv);
      this.verify(ti, inv.loc, 'initially: ' + stringifyExpr(inv),
                  [{ type: 'AssertStatement', loc: inv.loc, expression: inv }]);
    }
    return fls;
  }
}

export function vcgenProgram (prog: Syntax.Program): Array<VerificationCondition> {
  const vcgen = new VCGenerator(new Set(), 0, 0, new Set(), new Set(), tru);
  vcgen.visitProgram(prog);
  return vcgen.vcs;
}
