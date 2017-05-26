import VerificationCondition from "./verification";
import { Syntax, Visitor, stringifyExpr, loopTestingCode, checkPreconditions, replaceFunctionResult, isMutable, convertToAssignment, replaceThis } from "./javascript";
import { A, P, Classes, Vars, Locs, Heap, transformSpec, und, tru, fls, truthy, falsy, implies, and, or, eq, not, heapEq, heapStore, removePrefix, transformClassInvariant } from "./logic";
import { eraseTriggersProp } from "./qi";

class PureContextError extends Error {
  constructor() { super("not supported in pure functional context"); }
}

class QuantifierFreeContextError extends Error {
  constructor() { super("quantifiers not supported in this context"); }
}

class HeapReferenceContextError extends Error {
  constructor() { super("heap references not supported in this context"); }
}

class AssertionTranslator extends Visitor<A, void> {
  oldHeap: Heap;
  heap: Heap;
  inPost: string | null;
  allowsQuantifiers: boolean;
  allowsHeapReferences: boolean;

  constructor(oldHeap: Heap, heap: Heap, inPost: string | null) {
    super();
    this.oldHeap = oldHeap;
    this.heap = heap;
    this.inPost = inPost;
    this.allowsQuantifiers = true;
    this.allowsHeapReferences = true;
  }

  visitIdentifier(expr: Syntax.Identifier): A {
    if (isMutable(expr)) {
      if (!this.allowsHeapReferences) throw new HeapReferenceContextError();
      return { type: "HeapReference", heap: this.heap, loc: expr.name };
    } else {
      return expr.name;
    }
  }

  visitOldIdentifier(expr: Syntax.OldIdentifier): A {
    if (!this.allowsHeapReferences) throw new HeapReferenceContextError();
    if (!isMutable(expr.id)) { throw new Error("not mutable"); }
    return { type: "HeapReference", heap: this.oldHeap, loc: expr.id.name };
  }

  visitLiteral(expr: Syntax.Literal): A {
    return expr;
  }

  visitArrayExpression(expr: Syntax.ArrayExpression): A {
    return {
      type: "ArrayExpression",
      elements: expr.elements.map(e => this.visitExpression(e))
    };
  }

  visitUnaryExpression(expr: Syntax.UnaryExpression): A {
    const argument = this.visitExpression(expr.argument);
    return { type: "UnaryExpression", operator: expr.operator, argument };
  }

  visitBinaryExpression(expr: Syntax.BinaryExpression): A {
    const left = this.visitExpression(expr.left);
    const right = this.visitExpression(expr.right);
    return { type: "BinaryExpression", operator: expr.operator, left, right };
  }

  visitLogicalExpression(expr: Syntax.LogicalExpression): A {
    const origQF = this.allowsQuantifiers;
    this.allowsQuantifiers = false;
    const left = this.visitExpression(expr.left);
    this.allowsQuantifiers = origQF;
    const right = this.visitExpression(expr.right);
    if (expr.operator == "&&") {
      return { type: "ConditionalExpression", test: truthy(left), consequent: right, alternate: left };
    } else {
      return { type: "ConditionalExpression", test: truthy(left), consequent: left, alternate: right };
    }
  }

  visitConditionalExpression(expr: Syntax.ConditionalExpression): A {
    const origQF = this.allowsQuantifiers;
    this.allowsQuantifiers = false;
    const test = truthy(this.visitExpression(expr.test));
    this.allowsQuantifiers = origQF;
    const consequent = this.visitExpression(expr.consequent);
    const alternate = this.visitExpression(expr.alternate);
    return { type: "ConditionalExpression", test, consequent, alternate };
  }

  visitAssignmentExpression(expr: Syntax.AssignmentExpression): A {
    throw new PureContextError();
  }

  visitSequenceExpression(expr: Syntax.SequenceExpression): A {
    // ignore all expressions but the last
    return this.visitExpression(expr.expressions[expr.expressions.length - 1]);
  }

  visitCallExpression(expr: Syntax.CallExpression): A {
    return {
      type: "CallExpression",
      callee: this.visitExpression(expr.callee),
      heap: this.inPost && expr.callee.type == "Identifier" && this.inPost == expr.callee.name ? this.oldHeap : this.heap,
      args: expr.args.map(a => this.visitExpression(a))
    };
  }

  visitSpecExpression(expr: Syntax.SpecExpression): A {
    if (!this.allowsQuantifiers) throw new QuantifierFreeContextError();
    const callee: string = expr.callee.name;
    const r = truthy(translateExpression(this.heap + 1, this.heap + 1, this.inPost, expr.pre));
    const sPost = expr.callee.type == "Identifier" ? expr.callee.name : this.inPost;
    const s = truthy(translateExpression(this.heap + 1, this.heap + 2, sPost, expr.post));
    const forAll: P = transformSpec(callee, expr.args, r, s, this.heap + 1);
    const fnCheck: A = {
      type: "BinaryExpression",
      left: {
        type: "UnaryExpression",
        operator: "typeof",
        argument: callee
      },
      operator: "==",
      right: { type: "Literal", value: "function" }
    };
    const test = and(truthy(fnCheck), forAll);
    const consequent: A = { type: "Literal", value: true };
    const alternate: A = { type: "Literal", value: false };
    return { type: "ConditionalExpression", test, consequent, alternate };
  }

  visitPureExpression(expr: Syntax.PureExpression): A {
    const test: P = heapEq(this.heap, this.oldHeap);
    const consequent: A = { type: "Literal", value: true };
    const alternate: A = { type: "Literal", value: false };
    return { type: "ConditionalExpression", test, consequent, alternate };
  }

  visitNewExpression(expr: Syntax.NewExpression): A {
    throw new PureContextError();
  }

  visitInstanceOfExpression(expr: Syntax.InstanceOfExpression): A {
    const test: P = { type: "InstanceOf", left: this.visitExpression(expr.left), right: expr.right.name };
    const consequent: A = { type: "Literal", value: true };
    const alternate: A = { type: "Literal", value: false };
    return { type: "ConditionalExpression", test, consequent, alternate };
  }

  visitInExpression(expr: Syntax.InExpression): A {
    const test: P = { type: "HasProperty", object: this.visitExpression(expr.object), property: expr.property };
    const consequent: A = { type: "Literal", value: true };
    const alternate: A = { type: "Literal", value: false };
    return { type: "ConditionalExpression", test, consequent, alternate };
  }

  visitMemberExpression(expr: Syntax.MemberExpression): A {
    const object = this.visitExpression(expr.object);
    return { type: "MemberExpression", object, property: expr.property };
  }

  visitVariableDeclaration(stmt: Syntax.VariableDeclaration) {}
  visitBlockStatement(stmt: Syntax.BlockStatement) {}
  visitExpressionStatement(stmt: Syntax.ExpressionStatement) {}
  visitAssertStatement(stmt: Syntax.AssertStatement) {}
  visitIfStatement(stmt: Syntax.IfStatement) {}
  visitReturnStatement(stmt: Syntax.ReturnStatement) {}
  visitWhileStatement(stmt: Syntax.WhileStatement) {}
  visitDebuggerStatement(stmt: Syntax.DebuggerStatement) {}
  visitFunctionDeclaration(stmt: Syntax.FunctionDeclaration) {}
  visitClassDeclaration(stmt: Syntax.ClassDeclaration) {}
  visitProgram(prog: Syntax.Program) {}
}

function translateExpression(oldHeap: Heap, heap: Heap, inPost: string | null, expr: Syntax.Expression): A {
  const translator = new AssertionTranslator(oldHeap, heap, inPost);
  return translator.visitExpression(expr);
}

function translateNoHeapExpression(expr: Syntax.Expression): A {
  const translator = new AssertionTranslator(0, 0, null);
  translator.allowsHeapReferences = false;
  return translator.visitExpression(expr);
}

type BreakCondition = P;

class VCGenerator extends Visitor<A, BreakCondition> {
  classes: Classes;
  oldHeap: Heap;
  heap: Heap;
  locs: Locs;
  vars: Vars;
  prop: P;
  vcs: Array<VerificationCondition>;
  testBody: ReadonlyArray<Syntax.Statement>;

  constructor(classes: Classes, oldHeap: Heap, heap: Heap, locs: Locs, vars: Vars, prop: P = tru) {
    super();
    this.classes = classes;
    this.oldHeap = oldHeap;
    this.heap = heap;
    this.locs = locs;
    this.vars = vars;
    this.prop = prop;
    this.vcs = [];
    this.testBody = [];
  }

  have(p: P): void {
    this.prop = and(this.prop, p);
  }

  tryPre<T>(pre: P, fn: () => T): [Heap, P, T] {
    const origPre = this.prop, origHeap = this.heap, origBody = this.testBody;
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

  tryExpression(pre: P, expr: Syntax.Expression): [Heap, P, A] {
    return this.tryPre(pre, () => {
      return this.visitExpression(expr);
    });
  }

  freshVar(): string {
    let i = 0;
    while (this.vars.has(`_tmp_${i}`)) i++;
    this.vars.add(`_tmp_${i}`);
    return `_tmp_${i}`;
  }

  verify(vc: P, loc: Syntax.SourceLocation, desc: string, testBody: Array<Syntax.Statement> = []) {
    this.vcs.push(new VerificationCondition(this.classes, this.heap, this.locs, this.vars, and(this.prop, not(vc)), loc, desc, this.testBody.concat(testBody)));
  }

  visitIdentifier(expr: Syntax.Identifier): A {
    if (isMutable(expr)) {
      return { type: "HeapReference", heap: this.heap, loc: expr.name };
    } else {
      return expr.name;
    }
  }

  visitLiteral(expr: Syntax.Literal): A {
    return expr;
  }

  visitArrayExpression(expr: Syntax.ArrayExpression): A {
    return { type: "ArrayExpression", elements: expr.elements.map(e => this.visitExpression(e)) };
  }

  visitUnaryExpression(expr: Syntax.UnaryExpression): A {
     return { type: "UnaryExpression", operator: expr.operator, argument: this.visitExpression(expr) };
  }

  visitBinaryExpression(expr: Syntax.BinaryExpression): A {
    return {
      type: "BinaryExpression",
      operator: expr.operator,
      left: this.visitExpression(expr.left),
      right:  this.visitExpression(expr.right)
    };
  }

  visitLogicalExpression(expr: Syntax.LogicalExpression): A {
    const l = this.visitExpression(expr.left);
    if (expr.operator == "&&") {
      const [rHeap, rPost, rVal] = this.tryExpression(truthy(l), expr.right);
      this.have(implies(truthy(l), rPost));
      this.have(implies(falsy(l), heapEq(rHeap, this.heap)));
      this.heap = rHeap;
      return { type: "ConditionalExpression", test: truthy(l), consequent: rVal, alternate: l };
    } else {
      const [rHeap, rPost, rVal] = this.tryExpression(falsy(l), expr.right);
      this.have(implies(falsy(l), rPost));
      this.have(implies(truthy(l), heapEq(rHeap, this.heap)));
      this.heap = rHeap;
      return { type: "ConditionalExpression", test: falsy(l), consequent: rVal, alternate: l };
    }
  }

  visitConditionalExpression(expr: Syntax.ConditionalExpression): A {
    const t = this.visitExpression(expr.test);
    const [lHeap, lPost, lVal] = this.tryExpression(truthy(t), expr.consequent);
    const [rHeap, rPost, rVal] = this.tryExpression(falsy(t), expr.alternate);
    const newHeap = Math.max(lHeap, rHeap);
    this.have(implies(truthy(t), and(lPost, heapEq(newHeap, lHeap))));
    this.have(implies(falsy(t), and(rPost, heapEq(newHeap, rHeap))));
    this.heap = newHeap;
    return { type: "ConditionalExpression", test: truthy(t), consequent: lVal, alternate: rVal };
  }

  visitAssignmentExpression(expr: Syntax.AssignmentExpression): A {
    const t = this.visitExpression(expr.right);
    this.have(heapStore(this.heap++, expr.left.name, t));
    return t;
  }

  visitSequenceExpression(expr: Syntax.SequenceExpression): A {
    let val = und;
    for (const e of expr.expressions) {
      val = this.visitExpression(e);
    }
    return val;
  }

  visitCallExpression(expr: Syntax.CallExpression): A {
    // evaluate callee
    const callee = this.visitExpression(expr.callee);

    // evaluate arguments
    const args: Array<A> = expr.args.map(e => this.visitExpression(e));
    const heap = this.heap;

    // apply call trigger
    this.have({ type: "CallTrigger", callee, heap, args });

    // verify precondition
    const pre: P = { type: "Precondition", callee, heap, args };
    this.verify(pre, expr.loc, `precondition ${stringifyExpr(expr)}`);
    
    // assume postcondition
    this.have({ type: "Postcondition", callee, heap, args });

    // function call effect
    this.have(heapEq(this.heap + 1, { type: "HeapEffect", callee, heap, args }));

    return { type: "CallExpression", callee, heap: this.heap++, args };
  }

  visitOldIdentifier(expr: Syntax.OldIdentifier): A {
    throw new Error("Only possible in assertion context");
  }

  visitSpecExpression(expr: Syntax.SpecExpression): A {
    throw new Error("Only possible in assertion context");
  }

  visitPureExpression(expr: Syntax.PureExpression): A {
    throw new Error("Only possible in assertion context");
  }

  visitNewExpression(expr: Syntax.NewExpression): A {
    // evaluate arguments
    const args: Array<A> = expr.args.map(e => this.visitExpression(e));

    if (expr.callee.decl.type != "Class") throw new Error("Class not resolved");
    const clz: Syntax.ClassDeclaration = expr.callee.decl.decl;

    const object = this.freshVar();
    this.have({ type: "InstanceOf", left: object, right: clz.id.name });
    this.have(truthy({
      type: "BinaryExpression",
      left: {
        type: "UnaryExpression",
        operator: "typeof",
        argument: object
      },
      operator: "==",
      right: { type: "Literal", value: "object" }
    }));
    this.have(not(eq(object, { type: "Literal", value: null })));
    clz.fields.forEach((property, idx) => {
      this.have({ type: "HasProperty", object: object, property });
      this.have(eq({ type: "MemberExpression", object, property }, args[idx]));
    });

    // verify invariant
    const inv: A = translateNoHeapExpression(replaceThis(object, clz.invariant));
    this.verify(truthy(inv), expr.loc, `class invariant ${clz.id.name}`);
    
    return object;
  }

  visitInstanceOfExpression(expr: Syntax.InstanceOfExpression): A {
    const test: P = { type: "InstanceOf", left: this.visitExpression(expr.left), right: expr.right.name };
    const consequent: A = { type: "Literal", value: true };
    const alternate: A = { type: "Literal", value: false };
    return { type: "ConditionalExpression", test, consequent, alternate };
  }

  visitInExpression(expr: Syntax.InExpression): A {
    const test: P = { type: "HasProperty", object: this.visitExpression(expr.object), property: expr.property };
    const consequent: A = { type: "Literal", value: true };
    const alternate: A = { type: "Literal", value: false };
    return { type: "ConditionalExpression", test, consequent, alternate };
  }

  visitMemberExpression(expr: Syntax.MemberExpression): A {
    const object = this.visitExpression(expr.object);
    const property = expr.property;
    this.have({ type: "AccessTrigger", object: object });
    this.verify({ type: "HasProperty", object, property }, expr.loc, `property ${property} exists on object`,
               [{ type: "AssertStatement", loc: expr.loc,
                  expression: { type: "InExpression", object: expr.object, property, loc: expr.loc }}]);
    return { type: "MemberExpression", object, property: expr.property };
  }

  tryStatement(pre: P, stmt: Syntax.Statement): [Heap, P, BreakCondition] {
    return this.tryPre(pre, () => {
      return this.visitStatement(stmt);
    });
  }

  transformDef(f: Syntax.FunctionDeclaration, heap: number, toHeap: number = heap + 1, existsLocs: Locs = new Set(), existsVars: Vars = new Set(), q: P = tru): P {
    const callee: A = f.id.name;
    const args: Array<string> = f.params.map(p => p.name);
    let req = tru;
    for (const r of f.requires) {
      req = and(req, truthy(translateExpression(heap, heap, null, r)));
    }
    let ens = q;
    for (const s of f.ensures) {
      ens = and(ens, truthy(translateExpression(heap, toHeap, f.id.name, s)));
    }
    return transformSpec(callee, args, req, ens, heap, toHeap, existsLocs, existsVars, q);
  }

  visitFunctionBody(f: Syntax.FunctionDeclaration) {

    const startHeap = this.heap;
    const startBody = this.testBody;

    // add function name to scope
    this.vars.add(f.id.name);
    
    // add arguments to scope
    const args: Array<A> = [];
    for (const p of f.params) {
      args.push(p.name);
      this.vars.add(p.name);
    }

    // add special result variable
    this.vars.add("_res_");

    // assume preconditions
    for (const r of f.requires) {
      const tr = translateExpression(this.heap, this.heap, null, r);
      this.prop = and(this.prop, truthy(tr));
    }

    // assume non-rec spec
    this.prop = and(this.prop, this.transformDef(f, startHeap + 1));
    const pre = this.prop;

    // internal verification conditions
    const res = this.visitStatement(f.body);

    this.testBody = startBody.concat([{
      type: "ExpressionStatement",
      expression: {
        type: "AssignmentExpression",
        left: { type: "Identifier", name: "_res_", decl: { type: "Unresolved" },
                loc: f.loc, refs: [], isWrittenTo: false},
        right: { type: "CallExpression", callee: f.id, args: f.params, loc: f.loc },
        loc: f.loc
      },
      loc: f.loc
    }]);

    // ensure post conditions
    const callee: A = f.id.name;
    this.prop = and(this.prop, eq("_res_", { type: "CallExpression", callee, heap: startHeap, args }));

    for (const ens of f.ensures) {
      const ens2 = replaceFunctionResult(f, ens);
      const ti = translateExpression(startHeap, this.heap, f.id.name, ens);
      this.verify(truthy(ti), ens.loc, stringifyExpr(ens),
                  [{ type: "AssertStatement", loc: ens.loc, expression: ens2}]);
    }
    this.vcs.forEach(vc => {
      vc.description = f.id.name + ": " + vc.description;
    });

    // remove preconditions from prop for purpose of inlining
    this.prop = removePrefix(pre, this.prop);
    return res;
  }

  visitVariableDeclaration(stmt: Syntax.VariableDeclaration): BreakCondition {
    const origBody = this.testBody;
    this.testBody = this.testBody.concat({ type: "ExpressionStatement", expression: stmt.init, loc: stmt.init.loc });
    const t = this.visitExpression(stmt.init);
    if (stmt.kind == "const") {
      this.vars.add(stmt.id.name);
      this.prop = and(this.prop, eq(stmt.id.name, t));
      this.testBody = origBody.concat([convertToAssignment(stmt)]);
    } else {
      this.locs.add(stmt.id.name);
      this.prop = and(this.prop, heapStore(this.heap, stmt.id.name, t));
      this.heap++;
      this.testBody = origBody.concat(stmt);
    }
    return fls;
  }
  
  visitBlockStatement(stmt: Syntax.BlockStatement): BreakCondition {
    let bc = fls, origBody = this.testBody;
    for (const s of stmt.body) {
      const [tHeap, tProp, tBC] = this.tryStatement(not(bc), s);
      this.testBody = this.testBody.concat(s);
      this.prop = and(this.prop, 
                      implies(bc, heapEq(tHeap, this.heap)),
                      implies(not(bc), tProp));
      this.heap = tHeap;
      bc = or(bc, tBC);
    }
    this.testBody = origBody.concat(stmt);
    return bc;
  }
  
  visitExpressionStatement(stmt: Syntax.ExpressionStatement): BreakCondition {
    this.testBody = this.testBody.concat(stmt);
    this.visitExpression(stmt.expression);
    return fls;
  }
  
  visitAssertStatement(stmt: Syntax.AssertStatement): BreakCondition {
    const a = translateExpression(this.oldHeap, this.heap, null, stmt.expression);
    this.verify(truthy(a), stmt.loc, "assert: " + stringifyExpr(stmt.expression), [stmt]);
    return not(truthy(a));
  }
  
  visitIfStatement(stmt: Syntax.IfStatement): BreakCondition {
    const origBody = this.testBody;
    this.testBody = this.testBody.concat({ type: "ExpressionStatement", expression: stmt.test, loc: stmt.test.loc });
    const t = this.visitExpression(stmt.test);
    const [lHeap, lProp, lBC] = this.tryStatement(truthy(t), stmt.consequent);
    const [rHeap, rProp, rBC] = this.tryStatement(falsy(t), stmt.alternate);
    const newHeap = Math.max(lHeap, rHeap);
    this.prop = and(this.prop,
                    implies(truthy(t), and(lProp, heapEq(newHeap, lHeap))),
                    implies(falsy(t), and(rProp, heapEq(newHeap, rHeap))));
    this.heap = newHeap;
    this.testBody = origBody.concat(stmt);
    return or(and(truthy(t), lBC), and(falsy(t), rBC));
  }
  
  visitReturnStatement(stmt: Syntax.ReturnStatement): BreakCondition {
    const origBody = this.testBody;
    this.testBody = this.testBody.concat({
      type: "ExpressionStatement",
      expression: stmt.argument,
      loc: stmt.argument.loc });
    const t = this.visitExpression(stmt.argument);
    this.prop = and(this.prop, eq("_res_", t));
    this.testBody = origBody.concat(stmt);
    return tru;
  }
  
  visitWhileStatement(stmt: Syntax.WhileStatement): BreakCondition {
    // verify invariants on entry
    for (const inv of stmt.invariants) {
      const t = translateExpression(this.oldHeap, this.heap, null, inv);
      this.verify(truthy(t), inv.loc, "invariant on entry: " + stringifyExpr(inv),
                  [{ type: "AssertStatement", loc: inv.loc, expression: inv }]);
    }

    // havoc heap
    this.heap++;

    const startHeap = this.heap;
    const startProp = this.prop;
    const startBody = this.testBody;

    // assume loop condition true and invariants true
    this.testBody = this.testBody.concat({ type: "ExpressionStatement", expression: stmt.test, loc: stmt.test.loc });

    let testEnter = this.visitExpression(stmt.test);
    this.prop = and(this.prop, truthy(testEnter));
    for (const inv of stmt.invariants) {
      const ti = translateExpression(startHeap, this.heap, null, inv); // TODO old() for previous iteration
      this.prop = and(this.prop, truthy(ti));
    }

    // internal verification conditions
    const bcBody = this.visitStatement(stmt.body);

    // ensure invariants maintained
    for (const inv of stmt.invariants) {
      const ti = translateExpression(startHeap, this.heap, null, inv);
      const assertCode: Syntax.Statement = { type: "AssertStatement", loc: inv.loc, expression: inv };
      this.verify(truthy(ti), inv.loc, "invariant maintained: " + stringifyExpr(inv),
                  loopTestingCode(stmt).concat([assertCode]));
    }


    // we are going to use the returned verification conditions and break condition
    // but we will ignore its effects
    this.heap = startHeap;
    this.prop = startProp;
    this.testBody = startBody.concat(stmt);

    // assume loop condition false and invariants true
    const testExit = this.visitExpression(stmt.test);
    this.prop = and(this.prop, falsy(testExit));
    for (const inv of stmt.invariants) {
      const ti = translateExpression(this.oldHeap, this.heap, null, inv);
      this.prop = and(this.prop, truthy(ti));
    }
    return and(truthy(testEnter), bcBody);
  }
  
  visitDebuggerStatement(stmt: Syntax.DebuggerStatement): BreakCondition {
    return fls;
  }
  
  visitFunctionDeclaration(stmt: Syntax.FunctionDeclaration): BreakCondition {
    this.testBody = this.testBody.concat([checkPreconditions(stmt)]);
    const inliner = new VCGenerator(this.classes, this.heap + 1, this.heap + 1,
                                    new Set([...this.locs]),
                                    new Set([...this.vars]), this.prop);
    inliner.testBody = this.testBody;
    inliner.visitFunctionBody(stmt);
    this.vars.add(stmt.id.name);
    this.vcs = this.vcs.concat(inliner.vcs);
    const existsLocs = new Set([...inliner.locs].filter(l => !this.locs.has(l))),
          existsVars = new Set([...inliner.vars].filter(v => {
            return !this.vars.has(v) && !stmt.params.some(n => n.name == v);
          })),
          inlined_p: P = eraseTriggersProp(inliner.prop),
          inlined_spec: P = this.transformDef(stmt, this.heap + 1, inliner.heap,
                                              existsLocs, existsVars, inlined_p);
    this.prop = and(this.prop, inlined_spec);
    return fls;
  }

  visitClassDeclaration(stmt: Syntax.ClassDeclaration): BreakCondition {
    this.classes.add(stmt.id.name);
    this.testBody = this.testBody.concat([stmt]);
    const inv: A = translateNoHeapExpression(stmt.invariant);
    this.have(transformClassInvariant(stmt.id.name, stmt.fields, truthy(inv)));
    return fls;
  }

  visitProgram(prog: Syntax.Program): BreakCondition {

    // go through all statements
    for (const stmt of prog.body) {
      if (stmt.type == "FunctionDeclaration") {
        // function should maintain invariants
        prog.invariants.forEach(inv => { stmt.requires.push(inv); stmt.ensures.push(inv); });
      }
      this.visitStatement(stmt);
    }

    // main program body needs to establish invariants
    for (const inv of prog.invariants) {
      const ti = translateExpression(this.heap, this.heap, null, inv);
      this.verify(truthy(ti), inv.loc, "initially: " + stringifyExpr(inv),
                  [{ type: "AssertStatement", loc: inv.loc, expression: inv }]);
    }
    return fls;
  }
}

export function vcgenProgram(prog: Syntax.Program): Array<VerificationCondition> {
  const vcgen = new VCGenerator(new Set(), 0, 0, new Set(), new Set(), tru);
  vcgen.visitProgram(prog);
  return vcgen.vcs;
}