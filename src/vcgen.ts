import VerificationCondition from "./verification";
import { JSyntax, stringifyExpr, checkInvariants, checkPreconditions, replaceFunctionResult, isMutable } from "./javascript";
import { ASyntax, A, P, Vars, Locs, Heap, und, tru, fls, truthy, falsy, implies, and, iff, or, eq, not, heapPromote, heapStore } from "./propositions";

class PureContextError extends Error {
  constructor() { super("not supported in pure functional context"); }
}

function transformExpression(oldHeap: Heap, heap: Heap, inPost: string | null, expr: JSyntax.Expression): A {
  switch (expr.type) {
    case "Identifier":
      if (isMutable(expr)) {
        return { type: "HeapReference", heap, name: expr.name };
      } else {
        return { type: "Variable", name: expr.name };
      }
    case "OldIdentifier":
      if (!isMutable(expr.id)) { throw new Error("not mutable"); }
      return { type: "HeapReference", heap: oldHeap, name: expr.id.name };
    case "Literal":
      return expr;
    case "ArrayExpression":
      return {
        type: "ArrayExpression",
        elements: expr.elements.map(e => transformExpression(oldHeap, heap, inPost, e))
      };
    case "UnaryExpression":
      const argument = transformExpression(oldHeap, heap, inPost, expr.argument);
      return { type: "UnaryExpression", operator: expr.operator, argument };
    case "BinaryExpression": {
      const left = transformExpression(oldHeap, heap, inPost, expr.left);
      const right = transformExpression(oldHeap, heap, inPost, expr.right);
      return { type: "BinaryExpression", operator: expr.operator, left, right };
    }
    case "LogicalExpression": {
      const left = transformExpression(oldHeap, heap, inPost, expr.left);
      const right = transformExpression(oldHeap, heap, inPost, expr.right);
      if (expr.operator == "&&") {
        return { type: "ConditionalExpression", test: truthy(left), consequent: right, alternate: left };
      } else {
        return { type: "ConditionalExpression", test: truthy(left), consequent: left, alternate: right };
      }
    }
    case "ConditionalExpression": {
      const test = truthy(transformExpression(oldHeap, heap, inPost, expr.test));
      const consequent = transformExpression(oldHeap, heap, inPost, expr.consequent);
      const alternate = transformExpression(oldHeap, heap, inPost, expr.alternate);
      return { type: "ConditionalExpression", test, consequent, alternate };
    }
    case "AssignmentExpression": {
      throw new PureContextError();
    }
    case "SequenceExpression": {
      // ignore all expressions but the last
      return transformExpression(oldHeap, heap, inPost, expr.expressions[expr.expressions.length - 1]);
    }
    case "CallExpression":
      return {
        type: "CallExpression",
        callee: transformExpression(oldHeap, heap, inPost, expr.callee),
        heap: inPost && expr.callee.type == "Identifier" && inPost == expr.callee.name ? oldHeap : heap,
        args: expr.args.map(a => transformExpression(oldHeap, heap, inPost, a))
      };
    case "SpecExpression": {
      const args: Array<ASyntax.Variable> = [];
      for (const name of expr.args) {
        args.push({ type: "Variable", name });
      }
      const callee = transformExpression(oldHeap, heap, inPost, expr.callee);
      const preP: P = { type: "Precondition", callee, heap: 0, args };
      const postP: P = { type: "Postcondition", callee, heap: 0, args };
      const callP: P = { type: "CallTrigger", callee, heap: 0, args };
      const r = truthy(transformExpression(0, 0, inPost, expr.pre));
      const sPost = expr.callee.type == "Identifier" ? expr.callee.name : inPost;
      const s = truthy(transformExpression(0, 1, sPost, expr.post));
      const forAll: P = { type: "ForAll", callee, args,
        existsHeaps: new Set(), existsLocs: new Set(), existsVars: new Set(),
        prop: and(callP, implies(r, preP), implies(and(r, postP), s))
      };
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
  }
}

let nextUniqueFuncId: number = 0;
function uniqueFuncId() { return nextUniqueFuncId++; }

class VCState {
  heap: Heap;
  locs: Locs;
  vars: Vars;
  prop: P;
  val: A;
  bc: P;
  vcs: Array<VerificationCondition>;

  constructor(heap: Heap = 0, locs: Locs = new Set(), vars: Vars = new Set(), prop: P = tru, val: A = und, bc: P = fls, vcs: Array<VerificationCondition> = []) {
    this.heap = heap;
    this.locs = locs;
    this.vars = vars;
    this.prop = prop;
    this.val = val;
    this.bc = bc;
    this.vcs = vcs;
  }

  map(f: (x: A) => A): VCState {
    return new VCState(this.heap, this.locs, this.vars, this.prop, f(this.val), this.bc, this.vcs);
  }

  then(t: VCState): VCState {
    return new VCState(
      t.heap,
      t.locs,
      t.vars,
      and(this.prop,
          implies(this.bc, heapPromote(this.heap, t.heap)),
          implies(not(this.bc), t.prop)),
      t.val,
      or(this.bc, t.bc),
      this.vcs.concat(t.vcs.map(vc => ((vc.prop = and(this.prop, not(this.bc), vc.prop)), vc))));
  }

  static pure(heap: number, locs: Locs, vars: Vars, expr: A) {
    return new VCState(heap, locs, vars, tru, expr);
  }
}

export function verifyExpression(oldHeap: Heap, heap: Heap, locs: Locs, vars: Vars, expr: JSyntax.Expression): VCState {
  switch (expr.type) {
    case "Identifier":
      if (isMutable(expr)) {
        return VCState.pure(heap, locs, vars, { type: "HeapReference", heap, name: expr.name });
      } else {
        return VCState.pure(heap, locs, vars, { type: "Variable", name: expr.name });
      }
    case "OldIdentifier":
      throw new Error("Only possible in assertions");
    case "Literal":
      return VCState.pure(heap, locs, vars, expr);
    case "ArrayExpression":
      const elements: Array<A> = [];
      let res = VCState.pure(heap, locs, vars, und);
      for (const elem of expr.elements) {
        const t = verifyExpression(oldHeap, res.heap, res.locs, res.vars, elem);
        res = res.then(t);
        elements.push(t.val);
      }
      return res.map(v => ({ type: "ArrayExpression", elements }));
    case "UnaryExpression":
      const t = verifyExpression(oldHeap, heap, locs, vars, expr.argument);
      return t.map(v => ({ type: "UnaryExpression", operator: expr.operator, argument: v }));
    case "BinaryExpression": {
      const tl = verifyExpression(oldHeap, heap, locs, vars, expr.left);
      const tr = verifyExpression(oldHeap, tl.heap, tl.locs, tl.vars, expr.right);
      const res: A = { type: "BinaryExpression", operator: expr.operator, left: tl.val, right: tr.val };
      return tl.then(tr).map(v => res);
    }
    case "LogicalExpression": {
      const l = verifyExpression(oldHeap, heap, locs, vars, expr.left);
      const r = verifyExpression(oldHeap, l.heap, l.locs, l.vars, expr.right);
      if (expr.operator == "&&") {
        return new VCState(
          r.heap,
          r.locs,
          r.vars,
          and(l.prop, implies(truthy(l.val), r.prop)),
          { type: "ConditionalExpression", test: truthy(l.val), consequent: r.val, alternate: l.val },
          or(l.bc, and(truthy(l.val), r.bc)),
          l.vcs.concat(r.vcs.map(vc => ((vc.prop = and(l.prop, not(l.bc), truthy(l.val), vc.prop)), vc))));
      } else {
        return new VCState(
          r.heap,
          r.locs,
          r.vars,
          and(l.prop, implies(falsy(l.val), r.prop)),
          { type: "ConditionalExpression", test: falsy(l.val), consequent: r.val, alternate: l.val },
          or(l.bc, and(falsy(l.val), r.bc)),
          l.vcs.concat(r.vcs.map(vc => ((vc.prop = and(l.prop, not(l.bc), falsy(l.val), vc.prop)), vc))));
      }
    }
    case "ConditionalExpression": {
      const t = verifyExpression(oldHeap, heap, locs, vars, expr.test);
      const l = verifyExpression(oldHeap, t.heap, t.locs, t.vars, expr.consequent);
      const r = verifyExpression(oldHeap, t.heap, l.locs, l.vars, expr.alternate);
      const newHeap = Math.max(l.heap, r.heap);
      return new VCState(
        newHeap,
        r.locs,
        r.vars,
        and(t.prop,
            implies(truthy(t.val), and(l.prop, heapPromote(l.heap, newHeap))),
            implies(falsy(t.val), and(r.prop, heapPromote(r.heap, newHeap)))),
        { type: "ConditionalExpression", test: truthy(t.val), consequent: l.val, alternate: r.val },
        or(t.bc, and(truthy(t.val), l.bc), and(falsy(t.val), r.bc)),
        t.vcs.concat(l.vcs.map(vc => ((vc.prop = and(t.prop, not(t.bc), truthy(t.val), vc.prop)), vc)))
             .concat(r.vcs.map(vc => ((vc.prop = and(t.prop, not(t.bc), falsy(t.val), vc.prop)), vc))));
    }
    case "AssignmentExpression": {
      const t = verifyExpression(oldHeap, heap, locs, vars, expr.right);
      t.prop = and(t.prop, heapStore(t.heap, expr.left.name, t.val));
      t.heap++;
      return t;
    }
    case "SequenceExpression": {
      let res = VCState.pure(heap, locs, vars, und);
      for (const e of expr.expressions) {
        res = res.then(verifyExpression(oldHeap, res.heap, res.locs, res.vars, e));
      }
      return res;
    }
    case "CallExpression": {
      // evaluate callee
      let res = verifyExpression(oldHeap, heap, locs, vars, expr.callee);
      const callee = res.val;

      // evaluate arguments
      const args: Array<A> = [];
      for (const arg of expr.args) {
        const t = verifyExpression(oldHeap, res.heap, res.locs, res.vars, arg);
        res = res.then(t);
        args.push(t.val);
      }

      // apply call trigger
      res.prop = and(res.prop, { type: "CallTrigger", callee, heap: res.heap, args });

      // verify precondition
      res.vcs.push(new VerificationCondition(res.heap + 1, res.locs, res.vars, res.prop,
                                           { type: "Precondition", callee, heap: res.heap, args },
                                           `precondition ${stringifyExpr(expr)}`));
      
      // assume postcondition and return result
      res.prop = and(res.prop, { type: "Postcondition", callee, heap: res.heap, args });
      res.val = { type: "CallExpression", callee, heap: res.heap, args };
      res.heap++;
      return res;
    }
    case "SpecExpression":
      throw new Error("Unsupported");
    // case "FunctionExpression":
    //   throw new Error("not implemented yet"); 
  }
}

function verifyWhileLoop(heap: Heap, locs: Locs, vars: Vars, whl: JSyntax.WhileStatement): VCState {
  // return verification conditions:
  // - call req in test, invariants and body
  // - assert in body
  // - invariants maintained
  // break condition: test && return in body

  // assume loop condition true and invariants true
  let res = verifyExpression(heap, heap, locs, vars, whl.test);
  const enter = truthy(res.val);
  res.prop = and(res.prop, enter);
  for (const inv of whl.invariants) {
    const ti = transformExpression(heap, res.heap, null, inv); // TODO old() for previous iteration
    res.prop = and(res.prop, truthy(ti));
  }
  res = res.then(verifyStatement(heap, res.heap, res.locs, res.vars, whl.body));

  // internal verification conditions
  const testBody: Array<JSyntax.Statement> = [checkInvariants(whl), {
    type: "ExpressionStatement",
    expression: { type: "CallExpression", args: [],
                  callee: { type: "Identifier", name: "test", decl: {type: "Unresolved"}, refs: [], isWrittenTo: false}}
  }];
    
  res.vcs.forEach(vc => vc.body = testBody);
  res.bc = and(enter, res.bc);

  // ensure invariants maintained
  for (const inv of whl.invariants) {
    const ti = transformExpression(heap, res.heap, null, inv);
    res.vcs.push(new VerificationCondition(res.heap, res.locs, res.vars, res.prop, truthy(ti),
                "invariant maintained:\n" + stringifyExpr(inv),
                 testBody.concat([{ type: "AssertStatement", expression: inv }])));
  }
  return res;
}

function transformSpec(f: JSyntax.FunctionDeclaration, fromHeap: number = 0, toHeap: number = 1, existsLocs: Locs = new Set(), existsVars: Vars = new Set(), q: P = tru): P {
  const callee: ASyntax.Expression = { type: "Variable", name: f.id.name };
  
  // add arguments to scope 
  const args: Array<ASyntax.Variable> = [];
  for (const p of f.params) {
    args.push({ type: "Variable", name: p.name });
  }

  let req = tru;
  for (const r of f.requires) {
    req = and(req, truthy(transformExpression(0, 0, null, r)));
  }
  let ens = q;
  for (const s of f.ensures) {
    ens = and(ens, truthy(transformExpression(0, 1, f.id.name, s)));
  }
  const preP: P = { type: "Precondition", callee, heap: 0, args };
  const postP: P = { type: "Postcondition", callee, heap: 0, args };
  const callP: P = { type: "CallTrigger", callee, heap: 0, args };
  let prop: P;
  if (q.type == "True") {
    prop = and(callP, implies(req, preP), implies(and(req, postP), ens));
  } else {
    prop = and(callP, iff(req, preP), iff(postP, implies(req, ens)));
  }
  if (fromHeap != 0) {
    prop = and(heapPromote(0, fromHeap), prop);
  }
  if (toHeap != 1) {
    prop = and(heapPromote(1, toHeap), prop);
  }
  const existsHeaps: Set<Heap> = new Set([...Array(toHeap - fromHeap + 1).keys()].map(i => i + fromHeap));
  existsHeaps.delete(0); existsHeaps.delete(1);
  const forAll: P = { type: "ForAll", callee, heap: 0, args, existsHeaps, existsLocs, existsVars, prop };
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
  return and(truthy(fnCheck), forAll);
}

function verifyFunctionDeclaration(heap: Heap, locs: Locs, vars: Vars, f: JSyntax.FunctionDeclaration): VCState {

  // assumes all let-bound free variables have been havoc'd
  const vars2 = new Set([...vars]);
  
  // add arguments to scope
  const args: Array<A> = [];
  for (const p of f.params) {
    args.push({ type: "Variable", name: p.name });
    vars2.add(p.name);
  }

  // assume preconditions
  let p: P = tru;
  for (const req of f.requires) {
    const tr = transformExpression(heap, heap, null, req);
    p = and(p, truthy(tr));
  }

  // internal verification conditions
  const res = verifyStatement(heap, heap, locs, vars2, f.body);
  res.vcs.forEach(vc => vc.prop = and(p, vc.prop));
  res.prop = and(p, res.prop);

  // ensure post conditions
  res.vars.add("_res_");
  const callee: A = { type: "Variable", name: f.id.name };
  res.prop = and(eq({ type: "Variable", name: "_res_" },
                    { type: "CallExpression", callee, heap, args }),
                 res.prop);

  const testBody: Array<JSyntax.Statement> = [{
    type: "VariableDeclaration",
    id: { type: "Identifier", name: "_res_", decl: { type: "Unresolved" }, refs: [], isWrittenTo: false},
    kind: "const",
    init: { type: "CallExpression", callee: f.id, args: f.params }
  }];
  res.vcs.forEach(vc => vc.body = testBody);

  for (const ens of f.ensures) {
    const ens2 = replaceFunctionResult(f, ens);
    const ti = transformExpression(heap, res.heap, f.id.name, ens);
    res.vcs.push(new VerificationCondition(res.heap, res.locs, res.vars, res.prop, truthy(ti),
                                       stringifyExpr(ens),
                                       testBody.concat([{ type: "AssertStatement", expression: ens2 }])));
  }
  res.vcs.forEach(vc => {
    vc.description = f.id.name + ":\n" + vc.description;
  });
  return res;
}

export function verifyStatement(oldHeap: Heap, heap: Heap, locs: Locs, vars: Vars, stmt: JSyntax.Statement): VCState {
  switch (stmt.type) {
    case "VariableDeclaration": {
      const t = verifyExpression(oldHeap, heap, locs, vars, stmt.init);
      if (stmt.kind == "const") {
        t.vars.add(stmt.id.name);
        t.prop = and(t.prop, eq({type: "Variable", name: stmt.id.name}, t.val));
      } else {
        t.locs.add(stmt.id.name);
        t.prop = and(t.prop, heapStore(t.heap, stmt.id.name, t.val));
        t.heap++;
      }
      return t;
    }
    case "BlockStatement": {
      let res = VCState.pure(heap, locs, vars, und);
      for (const s of stmt.body) {
        res = res.then(verifyStatement(oldHeap, res.heap, res.locs, res.vars, s));
      }
      return res;
    }
    case "ExpressionStatement": {
      return verifyExpression(oldHeap, heap, locs, vars, stmt.expression);
    }
    case "AssertStatement": {
      const a = transformExpression(oldHeap, heap, null, stmt.expression);
      const vc = new VerificationCondition(heap, locs, vars, tru, truthy(a),
                                           "assert:\n" + stringifyExpr(stmt.expression));
      return new VCState(heap, locs, vars, tru, und, not(truthy(a)), [vc]);
    }
    case "IfStatement": {
      const t = verifyExpression(oldHeap, heap, locs, vars, stmt.test);
      const l = verifyStatement(oldHeap, t.heap, t.locs, t.vars, stmt.consequent);
      const r = verifyStatement(oldHeap, t.heap, l.locs, l.vars, stmt.alternate);
      const newHeap = Math.max(l.heap, r.heap);
      return new VCState(
        newHeap,
        r.locs,
        r.vars,
        and(t.prop,
            implies(truthy(t.val), and(l.prop, heapPromote(l.heap, newHeap))),
            implies(falsy(t.val), and(r.prop, heapPromote(r.heap, newHeap)))),
        { type: "ConditionalExpression", test: truthy(t.val), consequent: l.val, alternate: r.val },
        or(t.bc, and(truthy(t.val), l.bc), and(falsy(t.val), r.bc)),
        t.vcs.concat(l.vcs.map(vc => ((vc.prop = and(t.prop, not(t.bc), truthy(t.val), vc.prop)), vc)))
             .concat(r.vcs.map(vc => ((vc.prop = and(t.prop, not(t.bc), falsy(t.val), vc.prop)), vc))));
    }
    case "ReturnStatement": {
      const t = verifyExpression(oldHeap, heap, locs, vars, stmt.argument);
      const to: A = { type: "Variable", name: "_res_" };
      t.prop = and(t.prop, eq(to, t.val));
      t.bc = tru;
      return t;
    }
    case "WhileStatement": {
      // invariants on entry
      let vcs: Array<VerificationCondition> = [];
      for (const inv of stmt.invariants) {
        const t = transformExpression(oldHeap, heap, null, inv);
        vcs.push(new VerificationCondition(heap, locs, vars, tru, truthy(t), "invariant on entry:\n" + stringifyExpr(inv)));
      }

      // havoc heap and verify loop itself
      const twhile = verifyWhileLoop(heap + 1, locs, vars, stmt);

      // we are going to use the returned verification conditions and break condition
      // but we will ignore its effects
      const res = verifyExpression(oldHeap, twhile.heap + 1, twhile.locs, twhile.vars, stmt.test);

      // assume loop conditions false and invariants true
      res.prop = and(res.prop, not(truthy(res.val)));
      res.vcs = vcs.concat(twhile.vcs).concat(res.vcs);
      res.bc = or(twhile.bc, res.bc);
      for (const inv of stmt.invariants) {
        const ti = transformExpression(oldHeap, res.heap, null, inv);
        res.prop = and(res.prop, truthy(ti));
      }
      return res;
    }
    case "DebuggerStatement": {
      return VCState.pure(heap, locs, vars, und);
    }
    case "FunctionDeclaration": {
      const vars2 = new Set([...vars, stmt.id.name]);
      const id: A = { type: "Variable", name: stmt.id.name },
            eq_f: P = eq(id, { type: "FunctionLiteral", id: uniqueFuncId() }),
            non_rec_spec: P = transformSpec(stmt),
            fromHeap = Math.max(2, heap + 1); // H0 and H1 are reserved
      const res = verifyFunctionDeclaration(fromHeap, locs, vars2, stmt);
      res.vcs.forEach(vc => vc.prop = and(eq_f, non_rec_spec, vc.prop));
      const existsLocs = new Set([...res.locs].filter(l => !locs.has(l))),
            existsVars = new Set([...res.vars].filter(v => {
              return !vars2.has(v) && !stmt.params.some(n => n.name == v);
            })),
            inlined_spec: P = transformSpec(stmt, fromHeap, res.heap, existsLocs, existsVars, res.prop);
      return new VCState(heap, locs, vars2, and(eq_f, inlined_spec), und, fls, res.vcs);
    }
  }
}

export function transformProgram(prog: JSyntax.Program): Array<VerificationCondition> {

  // function should maintain invariants
  for (const inv of prog.invariants) {
    for (const f of prog.functions) {
      f.requires.push(inv);
      f.ensures.push(inv);
    }
  }

  // go through all statements
  let res = new VCState();
  let testBody: Array<JSyntax.Statement> = [];
  for (const stmt of prog.body) {
    testBody = testBody.concat([stmt]);
    const t = verifyStatement(res.heap, res.heap, res.locs, res.vars, stmt);
    t.vcs.forEach(vc => vc.body = testBody);
    res = res.then(t);
  }

  // we only care about the verification conditions
  const vcs = res.vcs;

  // main program body needs to establish invariants
  for (const inv of prog.invariants) {
    const ti = transformExpression(res.heap, res.heap, null, inv);
    vcs.push(new VerificationCondition(res.heap, res.locs, res.vars, res.prop, truthy(ti),
      "initially:\n" + stringifyExpr(inv),
      prog.body.concat([{ type: "AssertStatement", expression: inv }])));
  }

  // add function test bodies
  const funcTestBodies: Array<JSyntax.Statement> = [];
  for (const f of prog.functions) {
    funcTestBodies.push(checkPreconditions(f));
  }
  vcs.forEach(vc => {
    vc.body = funcTestBodies.concat(vc.body);
  });
  return vcs;
}