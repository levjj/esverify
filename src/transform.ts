import VerificationCondition, { VarName, Vars, SMTInput, SMTOutput } from "./vc";
import { JSyntax, stringifyExpr, checkInvariants, checkPreconditions, replaceFunctionResult } from "./javascript";
import { ASyntax, tru, fls, truthy, implies, and, or, eq, not } from "./assertions";
import { pushAll } from "./util";

function assignedInExpr(v: VarName, expr: JSyntax.Expression): boolean {
  switch (expr.type) {
    case "Identifier":
    case "OldIdentifier":
    case "Literal":
      return false;
    case "ArrayExpression":
      return expr.elements.some(e => assignedInExpr(v, e));
    case "UnaryExpression":
      return assignedInExpr(v, expr.argument);
    case "BinaryExpression": {
      return assignedInExpr(v, expr.left) || assignedInExpr(v, expr.right) ;
    }
    case "LogicalExpression": {
      return assignedInExpr(v, expr.left) || assignedInExpr(v, expr.right) ;
    }
    case "ConditionalExpression": {
      return assignedInExpr(v, expr.test) || assignedInExpr(v, expr.consequent) || assignedInExpr(v, expr.alternate);
    }
    case "AssignmentExpression": {
      return expr.left.name == v || assignedInExpr(v, expr.right);
    }
    case "SequenceExpression": {
      return expr.expressions.some(e => assignedInExpr(v, e));
    }
    case "CallExpression":
      return assignedInExpr(v, expr.callee) || expr.arguments.some(e => assignedInExpr(v, e));
    case "FunctionExpression":
      throw new Error("not implemented yet");
  }
}

function assignedInStmt(v: VarName, stmt: JSyntax.Statement): boolean {
  switch (stmt.type) {
    case "VariableDeclaration":
      return stmt.id.name != v && assignedInExpr(v, stmt.init);
    case "BlockStatement":
      for (const s of stmt.body) {
        if (s.type == "VariableDeclaration" && s.id.name == v) return false;
        if (assignedInStmt(v, s)) return true;
      }
      return false;
    case "ExpressionStatement":
      return assignedInExpr(v, stmt.expression);
    case "IfStatement":
      return assignedInExpr(v, stmt.test) ||
             assignedInStmt(v, stmt.consequent) ||
             assignedInStmt(v, stmt.alternate);
    case "ReturnStatement":
      return assignedInExpr(v, stmt.argument);
    case "WhileStatement":
      return assignedInExpr(v, stmt.test) || assignedInStmt(v, stmt.body);
    case "AssertStatement":
    case "DebuggerStatement":
      return false;
  }
}

function assignedInFun(v: VarName, f: JSyntax.FunctionDeclaration): boolean {
  if (f.params.some(p => p.name == v)) return false;
  return f.body.body.some(s => assignedInStmt(v, s));
}

function getVar(vars: Vars, v: VarName): ASyntax.Identifier {
  if (!(v in vars)) throw new Error("unknown identifier: " + v);
  return { type: "Identifier", name: v, version: vars[v] };
}

function phi(cond: ASyntax.Proposition, left: Transform,
                                        right: Transform):
                                        [Vars, ASyntax.Proposition, Array<VerificationCondition>] {
  let leftPr = left.prop,
      rightPr = right.prop;
  const nvars: Vars = {},
        allKeys = Object.keys(left.vars).concat(Object.keys(right.vars));
  for (const v of allKeys) {
    if (v in nvars) continue;
    if (v in left.vars && v in right.vars) {
      if (left.vars[v] < right.vars[v]) {
        leftPr = and(leftPr, eq(getVar(left.vars, v), getVar(right.vars, v)));
        nvars[v] = right.vars[v];
      } else if (left.vars[v] > right.vars[v]) {
        rightPr = and(rightPr, eq(getVar(right.vars, v), getVar(left.vars, v)));
        nvars[v] = left.vars[v];
      } else {
        nvars[v] = left.vars[v];
      }
    } else if (v in left) {
      nvars[v] = left.vars[v];
    } else {
      nvars[v] = right.vars[v];
    }
  }
  left.vcs.forEach(vc => vc.prop = and(cond, vc.prop));
  right.vcs.forEach(vc => vc.prop = and(not(cond), vc.prop));
  return [nvars, and(implies(cond, leftPr), implies(not(cond), rightPr)), left.vcs.concat(right.vcs)];
}

function havocVars(vars: Vars, f: (s: string) => boolean): Vars {
  const res: Vars = {};
  for (const v in vars) {
    res[v] = f(v) ? vars[v] + 1 : vars[v];
  }
  return res;
}

class Transform {
  vars: Vars;
  prop: ASyntax.Proposition;
  vcs: Array<VerificationCondition>;

  constructor(vars: Vars, prop: ASyntax.Proposition, vcs: Array<VerificationCondition>) {
    this.vars = vars;
    this.prop = prop;
    this.vcs = vcs;
  }

  then(t: Transform): Transform {
    this.vars = t.vars;
    this.prop = and(this.prop, t.prop);
    t.vcs.forEach(vc => vc.prop = and(t.prop, vc.prop));
    this.vcs = this.vcs.concat(t.vcs);
    return this;
  }
}

class ETransform extends Transform {
  val: ASyntax.Expression;

  constructor(vars: Vars, prop: ASyntax.Proposition, vcs: Array<VerificationCondition>, val: ASyntax.Expression) {
    super(vars, prop, vcs);
    this.val = val;
  }

  static pure(vars: Vars, val: ASyntax.Expression): ETransform {
    return new ETransform(vars, tru, [], val);
  }

  map(f: (x: ASyntax.Expression) => ASyntax.Expression): ETransform {
    return new ETransform(
      this.vars,
      this.prop,
      this.vcs,
      f(this.val)
    );
  }

  then(t: ETransform): ETransform {
    super.then(t);
    this.val = t.val;
    return this;
  }
}

class STransform extends Transform {
  bc: ASyntax.Proposition;

  constructor(vars: Vars, prop: ASyntax.Proposition, vcs: Array<VerificationCondition>, bc: ASyntax.Proposition = fls) {
    super(vars, prop, vcs);
    this.bc = bc;
  }

  then(t: STransform): STransform {
    t.vcs.forEach(vc => vc.prop = and(this.prop, vc.prop));
    this.vars = t.vars;
    this.prop = and(this.prop, implies(not(this.bc), t.prop));
    this.vcs = this.vcs.concat(t.vcs);
    this.bc = or(this.bc, t.bc);
    return this;
  }
}

export function transformExpression(ctxVars: Vars, vars: Vars, expr: JSyntax.Expression, ghost: boolean = false): ETransform {
  switch (expr.type) {
    case "Identifier":
      return ETransform.pure(vars, getVar(vars, expr.name));
    case "OldIdentifier":
      return ETransform.pure(vars, getVar(ctxVars, expr.id.name));
    case "Literal":
      return ETransform.pure(vars, expr);
    case "ArrayExpression":
      const elems: Array<ASyntax.Expression> = [];
      const res = ETransform.pure(vars, { type: "Literal", value: undefined });
      for (const elem of expr.elements) {
        const t = transformExpression(ctxVars, res.vars, elem, ghost);
        res.then(t);
        elems.push(t.val);
      }
      return res.map(v => ({ type: "ArrayExpression", elements: elems }));
    case "UnaryExpression":
      const t = transformExpression(ctxVars, vars, expr.argument, ghost);
      return t.map(v => ({ type: "UnaryExpression", operator: expr.operator, argument: v }));
    case "BinaryExpression": {
      debugger;
      const tl = transformExpression(ctxVars, vars, expr.left, ghost);
      const tr = transformExpression(ctxVars, tl.vars, expr.right, ghost);
      const res: ASyntax.Expression = { type: "BinaryExpression", operator: expr.operator, left: tl.val, right: tr.val };
      tl.then(tr);
      return tl.map(v => res);
    }
    case "LogicalExpression": {
      if (expr.operator == "&&") {
        const tl = transformExpression(ctxVars, vars, expr.left, ghost);
        const tr = transformExpression(ctxVars, tl.vars, expr.right, ghost);
        const [vars4, props4, vcs4] = phi(truthy(tl.val), tr, new ETransform(tl.vars, tru, [], tl.val));
        vcs4.forEach(vc => vc.prop = and(tl.prop, vc.prop));
        return new ETransform(vars4, props4, tl.vcs.concat(vcs4), {
          type: "ConditionalExpression", test: truthy(tl.val), consequent: tr.val, alternate: tl.val});
      } else {
        const tl = transformExpression(ctxVars, vars, expr.left, ghost);
        const tr = transformExpression(ctxVars, tl.vars, expr.right, ghost);
        const [vars4, props4, vcs4] = phi(truthy(tl.val), new ETransform(tl.vars, tru, [], tl.val), tr);
        vcs4.forEach(vc => vc.prop = and(tl.prop, vc.prop));
        return new ETransform(vars4, props4, tl.vcs.concat(vcs4), {
          type: "ConditionalExpression", test: truthy(tl.val), consequent: tl.val, alternate: tr.val});
      }
    }
    case "ConditionalExpression": {
      const tt = transformExpression(ctxVars, vars, expr.test, ghost);
      const tl = transformExpression(ctxVars, tt.vars, expr.consequent, ghost);
      const tr = transformExpression(ctxVars, tt.vars, expr.alternate, ghost);
      const [vars4, props4, vcs4] = phi(truthy(tt.val), tl, tr);
      vcs4.forEach(vc => vc.prop = and(tt.prop, vc.prop));
      return new ETransform(vars4, props4, tt.vcs.concat(vcs4), {
        type: "ConditionalExpression", test: truthy(tt.val), consequent: tl.val, alternate: tr.val});
    }
    case "AssignmentExpression": {
      if (ghost) throw new Error("assignment in pure functional context");
      const t = transformExpression(ctxVars, vars, expr.right);
      const vars2 = Object.assign({}, t.vars);
      ++vars2[expr.left.name];
      const to: ASyntax.Expression = { type: "Identifier", name: expr.left.name, version: vars2[expr.left.name] },
            asg: ASyntax.Proposition = { type: "Eq", left: to, right: t.val};
      return new ETransform(vars2, and(t.prop, asg), t.vcs, t.val);
    }
    case "SequenceExpression": {
      const res = ETransform.pure(vars, { type: "Literal", value: undefined });
      for (const elem of expr.expressions) {
        const t = transformExpression(ctxVars, res.vars, elem, ghost);
        res.then(t);
      }
      return res;
    }
    case "CallExpression":
      throw new Error("not implemented yet\n" + JSON.stringify(expr)); 
    case "FunctionExpression":
      throw new Error("not implemented yet"); 
  }
}

function transformWhileLoop(vars: Vars, whl: JSyntax.WhileStatement): STransform {
  // return verification conditions:
  // - call req in test, invariants and body
  // - assert in body
  // - invariants maintained
  // break condition: test && return in body

  // assume loop condition true and invariants true
  const tt = transformExpression(vars, vars, whl.test);
  const res: STransform = new STransform(tt.vars, and(tt.prop, truthy(tt.val)), []);
  for (const inv of whl.invariants) {
    const ti = transformExpression(vars, res.vars, inv, true);
    res.vars = ti.vars;
    res.prop = and(res.prop, ti.prop, truthy(ti.val));
  }
  const tb = transformStatement(vars, res.vars, whl.body);
  res.then(tb);

  // internal verification conditions
  const testBody: Array<JSyntax.TopLevel> = [checkInvariants(whl), {
    type: "ExpressionStatement",
    expression: { type: "CallExpression", arguments: [],
                  callee: { type: "Identifier", name: "test", decl: {type: "Unresolved"}, refs: [], isWrittenTo: false}}
  }];
    
  res.vcs.forEach(vc => vc.body = testBody);
  res.bc = and(truthy(tt.val), res.bc);

  // ensure invariants maintained
  for (const inv of whl.invariants) {
    const ti = transformExpression(vars, res.vars, inv, true);
    res.vcs.push(new VerificationCondition(ti.vars, and(res.prop, ti.prop), truthy(ti.val),
                "invariant maintained:\n" + stringifyExpr(inv),
                 vars, testBody.concat([{ type: "AssertStatement", expression: inv }])));
  }

  return res;
}

export function transformStatement(ctxVars: Vars, vars: Vars, stmt: JSyntax.Statement): STransform {
  switch (stmt.type) {
    case "VariableDeclaration": {
      const t = transformExpression(ctxVars, vars, stmt.init);
      const vars2 = Object.assign({}, t.vars);
      vars2[stmt.id.name] = 0;
      const to: ASyntax.Expression = { type: "Identifier", name: stmt.id.name, version: 0 },
            asg: ASyntax.Proposition = { type: "Eq", left: to, right: t.val};
      return new STransform(vars2, and(t.prop, asg), t.vcs);
    }
    case "BlockStatement": {
      const res: STransform = new STransform(vars, tru, []);
      for (const s of stmt.body) {
        const t = transformStatement(ctxVars, res.vars, s);
        res.then(t);
      }
      return res;
    }
    case "ExpressionStatement": {
      const t = transformExpression(ctxVars, vars, stmt.expression);
      return new STransform(t.vars, t.prop, t.vcs);
    }
    case "AssertStatement": {
      const t = transformExpression(ctxVars, vars, stmt.expression, true);
      const vc = new VerificationCondition(t.vars, t.prop, truthy(t.val), "assert:\n" + stringifyExpr(stmt.expression), ctxVars);
      return new STransform(t.vars, tru, t.vcs.concat(vc), not(truthy(t.val)));
    }
    case "IfStatement": {
      const tt = transformExpression(ctxVars, vars, stmt.test);
      const tl = transformStatement(ctxVars, tt.vars, stmt.consequent);
      const tr = transformStatement(ctxVars, tt.vars, stmt.alternate);
      const [vars2, props2, vcs2] = phi(truthy(tt.val), tl, tr);
      vcs2.forEach(vc => vc.prop = and(tt.prop, vc.prop));
      return new STransform(vars2, props2, tt.vcs.concat(vcs2),
                            or(and(truthy(tt.val), tl.bc), and(not(truthy(tt.val)), tr.bc))); 
    }
    case "ReturnStatement": {
      const t = transformExpression(ctxVars, vars, stmt.argument);
      if (!("_res_" in t.vars)) throw new Error("Return outside function");
      const to: ASyntax.Expression = { type: "Identifier", name: "_res_", version: vars["_res_"] },
            asg: ASyntax.Proposition = { type: "Eq", left: to, right: t.val };
      return new STransform(t.vars, and(t.prop, asg), t.vcs, tru);
    }
    case "WhileStatement": {
      // invariants on entry
      let vcs: Array<VerificationCondition> = [];
      for (const inv of stmt.invariants) {
        const t = transformExpression(ctxVars, vars, inv, true);
        vcs.push(new VerificationCondition(t.vars, t.prop, truthy(t.val), "invariant on entry:\n" + stringifyExpr(inv)));
      }

      // havoc changed variables
      const vars2 = havocVars(vars, v => assignedInExpr(v, stmt.test) || assignedInStmt(v, stmt.body));

      const twhile = transformWhileLoop(vars2, stmt);
      // we are going to use the returned verification conditions and break condition
      // but we will ignore its effects

      // havoc changed variables again
      const vars3 = havocVars(twhile.vars, v => assignedInExpr(v, stmt.test) || assignedInStmt(v, stmt.body));

      // assume loop conditions false and invariants true
      const tt = transformExpression(ctxVars, vars3, stmt.test);
      const res: STransform = new STransform(tt.vars,
        and(tt.prop, not(truthy(tt.val))), vcs.concat(twhile.vcs).concat(tt.vcs), twhile.bc);
      for (const inv of stmt.invariants) {
        const ti = transformExpression(ctxVars, res.vars, inv, true);
        res.vars = ti.vars;
        res.prop = and(res.prop, ti.prop, truthy(ti.val));
      }
      return res;
    }
    case "DebuggerStatement": {
      return new STransform(vars, tru, []);
    }
  }
}

function transformFunctionDeclaration(vars: Vars, f: JSyntax.FunctionDeclaration): Transform {
  // assumes mutable vars from outer scope are fresh
  const vcs: Array<VerificationCondition> = [];
  const vars2 = Object.assign({}, vars);
  for (const p of f.params) {
    vars2[p.name] = 0;
  }
  vars2["_res_"] = "_res_" in vars2 ? vars2["_res_"] + 1 : 0; 

  const res: Transform = new Transform(vars2, tru, []);
  for (const req of f.requires) {
    const tr = transformExpression(vars2, res.vars, req, true);
    res.vars = tr.vars;
    res.prop = and(res.prop, tr.prop, truthy(tr.val));
  }
  const tb = transformStatement(vars2, res.vars, f.body);
  res.then(tb);

  // internal verification conditions
  const testBody: Array<JSyntax.TopLevel> = [{
    type: "VariableDeclaration",
    id: { type: "Identifier", name: "_res_", decl: { type: "Unresolved" }, refs: [], isWrittenTo: false},
    kind: "const",
    init: { type: "CallExpression", callee: f.id, arguments: f.params }
  }];
  res.vcs.forEach(vc => vc.body = testBody);

  // ensure invariants maintained
  for (const ens of f.ensures) {
    const ens2 = replaceFunctionResult(f, ens);
    const ti = transformExpression(vars2, res.vars, ens2, true);
    res.vcs.push(new VerificationCondition(ti.vars, and(res.prop, ti.prop), truthy(ti.val),
                 stringifyExpr(ens),
                 vars2, testBody.concat([{ type: "AssertStatement", expression: ens2 }])));
  }
  res.vcs.forEach(vc => {
    delete vc.freeVars["_res_"];
    vc.description = f.id.name + ":\n" + vc.description;
  });

  return res;
}

export function transformProgram(prog: JSyntax.Program): Array<VerificationCondition> {
  const res: Transform = new STransform({}, tru, []);

  let testBody: Array<JSyntax.Statement> = [];
  const funs: Array<JSyntax.FunctionDeclaration> = [];

  for (const stmt of prog.body) {
    if (stmt.type != "FunctionDeclaration") {
      testBody = testBody.concat([stmt]);
      const t = transformStatement({}, res.vars, stmt);
      t.vcs.forEach(vc => vc.body = testBody);
      res.then(t);
    } else {
      funs.push(stmt);
    }
  }

  const vcs = res.vcs;

  // invariants
  for (const inv of prog.invariants) {
    const ti = transformExpression({}, res.vars, inv, true);
    vcs.push(new VerificationCondition(res.vars, res.prop, truthy(ti.val),
      "initially:\n" + stringifyExpr(inv),
      {}, prog.body.concat([{ type: "AssertStatement", expression: inv }])));
    for (const f of funs) {
      f.requires.push(inv);
      f.ensures.push(inv);
    }
  }


  // havoc changed variables
  const vars2 = havocVars(res.vars, v => funs.some(f => assignedInFun(v, f)));

  // add functions
  const fdecls: Array<JSyntax.TopLevel> = [];
  for (const f of funs) {
    const tf = transformFunctionDeclaration(vars2, f);
    pushAll(vcs, tf.vcs);
    fdecls.push(checkPreconditions(f));
  }
  vcs.forEach(vc => {
    vc.body = fdecls.concat(vc.body);
  });
  return vcs;
}
