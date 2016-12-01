import VerificationCondition, { VarName, Vars, SMTInput, SMTOutput } from "./vc";
import { JSyntax, stringifyExpr, checkInvariants, checkPreconditions, replaceFunctionResult } from "./javascript";
import { ASyntax, tru, fls, truthy, implies, and, or, eq, not, propositionToSMT } from "./assertions";
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

function freshResVar(vars: Vars): [Vars, VarName] {
  let i = 0;
  while (`tmp_${i}` in vars) i++;
  return [Object.assign({}, vars, {[`tmp_${i}`]: 0, "_res_": i}), `tmp_${i}`]
}

class PureContextError extends Error {
  constructor() { super("not supported in pure functional context"); }
}

type Bindings = { [varName: string]: ASyntax.Expression };

function pureExpression(ctxVars: Vars, vars: Vars, lets: Bindings, expr: JSyntax.Expression): ASyntax.Expression {
  switch (expr.type) {
    case "Identifier":
      if (expr.name in lets) return lets[expr.name];
      return getVar(vars, expr.name);
    case "OldIdentifier":
      return getVar(ctxVars, expr.id.name);
    case "Literal":
      return expr;
    case "ArrayExpression":
      return {
        type: "ArrayExpression",
        elements: expr.elements.map(e => pureExpression(ctxVars, vars, lets, e))
      };
    case "UnaryExpression":
      const argument = pureExpression(ctxVars, vars, lets, expr.argument);
      return { type: "UnaryExpression", operator: expr.operator, argument };
    case "BinaryExpression": {
      const left = pureExpression(ctxVars, vars, lets, expr.left);
      const right = pureExpression(ctxVars, vars, lets, expr.right);
      return { type: "BinaryExpression", operator: expr.operator, left, right };
    }
    case "LogicalExpression": {
      const left = pureExpression(ctxVars, vars, lets, expr.left);
      const right = pureExpression(ctxVars, vars, lets, expr.right);
      if (expr.operator == "&&") {
        return { type: "ConditionalExpression", test: truthy(left), consequent: right, alternate: left };
      } else {
        return { type: "ConditionalExpression", test: truthy(left), consequent: left, alternate: right };
      }
    }
    case "ConditionalExpression": {
      const test = truthy(pureExpression(ctxVars, vars, lets, expr.test));
      const consequent = pureExpression(ctxVars, vars, lets, expr.consequent);
      const alternate = pureExpression(ctxVars, vars, lets, expr.alternate);
      return { type: "ConditionalExpression", test, consequent, alternate };
    }
    case "AssignmentExpression": {
      throw new PureContextError();
    }
    case "SequenceExpression": {
      // ignore all expressions but the last
      return pureExpression(ctxVars, vars, lets, expr.expressions[expr.expressions.length - 1]);
    }
    case "CallExpression":
      if (expr.callee.type == "Identifier" &&
          expr.callee.decl.type == "Func") {
        return {
          type: "CallExpression",
          callee: expr.callee.decl.decl.id.name,
          arguments: expr.arguments.map(a => pureExpression(ctxVars, vars, lets, a))
        };
      }
    case "FunctionExpression":
      throw new PureContextError();
  }
}

function pureStatements(ctxVars: Vars, vars: Vars, stmts: Array<JSyntax.Statement>): ASyntax.Expression {
  if (stmts.length < 0) throw new PureContextError();
  const last = stmts[stmts.length - 1];
  if (last.type != "ReturnStatement") throw new PureContextError();
  const lets: Bindings = {};
  for (const stmt of stmts.slice(0, -1)) {
    switch (stmt.type) {
      case "VariableDeclaration":
        lets[stmt.id.name] = pureExpression(ctxVars, vars, lets, stmt.init);
        break;
      case "BlockStatement":
      case "ExpressionStatement":
      case "IfStatement":
      case "ReturnStatement":
      case "WhileStatement":
        throw new PureContextError();
      case "AssertStatement":
      case "DebuggerStatement":
        break; // ignore
    }
  }
  return pureExpression(ctxVars, vars, lets, last.argument);
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
    } else if (v in left.vars) {
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
    t.vcs.forEach(vc => vc.prop = and(this.prop, vc.prop));
    this.vars = t.vars;
    this.prop = and(this.prop, t.prop);
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
    // prepend to t's VCs
    t.vcs.forEach(vc => vc.prop = and(this.prop, not(this.bc), vc.prop));

    // propagate variables
    let propVars = tru;
    for (const v of Object.keys(t.vars)) {
      if (v in this.vars && this.vars[v] < t.vars[v]) {
        propVars = and(propVars, eq(getVar(this.vars, v), getVar(t.vars, v)));
      }
    }
    this.vars = t.vars;

    // create resulting transform
    this.prop = and(this.prop, implies(this.bc, propVars), implies(not(this.bc), t.prop));
    this.vcs = this.vcs.concat(t.vcs);
    this.bc = or(this.bc, t.bc);
    return this;
  }
}

function transformFunctionCall(ctxVars: Vars, vars: Vars, f: JSyntax.FunctionDeclaration, args: Array<ASyntax.Expression>, expanding: boolean): ETransform {
  // create result variable
  const [vars2, resVarName] = freshResVar(vars);
  const resVar: ASyntax.Identifier = { type: "Identifier", name: resVarName, version: vars2[resVarName] };
  const call: ASyntax.Expression = { type: "CallExpression", callee: f.id.name, arguments: [] };

  // bind arguments
  let prop = tru;
  f.params.forEach((p, idx) => {
    vars2[p.name] = p.name in vars2 ? vars2[p.name] + 1 : 0;
    const v: ASyntax.Expression = { type: "Identifier", name: p.name, version: vars2[p.name] };
    prop = and(prop, eq(v, args[idx]));
    call.arguments.push(v);
  });

  // require preconditions
  const vcs = f.requires.map(req =>
    new VerificationCondition(vars2, prop, truthy(pureExpression(vars2, vars2, {}, req)),
                              f.id.name + ":\nrequires:\n" + stringifyExpr(req),
                              ctxVars));

  const res = new ETransform(vars2, and(prop, eq(resVar, call)), vcs, resVar);

  // may expand body
  if (expanding) {
    const body = transformStatement(vars, vars2, f.body, false);
    res.vars = body.vars;
    res.prop = and(res.prop, body.prop);
  } else {
    res.vars = havocVars(res.vars, v => assignedInStmt(v, f.body));
  }

  // assume post conditions
  for (const post of f.ensures) {
    res.prop = and(res.prop, truthy(pureExpression(vars, res.vars, {}, post)));
  }

  return res;
}

export function transformExpression(ctxVars: Vars, vars: Vars, expr: JSyntax.Expression, expanding: boolean): ETransform {
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
        const t = transformExpression(ctxVars, res.vars, elem, expanding);
        res.then(t);
        elems.push(t.val);
      }
      return res.map(v => ({ type: "ArrayExpression", elements: elems }));
    case "UnaryExpression":
      const t = transformExpression(ctxVars, vars, expr.argument, expanding);
      return t.map(v => ({ type: "UnaryExpression", operator: expr.operator, argument: v }));
    case "BinaryExpression": {
      const tl = transformExpression(ctxVars, vars, expr.left, expanding);
      const tr = transformExpression(ctxVars, tl.vars, expr.right, expanding);
      const res: ASyntax.Expression = { type: "BinaryExpression", operator: expr.operator, left: tl.val, right: tr.val };
      tl.then(tr);
      return tl.map(v => res);
    }
    case "LogicalExpression": {
      const tl = transformExpression(ctxVars, vars, expr.left, expanding);
      const tr = transformExpression(ctxVars, tl.vars, expr.right, expanding);
      if (expr.operator == "&&") {
        const [vars4, props4, vcs4] = phi(truthy(tl.val), tr, new ETransform(tl.vars, tru, [], tl.val));
        vcs4.forEach(vc => vc.prop = and(tl.prop, vc.prop));
        return new ETransform(vars4, props4, tl.vcs.concat(vcs4), {
          type: "ConditionalExpression", test: truthy(tl.val), consequent: tr.val, alternate: tl.val});
      } else {
        const [vars4, props4, vcs4] = phi(truthy(tl.val), new ETransform(tl.vars, tru, [], tl.val), tr);
        vcs4.forEach(vc => vc.prop = and(tl.prop, vc.prop));
        return new ETransform(vars4, props4, tl.vcs.concat(vcs4), {
          type: "ConditionalExpression", test: truthy(tl.val), consequent: tl.val, alternate: tr.val});
      }
    }
    case "ConditionalExpression": {
      const tt = transformExpression(ctxVars, vars, expr.test, expanding);
      const tl = transformExpression(ctxVars, tt.vars, expr.consequent, expanding);
      const tr = transformExpression(ctxVars, tt.vars, expr.alternate, expanding);
      const [vars4, props4, vcs4] = phi(truthy(tt.val), tl, tr);
      vcs4.forEach(vc => vc.prop = and(tt.prop, vc.prop));
      return new ETransform(vars4, props4, tt.vcs.concat(vcs4), {
        type: "ConditionalExpression", test: truthy(tt.val), consequent: tl.val, alternate: tr.val});
    }
    case "AssignmentExpression": {
      const t = transformExpression(ctxVars, vars, expr.right, expanding);
      const vars2 = Object.assign({}, t.vars);
      ++vars2[expr.left.name];
      const to: ASyntax.Expression = { type: "Identifier", name: expr.left.name, version: vars2[expr.left.name] },
            asg: ASyntax.Proposition = { type: "Eq", left: to, right: t.val};
      return new ETransform(vars2, and(t.prop, asg), t.vcs, t.val);
    }
    case "SequenceExpression": {
      const res = ETransform.pure(vars, { type: "Literal", value: undefined });
      for (const elem of expr.expressions) {
        const t = transformExpression(ctxVars, res.vars, elem, expanding);
        res.then(t);
      }
      return res;
    }
    case "CallExpression":
      if (expr.callee.type == "Identifier" &&
          expr.callee.decl.type == "Func") { // a known top level function
        const func = expr.callee.decl.decl;

        // evaluate arguments
        const res = ETransform.pure(vars, { type: "Literal", value: undefined });
        const args: Array<ASyntax.Expression> = [];
        for (const fv of func.freeVars) {
          args.push({ type: "Identifier", name: fv, version: vars[fv] });
        }
        for (const arg of expr.arguments) {
          const t = transformExpression(ctxVars, res.vars, arg, expanding);
          res.then(t);
          args.push(t.val);
        }
        
        // try to expand function
        const invocation = transformFunctionCall(ctxVars, res.vars, func, args, expanding);
        res.then(invocation);

        // pop stack frame
        res.vars["_res_"] = vars["_res_"];
        func.params.forEach(p => {
          res.vars[p.name]++;   // havoc function parameters
          if (p.name in vars) { // but remember old value if available
            res.prop = and(res.prop, eq(getVar(vars, p.name), getVar(res.vars, p.name)));
          }
        });
        return res;
      }
    case "FunctionExpression":
      throw new Error("not implemented yet"); 
  }
}

function transformWhileLoop(vars: Vars, whl: JSyntax.WhileStatement, expanding: boolean): STransform {
  // return verification conditions:
  // - call req in test, invariants and body
  // - assert in body
  // - invariants maintained
  // break condition: test && return in body

  // assume loop condition true and invariants true
  const tt = transformExpression(vars, vars, whl.test, expanding);
  const res: STransform = new STransform(tt.vars, and(tt.prop, truthy(tt.val)), []);
  for (const inv of whl.invariants) {
    const ti = pureExpression(vars, res.vars, {}, inv);
    res.prop = and(res.prop, truthy(ti));
  }
  const tb = transformStatement(vars, res.vars, whl.body, expanding);
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
    const ti = pureExpression(vars, res.vars, {}, inv);
    res.vcs.push(new VerificationCondition(res.vars, res.prop, truthy(ti),
                "invariant maintained:\n" + stringifyExpr(inv),
                 vars, testBody.concat([{ type: "AssertStatement", expression: inv }])));
  }

  return res;
}

export function transformStatement(ctxVars: Vars, vars: Vars, stmt: JSyntax.Statement, expanding: boolean): STransform {
  switch (stmt.type) {
    case "VariableDeclaration": {
      const t = transformExpression(ctxVars, vars, stmt.init, expanding);
      const vars2 = Object.assign({}, t.vars);
      vars2[stmt.id.name] = 0;
      const to: ASyntax.Expression = { type: "Identifier", name: stmt.id.name, version: 0 },
            asg: ASyntax.Proposition = { type: "Eq", left: to, right: t.val};
      return new STransform(vars2, and(t.prop, asg), t.vcs);
    }
    case "BlockStatement": {
      const res: STransform = new STransform(vars, tru, []);
      for (const s of stmt.body) {
        const t = transformStatement(ctxVars, res.vars, s, expanding);
        res.then(t);
      }
      return res;
    }
    case "ExpressionStatement": {
      const t = transformExpression(ctxVars, vars, stmt.expression, expanding);
      return new STransform(t.vars, t.prop, t.vcs);
    }
    case "AssertStatement": {
      const t = pureExpression(ctxVars, vars, {}, stmt.expression);
      const vc = new VerificationCondition(vars, tru, truthy(t), "assert:\n" + stringifyExpr(stmt.expression), ctxVars);
      return new STransform(vars, tru, [vc], not(truthy(t)));
    }
    case "IfStatement": {
      const tt = transformExpression(ctxVars, vars, stmt.test, expanding);
      const tl = transformStatement(ctxVars, tt.vars, stmt.consequent, expanding);
      const tr = transformStatement(ctxVars, tt.vars, stmt.alternate, expanding);
      const [vars2, props2, vcs2] = phi(truthy(tt.val), tl, tr);
      vcs2.forEach(vc => vc.prop = and(tt.prop, vc.prop));
      return new STransform(vars2, props2, tt.vcs.concat(vcs2),
                            or(and(truthy(tt.val), tl.bc), and(not(truthy(tt.val)), tr.bc))); 
    }
    case "ReturnStatement": {
      const t = transformExpression(ctxVars, vars, stmt.argument, expanding);
      if (!("_res_" in t.vars)) throw new Error("Return outside function");
      const resVar = `tmp_${t.vars["_res_"]}`;
      const to: ASyntax.Expression = { type: "Identifier", name: resVar, version: vars[resVar] },
            asg: ASyntax.Proposition = { type: "Eq", left: to, right: t.val };
      return new STransform(t.vars, and(t.prop, asg), t.vcs, tru);
    }
    case "WhileStatement": {
      // invariants on entry
      let vcs: Array<VerificationCondition> = [];
      for (const inv of stmt.invariants) {
        const t = pureExpression(ctxVars, vars, {}, inv);
        vcs.push(new VerificationCondition(vars, tru, truthy(t), "invariant on entry:\n" + stringifyExpr(inv)));
      }

      // havoc changed variables
      const vars2 = havocVars(vars, v => assignedInExpr(v, stmt.test) || assignedInStmt(v, stmt.body));

      const twhile = transformWhileLoop(vars2, stmt, expanding);
      // we are going to use the returned verification conditions and break condition
      // but we will ignore its effects

      // havoc changed variables again
      const vars3 = havocVars(twhile.vars, v => assignedInExpr(v, stmt.test) || assignedInStmt(v, stmt.body));

      // assume loop conditions false and invariants true
      const tt = transformExpression(ctxVars, vars3, stmt.test, expanding);
      const res: STransform = new STransform(tt.vars,
        and(tt.prop, not(truthy(tt.val))), vcs.concat(twhile.vcs).concat(tt.vcs), twhile.bc);
      for (const inv of stmt.invariants) {
        const ti = pureExpression(ctxVars, res.vars, {}, inv);
        res.prop = and(res.prop, truthy(ti));
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
  const [vars2, resVarName] = freshResVar(vars);
  const resVar: ASyntax.Identifier = { type: "Identifier", name: resVarName, version: vars2[resVarName] };
  
  // add arguments to scope 
  const args: Array<ASyntax.Expression> = [];
  for (const fv of f.freeVars) {
    args.push({ type: "Identifier", name: fv, version: vars[fv] });
  }
  for (const p of f.params) {
    vars2[p.name] = 0;
    args.push({ type: "Identifier", name: p.name, version: 0 });
  }
  const call: ASyntax.Expression = { type: "CallExpression", callee: f.id.name, arguments: args };

  const res: Transform = new Transform(vars2, eq(resVar, call), []);
  for (const req of f.requires) {
    const tr = pureExpression(vars2, res.vars, {}, req);
    res.prop = and(res.prop, truthy(tr));
  }
  const tb = transformStatement(vars2, res.vars, f.body, true);
  res.then(tb);

  // internal verification conditions
  const testBody: Array<JSyntax.TopLevel> = [{
    type: "VariableDeclaration",
    id: { type: "Identifier", name: "_res_", decl: { type: "Unresolved" }, refs: [], isWrittenTo: false},
    kind: "const",
    init: { type: "CallExpression", callee: f.id, arguments: f.params }
  }];
  res.vcs.forEach(vc => vc.body = testBody);

  // ensure post conditions
  for (const ens of f.ensures) {
    const ens2 = replaceFunctionResult(f, ens);
    const ti = pureExpression(vars2, res.vars, {}, ens);
    res.vcs.push(new VerificationCondition(res.vars, res.prop, truthy(ti),
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
      const t = transformStatement({}, res.vars, stmt, true);
      t.vcs.forEach(vc => vc.body = testBody);
      res.then(t);
    } else {
      funs.push(stmt);
    }
  }

  const vcs = res.vcs;

  // invariants
  for (const inv of prog.invariants) {
    const ti = pureExpression({}, res.vars, {}, inv);
    vcs.push(new VerificationCondition(res.vars, res.prop, truthy(ti),
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
  const funcTestBodies: Array<JSyntax.TopLevel> = [];
  for (const f of funs) {
    const tf = transformFunctionDeclaration(vars2, f);
    pushAll(vcs, tf.vcs);
    funcTestBodies.push(checkPreconditions(f));
  }
  vcs.forEach(vc => {
    vc.body = funcTestBodies.concat(vc.body);
    vc.fns = funs;
  });
  return vcs;
}