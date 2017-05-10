import VerificationCondition, { VarName, Vars, SMTInput, SMTOutput } from "./verification";
import { JSyntax, stringifyExpr, declName, checkInvariants, checkPreconditions, replaceFunctionResult } from "./javascript";
import { ASyntax, tru, fls, truthy, implies, and, iff, or, eq, not, propositionToSMT, expressionToSMT } from "./propositions";
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
      return assignedInExpr(v, expr.callee) || expr.args.some(e => assignedInExpr(v, e));
    // case "FunctionExpression":
    //   throw new Error("not implemented yet");
    case "SpecExpression":
      return assignedInExpr(v, expr.callee) || assignedInExpr(v, expr.pre) || assignedInExpr(v, expr.post);
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
    case "FunctionDeclaration":
      if (stmt.params.some(p => p.name == v)) return false;
      return assignedInStmt(v, stmt.body);
  }
}

function getVar(vars: Vars, name: VarName): ASyntax.Identifier {
  if (!(name in vars)) throw new Error("unknown identifier: " + name);
  return { type: "Identifier", name, version: vars[name] };
}

function freshVar(vars: Vars, name: VarName): ASyntax.Identifier {
  if (!(name in vars)) {
    vars[name] = 0;
  } else {
    vars[name]++;
  }
  return getVar(vars, name);
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
      return {
        type: "CallExpression",
        callee: pureExpression(ctxVars, vars, lets, expr.callee),
        args: expr.args.map(a => pureExpression(ctxVars, vars, lets, a))
      };
    case "SpecExpression": {
      const vars2 = Object.assign({}, vars);
      const args: Array<ASyntax.Identifier> = [];
      for (const p of expr.args) {
        args.push(freshVar(vars2, p));
      }
      const callee = pureExpression(ctxVars, vars, lets, expr.callee);
      const preP: ASyntax.Proposition = { type: "Precondition", callee, args };
      const postP: ASyntax.Proposition = { type: "Postcondition", callee, args };
      const callP: ASyntax.Proposition = { type: "CallTrigger", callee, args };
      const r = truthy(pureExpression(ctxVars, vars2, lets, expr.pre));
      const s = truthy(pureExpression(ctxVars, vars2, lets, expr.post));
      const forAll: ASyntax.Proposition = { type: "ForAll", callee, args,
        prop: and(callP, implies(r, preP), implies(and(r, postP), s))
      };
      const fnCheck: ASyntax.Expression = {
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
      const consequent: ASyntax.Expression = { type: "Literal", value: true };
      const alternate: ASyntax.Expression = { type: "Literal", value: false };
      return { type: "ConditionalExpression", test, consequent, alternate };
    }

    // case "FunctionExpression":
    //   throw new PureContextError();
  }
}

function pureStatements(ctxVars: Vars, vars: Vars, stmts: Array<JSyntax.Statement>): ASyntax.Expression {
  if (stmts.length < 1) throw new PureContextError();
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
      case "FunctionDeclaration":
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

let nextUniqueFuncId = 0
function uniqueFuncId() { return nextUniqueFuncId++; }

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

export function transformExpression(ctxVars: Vars, vars: Vars, expr: JSyntax.Expression): ETransform {
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
        const t = transformExpression(ctxVars, res.vars, elem);
        res.then(t);
        elems.push(t.val);
      }
      return res.map(v => ({ type: "ArrayExpression", elements: elems }));
    case "UnaryExpression":
      const t = transformExpression(ctxVars, vars, expr.argument);
      return t.map(v => ({ type: "UnaryExpression", operator: expr.operator, argument: v }));
    case "BinaryExpression": {
      const tl = transformExpression(ctxVars, vars, expr.left);
      const tr = transformExpression(ctxVars, tl.vars, expr.right);
      const res: ASyntax.Expression = { type: "BinaryExpression", operator: expr.operator, left: tl.val, right: tr.val };
      tl.then(tr);
      return tl.map(v => res);
    }
    case "LogicalExpression": {
      const tl = transformExpression(ctxVars, vars, expr.left);
      const tr = transformExpression(ctxVars, tl.vars, expr.right);
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
      const tt = transformExpression(ctxVars, vars, expr.test);
      const tl = transformExpression(ctxVars, tt.vars, expr.consequent);
      const tr = transformExpression(ctxVars, tt.vars, expr.alternate);
      const [vars4, props4, vcs4] = phi(truthy(tt.val), tl, tr);
      vcs4.forEach(vc => vc.prop = and(tt.prop, vc.prop));
      return new ETransform(vars4, props4, tt.vcs.concat(vcs4), {
        type: "ConditionalExpression", test: truthy(tt.val), consequent: tl.val, alternate: tr.val});
    }
    case "AssignmentExpression": {
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
        const t = transformExpression(ctxVars, res.vars, elem);
        res.then(t);
      }
      return res;
    }
    case "CallExpression": {
      // evaluate callee
      const res = transformExpression(ctxVars, vars, expr.callee);
      const callee = res.val;

      // evaluate arguments
      const args: Array<ASyntax.Expression> = [];
      for (const arg of expr.args) {
        const t = transformExpression(ctxVars, res.vars, arg);
        res.then(t);
        args.push(t.val);
      }

      // apply call trigger
      res.prop = and(res.prop, { type: "CallTrigger", callee, args });

      // verify precondition
      res.vcs.push(new VerificationCondition(res.vars, res.prop,
                                           { type: "Precondition", callee, args },
                                           `precondition ${stringifyExpr(expr)}`));
      
      // assume postcondition and return result
      res.prop = and(res.prop, { type: "Postcondition", callee, args });
      res.val = { type: "CallExpression", callee, args };
      return res;
    }
    case "SpecExpression":
      throw new Error("Unsupported");
    // case "FunctionExpression":
    //   throw new Error("not implemented yet"); 
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
    const ti = pureExpression(vars, res.vars, {}, inv);
    res.prop = and(res.prop, truthy(ti));
  }
  const tb = transformStatement(vars, res.vars, whl.body);
  res.then(tb);

  // internal verification conditions
  const testBody: Array<JSyntax.Statement> = [checkInvariants(whl), {
    type: "ExpressionStatement",
    expression: { type: "CallExpression", args: [],
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

function transformSpec(vars: Vars, f: JSyntax.FunctionDeclaration): ASyntax.Proposition {
  const vars2 = Object.assign({}, vars);
  const callee: ASyntax.Identifier = { type: "Identifier", name: f.id.name, version: 0 };
  
  // add arguments to scope 
  const args: Array<ASyntax.Identifier> = [];
  for (const p of f.params) {
    args.push(freshVar(vars2, p.name));
  }

  let req = tru;
  for (const r of f.requires) {
    req = and(req, truthy(pureExpression(vars2, vars2, {}, r)));
  }
  let ens = tru;
  for (const r of f.ensures) {
    ens = and(ens, truthy(pureExpression(vars2, vars2, {}, r)));
  }
  const preP: ASyntax.Proposition = { type: "Precondition", callee, args };
  const postP: ASyntax.Proposition = { type: "Postcondition", callee, args };
  const callP: ASyntax.Proposition = { type: "CallTrigger", callee, args };
  const forAll: ASyntax.Proposition = { type: "ForAll", callee, args,
    prop: and(callP, iff(req, preP), iff(postP, implies(req, ens)))
  };
  const fnCheck: ASyntax.Expression = {
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

function verifyFunctionDeclaration(vars: Vars, f: JSyntax.FunctionDeclaration): Transform {

  // havoc all let-bound free variable
  const vars2 = Object.assign({_res_: 0}, havocVars(vars, v => f.freeVars.some(decl =>
    decl.type == "Var" && decl.decl.id.name == v && decl.decl.kind == "let")));

  const vcs: Array<VerificationCondition> = [];
  
  // add arguments to scope 
  const args: Array<ASyntax.Expression> = [];
  for (const p of f.params) {
    args.push(freshVar(vars2, p.name));
  }
  const callee: ASyntax.Expression = { type: "Identifier", name: f.id.name, version: 0 };
  const eq_call: ASyntax.Proposition = eq({ type: "Identifier", name: "_res_", version: 0 },
                                          { type: "CallExpression", callee, args });
  const res: Transform = new Transform(vars2, eq_call, []);
  for (const req of f.requires) {
    const tr = pureExpression(vars2, res.vars, {}, req);
    res.prop = and(res.prop, truthy(tr));
  }
  const tb = transformStatement(vars2, res.vars, f.body);
  res.then(tb);

  // internal verification conditions
  const testBody: Array<JSyntax.Statement> = [{
    type: "VariableDeclaration",
    id: { type: "Identifier", name: "_res_", decl: { type: "Unresolved" }, refs: [], isWrittenTo: false},
    kind: "const",
    init: { type: "CallExpression", callee: f.id, args: f.params }
  }];
  res.vcs.forEach(vc => vc.body = testBody);

  // ensure post conditions
  for (const ens of f.ensures) {
    const ens2 = replaceFunctionResult(f, ens);
    const vars3 = Object.assign({}, vars2);
    delete vars3[f.id.name]; // funcName not free
    delete vars3["_res_"]; // res not free
    const ti = pureExpression(vars2, res.vars, {}, ens);
    res.vcs.push(new VerificationCondition(res.vars, res.prop, truthy(ti),
                 stringifyExpr(ens),
                 vars3, testBody.concat([{ type: "AssertStatement", expression: ens2 }])));
  }
  res.vcs.forEach(vc => {
    // delete vc.freeVars["_res_"];
    vc.description = f.id.name + ":\n" + vc.description;
  });

  return res;
}

export function transformStatement(ctxVars: Vars, vars: Vars, stmt: JSyntax.Statement): STransform {
  switch (stmt.type) {
    case "VariableDeclaration": {
      const t = transformExpression(ctxVars, vars, stmt.init);
      const vars2 = Object.assign({}, t.vars);
      vars2[stmt.id.name] = 0; // TODO enable shadowing
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
      const t = pureExpression(ctxVars, vars, {}, stmt.expression);
      const vc = new VerificationCondition(vars, tru, truthy(t), "assert:\n" + stringifyExpr(stmt.expression), ctxVars);
      return new STransform(vars, tru, [vc], not(truthy(t)));
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
      const to: ASyntax.Expression = { type: "Identifier", name: "_res_", version: 0 },
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
        const ti = pureExpression(ctxVars, res.vars, {}, inv);
        res.prop = and(res.prop, truthy(ti));
      }
      return res;
    }
    case "DebuggerStatement": {
      return new STransform(vars, tru, []);
    }
    case "FunctionDeclaration": {
      const vars2 = Object.assign({}, vars);
      vars2[stmt.id.name] = 0; // TODO enable shadowing
      const id: ASyntax.Expression = { type: "Identifier", name: stmt.id.name, version: 0 },
            eq_f: ASyntax.Proposition = eq(id, { type: "FunctionLiteral", id: uniqueFuncId() }),
            spec_f: ASyntax.Proposition = transformSpec(vars2, stmt);
      const t: Transform = verifyFunctionDeclaration(vars2, stmt);
      t.vcs.forEach(vc => vc.prop = and(eq_f, spec_f, vc.prop));
      return new STransform(vars2, and(eq_f, spec_f), t.vcs);
    }
  }
}

export function transformProgram(prog: JSyntax.Program): Array<VerificationCondition> {

  const res: Transform = new STransform({}, tru, []);

  // function should maintain invariants
  for (const inv of prog.invariants) {
    for (const f of prog.functions) {
      f.requires.push(inv);
      f.ensures.push(inv);
    }
  }

  // go through all statements
  let testBody: Array<JSyntax.Statement> = [];
  for (const stmt of prog.body) {
    testBody = testBody.concat([stmt]);
    const t = transformStatement({}, res.vars, stmt);
    t.vcs.forEach(vc => vc.body = testBody);
    res.then(t);
  }

  // we only care about the verification conditions
  const vcs = res.vcs;

  // main program body needs to establish invariants
  for (const inv of prog.invariants) {
    const ti = pureExpression({}, res.vars, {}, inv);
    vcs.push(new VerificationCondition(res.vars, res.prop, truthy(ti),
      "initially:\n" + stringifyExpr(inv),
      {}, prog.body.concat([{ type: "AssertStatement", expression: inv }])));
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