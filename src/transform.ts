import { VarName, Vars, SMTInput, SMTOutput } from "./vc";
import { JSyntax } from "./javascript";
import { ASyntax, tru, fls, truthy, implies, and, or, eq, not } from "./assertions";

export function createVars(names: Array<VarName> = []): Vars {
  return names.reduce((vars: Vars, n: VarName) => {
    vars[n] = 0;
    return vars;
  }, {});
}

function getVar(v: VarName, vars: Vars): ASyntax.Identifier {
  const version = v in vars ? vars[v] : 0;
  return { type: "Identifier", name: v, version };
}

function phi(cond: ASyntax.Proposition, left: Vars, leftP: ASyntax.Proposition,
                                        right: Vars, rightP: ASyntax.Proposition):
                                        [Vars, ASyntax.Proposition] {
  let leftPr = leftP,
      rightPr = rightP;
  const nvars: Vars = {},
        allKeys = Object.keys(left).concat(Object.keys(right));
  for (const v of allKeys) {
    if (v in nvars) continue;
    if (v in left && v in right) {
      if (left[v] < right[v]) {
        leftPr = and(leftPr, eq(getVar(v, left), getVar(v, right)));
        nvars[v] = right[v];
      } else if (left[v] > right[v]) {
        rightPr = and(rightPr, eq(getVar(v, right), getVar(v, left)));
        nvars[v] = left[v];
      } else {
        nvars[v] = left[v];
      }
    } else if (v in left) {
      nvars[v] = left[v];
    } else {
      nvars[v] = right[v];
    }
  }
  return [nvars, and(implies(cond, leftPr), implies(not(cond), rightPr))];
}

export function assignedInExpr(v: VarName, expr: JSyntax.Expression): boolean {
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

export function assignedInStmt(v: VarName, stmt: JSyntax.Statement): boolean {
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

export function assignedInFun(v: VarName, f: JSyntax.FunctionDeclaration): boolean {
  if (f.params.some(p => p.name == v)) return false;
  return f.body.body.some(s => assignedInStmt(v, s));
}

export function havocVars(vars: Vars, f: (s: string) => boolean): Vars {
  const res: Vars = {};
  for (const v in vars) {
    res[v] = f(v) ? vars[v] + 1 : vars[v];
  }
  return res;
}

type StateE = [Vars, ASyntax.Proposition, ASyntax.Expression];

export function transformExpression(vars: Vars, expr: JSyntax.Expression, readOnly: boolean = false): StateE {
  switch (expr.type) {
    case "Identifier":
      return [vars, tru, { type: "Identifier", name: expr.name, version: vars[expr.name] }];
    case "OldIdentifier":
      if (!expr.version) throw new Error("version expected");
      return [vars, tru, { type: "Identifier", name: expr.id.name, version: expr.version }];
    case "Literal":
      return [vars, tru, expr];
    case "ArrayExpression":
      type CollectE = [Vars, ASyntax.Proposition, Array<ASyntax.Expression>];
      const initial: CollectE = [vars, tru, []];
      const [vars4, p4, elems]: CollectE = expr.elements.reduce(([vars2, p2, elems]: CollectE, ele: JSyntax.Expression) => {
        const [vars3, p3, v] = transformExpression(vars2, ele, readOnly);
        elems.push(v);
        return <CollectE>[vars4, and(p2, p3), elems];
      }, initial);
      return [vars4, p4, { type: "ArrayExpression", elements: elems }];
    case "UnaryExpression":
      const [vars2, props, v] = transformExpression(vars, expr.argument, readOnly);
      return [vars2, props, { type: "UnaryExpression", operator: expr.operator, argument: v}];
    case "BinaryExpression": {
      const [vars2, props, v] = transformExpression(vars, expr.left, readOnly);
      const [vars3, props2, v2] = transformExpression(vars2, expr.right, readOnly);
      return [vars3, and(props, props2), {
        type: "BinaryExpression", operator: expr.operator, left: v, right: v2}];
    }
    case "LogicalExpression": {
      if (expr.operator == "&&") {
        const [vars2, props2, v2] = transformExpression(vars, expr.left, readOnly);
        const [vars3, props3, v3] = transformExpression(vars2, expr.right, readOnly);
        const [vars4, props4] = phi(truthy(v2), vars3, props3, vars2, tru);
        return [vars4, props4, {
          type: "ConditionalExpression", test: truthy(v2), consequent: v3, alternate: v2}];
      } else {
        const [vars2, props2, v2] = transformExpression(vars, expr.left, readOnly);
        const [vars3, props3, v3] = transformExpression(vars2, expr.right, readOnly);
        const [vars4, props4] = phi(truthy(v2), vars2, tru, vars3, props3);
        return [vars4, props4, {
          type: "ConditionalExpression", test: truthy(v2), consequent: v2, alternate: v3}];
      }
    }
    case "ConditionalExpression": {
      const [vars2, props2, v2] = transformExpression(vars, expr.test, readOnly);
      const [vars3, props3, v3] = transformExpression(vars2, expr.consequent, readOnly);
      const [vars4, props4, v4] = transformExpression(vars2, expr.alternate, readOnly);
      const [vars5, props5] = phi(truthy(v2), vars3, props3, vars4, props4);
      return [vars5, props5, {
          type: "ConditionalExpression", test: truthy(v2), consequent: v3, alternate: v4}];
    }
    case "AssignmentExpression": {
      if (readOnly) throw new Error("assignment in pure functional context");
      const [vars2, props2, v2] = transformExpression(vars, expr.right);
      const vars3 = Object.assign({}, vars2);
      ++vars3[expr.left.name];
      const to: ASyntax.Expression = { type: "Identifier", name: expr.left.name, version: vars3[expr.left.name] },
            asg: ASyntax.Proposition = { type: "Eq", left: to, right: v2};
      return [vars3, and(props2, asg), v2];
    }
    case "SequenceExpression": {
      const initial: StateE = [vars, tru, { type: "Literal", value: undefined }];
      return expr.expressions.reduce(([vars2, props2, v]: StateE, e: JSyntax.Expression): StateE => {
        const [vars3, props3, v3] = transformExpression(vars2, e, readOnly);
        return [ vars3, and(props2, props3), v3];
      }, initial);
    }
    case "CallExpression":
      throw new Error("not implemented yet\n" + JSON.stringify(expr)); 
    case "FunctionExpression":
      throw new Error("not implemented yet"); 
  }
}

//             Variables, Verification Condition, Break Condition
type StateS = [Vars, ASyntax.Proposition, ASyntax.Proposition];

export function transformStatement(vars: Vars, stmt: JSyntax.Statement): StateS {
  switch (stmt.type) {
    case "VariableDeclaration": {
      const [vars2, props2, v2] = transformExpression(vars, stmt.init);
      vars2[stmt.id.name] = 0;
      const to: ASyntax.Expression = { type: "Identifier", name: stmt.id.name, version: 0 },
            asg: ASyntax.Proposition = { type: "Eq", left: to, right: v2};
      return [vars2, and(props2, asg), fls];
    }
    case "BlockStatement": {
      const initial: StateS = [vars, tru, fls];
      return stmt.body.reduce(([vars2, props2, bc]: StateS, s: JSyntax.Statement): StateS => {
        const [vars3, props3, bc3] = transformStatement(vars2, s);
        return [vars3, and(props2, implies(not(bc), props3)), or(bc, bc3)];
      }, initial);
    }
    case "ExpressionStatement": {
      const [vars2, props2] = transformExpression(vars, stmt.expression);
      return [vars2, props2, fls];
    }
    case "AssertStatement": {
      const [,, v] = transformExpression(vars, stmt.expression, true);
      return [vars, truthy(v), fls];
    }
    case "IfStatement": {
      const [vars2, props2, v2] = transformExpression(vars, stmt.test);
      const [vars3, props3, bc3] = transformStatement(vars2, stmt.consequent);
      const [vars4, props4, bc4] = transformStatement(vars2, stmt.alternate);
      const [vars5, props5] = phi(truthy(v2), vars3, props3, vars4, props4);
      return [vars5, props5, or(and(truthy(v2), bc3), and(not(truthy(v2)), bc4))];
    }
    case "ReturnStatement": {
      const [vars2, props2, v2]: StateE = transformExpression(vars, stmt.argument);
      if (!("_res_" in vars)) throw new Error("Return outside function");
      const to: ASyntax.Expression = { type: "Identifier", name: "_res_", version: vars["_res_"]},
            asg: ASyntax.Proposition = { type: "Eq", left: to, right: v2 };
      return [vars2, and(props2, asg), tru];
    }
    case "WhileStatement": {
      // havoc changed variables
      const vars2 = havocVars(vars, v => assignedInExpr(v, stmt.test) || assignedInStmt(v, stmt.body));

      // computed return conditions and values
      const [vars3, p, v] = transformExpression(vars2, stmt.test);
      const [vars4, p2, bc] = transformStatement(vars3, stmt.body);

      // havoc variables again
      const vars5 = havocVars(vars4, v => assignedInExpr(v, stmt.test) || assignedInStmt(v, stmt.body));

      // transform condition and invariants
      const [vars6, p6, v6] = transformExpression(vars5, stmt.test);
      const invariants = stmt.invariants.reduce((p2: ASyntax.Proposition, inv: JSyntax.Expression) => {
        const [,, v7] = transformExpression(vars6, inv, true);
        return and(p2, truthy(v7));
      }, tru);

      return [vars6, and(
        p6,
        not(truthy(v6)),
        invariants,
        p,
        implies(truthy(v), p2)
      ), and(truthy(v), bc)];
    }
    case "DebuggerStatement": {
      return [vars, tru, fls];
    }
  }
}

export function transformTopLevel(vars: Vars, stmt: JSyntax.TopLevel): StateS {
  switch (stmt.type) {
    case 'ReturnStatement':
      throw new Error("global return not permitted");
    case 'FunctionDeclaration':
      // TODO not implemented yet
      return [vars, tru, fls];
    default:
      return transformStatement(vars, stmt);
  }
}

export function transformProgram(prog: Array<JSyntax.TopLevel>): StateS {
  const vars: Vars = {};
  const initial: StateS = [vars, tru, fls];
  return prog.reduce(([vars2, props2, bc]: StateS, s: JSyntax.TopLevel): StateS => {
    const [vars3, props3, bc3] = transformTopLevel(vars2, s);
    return [vars3, and(props2, implies(not(bc), props3)), or(bc, bc3)];
  }, initial);
}

function smtToArray(smt: SMTOutput): Array<any> {
  const s = smt.trim();
  if (s == "empty") return [];
  const m = s.match(/^\(cons (\w+|\(.*\))\ (.*)\)$/);
  if (!m) throw new Error("Cannot parse output!");
  const [_, h, t] = m;
  return [smtToValue(h)].concat(smtToArray(t));
}

export function smtToValue(smt: SMTOutput): any {
  const s = smt.trim();
  if (s == "jsundefined") return undefined;
  if (s == "jsnull") return null;
  const m = s.match(/^\((\w+)\ (.*)\)$/);
  if (!m) throw new Error("Cannot parse output!");
  const [_, tag, v] = m;
  switch (tag) {
    case "jsbool": return v == "true";
    case "jsnum": const neg = v.match(/\(- ([0-9]+)\)/); return neg ? -neg[1] : +v;
    case "jsstr": return v.substr(1, v.length - 2);
    case "jsarr": return smtToArray(v);
    default: throw new Error("unsupported");
  }
}

function callMatchesParams(expr: JSyntax.CallExpression, f: JSyntax.FunctionDeclaration): boolean {
  if (expr.arguments.length != f.params.length) return false;
  for (let i = 0; i < expr.arguments.length; i++) {
    const arg: JSyntax.Expression = expr.arguments[i];
    if (arg.type != "Identifier" ||
        arg.decl.type != "Param" ||
        arg.decl.func != f ||
        arg.decl.decl != f.params[i]) {
     return false;
    }
  }
  return true;
}

export function replaceFunctionResult(f: JSyntax.FunctionDeclaration, expr: JSyntax.Expression): JSyntax.Expression {
  switch (expr.type) {
    case "Identifier":
    case "OldIdentifier":
    case "Literal":
      return expr;
    case "ArrayExpression":
      return { type: "ArrayExpression", elements: expr.elements.map(e => replaceFunctionResult(f, e)) };
    case "UnaryExpression":
      return { type: "UnaryExpression", operator: expr.operator, argument: replaceFunctionResult(f, expr.argument)};
    case "BinaryExpression":
      return {
        type: "BinaryExpression",
        operator: expr.operator,
        left: replaceFunctionResult(f, expr.left),
        right: replaceFunctionResult(f, expr.right)
      };
    case "LogicalExpression":
      return {
        type: "LogicalExpression",
        operator: expr.operator,
        left: replaceFunctionResult(f, expr.left),
        right: replaceFunctionResult(f, expr.right)
      };
    case "ConditionalExpression":
      return {
        type: "ConditionalExpression",
        test: replaceFunctionResult(f, expr.test),
        consequent: replaceFunctionResult(f, expr.consequent),
        alternate: replaceFunctionResult(f, expr.alternate)
      };
    case "AssignmentExpression":
      return {
        type: "AssignmentExpression",
        left: expr.left, 
        right: replaceFunctionResult(f, expr.right)
      };
    case "SequenceExpression":
      return { type: "SequenceExpression", expressions: expr.expressions.map(e => replaceFunctionResult(f, e)) };
    case "CallExpression":
      if (expr.callee.type == "Identifier" &&
          expr.callee.decl.type == "Func" &&
          expr.callee.decl.decl == f &&
          callMatchesParams(expr, f)) {
        return { type: "Identifier", name: "_res_", decl: { type: "Unresolved" }, refs: [], isWrittenTo: false };
      }
      return {
        type: "CallExpression",
        callee: replaceFunctionResult(f, expr.callee),
        arguments: expr.arguments.map(e => replaceFunctionResult(f, e))
      }
    case "FunctionExpression":
      throw new Error("not implemented yet"); 
  }

}

export function replaceOld(vars: Vars | null, expr: JSyntax.Expression): JSyntax.Expression {
  switch (expr.type) {
    case "OldIdentifier":
      if (vars) {
        return { type: "OldIdentifier", id: expr.id, version: vars[expr.id.name] };
      }
      return { type: "Identifier", name: expr.id.name + "_0", decl: { type: "Unresolved" }, refs: [], isWrittenTo: false};
    case "Identifier":
    case "Literal":
      return expr;
    case "ArrayExpression":
      return { type: "ArrayExpression", elements: expr.elements.map(e => replaceOld(vars, e)) };
    case "UnaryExpression":
      return { type: "UnaryExpression", operator: expr.operator, argument: replaceOld(vars, expr.argument)};
    case "BinaryExpression":
      return {
        type: "BinaryExpression",
        operator: expr.operator,
        left: replaceOld(vars, expr.left),
        right: replaceOld(vars, expr.right)
      };
    case "LogicalExpression":
      return {
        type: "LogicalExpression",
        operator: expr.operator,
        left: replaceOld(vars, expr.left),
        right: replaceOld(vars, expr.right)
      };
    case "ConditionalExpression":
      return {
        type: "ConditionalExpression",
        test: replaceOld(vars, expr.test),
        consequent: replaceOld(vars, expr.consequent),
        alternate: replaceOld(vars, expr.alternate)
      };
    case "AssignmentExpression":
      return {
        type: "AssignmentExpression",
        left: expr.left, 
        right: replaceOld(vars, expr.right)
      };
    case "SequenceExpression":
      return { type: "SequenceExpression", expressions: expr.expressions.map(e => replaceOld(vars, e)) };
    case "CallExpression":
      return {
        type: "CallExpression",
        callee: replaceOld(vars, expr.callee),
        arguments: expr.arguments.map(e => replaceOld(vars, e))
      }
    case "FunctionExpression":
      throw new Error("not implemented yet"); 
  }
}
