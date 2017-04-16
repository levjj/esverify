import { Vars, SMTInput, SMTOutput } from "./vc";
import { flatMap } from "./util";

export namespace ASyntax {
  export interface Identifier { type: "Identifier"; name: string; version: number; }
  interface Literal { type: "Literal";
                      value: undefined | null | boolean | number | string; }
  interface FunctionLiteral { type: "FunctionLiteral";
                              name: string;
                              freeVars: Array<Expression>; }
  interface ArrayExpression { type: "ArrayExpression";
                              elements: Array<Expression>; }
  type UnaryOperator = "-" | "+" | "!" | "~" | "typeof" | "void";
  interface UnaryExpression { type: "UnaryExpression";
                              operator: UnaryOperator;
                              argument: Expression; }
  type BinaryOperator = "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">="
                      | "<<" | ">>" | ">>>" | "+" | "-" | "*" | "/" | "%"
                      | "|" | "^" | "&";
  interface BinaryExpression { type: "BinaryExpression";
                               operator: BinaryOperator;
                               left: Expression;
                               right: Expression; }
  interface ConditionalExpression { type: "ConditionalExpression";
                                    test: Proposition;
                                    consequent: Expression;
                                    alternate: Expression; }
  interface CallExpression { type: "CallExpression";
                             callee: Expression;
                             args: Array<Expression>; }
  interface ClosedVarExpression { type: "ClosedVarExpression";
                                  funcName: string;
                                  freeVar: number; }
  export type Expression = Identifier
                         | Literal
                         | FunctionLiteral
                         | ArrayExpression
                         | UnaryExpression
                         | BinaryExpression
                         | ConditionalExpression
                         | CallExpression
                         | ClosedVarExpression;

  export interface Truthy { type: "Truthy"; expr: Expression; }
  export interface And { type: "And"; clauses: Array<Proposition>; }
  export interface Or { type: "Or"; clauses: Array<Proposition>; }
  export interface Eq { type: "Eq"; left: Expression, right: Expression; }
  export interface Not { type: "Not"; arg: Proposition; }
  export interface True { type: "True"; }
  export interface False { type: "False"; }
  export interface Precondition { type: "Precondition";
                                  callee: Expression;
                                  args: Array<Expression>; }
  export interface Postcondition { type: "Postcondition";
                                   callee: Expression;
                                   args: Array<Expression>; }
  export type Proposition = Truthy
                          | And
                          | Or
                          | Eq
                          | Not
                          | True
                          | False
                          | Precondition
                          | Postcondition;
}

const unOpToSMT: {[unop: string]: string} = {
  "-": "_js-negative",
  "+":"_js-positive",
  "!": "_js-not",
  "~": "_js-bnot",
  "typeof": "_js-typeof",
  "void": "_js-void"
};

const binOpToSMT: {[binop: string]: string} = {
  "==": "_js-eq", // non-standard
  "!=": "_js-neq", // non-standard
  "===": "_js-eq", // non-standard
  "!==": "_js-neq", // non-standard
  "<": "_js_lt",
  "<=": "_js_leq",
  ">": "_js_gt",
  ">=": "_js-geq",
  "+": "_js-plus",
  "-": "_js-minus",
  "*": "_js-multiply",
  "/": "_js-divide",
  "%": "_js-mod",
  "<<": "_js-lshift",
  ">>": "_js-rshift",
  ">>>": "_js-rzshift",
  "|": "_js-bor",
  "^": "_js-bxor",
  "&": "_js-band",
  "in": "_js-in", // unsupported
  "instanceof": "_js-instanceof" // unsupported
};

export const tru: ASyntax.Proposition = { type: "True" };
export const fls: ASyntax.Proposition = { type: "False" };

export function truthy(expr: ASyntax.Expression): ASyntax.Proposition {
  return { type: "Truthy", expr };
}

export function implies(cond: ASyntax.Proposition, cons: ASyntax.Proposition): ASyntax.Proposition {
  return or(not(cond), cons);
}

export function and(...props: Array<ASyntax.Proposition>): ASyntax.Proposition {
  const clauses: Array<ASyntax.Proposition> = flatMap(props,
    c => c.type == "And" ? c.clauses : [c]) 
    .filter(c => c.type != "True");
  if (clauses.find(c => c.type == "False")) return fls;
  if (clauses.length == 0) return tru;
  if (clauses.length == 1) return clauses[0];
  return { type: "And", clauses };
}

export function or(...props: Array<ASyntax.Proposition>): ASyntax.Proposition {
  const clauses: Array<ASyntax.Proposition> = flatMap(props,
    c => c.type == "Or" ? c.clauses : [c]) 
    .filter(c => c.type != "False");
  if (clauses.find(c => c.type == "True")) return tru;
  if (clauses.length == 0) return fls;
  if (clauses.length == 1) return clauses[0];
  return { type: "Or", clauses };
}

export function eq(left: ASyntax.Expression, right: ASyntax.Expression): ASyntax.Proposition {
  return { type: "Eq", left, right };
}

export function not(arg: ASyntax.Proposition): ASyntax.Proposition {
  if (arg.type == "True") return fls;
  if (arg.type == "False") return tru;
  if (arg.type == "Not") return arg.arg;
  return { type: "Not", arg };
}

export function varsToSMT(vars: Vars): SMTInput {
  let smt = '';
  for (const v in vars) {
    for (let i = 0; i <= vars[v]; i++) {
      smt += `(declare-const ${v}_${i} JSVal)\n`;
    }
  }
  return smt;
}

function arrayToSMT(elements: Array<ASyntax.Expression>): SMTInput {
  if (elements.length === 0) return `empty`;
  const [head, ...tail] = elements;
  const h = head || {type: "Literal", value: "undefined"};
  return `(cons ${expressionToSMT(h)} ${arrayToSMT(tail)})`;
}

export function expressionToSMT(expr: ASyntax.Expression): SMTInput {
  switch (expr.type) {
    case "Identifier":
      return expr.name + "_" + expr.version;
    case "Literal":
      if (expr.value === undefined) return `jsundefined`;
      if (expr.value === null) return `jsnull`;
      switch (typeof expr.value) {
        case "boolean": return `(jsbool ${expr.value})`;
        case "number": return `(jsnum ${expr.value})`;
        case "string": return `(jsstr "${expr.value}")`;
        default: throw new Error("unsupported");
      }
    case "FunctionLiteral": {
      if (expr.freeVars.length == 0) return `jsfun-${expr.name}`;
      return `(jsfun-${expr.name} ${expr.freeVars.map(expressionToSMT).join(' ')})`;
    }
    case 'ArrayExpression':
      return `(jsarray ${arrayToSMT(expr.elements)})`;
    case "UnaryExpression":
      const arg = expressionToSMT(expr.argument),
            op = unOpToSMT[expr.operator];
      return `(${op} ${arg})`;
    case "BinaryExpression": {
      const left = expressionToSMT(expr.left),
            right = expressionToSMT(expr.right),
            binop = binOpToSMT[expr.operator];
      return `(${binop} ${left} ${right})`;
    }
    case "ConditionalExpression":
      const test = propositionToSMT(expr.test),
            then = expressionToSMT(expr.consequent),
            elze = expressionToSMT(expr.alternate);
      return `(ite ${test} ${then} ${elze})`;
    case "CallExpression":
      return `(app ${expressionToSMT(expr.callee)} ${expr.args.map(expressionToSMT).join(" ")})`;
    case "ClosedVarExpression":
      return `(jsfun-${expr.funcName}-${expr.freeVar} f)`;
  }
}

export function propositionToSMT(prop: ASyntax.Proposition): SMTInput {
  switch (prop.type) {
    case "Truthy": return `(_truthy ${expressionToSMT(prop.expr)})`;
    case "And": {
      const clauses: Array<SMTInput> = flatMap(prop.clauses,
        c => c.type == "And" ? c.clauses : [c]) 
        .map(propositionToSMT)
        .filter(s => s != `true`);
      if (clauses.find(s => s == `false`)) return `false`;
      if (clauses.length == 0) return `true`;
      if (clauses.length == 1) return clauses[0];
      return `(and ${clauses.join(' ')})`;
    }
    case "Or": {
      const clauses: Array<SMTInput> = flatMap(prop.clauses,
        c => c.type == "Or" ? c.clauses : [c]) 
        .map(propositionToSMT)
        .filter(s => s != `false`);
      if (clauses.find(s => s == `true`)) return `true`;
      if (clauses.length == 0) return `false`;
      if (clauses.length == 1) return clauses[0];
      return `(or ${clauses.join(' ')})`;
    }
    case "Eq":
      const left: SMTInput = expressionToSMT(prop.left);
      const right: SMTInput = expressionToSMT(prop.right);
      if (left == right) return `true`;
      return `(= ${left} ${right})`;
    case "Not":
      const arg: SMTInput = propositionToSMT(prop.arg);
      if (arg == "true") return `false`;
      if (arg == "false") return `true`;
      return `(not ${arg})`;
    case "True": return `true`;
    case "False": return `false`;
    case "Precondition":
      return `(pre ${expressionToSMT(prop.callee)} ${prop.args.map(expressionToSMT).join(" ")})`;
    case "Postcondition":
      return `(post ${expressionToSMT(prop.callee)} ${prop.args.map(expressionToSMT).join(" ")})`;
  }
}

export function propositionToAssert(prop: ASyntax.Proposition): SMTInput {
  if (prop.type == "And") {
    return prop.clauses.map(propositionToAssert).join("");
  }
  return `(assert ${propositionToSMT(prop)})\n`;
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

// function replaceFreeVarExpr(expr: ASyntax.Expression, fv: string, e: ASyntax.Expression): ASyntax.Expression {
//   switch (expr.type) {
//     case "Identifier": return expr.name == fv ? e : expr;
//     case "Literal": return expr;
//     case "FunctionLiteral": return { type: "FunctionLiteral",
//                                      name: expr.name,
//                                      freeVars: expr.freeVars.map(a => replaceFreeVarExpr(a, fv, e)) };
//     case 'ArrayExpression': return { type: "ArrayExpression",
//                                      elements: expr.elements.map(a => replaceFreeVarExpr(a, fv, e)) };
//     case "UnaryExpression": return { type: "UnaryExpression",
//                                      operator: expr.operator,
//                                      argument: replaceFreeVarExpr(expr.argument, fv, e) };
//     case "BinaryExpression": return { type: "BinaryExpression",
//                                       operator: expr.operator,
//                                       left: replaceFreeVarExpr(expr.left, fv, e),
//                                       right: replaceFreeVarExpr(expr.right, fv, e) };
//     case "ConditionalExpression": return { type: "ConditionalExpression",
//                                            test: replaceFreeVar(expr.test, fv, e),
//                                            consequent: replaceFreeVarExpr(expr.consequent, fv, e),
//                                            alternate: replaceFreeVarExpr(expr.alternate, fv, e) };
//     case "CallExpression": return { type: "CallExpression",
//                                     callee: replaceFreeVarExpr(expr.callee, fv, e),
//                                     args: expr.args.map(a => replaceFreeVarExpr(a, fv, e)) };
//     case "ClosedVarExpression": return expr;
//   }
// }

// export function replaceFreeVar(prop: ASyntax.Proposition, fv: string, e: ASyntax.Expression): ASyntax.Proposition {
//   switch (prop.type) {
//     case "Truthy": return { type: "Truthy", expr: replaceFreeVarExpr(prop.expr, fv, e) };
//     case "And": return { type: "And", clauses: prop.clauses.map(c => replaceFreeVar(c, fv, e)) };
//     case "Or": return { type: "Or", clauses: prop.clauses.map(c => replaceFreeVar(c, fv, e)) };
//     case "Eq": return { type: "Eq",
//                         left: replaceFreeVarExpr(prop.left, fv, e),
//                         right: replaceFreeVarExpr(prop.right, fv, e) }
//     case "Not": return { type: "Not", arg: replaceFreeVar(prop.arg, fv, e) };
//     case "True": return prop;
//     case "False": return prop;
//     case "Precondition": return { type: "Precondition",
//                                   callee: replaceFreeVarExpr(prop.callee, fv, e),
//                                   args: prop.args.map(a => replaceFreeVarExpr(a, fv, e)) };
//     case "Postcondition": return { type: "Postcondition",
//                                    callee: replaceFreeVarExpr(prop.callee, fv, e),
//                                    args: prop.args.map(a => replaceFreeVarExpr(a, fv, e)) };
//   }
// }
