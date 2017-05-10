import { Vars, SMTInput, SMTOutput } from "./verification";
import { flatMap } from "./util";

export namespace ASyntax {
  export interface Identifier { type: "Identifier"; name: string; version: number; }
  interface Literal { type: "Literal";
                      value: undefined | null | boolean | number | string; }
  interface FunctionLiteral { type: "FunctionLiteral";
                              id: number; }
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
  export type Expression = Identifier
                         | Literal
                         | FunctionLiteral
                         | ArrayExpression
                         | UnaryExpression
                         | BinaryExpression
                         | ConditionalExpression
                         | CallExpression;

  export interface Truthy { type: "Truthy"; expr: Expression; }
  export interface And { type: "And"; clauses: Array<Proposition>; }
  export interface Or { type: "Or"; clauses: Array<Proposition>; }
  export interface Eq { type: "Eq"; left: Expression, right: Expression; }
  export interface Iff { type: "Iff"; left: Proposition, right: Proposition; }
  export interface Not { type: "Not"; arg: Proposition; }
  export interface True { type: "True"; }
  export interface False { type: "False"; }
  export interface Precondition { type: "Precondition";
                                  callee: Expression;
                                  args: Array<Expression>; }
  export interface Postcondition { type: "Postcondition";
                                   callee: Expression;
                                   args: Array<Expression>; }
  export interface ForAll { type: "ForAll";
                            callee: Expression;
                            args: Array<Identifier>;
                            prop: Proposition; }
  export interface CallTrigger { type: "CallTrigger";
                                 callee: Expression;
                                 args: Array<Expression>; }
  export type Proposition = Truthy
                          | And
                          | Or
                          | Iff
                          | Eq
                          | Not
                          | True
                          | False
                          | Precondition
                          | Postcondition
                          | ForAll
                          | CallTrigger;
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

export function iff(left: ASyntax.Proposition, right: ASyntax.Proposition): ASyntax.Proposition {
  return { type: "Iff", left, right };
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
      return `(jsfun ${expr.id})`;
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
    case "CallExpression": {
      if (expr.args.length == 1) {
        return `(app1 ${expressionToSMT(expr.callee)} ${expr.args.map(expressionToSMT).join(" ")})`;
      } else if (expr.args.length == 2) {
        return `(app2 ${expressionToSMT(expr.callee)} ${expr.args.map(expressionToSMT).join(" ")})`;
      } else {
        throw new Error("unsupported");
      }
    }
  }
}

export function propositionToSMT(prop: ASyntax.Proposition): SMTInput {
  switch (prop.type) {
    case "Truthy": {
      if (prop.expr.type == "ConditionalExpression" &&
          prop.expr.consequent.type == "Literal" &&
          prop.expr.consequent.value === true &&
          prop.expr.alternate.type == "Literal" &&
          prop.expr.alternate.value === false) {
        return propositionToSMT(prop.expr.test);
      }
      return `(_truthy ${expressionToSMT(prop.expr)})`;
    }
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
    case "Iff": {
      const left: SMTInput = propositionToSMT(prop.left);
      const right: SMTInput = propositionToSMT(prop.right);
      if (left == `true`) return right;
      if (right == `true`) return left;
      if (left == right) return `true`;
      return `(= ${left} ${right})`;
    }
    case "Eq": {
      const left: SMTInput = expressionToSMT(prop.left);
      const right: SMTInput = expressionToSMT(prop.right);
      if (left == right) return `true`;
      return `(= ${left} ${right})`;
    }
    case "Not": {
      const arg: SMTInput = propositionToSMT(prop.arg);
      if (arg == "true") return `false`;
      if (arg == "false") return `true`;
      return `(not ${arg})`;
    }
    case "True": return `true`;
    case "False": return `false`;
    case "Precondition":
      if (prop.args.length == 1) {
        return `(pre1 ${expressionToSMT(prop.callee)} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else if (prop.args.length == 2) {
        return `(pre2 ${expressionToSMT(prop.callee)} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else {
        throw new Error("unsupported");
      }
    case "Postcondition":
      if (prop.args.length == 1) {
        return `(post1 ${expressionToSMT(prop.callee)} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else if (prop.args.length == 2) {
        return `(post2 ${expressionToSMT(prop.callee)} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else {
        throw new Error("unsupported");
      }
    case "ForAll": {
      const params = `(${prop.args.map(p => `(${expressionToSMT(p)} JSVal)`).join(' ')})`;
      const triggerArgs = `${expressionToSMT(prop.callee)} ${prop.args.map(expressionToSMT).join(' ')}`;
      if (prop.args.length != 1 && prop.args.length != 2) throw new Error("Not supported");
      const trigger = (prop.args.length == 1 ? "call1 " : "call2 ") + triggerArgs;
      return `(forall ${params} (! ${propositionToSMT(prop.prop)} :pattern ((${trigger}))))`;
    }
    case "CallTrigger":
      if (prop.args.length == 1) {
        return `(call1 ${expressionToSMT(prop.callee)} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else if (prop.args.length == 2) {
        return `(call2 ${expressionToSMT(prop.callee)} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else {
        throw new Error("unsupported");
      }
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
  if (tag.startsWith("jsfun_")) return null;
  switch (tag) {
    case "jsbool": return v == "true";
    case "jsnum": const neg = v.match(/\(- ([0-9]+)\)/); return neg ? -neg[1] : +v;
    case "jsstr": return v.substr(1, v.length - 2);
    case "jsarr": return smtToArray(v);
    default: throw new Error("unsupported");
  }
}
