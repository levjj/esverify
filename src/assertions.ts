import { SMTInput } from "../index";

export namespace ASyntax {
  interface Identifier { type: "Identifier"; name: string; version: number; }
  interface Literal { type: "Literal";
                      value: undefined | null | boolean | number | string; }
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
  export type Expression = Identifier
                         | Literal
                         | ArrayExpression
                         | UnaryExpression
                         | BinaryExpression
                         | ConditionalExpression;

  interface Truthy { type: "Truthy"; expr: Expression; }
  interface Implies { type: "Implies"; cond: Proposition; cons: Proposition; }
  interface And { type: "And"; clauses: Array<Proposition>; }

  export type Proposition = Truthy
                          | Implies
                          | And;
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

function arrayToSMT(elements: Array<ASyntax.Expression>): SMTInput {
  if (elements.length === 0) return `empty`;
  const [head, ...tail] = elements;
  const h = head || {type: "Literal", value: "undefined"};
  return `(cons ${expressionToSMT(h)} ${arrayToSMT(tail)})`;
}

export function expressionToSMT(expr: ASyntax.Expression): SMTInput {
  switch (expr.type) {
    case "Identifier":
      return expr.name + " " + expr.version;
    case "Literal":
      if (expr.value === undefined) return `jsundefined`;
      if (expr.value === null) return `jsnull`;
      switch (typeof expr.value) {
        case "boolean": return `(jsbool ${expr.value})`;
        case "number": return `(jsnum ${expr.value})`;
        case "string": return `(jsstr "${expr.value}")`;
        default: throw new Error("unsupported");
      }
    case 'ArrayExpression':
      return `(jsarray ${arrayToSMT(expr.elements)})`;
    case "UnaryExpression":
      const arg = expressionToSMT(expr.argument),
            op = unOpToSMT[expr.operator];
      return `(${op} ${arg})`;
    case "BinaryExpression":
      const left = expressionToSMT(expr.left),
            right = expressionToSMT(expr.right),
            binop = binOpToSMT[expr.operator];
      return `(${binop} ${left} ${right})`;
    case "ConditionalExpression":
      const test = propositionToSMT(expr.test),
            then = expressionToSMT(expr.consequent),
            elze = expressionToSMT(expr.alternate);
      return `(ite ${test} ${then} ${elze})`;
    default:
      throw new Error("unsupported");
  }
}

export function propositionToSMT(prop: ASyntax.Proposition): SMTInput {
  switch (prop.type) {
    case "Truthy": return `(_truthy ${expressionToSMT(prop.expr)})`;
    case "Implies": return `(=> ${prop.cond} ${prop.cons})`;
    case "And": return `(and ${prop.clauses.join(' ')})`;
  }
}