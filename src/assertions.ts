import { SMTInput, SMTOutput, AExpression, Vars } from "../index";

import { getVar } from "./javascript";

const unOpToSMT: {[unop: string]: string} = {
  "typeof": "_js-typeof",
  "-": "_js-negative",
  "+":"_js-positive",
  "!": "_js-not",
  "~": "_js-bnot",
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

function arrayToSMT(elements: Array<AExpression>, vars: Vars): SMTInput {
  if (elements.length === 0) return `empty`;
  const [head, ...tail] = elements;
  return `(cons ${assertionToSMT(head, vars)} ${arrayToSMT(tail, vars)})`;
}

export function assertionToSMT(expr: AExpression, vars: Vars = {}): SMTInput {
  switch (expr.type) {
    case "Identifier": return getVar(expr.name, vars);
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
      return `(jsarray ${arrayToSMT(expr.elements, vars)})`;
    case "UnaryExpression":
      const arg = assertionToSMT(expr.argument, vars),
            op = unOpToSMT[expr.operator];
      return `(${op} ${arg})`;
    case "BinaryExpression":
      const left = assertionToSMT(expr.left, vars),
            right = assertionToSMT(expr.right, vars),
            binop = binOpToSMT[expr.operator];
      return `(${binop} ${left} ${right})`;
    case "ConditionalExpression":
      const test = assertionToSMT(expr.test, vars),
            then = assertionToSMT(expr.consequent, vars),
            elze = assertionToSMT(expr.alternate, vars);
      return `(ite (_truthy ${test}) ${then} ${elze})`;
    case "CallExpression":
      if (expr.callee.type == "Identifier" &&
        expr.callee.name == "old" &&
        expr.arguments.length == 1) {
        return assertionToSMT(expr.arguments[0], {});
      }
      throw new Error("unsupported");
    default:
      throw new Error("unsupported");
  }
}
