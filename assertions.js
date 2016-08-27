/*
AExpression = Identifier (name: string)
            | Literal (value: boolean | number | string)
            | UnaryExpression (operator: "+" | "-",
                               argument: AExpression)
            | BinaryExpression (operator: "=",
                                left: AExpression,
                                right: AExpression)
*/

const unOpToSMT = {
  "typeof": "_js-typeof",
  "-": "_js-negative",
  "+":"_js-positive",
  "!": "_js-not",
  "~": "_js-bnot",
  "void": "_js-void"
};

const binOpToSMT = {
  "==": "_js-eq",
  "!=": "_js-neq",
  "===": "=",
  //"!==": "neq",
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

export default function assertionToSMT(expr) {
  // AExpression -> SMTInput
  switch (expr.type) {
    case "Identifier": return expr.name;
    case "Literal": switch (typeof expr.value) {
      case "boolean": return `(jsbool ${expr.value})`;
      case "number": return `(jsnum ${expr.value})`;
      case "string": return expr.value == "number" ? "JSNum" : "JSBool";
      default: throw new Error("unsupported");
    }
    case "UnaryExpression":
      const arg = assertionToSMT(expr.argument),
            op = unOpToSMT[expr.operator];
      return `(${op} ${arg})`;
    case "BinaryExpression":
      const left = assertionToSMT(expr.left),
            right = assertionToSMT(expr.right),
            binop = binOpToSMT[expr.operator];
      if (expr.operator === "!==") {
        return `(not (= ${left} ${right}))`;
      }
      return `(${binop} ${left} ${right})`;
    default: throw new Error("unsupported");
  }
}
