/*
AExpression = Identifier (name: string)
            | Literal (value: undefined | null | boolean | number | string)
            | ArrayExpression (elements: Array<AExpression>),
            | UnaryExpression (operator: "+" | "-",
                               argument: AExpression)
            | BinaryExpression (operator: "=",
                                left: AExpression,
                                right: AExpression)
            | CallExpression (callee: Identifier,
                              params: Array<Identifier>)
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

function arrayToSMT(elements) {
  // Array<AExpression> -> SMTInput
  if (elements.length === 0) return `empty`;
  const [head, ...tail] = elements;
  return `(cons ${assertionToSMT(head)} ${arrayToSMT(tail)})`;
}

export function assertionToSMT(expr) {
  // AExpression -> SMTInput
  switch (expr.type) {
    case "Identifier": return expr.name;
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
      const arg = assertionToSMT(expr.argument),
            op = unOpToSMT[expr.operator];
      return `(${op} ${arg})`;
    case "BinaryExpression":
      const left = assertionToSMT(expr.left),
            right = assertionToSMT(expr.right),
            binop = binOpToSMT[expr.operator];
      return `(${binop} ${left} ${right})`;
    default:
      throw new Error("unsupported");
  }
}
