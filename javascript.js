/*

Stmt = var x1, x2, ..., xn;
     | x = (function f(y1, ..., yn) { Stmt+ return x; });
     | x = LITERAL;
     | x = null;
     | x = this;
     | x = [ y1, ..., yn ];
     | x = { Prop* };
     | x = y;
     | x = y[z];
     | x[y] = z;
     | x = delete y;
     | x = delete y[z];
     | x = UNOP y;
     | x = y BINOP z;
     | x = f(y1, ..., yn);
     | x = z[f](y1, ..., yn);
     | x = new f(y1, ..., yn);
     | break l;
     | throw x;
     | ;
     | debugger;
     | l: Stmt
     | if (x) { Stmt+ } else { }
     | if (x) { } else { Stmt+ }
     | while(x) { Stmt+ }
     | for (x in y) { Stmt+ }
     | try { Stmt+ } catch (x) { Stmt+ }
     | try { Stmt+ } finally { Stmt+ }

Prop = STRING : y
     | get p() { Stmt+ }
     | set p(x) { Stmt+ }

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

function arrayToSMT(elements) {
  if (elements.length === 0) return `empty`;
  const [head, ...tail] = elements;
  return `(cons ${head.name} ${arrayToSMT})`;
}

function expressionToSMT(expr) {
  switch (expr.type) {
    case 'FunctionExpression':
      throw new Error("unsupported");
    case 'ThisExpression':
      throw new Error("unsupported");
    case 'ArrayExpression':
      return `(jsarray ${arrayToSMT(expr.elements)})`;
    case 'ObjectExpression':
      throw new Error("unsupported");
    case 'UnaryExpression':
      if (expr.operator == 'delete') throw new Error("unsupported");
      return `(${unOpToSMT[expr.operator]} ${expr.argument.name})`;
    case 'BinaryExpression':
      if (expr.operator === "!==") {
        return `(not (= ${expr.right.name} ${expr.left.name}))`;
      }
      return `(${binOpToSMT[expr.operator]} ${expr.right.name} ${expr.left.name})`;
    case 'CallExpression':
      throw new Error("unsupported");
    case 'NewExpression':
      throw new Error("unsupported");
    case 'MemberExpression':
      throw new Error("unsupported");
    case 'Identifier':
      return expr.name;
    case 'Literal':
      if (expr.value === null) return `jsnull`;
      switch (typeof expr.value) {
        case "boolean": return `(jsbool ${expr.value})`;
        case "number": return `(jsnum ${expr.value})`;
        case "string": return `(jsstr "${expr.value}")`;
        default: throw new Error("unsupported");
      }
    default: throw new Error("unsupported");
  }
}

export default function statementToSMT(stmt, antecedents = []) {
  function as(s) {
    if (antecedents.length == 0) return `(assert ${s})`;
    return `(assert (=> (and ${antecedents.join(' ')}) ${s}))`;
  }
  // Statement -> SMTInput
  switch (stmt.type) {
    case 'BlockStatement':
      return stmt.body.map(s => statementToSMT(s, antecedents)).join('\n');
    case 'IfStatement':
      const tst = `(_js-truthy ${stmt.test.name})`;
      if (stmt.alternate.length === 1 && stmt.alternate.body[0].type == "EmptyStatement") {
        return statementToSMT(stmt.consequent,
                              antecedents.concat([tst])); 
      } else {
        return statementToSMT(stmt.alternate,
                              antecedents.concat([`(not ${tst})`]));
      }
    case 'LabeledStatement':
      return statementToSMT(stmt.body);
    case 'EmptyStatement': return "";
    case 'BreakStatement':
      throw new Error("unsupported");
    case 'ReturnStatement':
      return as(`(= _res ${stmt.argument.name})`);
    case 'ThrowStatement':
      throw new Error("unsupported");
    case 'TryStatement':
      throw new Error("unsupported");
    case 'WhileStatement':
      throw new Error("unsupported");
    case 'ForInStatement':
      throw new Error("unsupported");
    case 'DebuggerStatement': return "";
    case 'VariableDeclaration':
      return stmt.declarations
              .map(decl => `(declare-const ${decl.id.name} JSVal)`)
              .join('');
    case 'ExpressionStatement':
      const {left, right} = stmt.expression;
      if (left.type == 'MemberExpression') {
        throw new Error("unsupported");
      }
      return as(`(= ${left.name} ${expressionToSMT(right)})`);
    default: throw new Error('Unknown AST node in statement');
  }
}
