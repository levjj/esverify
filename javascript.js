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
  // Array<Identifier> -> SMTInput
  if (elements.length === 0) return `empty`;
  const [head, ...tail] = elements;
  return `(cons ${head.name} ${arrayToSMT(tail)})`;
}

function expressionToSMT(expr) {
  // Statement -> SMTInput
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
      return `(${binOpToSMT[expr.operator]} ${expr.left.name} ${expr.right.name})`;
    case 'CallExpression':
      throw new Error("unsupported");
    case 'NewExpression':
      throw new Error("unsupported");
    case 'MemberExpression':
      throw new Error("unsupported");
    case 'Identifier':
      return expr.name;
    case 'Literal':
      if (expr.value === undefined) return `jsundefined`;
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

// type Antedecents = Array<SMTInput>
// type BreakLabel = string;
// type BreakCondition = {cond: Antedecents, label: BreakLabel}

export function statementToSMT(stmt, pc = []) {
  // Statement, Antedecents -> [SMTInput, Array<BreakCondition>]
  function as(s) {
    if (pc.length == 0) return [`(assert ${s})\n`, []];
    return [`(assert (=> (and ${pc.join(' ')}) ${s}))\n`, []];
  }
  switch (stmt.type) {
    case 'BlockStatement':
      return stmt.body.reduce(([smt, bc], s) => {
        const breakConds = bc.map(bc => `(and ${bc.cond.join(' ')})`),
              newPC = breakConds.length == 0 ? pc : pc.concat(
                [`(not (or ${breakConds.join(' ')}))`]),
              [ssmt, sbc] = statementToSMT(s, newPC);
        return [smt + ssmt, bc.concat(sbc)];
      }, ["", []]);
    case 'IfStatement':
      const tst = `(_truthy ${stmt.test.name})`,
            [smt1, bc1] = statementToSMT(stmt.consequent, pc.concat([tst])),
            [smt2, bc2] = statementToSMT(stmt.alternate, pc.concat([`(not ${tst})`])),
            thenBreakConds = bc1.map(({label, cond}) =>
              ({label, cond: cond.concat([tst])})),
            elseBreakConds = bc2.map(({label, cond}) =>
              ({label, cond: cond.concat([`(not ${tst})`])}));
      return [smt1 + smt2, thenBreakConds.concat(elseBreakConds)];
    case 'LabeledStatement':
      const [smt, bc] = statementToSMT(stmt.body);
      // after this statement, breaks with this label are resolved
      return [smt, bc.filter(({label}) => label != stmt.label.name)];
    case 'EmptyStatement': return ["", []];
    case 'BreakStatement':
      // break unconditionally
      // (any statements in ablock after break are unreachable)
      return ["", [{label: stmt.label.name, cond: []}]];
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
    case 'DebuggerStatement': return ["", []];
    case 'VariableDeclaration':
      return [stmt.declarations
              .map(decl => `(declare-const ${decl.id.name} JSVal)\n`)
              .join(''), []];
    case 'ExpressionStatement':
      const {left, right} = stmt.expression;
      if (left.type == 'MemberExpression') {
        throw new Error("unsupported");
      }
      return as(`(= ${left.name} ${expressionToSMT(right)})`);
    default: throw new Error('Unknown AST node in statement');
  }
}

function smtToArray(smt) {
  // SMTOutput -> Array<any>
  const s = smt.trim();
  if (s == "empty") return [];
  const [_, h, t] = s.match(/^\(cons (\w+|\(.*\))\ (.*)\)$/);
  return [smtToValue(h)].concat(smtToArray(t));
}

export function smtToValue(smt) {
  // SMTOutput -> any
  const s = smt.trim();
  if (s == "jsundefined") return undefined;
  if (s == "jsnull") return null;
  const [_, tag, v] = s.match(/^\((\w+)\ (.*)\)$/);
  switch (tag) {
    case "jsbool": return v == "true";
    case "jsnum": return +v;
    case "jsstr": return v.substr(1, v.length - 2);
    case "jsarr": return smtToArray(v);
    default: throw new Error("unsupported");
  }
}
