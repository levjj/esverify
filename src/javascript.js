import { arr } from "lively.lang";

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

// type VarName = string;
// type Vars = { [VarName]: number }  // latest assigned value

export function createVars(names = []) {
  // Array<VarName> -> Vars
  return names.reduce((vars, n) => {
    vars[n] = 0;
    return vars;
  }, {});
}

function incVar(v, vars) {
  // VarName, Vars -> Vars
  if (!(v in vars)) return {...vars, [v]: 0};
  return {...vars, [v]: vars[v] + 1};
}

export function getVar(v, vars) {
  // VarName, Vars -> SMTInput
  if (!(v in vars)) return v + "_0";
  return v + "_" + vars[v];
}

function phiVars(pc, myVars, altVars) {
    // Array<SMTInput>, Vars, Vars -> SMTInput
  let smt = '';
  for (const v in altVars) {
    if (myVars[v] < altVars[v]) {
      smt += `(assert (=> (and ${pc.join(' ')}) (= ${getVar(v, altVars)} ${getVar(v, myVars)})))\n`;
    }
  }
  return smt;
}

function joinVars(vars1, vars2) {
  // Vars, Vars -> [SMTInput, Vars]
  const res = {};
  const allKeys = arr.uniq(Object.keys(vars1).concat(Object.keys(vars2)));
  for (const v of allKeys) {
    res[v] = v in vars1 ? (v in vars2 ? Math.max(vars1[v], vars2[v]) : vars1[v]) : vars2[v];
  }
  return res;
}

export function varsToSMT(vars) {
  // Vars -> SMTInput
  let smt = '';
  for (const v in vars) {
    for (let i = 0; i <= vars[v]; i++) {
      smt += `(declare-const ${v}_${i} JSVal)\n`;
    }
  }
  return smt;
}

function arrayToSMT(elements, vars) {
  // Array<Identifier>, Vars -> SMTInput
  if (elements.length === 0) return "empty";
  const [head, ...tail] = elements;
  return `(cons ${getVar(head.name, vars)} ${arrayToSMT(tail, vars)})`;
}

function expressionToSMT(expr, vars) {
  // Expression, Vars -> SMTInput
  switch (expr.type) {
    case 'FunctionExpression':
      return "jsfun"
    case 'ArrayExpression':
      return `(jsarray ${arrayToSMT(expr.elements, vars)})`;
    case 'UnaryExpression':
      if (expr.operator == 'delete') throw new Error("unsupported");
      return `(${unOpToSMT[expr.operator]} ${getVar(expr.argument.name, vars)})`;
    case 'BinaryExpression':
      return `(${binOpToSMT[expr.operator]} ${getVar(expr.left.name, vars)} ${getVar(expr.right.name, vars)})`;
    case 'Identifier':
      return getVar(expr.name, vars);
    case 'Literal':
      if (expr.value === undefined) return "jsundefined";
      if (expr.value === null) return "jsnull";
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

function assertEq(left, right, vars, pc) {
  // VarName, SMTInput, Vars, Array<SMTInput> -> [SMTInput, Array<BreakCondition>, Vars]
  const nvars = incVar(left, vars),
        eq = `(= ${getVar(left, nvars)} ${right})`;
  if (pc.length == 0) return [`(assert ${eq})\n`, nvars, []];
  return [`(assert (=> (and ${pc.join(' ')}) ${eq}))\n`, nvars, []];
}

export function statementToSMT(stmt, vars = {}, pc = []) {
  // Statement, Vars, Array<SMTInput> -> [SMTInput, Vars, Array<BreakCondition>]
  switch (stmt.type) {
    case 'Program':
    case 'BlockStatement':
      return stmt.body.reduce(([smt, vars, bc], s) => {
        const breakConds = bc.map(bc => `(and ${bc.cond.join(' ')})`),
              newPC = breakConds.length == 0 ? pc : pc.concat(
                [`(not (or ${breakConds.join(' ')}))`]),
              [ssmt, nvars, sbc] = statementToSMT(s, vars, newPC);
        return [smt + ssmt, nvars, bc.concat(sbc)];
      }, ["", vars, []]);
    case 'IfStatement':
      const tst = `(_truthy ${getVar(stmt.test.name, vars)})`,
            [smt1, nvars1, bc1] = statementToSMT(stmt.consequent, vars, pc.concat([tst])),
            [smt2, nvars2, bc2] = statementToSMT(stmt.alternate, vars, pc.concat([`(not ${tst})`])),
            thenBreakConds = bc1.map(({label, cond}) =>
              ({label, cond: cond.concat([tst])})),
            elseBreakConds = bc2.map(({label, cond}) =>
              ({label, cond: cond.concat([`(not ${tst})`])})),
            smt1phi = phiVars(pc.concat([tst]), nvars1, nvars2),
            smt2phi = phiVars(pc.concat([`(not ${tst})`]), nvars2, nvars1),
            nvars3 = joinVars(nvars1, nvars2);
      return [smt1 + smt1phi + smt2 + smt2phi, nvars3, thenBreakConds.concat(elseBreakConds)];
    case 'LabeledStatement':
      const [smt, nvars, bc] = statementToSMT(stmt.body, vars, []);
      // after this statement, breaks with this label are resolved
      return [smt, nvars, bc.filter(({label}) => label != stmt.label.name)];
    case 'DebuggerStatement':
    case 'EmptyStatement':
      return ["", vars, []];
    case 'BreakStatement':
      // break unconditionally
      // (any statements in ablock after break are unreachable)
      return ["", vars, [{label: stmt.label.name, cond: []}]];
    case 'ReturnStatement':
      return assertEq("_res", getVar(stmt.argument.name, vars), vars, pc);
    case 'VariableDeclaration':
      // assign "undefined"
      return stmt.declarations.reduce(([smt, nvars, bc], {id}) => {
        const [ssmt, nvars2, sbc] = assertEq(id.name, "jsundefined", nvars, pc);
        return [smt + ssmt, nvars2, bc.concat(sbc)];
      }, ["", vars, []]);
    case 'ExpressionStatement':
      const {left, right} = stmt.expression;
      if (left.type == 'MemberExpression') {
        throw new Error("unsupported");
      }
      return assertEq(left.name, expressionToSMT(right, vars), vars, pc);
    default: throw new Error("unsupported");
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
    case "jsnum": const neg = v.match(/\(- ([0-9]+)\)/); return neg ? -neg[1] : +v;
    case "jsstr": return v.substr(1, v.length - 2);
    case "jsarr": return smtToArray(v);
    default: throw new Error("unsupported");
  }
}
