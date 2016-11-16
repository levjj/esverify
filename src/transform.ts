import { SMTInput, SMTOutput, VarName, Vars } from "../index";
import { findInvariants } from "./visitors";

export function createVars(names: Array<VarName> = []): Vars {
  return names.reduce((vars: Vars, n: VarName) => {
    vars[n] = 0;
    return vars;
  }, {});
}

function incVar(v: VarName, vars: Vars): Vars {
  if (!(v in vars)) return Object.assign({}, vars, {[v]: 0});
  return Object.assign({}, vars, {[v]: vars[v] + 1});
}

export function getVar(v: VarName, vars: Vars): SMTInput {
  if (!(v in vars)) return v + "_0";
  return v + "_" + vars[v];
}

function phiVars(pc: Array<SMTInput>, myVars: Vars, altVars: Vars): SMTInput {
  let smt = '';
  for (const v in altVars) {
    if (myVars[v] < altVars[v]) {
      smt += `(assert (=> (and ${pc.join(' ')}) (= ${getVar(v, altVars)} ${getVar(v, myVars)})))\n`;
    }
  }
  return smt;
}

function joinVars(vars1: Vars, vars2: Vars): Vars {
  const res: Vars = {};
  const allKeys = arr.uniq(Object.keys(vars1).concat(Object.keys(vars2)));
  for (const v of allKeys) {
    res[v] = v in vars1 ? (v in vars2 ? Math.max(vars1[v], vars2[v]) : vars1[v]) : vars2[v];
  }
  return res;
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

function incByOne(vars: Vars, nvars: Vars): Vars {
  const res: Vars = {};
  for (const v in vars) {
    res[v] = nvars[v] > vars[v] ? vars[v] + 1 : vars[v];
  }
  return res;
}

function arrayToSMT(elements: Array<JSyntax.Expression | null>, vars: Vars): SMTInput {
  if (elements.length === 0) return "empty";
  const [head, ...tail] = elements;
  const h = head || {type: "Literal", value: "undefined"};
  return `(cons ${expressionToSMT(h, vars)} ${arrayToSMT(tail, vars)})`;
}

function expressionToSMT(expr: JSyntax.Expression, vars: Vars): SMTInput {
  switch (expr.type) {
    case 'ArrayExpression':
      return `(jsarray ${arrayToSMT(expr.elements, vars)})`;
    case 'UnaryExpression':
      return `(${unOpToSMT[expr.operator]} ${expressionToSMT(expr.argument, vars)})`;
    case 'BinaryExpression':
      return `(${binOpToSMT[expr.operator]} ${expressionToSMT(expr.left, vars)} ${expressionToSMT(expr.right, vars)})`;
    case 'LogicalExpression':
      return `(${logOpToSMT[expr.operator]} ${expressionToSMT(expr.left, vars)} ${expressionToSMT(expr.right, vars)})`;
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
    case "ConditionalExpression":
      const test = expressionToSMT(expr.test, vars),
            then = expressionToSMT(expr.consequent, vars),
            elze = expressionToSMT(expr.alternate, vars);
      return `(ite (_truthy ${test}) ${then} ${elze})`;
    case "CallExpression":
      throw new Error("unsupported");
    case "FunctionExpression":
      throw new Error("unsupported");
  }
}

type Antedecents = Array<SMTInput>;
type BreakLabel = string;
type BreakCondition = {cond: Antedecents, label: BreakLabel};
type State = [SMTInput, Vars, Array<BreakCondition>];

function assert(cond: SMTInput, vars: Vars, pc: Array<SMTInput>): State {
  if (pc.length == 0) return [`(assert ${cond})\n`, vars, []];
  return [`(assert (=> (and ${pc.join(' ')}) ${cond}))\n`, vars, []];
}

function assertEq(left: VarName, right: SMTInput, vars: Vars, pc: Array<SMTInput>): State {
  const nvars = incVar(left, vars);
  return assert(`(= ${getVar(left, nvars)} ${right})`, nvars, pc);
}

export function statementToSMT(stmt: JSyntax.Program | JSyntax.Statement, vars: Vars = {}, pc: Array<SMTInput> = []): State {
  switch (stmt.type) {
    case 'Program':
    case 'BlockStatement':
      const initial: State = ["", vars, []];
      return stmt.body.reduce(([smt, vars, bc]: State, s: JSyntax.Statement): State => {
        const breakConds = bc.map(bc => `(and ${bc.cond.join(' ')})`),
              newPC = breakConds.length == 0 ? pc : pc.concat(
                [`(not (or ${breakConds.join(' ')}))`]),
              [ssmt, nvars, sbc] = statementToSMT(s, vars, newPC);
        return [smt + ssmt, nvars, bc.concat(sbc)];
      }, initial);
    case 'IfStatement':
      const tst = `(_truthy ${expressionToSMT(stmt.test, vars)})`,
            [smt1, nvars1, bc1] = statementToSMT(stmt.consequent, vars, pc.concat([tst])),
            alt = stmt.alternate || { type: "EmptyStatement" },
            [smt2, nvars2, bc2] = statementToSMT(alt, vars, pc.concat([`(not ${tst})`])),
            thenBreakConds = bc1.map(({label, cond}) =>
              ({label, cond: cond.concat([tst])})),
            elseBreakConds = bc2.map(({label, cond}) =>
              ({label, cond: cond.concat([`(not ${tst})`])})),
            smt1phi = phiVars(pc.concat([tst]), nvars1, nvars2),
            smt2phi = phiVars(pc.concat([`(not ${tst})`]), nvars2, nvars1),
            nvars3 = joinVars(nvars1, nvars2);
      return [smt1 + smt1phi + smt2 + smt2phi, nvars3, thenBreakConds.concat(elseBreakConds)];
    case 'DebuggerStatement':
    case 'EmptyStatement':
      return ["", vars, []];
    case 'ReturnStatement':
      if (stmt.argument) {
        return assertEq("_res", expressionToSMT(stmt.argument, vars), vars, pc);
      }
      //TODO: break
      return ["", vars, []]
    case 'VariableDeclaration':
      // assign "undefined"
      const initialS: State = ["", vars, []];
      return stmt.declarations.reduce(([smt, nvars, bc]: State, decl: JSyntax.VariableDeclarator): State => {
        const init = decl.init ? expressionToSMT(decl.init, vars) : "jsundefined";
        const [ssmt, nvars2, sbc] = assertEq(decl.id.name, init, nvars, pc);
        return [smt + ssmt, nvars2, bc.concat(sbc)];
      }, initialS);
    case 'WhileStatement':
      const [, lvars] = statementToSMT(stmt.body, vars, pc); // ignore loop body
      const wvars = incByOne(vars, lvars); // but increment changed vars
      let wsmt = `(and (not (_truthy ${expressionToSMT(stmt.test, wvars)}))`;
      findInvariants(stmt.body).forEach(str => {
        wsmt += ` (_truthy ${expressionToSMT(parse(str).body[0].expression, wvars)})`;
      });
      return assert(wsmt + ')', wvars, pc);
    case 'ExpressionStatement':
      const {left, right} = stmt.expression;
      if (left.type == 'MemberExpression') {
        throw new Error("unsupported");
      }
      return assertEq(left.name, expressionToSMT(right, vars), vars, pc);
    default: throw new Error("unsupported");
  }
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
