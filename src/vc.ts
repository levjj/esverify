/* global fetch */

/// <reference path="../typings/isomorphic-fetch/isomorphic-fetch.d.ts"/>

import { createVars } from "./transform";
import { varsToSMT, expressionToSMT, propositionToSMT } from "./assertions";
import { preamble } from "./defs-smt";
import { pushAll } from "./util";
import { JSyntax, stringifyExpr, stringifyStmt } from "./javascript";
import { smtToValue, havocVars, assignedInExpr, assignedInStmt, assignedInFun, transformProgram, transformTopLevel, transformStatement, transformExpression, replaceFunctionResult, replaceOld } from "./transform";
import { ASyntax, tru, truthy, and, not } from "./assertions";

export type SMTInput = string;
export type SMTOutput = string;

export type VarName = string;
export type Vars = { [varName: string]: number; };  // latest assigned value

type Model = { [varName: string]: any };

type Result = { status: "unverified" }
            | { status: "inprogress" }
            | { status: "sat" }
            | { status: "unsat", model: Model, error: Error }
            | { status: "failed", error: Error }
            | { status: "notest", model: Model };

function vcStatement(vars: Vars, prop: ASyntax.Proposition, stmt: JSyntax.Statement): Array<VerificationCondition> {
  const vars2 = Object.assign({}, vars);
  const vcs: Array<VerificationCondition> = [];
  switch (stmt.type) {
    case "BlockStatement":
      let vars3 = vars2, p3 = prop;
      for (const s of stmt.body) {
        pushAll(vcs, vcStatement(vars3, p3, s));
        const state = transformStatement(vars3, s);
        vars3 = state[0];
        p3 = and(p3, state[1], not(state[2]));
      }
      break;
    case "AssertStatement": {
      const [,,post] = transformExpression(vars2, stmt.expression, true);
      vcs.push(new VerificationCondition(vars2, prop, truthy(post), "assert:\n" + stringifyExpr(stmt.expression)));
      break;
    }
    case "IfStatement": {
      const [vars3, p3, v] = transformExpression(vars2, stmt.test);
      pushAll(vcs, vcStatement(vars3, and(prop, p3, truthy(v)), stmt.consequent));
      pushAll(vcs, vcStatement(vars3, and(prop, p3, not(truthy(v))), stmt.alternate));
      break;
    }
    case "WhileStatement": {
      // invariants on entry
      for (const inv of stmt.invariants) {
        const [,,post] = transformExpression(vars2, inv, true);
        vcs.push(new VerificationCondition(vars2, prop, truthy(post), "invariant on entry:\n" + stringifyExpr(inv)));
      }

      // havoc changed variables
      const vars3 = havocVars(vars2, v => assignedInExpr(v, stmt.test) || assignedInStmt(v, stmt.body));

      // assume invariants
      const [vars4, prop4, v4] = transformExpression(vars3, stmt.test);
      let pre4 = and(prop, prop4, truthy(v4));
      for (const inv of stmt.invariants) {
        const [,,post] = transformExpression(vars4, inv, true);
        pre4 = and(pre4, truthy(post));
      }

      // internal assertions
      pushAll(vcs, vcStatement(vars4, pre4, stmt.body));

      // ensure invariants maintained
      const [vars5, prop5] = transformStatement(vars4, stmt.body);
      for (const inv of stmt.invariants) {
        const [,,post] = transformExpression(vars5, inv, true);
        vcs.push(new VerificationCondition(vars5, and(pre4, prop5), truthy(post),
                 "invariant maintained:\n" + stringifyExpr(inv),
                 vars4, stmt.body.body.concat([{ type: "AssertStatement", expression: inv }])));
      }
      break;
    }
    case "ReturnStatement":
    case "VariableDeclaration":
    case "ExpressionStatement":
    case "DebuggerStatement":
  }
  return vcs;
}

function vcFunction(vars: Vars, pre: ASyntax.Proposition, f: JSyntax.FunctionDeclaration): Array<VerificationCondition> {
  const vcs: Array<VerificationCondition> = [];
  const vars2 = Object.assign({}, vars);
  for (const p of f.params) {
    vars2[p.name] = 0;
  }
  vars2["_res_"] = "_res_" in vars2 ? vars2["_res_"] + 1 : 0; 

  // assume preconditions
  let pre2 = pre;
  for (const req of f.requires) {
    const [,,post] = transformExpression(vars2, req, true);
    pre2 = and(pre2, truthy(post));
  }

  // internal assertions
  const ivcs = vcStatement(vars2, pre2, f.body);
  ivcs.forEach(vc => {
    vc.description = f.id.name + ":\n" + vc.description;
    vc.body = vc.body.length == 0 ? f.body.body : vc.body;
    vc.freeVars = vars2;
  });
  pushAll(vcs, ivcs);

  // ensure postconditions
  const [vars3, prop3] = transformStatement(vars2, f.body);
  const vars2w = Object.assign({}, vars2);
  delete vars2w["_res_"]; // remove _res_
  const invocation: JSyntax.TopLevel = {
    type: "VariableDeclaration",
    id: { type: "Identifier", name: "_res_", decl: { type: "Unresolved" }, refs: [], isWrittenTo: false},
    kind: "const",
    init: { type: "CallExpression", callee: f.id, arguments: f.params }
  };
  for (const ens of f.ensures) {
    const ens2 = replaceFunctionResult(f, ens);
    const [,,post] = transformExpression(vars3, replaceOld(vars2w, ens2), true);
    vcs.push(new VerificationCondition(
      vars3, and(pre2, prop3), truthy(post),
      f.id.name + ":\n" + stringifyExpr(ens),
      vars2w, [f, invocation, { type: "AssertStatement", expression: replaceOld(null, ens2) }]));
  }
  return vcs;
}

export function vcProgram(prog: JSyntax.Program): Array<VerificationCondition> {
  const vcs: Array<VerificationCondition> = [];
  const funs: Array<JSyntax.FunctionDeclaration> = [];

  let vars: Vars = {}, prop:ASyntax.Proposition = tru,
      pre: Array<JSyntax.TopLevel> = [];
  for (const stmt of prog.body) {
    pre = pre.concat([stmt]);
    if (stmt.type != "FunctionDeclaration") {
      const ivcs = vcStatement(vars, prop, stmt);
      ivcs.forEach(ivc => {
        ivc.body = ivc.body.length == 0 ? pre : ivc.body;
      });
      pushAll(vcs, ivcs);
      const state = transformStatement(vars, stmt);
      vars = state[0];
      prop = and(prop, state[1], not(state[2]));
    } else {
      funs.push(stmt);
    }
  }

  // invariants
  for (const inv of prog.invariants) {
    const [,,post] = transformExpression(vars, inv, true);
    vcs.push(new VerificationCondition(vars, prop, truthy(post),
      "initially:\n" + stringifyExpr(inv),
      {}, prog.body.concat([{ type: "AssertStatement", expression: inv }])));
    for (const f of funs) {
      f.requires.push(inv);
      f.ensures.push(inv);
    }
  }

  // havoc changed variables
  const vars2 = havocVars(vars, v => funs.some(f => assignedInFun(v, f)));

  // add functions
  for (const f of funs) {
    pushAll(vcs, vcFunction(vars2, prop, f));
  }
  return vcs;
}

export default class VerificationCondition {
  vars: Vars;
  prop: ASyntax.Proposition;
  post: ASyntax.Proposition;
  freeVars: Vars;
  body: Array<JSyntax.TopLevel>;
  description: string;
  _smtin: SMTInput | null;
  _smtout: SMTOutput | null;
  _result: Result;

  constructor(vars: Vars, prop: ASyntax.Proposition, post: ASyntax.Proposition, description: string, freeVars: Vars = {}, body: Array<JSyntax.TopLevel> = []) {
 this.vars = vars;
    this.prop = prop;
    this.post = post;
    this.freeVars = freeVars;
    this.body = body;
    this.description = description;
    this._smtin = null;
    this._smtout = null;
    this._result = { status: "unverified" };
  }
  
  smtInput(): SMTInput {
    const declarations = varsToSMT(this.vars),
          requirements = `(assert ${propositionToSMT(this.prop)})`,
          post = `(assert (not ${propositionToSMT(this.post)}))`;
    return this._smtin =
`${preamble}

; declarations
${declarations}

; requirements
${requirements}

; post condition
${post}

(check-sat)
(get-value (${Object.keys(this.freeVars).map(v => `${v}_${this.freeVars[v]}`).join(' ')}))`;
  }
  
  getModel(): Model {
    let res = this._smtout;
    if (!res || !res.startsWith("sat")) throw new Error("no model available");
    if (Object.keys(this.freeVars).length == 0) return {};
    // remove "sat"
    res = res.slice(3, res.length);
    // remove outer parens
    res = res.trim().slice(2, res.length - 4);
    const model: Model = {};
    res.split(/\)\s+\(/m).forEach(str => {
      // these are now just pairs of varname value
      const both = str.trim().split(" ");
      if (both.length < 2) return;
      const name = both[0].trim(),
            value = both.slice(1, both.length).join(" ").trim();
      model[name.substr(0, name.length - 2)] = smtToValue(value);
    });
    return model;
  }

  testCode(): string {
    const model = this.getModel(),
          declarations = Object.keys(model).map(v =>
            `let ${v} = ${JSON.stringify(model[v])};\n`),
          oldValues = Object.keys(model).map(v =>
            `let ${v}_0 = ${v};\n`);
    return `
function assert(p) { if (!p) throw new Error("assertion failed"); }
${declarations.join("")}
${oldValues.join("")}

${this.body.map(s => stringifyStmt(s)).join("\n")}`;
  }
  
  runTest(m: Model = this.getModel()) {
    eval(this.testCode());
  }

  result(): Result {
    return this._result;
  }
  
  async solve(): Promise<Result> {
    this._result = { status: "inprogress" };
    try {
      this._smtout = await (typeof fetch === "undefined" ? this.solveLocal() : this.solveRequest());
    } catch (e) {
      this._result = { status: "failed", error: e };
      return this._result;
    }
    if (this._smtout && this._smtout.startsWith("sat")) {
      const m = this.getModel();
      try {
        this.runTest(m);
        this._result = { status: "notest", model: m };
      } catch (e) {
        this._result = { status: "unsat", model: m, error: e };
      }
    } else {
      this._result = { status: "sat" };
    }
    return this._result;
  }

  solveLocal(): Promise<string> {
    const spawn = require('child_process').spawn;
    const p = spawn('/home/cs/Projects/jsfxs/z3/build/z3', ['-smt2', '-in'],
                    {stdio: ['pipe', 'pipe', 'ignore']});
    return new Promise((resolve, reject) => {
      let result: string = "";
      p.stdout.on('data', (data: Object) => {
         result += data.toString();
      });
      p.on('exit', (code: number) => resolve(result));
      p.stdin.write(this.smtInput());
      p.stdin.end();
    });
  }

  async solveRequest(): Promise<string> {
    const req = await fetch("/nodejs/Z3server/", {
      method: "POST",
      body: this.smtInput()
    });
    return req.text();
  }

}
