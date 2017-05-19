/* global fetch require console */
/// <reference path="../typings/isomorphic-fetch/isomorphic-fetch.d.ts"/>
declare const require: (s: string) => any;
declare const console: { log: any };

import { P, Vars, Locs, Heap, Heaps, SMTInput, SMTOutput } from "./propositions";
import { Model, smt, smtToModel } from "./smt";
import { JSyntax, stringifyStmt } from "./javascript";

export type SMTOutput = string;

export type Result = { status: "unverified" }
                   | { status: "inprogress" }
                   | { status: "verified" }
                   | { status: "incorrect", model: Model, error: Error }
                   | { status: "unknown" }
                   | { status: "error", error: Error }
                   | { status: "tested", model: Model };

export default class VerificationCondition {
  heaps: Heaps;
  locs: Locs;
  vars: Vars;
  prop: P;
  body: Array<JSyntax.Statement>;
  description: string;
  _smtin: SMTInput | null;
  _smtout: SMTOutput | null;
  _result: Result;

  constructor(heap: Heap, locs: Locs, vars: Vars, prop: P, description: string, body: Array<JSyntax.Statement> = []) {
    this.heaps = new Set([...Array(heap+1).keys()]);
    this.locs = locs;
    this.vars = vars;
    this.prop = prop;
    this.body = body;
    this.description = description;
    this._smtin = null;
    this._smtout = null;
    this._result = { status: "unverified" };
  }

  smtInput(): SMTInput {
    return this._smtin = smt(this.heaps, this.locs, this.vars, this.prop);
  }

  getModel(): Model {
    if (!this._smtout) throw new Error("no model available");
    return smtToModel(this._smtout);
  }

  testCode(): string {
    const model = this.getModel(),
          declarations = Object.keys(model).map(v =>
            `let ${v} = ${JSON.stringify(model[v])};\n`),
          oldValues = Object.keys(model).map(v =>
            `let ${v}_0 = ${v};\n`);
    return `
function assert(p) { if (!p) throw new Error("assertion failed"); }
function pure() { return true; /* not tested dynamically */ }
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
      this._result = { status: "error", error: e };
      return this._result;
    }
    if (this._smtout && this._smtout.startsWith("sat")) {
      const m = this.getModel();
      try {
        this.runTest(m);
        this._result = { status: "tested", model: m };
      } catch (e) {
        if (e instanceof Error && e.message == "assertion failed") {
          this._result = { status: "incorrect", model: m, error: e };
        } else {
          this._result = { status: "error", error: e };
        }
      }
    } else if (this._smtout && this._smtout.startsWith("unknown")) {
      this._result = { status: "unknown" };
    } else if (this._smtout && this._smtout.startsWith("unsat")) {
      this._result = { status: "verified" };
    } else {
      this._result = { status: "error", error: new Error("unexpected: " + this._smtout) };
    }
    return this._result;
  }

  solveLocal(): Promise<string> {
    const spawn = require('child_process').spawn;
    const p = spawn('z3', ['-smt2', '-in'],
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
    const req = await fetch("/z3", {
      method: "POST",
      body: this.smtInput()
    });
    return req.text();
  }

  debugOut() { 
    console.log("\n" + this.description);
    console.log("-----------------");
    console.log(this._result);
    console.log("SMT Input:");
    console.log(this._smtin);
    console.log("SMT Output:");
    console.log(this._smtout);
    if (this._smtout && this._smtout.startsWith("sat")) {
      console.log("Test Body:");
      console.log(this.testCode());
    }
  }
}