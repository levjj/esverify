import "isomorphic-fetch";
declare const console: { log: (s: string) => void };
declare const require: (s: string) => any;

import { P, Vars, Locs, Heap, Heaps } from "./logic";
import { Model, SMTInput, SMTOutput, vcToSMT, smtToModel } from "./smt";
import { Syntax, stringifyStmt } from "./javascript";
import { Message, MessageException } from "./message";
import { options } from "./options";

export type SMTOutput = string;

export default class VerificationCondition {
  heaps: Heaps;
  locs: Locs;
  vars: Vars;
  prop: P;
  body: Array<Syntax.Statement>;
  loc: Syntax.SourceLocation;
  description: string;
  inprocess: boolean;
  result: Message | null;
  debug: boolean;

  constructor(heap: Heap, locs: Locs, vars: Vars, prop: P, loc: Syntax.SourceLocation, description: string, body: Array<Syntax.Statement> = []) {
    this.heaps = new Set([...Array(heap+1).keys()]);
    this.locs = locs;
    this.vars = vars;
    this.prop = prop;
    this.loc = loc;
    this.description = description;
    this.body = body;
    this.inprocess = false;
    this.result = null;
    this.debug = false;
  }

  private prepareSMT(): SMTInput {
    const smt = vcToSMT(this.heaps, this.locs, this.vars, this.prop);
    if (this.debug) {
      console.log('SMT Input:');
      console.log('------------');
      console.log(smt);
      console.log('------------');
    }
    return smt;
  }

  private testCode(model: Model): string {
    const declarations = Object.keys(model).map(v =>
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

  private process(out: SMTOutput): Message {
    if (this.debug) {
      console.log('SMT Output:');
      console.log('------------');
      console.log(out);
      console.log('------------');
    }
    if (out && out.startsWith("sat")) {
      const m = smtToModel(out);
      try {
        eval(this.testCode(m));
        return { status: "unverified", description: this.description, loc: this.loc, model: m };
      } catch (e) {
        if (e instanceof Error && e.message == "assertion failed") {
          return { status: "incorrect", description: this.description, loc: this.loc, model: m, error: e };
        } else {
          return { status: "error", loc: this.loc, error: e };
        }
      }
    } else if (out && out.startsWith("unsat")) {
      return { status: "verified", description: this.description, loc: this.loc };
    } else {
      return { status: "error", loc: this.loc, error: new Error("unexpected: " + out) };
    }
  }

  private solveLocal(smt: SMTInput): Promise<SMTOutput> {
    if (this.debug) console.log(`${this.description}: solving locally with ${options.z3path}`);
    return new Promise<SMTOutput>((resolve, reject) => {
      const spawn = require('child_process').spawn;
      const p = spawn(options.z3path, ['-smt2', '-in'], {stdio: ['pipe', 'pipe', 'ignore']});
      let result: string = "";
      p.stdout.on('data', (data: Object) => { result += data.toString(); });
      p.on('exit', (code: number) => resolve(result));
      p.on('error', reject);
      p.stdin.write(smt);
      p.stdin.end();
    });
  }

  private solveRemote(smt: SMTInput): Promise<SMTOutput> {
    if (this.debug) console.log(`${this.description}: sending request to ${options.remoteURL}`);
    return fetch(options.remoteURL, { method: "POST", body: smt }).then(req => req.text());
  }

  async verify(): Promise<Message> {
    this.inprocess = true;
    try {
      const smtin = this.prepareSMT();
      const smtout = await (options.local ? this.solveLocal(smtin) : this.solveRemote(smtin));
      return this.result = this.process(smtout);
    } catch (error) {
      if (error instanceof MessageException) return this.result = error.msg;
      return this.result = { status: "error", loc: this.loc, error };
    } finally {
      this.inprocess = false;
    }
  }

  runTest() {
    if (!this.result || (this.result.status != "incorrect" && this.result.status != "unverified")) {
      throw new Error("no model available");
    }
    eval(this.testCode(this.result.model));
  }

  enableDebugging() { this.debug = true; }
}