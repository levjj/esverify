declare const console: { log: (s: string) => void };
declare const require: (s: string) => any;
declare const fetch: (s: string, opts: any) => Promise<any>;

import { P, Vars, Locs, Heap, Heaps } from "./logic";
import { Model, SMTInput, SMTOutput, vcToSMT, smtToModel } from "./smt";
import { Syntax, stringifyStmt } from "./javascript";
import { Message, MessageException, unexpected } from "./message";
import { options } from "./options";

export type SMTOutput = string;

export default class VerificationCondition {
  heaps: Heaps;
  locs: Locs;
  vars: Vars;
  prop: P;
  testBody: Array<Syntax.Statement>;
  loc: Syntax.SourceLocation;
  description: string;
  inprocess: boolean;
  result: Message | null;

  constructor(heap: Heap, locs: Locs, vars: Vars, prop: P, loc: Syntax.SourceLocation, description: string, body: Array<Syntax.Statement> = []) {
    this.heaps = new Set([...Array(heap+1).keys()]);
    this.locs = new Set([...locs]);
    this.vars = new Set([...vars]);
    this.prop = prop;
    this.loc = loc;
    this.description = description;
    this.testBody = body;
    this.inprocess = false;
    this.result = null;
  }

  private prepareSMT(): SMTInput {
    const smt = vcToSMT(this.heaps, this.locs, this.vars, this.prop);
    if (options.verbose) {
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
function spec() { return true; /* not tested dynamically */ }
${declarations.join("")}
${oldValues.join("")}

${this.testBody.map(s => stringifyStmt(s)).join("\n")}`;
  }

  private process(out: SMTOutput): Message {
    if (!options.quiet && options.verbose) {
      console.log('SMT Output:');
      console.log('------------');
      console.log(out);
      console.log('------------');
    }
    if (out && out.startsWith("sat")) {
      const m = smtToModel(out);
      const code = this.testCode(m);
      if (!options.quiet && options.verbose) {
        console.log('Test Code:');
        console.log('------------');
        console.log(code);
        console.log('------------');
      }
      try {
        eval(code);
        return { status: "unverified", description: this.description, loc: this.loc, model: m };
      } catch (e) {
        if (e instanceof Error && e.message == "assertion failed") {
          return { status: "error", type: "incorrect", description: this.description, loc: this.loc, model: m, error: e };
        } else {
          return unexpected(e, this.loc);
        }
      }
    } else if (out && out.startsWith("unsat")) {
      return { status: "verified", description: this.description, loc: this.loc };
    } else {
      return unexpected(new Error("unexpected: " + out), this.loc);
    }
  }

  private solveLocal(smt: SMTInput): Promise<SMTOutput> {
    if (!options.quiet && options.verbose) {
      console.log(`${this.description}: solving locally with ${options.z3path}`);
    }
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
    if (!options.quiet && options.verbose) {
      console.log(`${this.description}: sending request to ${options.z3url}`);
    }
    return fetch(options.z3url, { method: "POST", body: smt }).then(req => req.text());
  }

  async verify(): Promise<Message> {
    this.inprocess = true;
    try {
      const smtin = this.prepareSMT();
      const smtout = await (options.remote ? this.solveRemote(smtin) : this.solveLocal(smtin));
      return this.result = this.process(smtout);
    } catch (error) {
      if (error instanceof MessageException) return this.result = error.msg;
      return this.result = unexpected(error, this.loc);
    } finally {
      this.inprocess = false;
    }
  }

  runTest() {
    if (!this.result) throw new Error("no model available");
    if (this.result.status == "verified") throw new Error("no model available");
    if (this.result.status == "error" && this.result.type != "incorrect") throw new Error("no model available");
    eval(this.testCode(this.result.model));
  }
}