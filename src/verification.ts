declare const console: { log: (s: string) => void };
declare const require: (s: string) => any;
declare const fetch: (s: string, opts: any) => Promise<any>;

import { P, Vars, Locs, Heap, Heaps, Classes } from './logic';
import { Model, SMTInput, vcToSMT, smtToModel } from './smt';
import { Syntax, stringifyStmt } from './javascript';
import { Message, MessageException, unexpected } from './message';
import { options } from './options';

export type SMTOutput = string;

let checkedLocalZ3Version: boolean = false;

export default class VerificationCondition {
  classes: Classes;
  heaps: Heaps;
  locs: Locs;
  vars: Vars;
  prop: P;
  loc: Syntax.SourceLocation;
  freeVars: Vars;
  testBody: Array<Syntax.Statement>;
  description: string;
  inprocess: boolean;
  result: Message | null;

  constructor (classes: Classes, heap: Heap, locs: Locs, vars: Vars, prop: P, loc: Syntax.SourceLocation, description: string, freeVars: Vars, body: Array<Syntax.Statement>) {
    this.classes = new Set([...classes]);
    this.heaps = new Set([...Array(heap + 1).keys()]);
    this.locs = new Set([...locs]);
    this.vars = new Set([...vars]);
    this.prop = prop;
    this.loc = loc;
    this.description = description;
    this.freeVars = freeVars;
    this.testBody = body;
    this.inprocess = false;
    this.result = null;
  }

  async verify (): Promise<Message> {
    this.inprocess = true;
    try {
      const smtin = this.prepareSMT();
      const smtout = await (options.remote ? this.solveRemote(smtin) : this.solveLocal(smtin));
      return this.result = this.process(smtout);
    } catch (error) {
      if (error instanceof MessageException) return this.result = error.msg;
      return this.result = unexpected(error, this.loc, this.description);
    } finally {
      this.inprocess = false;
    }
  }

  runTest () {
    if (!this.result) throw new Error('no model available');
    if (this.result.status === 'verified' || this.result.status === 'unknown') throw new Error('no model available');
    if (this.result.status === 'error' && this.result.type !== 'incorrect') throw new Error('no model available');
    /* tslint:disable:no-eval */
    eval(this.testCode(this.result.model));
  }

  private prepareSMT (): SMTInput {
    const smt = vcToSMT(this.classes, this.heaps, this.locs, this.vars, this.freeVars, this.prop);
    if (options.verbose) {
      console.log('SMT Input:');
      console.log('------------');
      console.log(smt);
      console.log('------------');
    }
    return smt;
  }

  private testCode (model: Model): string {
    const declarations = Object.keys(model).map(v =>
            `let ${v} = ${typeof(model[v]) === 'function' ? '(function(){})' : JSON.stringify(model[v])};\n`);
    const oldValues = Object.keys(model).map(v =>
            `let old_${v} = ${v};\n`);
    return `
function assert(p) { if (!p) throw new Error("assertion failed"); }
function pure() { return true; /* not tested dynamically */ }
function spec() { return true; /* not tested dynamically */ }
${declarations.join('')}
${oldValues.join('')}

${this.testBody.map(s => stringifyStmt(s)).join('\n')}`;
  }

  private process (out: SMTOutput): Message {
    if (!options.quiet && options.verbose) {
      console.log('SMT Output:');
      console.log('------------');
      console.log(out);
      console.log('------------');
    }
    if (out && out.startsWith('sat')) {
      const m = smtToModel(out);
      const code = this.testCode(m);
      if (!options.quiet && options.verbose) {
        console.log('Test Code:');
        console.log('------------');
        console.log(code);
        console.log('------------');
      }
      try {
        /* tslint:disable:no-eval */
        eval(code);
        return { status: 'unverified', description: this.description, loc: this.loc, model: m };
      } catch (e) {
        if (e instanceof Error && e.message === 'assertion failed') {
          return { status: 'error', type: 'incorrect', description: this.description, loc: this.loc, model: m, error: e };
        } else {
          return unexpected(e, this.loc, this.description);
        }
      }
    } else if (out && out.startsWith('unsat')) {
      return { status: 'verified', description: this.description, loc: this.loc };
    } else if (out && out.startsWith('unknown')) {
      return { status: 'unknown', description: this.description, loc: this.loc };
    } else {
      return unexpected(new Error('unexpected: ' + out), this.loc);
    }
  }

  private solveLocal (smt: SMTInput): Promise<SMTOutput> {
    if (!options.quiet && options.verbose) {
      console.log(`${this.description}: solving locally with ${options.z3path}`);
    }
    let p = Promise.resolve('');
    if (!checkedLocalZ3Version) {
      p = p.then(() => new Promise<SMTOutput>((resolve, reject) => {
        const exec = require('child_process').exec;
        exec(options.z3path + ' -version', (err: Error, out: string) => {
          if (err) {
            reject(new Error('cannot invoke z3: ' + String(err)));
          } else {
            const vstr = out.toString().match(/(\d+)\.(\d+)\.\d+/);
            if (!vstr || +vstr[1] < 4 || +vstr[2] < 5) {
              reject(new Error('esverify requires z3 verison 4.5 or above'));
            } else {
              checkedLocalZ3Version = true;
              resolve('');
            }
          }
        });
      }));
    }
    p = p.then(() => new Promise<SMTOutput>((resolve, reject) => {
      const spawn = require('child_process').spawn;
      const p = spawn(options.z3path, ['-smt2', '-in'], {stdio: ['pipe', 'pipe', 'ignore']});
      let result: string = '';
      p.stdout.on('data', (data: Object) => { result += data.toString(); });
      p.on('exit', (code: number) => resolve(result));
      p.on('error', reject);
      p.stdin.write(smt);
      p.stdin.end();
    }));
    return p;
  }

  private solveRemote (smt: SMTInput): Promise<SMTOutput> {
    if (!options.quiet && options.verbose) {
      console.log(`${this.description}: sending request to ${options.z3url}`);
    }
    return fetch(options.z3url, { method: 'POST', body: smt }).then(req => req.text());
  }
}
