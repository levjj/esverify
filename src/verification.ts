import { stringifyTestCode } from './codegen';
import { Substituter, Syntax, nullLoc } from './javascript';
import { Classes, FreeVars, Heap, Heaps, Locs, P, Vars } from './logic';
import { Message, MessageException, unexpected } from './message';
import { Model, valueToJavaScript } from './model';
import { options } from './options';
import { SMTInput, SMTOutput, vcToSMT } from './smt';

declare const console: { log: (s: string) => void };
declare const require: (s: string) => any;
declare const fetch: (s: string, opts: any) => Promise<any>;

let checkedLocalZ3Version: boolean = false;

export default class VerificationCondition {
  classes: Classes;
  heaps: Heaps;
  locs: Locs;
  vars: Vars;
  prop: P;
  loc: Syntax.SourceLocation;
  freeVars: FreeVars;
  testBody: Array<Syntax.Statement>;
  description: string;
  inprocess: boolean;
  result: Message | null;

  constructor (classes: Classes, heap: Heap, locs: Locs, vars: Vars, prop: P, loc: Syntax.SourceLocation,
               description: string, freeVars: FreeVars, body: Array<Syntax.Statement>) {
    this.classes = new Set([...classes]);
    this.heaps = new Set([...Array(heap + 1).keys()]);
    this.locs = new Set([...locs]);
    this.vars = new Set([...vars]);
    this.prop = prop;
    this.loc = loc;
    this.description = description;
    this.freeVars = [...freeVars];
    this.testBody = body;
    this.inprocess = false;
    this.result = null;
  }

  async verify (): Promise<Message> {
    this.inprocess = true;
    try {
      const smtin = this.prepareSMT();
      const smtout = await (options.remote ? this.solveRemote(smtin) : this.solveLocal(smtin));
      const modelOrMessage = this.processSMTOutput(smtout);
      return this.result = modelOrMessage instanceof Model
        ? this.runTest(modelOrMessage)
        : modelOrMessage;
    } catch (error) {
      if (error instanceof MessageException) return this.result = error.msg;
      return this.result = unexpected(error, this.loc, this.description);
    } finally {
      this.inprocess = false;
    }
  }

  runTest (model: Model | undefined): Message {
    if (model === undefined) {
      if (!this.result) throw new Error('no model available');
      if (this.result.status === 'verified' || this.result.status === 'unknown' || this.result.status === 'timeout' ||
         (this.result.status === 'error' && this.result.type !== 'incorrect')) {
        throw new Error('no model available');
      }
      return this.runTest(this.result.model);
    } else {
      const code = this.testCode(model);
      try {
        /* tslint:disable:no-eval */
        eval(code);
        return { status: 'unverified', description: this.description, loc: this.loc, model };
      } catch (e) {
        if (e instanceof Error && (e instanceof TypeError || e.message === 'assertion failed')) {
          return {
            status: 'error',
            type: 'incorrect',
            description: this.description,
            loc: this.loc,
            model,
            error: e
          };
        } else {
          return unexpected(e, this.loc, this.description);
        }
      }
    }
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
    const sub: Substituter = new Substituter();
    this.freeVars.forEach(freeVar => {
      const expr = valueToJavaScript(model.valueOf(freeVar));
      const und: Syntax.Literal = { type: 'Literal', value: undefined, loc: nullLoc() };
      sub.replaceVar(`__free__${typeof freeVar === 'string' ? freeVar : freeVar.name}`, und, expr);
    });
    const code = stringifyTestCode(this.testBody.map(s => sub.visitStatement(s)));
    if (!options.quiet && options.verbose) {
      console.log('Test Code:');
      console.log('------------');
      console.log(code);
      console.log('------------');
    }
    return code;
  }

  private processSMTOutput (out: SMTOutput): Model | Message {
    if (out && out.startsWith('sat')) {
      return new Model(out);
    } else if (out && out.startsWith('unsat')) {
      return { status: 'verified', description: this.description, loc: this.loc };
    } else if (out && out.startsWith('unknown')) {
      return { status: 'unknown', description: this.description, loc: this.loc };
    } else if (out && out.startsWith('timeout')) {
      return { status: 'timeout', description: this.description, loc: this.loc };
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
            if (!vstr || +vstr[1] < 4 || +vstr[2] < 6) {
              reject(new Error('esverify requires z3 verison 4.6 or above'));
            } else {
              checkedLocalZ3Version = true;
              resolve('');
            }
          }
        });
      }));
    }
    if (!options.quiet && options.verbose) {
      p = p.then(() => new Promise<string>((resolve, reject) => {
        const writeFile = require('fs').writeFile;
        writeFile(options.logsmt, smt, (err: Error, out: string) => {
          if (err) {
            reject(new Error('cannot write: ' + String(err)));
          } else {
            resolve('');
          }
        });
      }));
    }
    p = p.then(() => new Promise<SMTOutput>((resolve, reject) => {
      const spawn = require('child_process').spawn;
      const p = spawn(options.z3path, [`-T:${options.timeout}`, '-smt2', '-in'], { stdio: ['pipe', 'pipe', 'ignore'] });
      let result: string = '';
      p.stdout.on('data', (data: Object) => { result += data.toString(); });
      p.on('exit', (code: number) => {
        if (!options.quiet && options.verbose) {
          console.log('SMT Output:');
          console.log('------------');
          console.log(result);
          console.log('------------');
        }
        return resolve(result);
      });
      p.on('error', reject);
      p.stdin.write(smt);
      p.stdin.end();
    }));
    return p;
  }

  private async solveRemote (smt: SMTInput): Promise<SMTOutput> {
    if (!options.quiet && options.verbose) {
      console.log(`${this.description}: sending request to ${options.z3url}`);
    }
    const req = await fetch(options.z3url, { method: 'POST', body: smt });
    const smtout = await req.text();
    if (!options.quiet && options.verbose) {
      console.log('SMT Output:');
      console.log('------------');
      console.log(smtout);
      console.log('------------');
    }
    return smtout;
  }
}
