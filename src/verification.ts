import { stringifyTestCode } from './codegen';
import { Substituter, Syntax, nullLoc, TestCode, eqSourceLocation, compEndPosition } from './javascript';
import { Classes, FreeVars, Heap, Heaps, Locs, P, Vars, not, and } from './logic';
import { Message, MessageException, unexpected } from './message';
import { Model, valueToJavaScript, valueToPlain } from './model';
import { options } from './options';
import { SMTInput, SMTOutput, vcToSMT } from './smt';
import { sourceAsJavaScriptAssertion } from './parser';
import { VCGenerator } from './vcgen';
import { Interpreter, interpret } from './interpreter';
import { generatePreamble } from './preamble';

export type Assumption = [string, P];

declare const console: { log: (s: string) => void };
declare const require: (s: string) => any;
declare const fetch: (s: string, opts: any) => Promise<any>;

let checkedLocalZ3Version: boolean = false;

export default class VerificationCondition {
  private classes: Classes;
  private heaps: Heaps;
  private locs: Locs;
  private vars: Vars;
  private prop: P;
  private assumptions: Array<Assumption>;
  private assertion: P;
  private loc: Syntax.SourceLocation;
  private freeVars: FreeVars;
  private testBody: TestCode;
  private testAssertion: TestCode;
  private description: string;
  private heapHints: Array<[Syntax.SourceLocation, Heap]>;
  private watches: Array<string>;

  private model: Model | null;
  private interpreter: Interpreter | null;
  private result: Message | null;

  constructor (classes: Classes, heap: Heap, locs: Locs, vars: Vars, prop: P, assumptions: Array<Assumption>,
               assertion: P, loc: Syntax.SourceLocation, description: string, freeVars: FreeVars,
               testBody: TestCode, testAssertion: TestCode, heapHints: Array<[Syntax.SourceLocation, Heap]>) {
    this.classes = new Set([...classes]);
    this.heaps = new Set([...Array(heap + 1).keys()]);
    this.locs = new Set([...locs]);
    this.vars = new Set([...vars]);
    this.prop = prop;
    this.assumptions = assumptions;
    this.assertion = assertion;
    this.loc = loc;
    this.description = description;
    this.freeVars = [...freeVars];
    this.testBody = testBody;
    this.testAssertion = testAssertion;
    this.heapHints = heapHints;
    this.watches = [];

    this.model = null;
    this.interpreter = null;
    this.result = null;
  }

  async verify (): Promise<Message> {
    try {
      this.model = null;
      this.interpreter = null;
      this.result = null;
      const smtin = this.prepareSMT();
      const smtout = await (options.remote ? this.solveRemote(smtin) : this.solveLocal(smtin));
      const modelOrMessage = this.processSMTOutput(smtout);
      if (modelOrMessage instanceof Model) {
        this.model = modelOrMessage;
        return this.result = this.runTest();
      } else {
        return this.result = modelOrMessage;
      }
    } catch (error) {
      if (error instanceof MessageException) return this.result = error.msg;
      return this.result = unexpected(error, this.loc, this.description);
    }
  }

  getDescription (): string {
    return this.description;
  }

  getLocation (): Syntax.SourceLocation {
    return this.loc;
  }

  setDescription (description: string): void {
    this.description = description;
  }

  hasModel (): boolean {
    return this.model !== null;
  }

  runTest (): Message {
    const code = this.testSource();
    try {
      /* tslint:disable:no-eval */
      eval(code);
      return { status: 'unverified', description: this.description, loc: this.loc, model: this.getModel() };
    } catch (e) {
      if (e instanceof Error && (e instanceof TypeError || e.message === 'assertion failed')) {
        return {
          status: 'error',
          type: 'incorrect',
          description: this.description,
          loc: this.loc,
          model: this.getModel(),
          error: e
        };
      } else {
        return unexpected(e, this.loc, this.description);
      }
    }
  }

  runWithInterpreter (): Message {
    const interpreter = this.getInterpreter();
    try {
      interpreter.run();
      this.result = { status: 'unverified', description: this.description, loc: this.loc, model: this.getModel() };
      return this.result;
    } catch (e) {
      if (e instanceof Error && (e instanceof TypeError || e.message === 'assertion failed')) {
        return this.result = {
          status: 'error',
          type: 'incorrect',
          description: this.description,
          loc: this.loc,
          model: this.getModel(),
          error: e
        };
      } else {
        return this.result = unexpected(e, this.loc, this.description);
      }
    }
  }

  addAssumption (source: string): void {
    const assumption = sourceAsJavaScriptAssertion(source);
    const maxHeap = Math.max(...this.heaps.values());
    const assumptions = this.assumptions.map(([src]) => src);
    const vcgen = new VCGenerator(new Set([...this.classes]), maxHeap, maxHeap,
                                  new Set([...this.locs]), new Set([...this.vars]), assumptions, this.heapHints,
                                  this.prop);
    const [assumptionP] = vcgen.assume(assumption);
    this.assumptions = this.assumptions.concat([[source, assumptionP]]);
  }

  getAssumptions (): Array<string> {
    return this.assumptions.map(([src]) => src);
  }

  removeAssumption (idx: number): void {
    this.assumptions = this.assumptions.filter((_, i) => i !== idx);
  }

  assert (source: string): VerificationCondition {
    const assertion = sourceAsJavaScriptAssertion(source);
    const maxHeap = Math.max(...this.heaps.values());
    const assumptions = this.assumptions.map(([src]) => src);
    const vcgen = new VCGenerator(new Set([...this.classes]), maxHeap, maxHeap,
                                  new Set([...this.locs]), new Set([...this.vars]), assumptions,
                                  this.heapHints, this.prop);
    const [assertionP, , assertionT] = vcgen.assert(assertion);
    return new VerificationCondition(this.classes, maxHeap, this.locs, this.vars, this.prop, this.assumptions,
                                     assertionP, this.loc, source, this.freeVars, this.testBody, assertionT,
                                     this.heapHints);
  }

  steps (): number {
    return this.getInterpreter().steps;
  }

  pc (): Syntax.SourceLocation {
    return this.getInterpreter().loc();
  }

  iteration (): number {
    return this.getInterpreter().iteration();
  }

  callstack (): Array<[string, Syntax.SourceLocation, number]> {
    return this.getInterpreter().callstack();
  }

  getWatches (): Array<Array<[string, any, any]>> {
    const heap = this.guessCurrentHeap();
    const scopes: Array<Array<[string, any, any]>> = this.getInterpreter().scopes().map(scope =>
      scope.map(([varname, dynamicValue]): [string, any, any] => {
        const staticValue = this.modelValue(varname, heap);
        return [varname, dynamicValue, staticValue];
      })
    );
    scopes.push(this.watches.map((watchSource: string): [string, any, any] => {
      let dynamicValue: any = '<<error>>';
      let staticValue: any = '<<error>>';
      try {
        dynamicValue = this.getInterpreter().eval(watchSource, []);
        staticValue = this.getInterpreter().eval(watchSource, this.currentBindingsFromModel());
      } catch (e) { /* ignore errors */ }
      return [watchSource, dynamicValue, staticValue];
    }));
    return scopes;
  }

  addWatch (source: string): void {
    this.watches.push(source);
  }

  restart (): void {
    this.getInterpreter().restart();
    this.stepToSource();
  }

  goto (pos: Syntax.Position, iteration: number = 0): void {
    this.getInterpreter().goto(pos, iteration);
    this.stepToSource();
  }

  stepInto (): void {
    this.getInterpreter().stepInto();
    this.stepToSource();
  }

  stepOver (): void {
    this.getInterpreter().stepOver();
    this.stepToSource();
  }

  stepOut (): void {
    this.getInterpreter().stepOut();
    this.stepToSource();
  }

  getAnnotations (): Array<[Syntax.SourceLocation, Array<any>, any]> {
    return this.getInterpreter().annotations
    .filter(annotation => annotation.location.file === options.filename)
    .map((annotation): [Syntax.SourceLocation, Array<any>, any] => {
      const heap = this.guessCurrentHeap(annotation.location);
      const staticValue = this.modelValue(annotation.variableName, heap);
      return [annotation.location, annotation.values, staticValue];
    });
  }

  getResult (): Message | null {
    return this.result;
  }

  private prepareSMT (): SMTInput {
    const prop = and(this.prop, ...this.assumptions.map(([,p]) => p), not(this.assertion));
    const smt = vcToSMT(this.classes, this.heaps, this.locs, this.vars, this.freeVars, prop);
    if (options.verbose) {
      console.log('SMT Input:');
      console.log('------------');
      console.log(smt);
      console.log('------------');
    }
    return smt;
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

  private getModel (): Model {
    if (!this.model) throw new Error('no model available');
    return this.model;
  }

  private testCode (): TestCode {
    const sub: Substituter = new Substituter();
    this.freeVars.forEach(freeVar => {
      const expr = valueToJavaScript(this.getModel().valueOf(freeVar));
      const und: Syntax.Literal = { type: 'Literal', value: undefined, loc: nullLoc() };
      sub.replaceVar(`__free__${typeof freeVar === 'string' ? freeVar : freeVar.name}`, und, expr);
    });
    const testCode = this.testBody.concat(this.testAssertion);
    return testCode.map(s => sub.visitStatement(s));
  }

  private testSource (): string {
    const code = stringifyTestCode(this.testCode());
    if (!options.quiet && options.verbose) {
      console.log('Test Code:');
      console.log('------------');
      console.log(code);
      console.log('------------');
    }
    return code;
  }

  private getInterpreter (): Interpreter {
    if (!this.interpreter) {
      const prog: Syntax.Program = {
        body: [...this.testCode()],
        invariants: []
      };
      this.interpreter = interpret(prog);
      this.stepToSource();
    }
    return this.interpreter;
  }

  private stepToSource (): void {
    const interpreter = this.getInterpreter();
    while (interpreter.loc().file !== options.filename) {
      interpreter.stepInto();
    }
  }

  private guessCurrentHeap (loc: Syntax.SourceLocation = this.pc()): Heap {
    // find index of heap hint
    const idx = this.heapHints.findIndex(([loc2]) => eqSourceLocation(loc, loc2));
    if (idx >= 0) {
      return this.heapHints[idx][1];
    } else {
      // no exact match found in heap hints
      // find index of first heap hint that is not earlier
      const idx = this.heapHints.findIndex(([loc2]) => !compEndPosition(loc, loc2));
      if (idx >= 0) {
        return this.heapHints[idx][1];
      } else if (this.heapHints.length > 0) {
        // no heap hint found that is later, so use last
        return this.heapHints[this.heapHints.length - 1][1];
      } else {
        throw new Error('unable to guess current heap');
      }
    }
  }

  private modelValue (varname: string, currentHeap: Heap): any {
    const model = this.getModel();
    if (model.mutableVariables().has(varname)) {
      try {
        return valueToPlain(model.valueOf({ name: varname, heap: currentHeap }));
      } catch (e) {
        return undefined;
      }
    } else {
      return valueToPlain(model.valueOf(varname));
    }
  }

  private currentBindingsFromModel (): Array<[string, any]> {
    const model = this.getModel();
    const heap = this.guessCurrentHeap();
    const bindings: Array<[string, any]> = [];
    for (const varname of model.variables()) {
      if (generatePreamble().vars.has(varname) || generatePreamble().locs.has(varname)) {
        continue;
      }
      bindings.push([varname, this.modelValue(varname, heap)]);
    }
    return bindings;
  }
}
