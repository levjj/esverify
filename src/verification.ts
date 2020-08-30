import { stringifyTestCode } from './codegen';
import { Substituter, Syntax, nullLoc, TestCode, eqSourceLocation, compEndPosition, id,
         replaceVarAssertion, replaceVarExpr } from './javascript';
import { Classes, FreeVars, Heap, Heaps, Locs, P, Vars, not, and } from './logic';
import { Message, MessageException, unexpected } from './message';
import { Model, valueToJavaScript, JSVal } from './model';
import { getOptions } from './options';
import { SMTInput, SMTOutput, vcToSMT } from './smt';
import { sourceAsJavaScriptAssertion, sourceAsJavaScriptExpression } from './parser';
import { VCGenerator } from './vcgen';
import { Interpreter, interpret } from './interpreter';
import { generatePreamble } from './preamble';

export type Assumption = Readonly<{source: string, prop: P, canBeDeleted: boolean}>;

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
  private aliases: { [from: string]: string };
  private watches: Array<[string, Syntax.Expression]>;

  private model: Model | null;
  private interpreter: Interpreter | null;
  private result: Message | null;

  constructor (classes: Classes, heap: Heap, locs: Locs, vars: Vars, prop: P, assumptions: Array<Assumption>,
               assertion: P, loc: Syntax.SourceLocation, description: string, freeVars: FreeVars,
               testBody: TestCode, testAssertion: TestCode, heapHints: Array<[Syntax.SourceLocation, Heap]>,
               aliases: { [from: string]: string }) {
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
    this.aliases = aliases;
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
      const smtout = await (getOptions().remote ? this.solveRemote(smtin) : this.solveLocal(smtin));
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
    let assumption = sourceAsJavaScriptAssertion(source);
    for (const aliasedVar in this.aliases) {
      const replacement = this.aliases[aliasedVar];
      assumption = replaceVarAssertion(aliasedVar, id(replacement), id(replacement), assumption);
    }
    const maxHeap = Math.max(...this.heaps.values());
    const assumptions = this.assumptions.map(({ source }) => source);
    const vcgen = new VCGenerator(new Set([...this.classes]), maxHeap, maxHeap,
                                  new Set([...this.locs]), new Set([...this.vars]), assumptions, this.heapHints,
                                  true, this.prop);
    const [assumptionP] = vcgen.assume(assumption);
    this.assumptions = this.assumptions.concat([{ source, prop: assumptionP, canBeDeleted: true }]);
  }

  getAssumptions (): Array<[string, boolean]> {
    return this.assumptions.map(({ source, canBeDeleted }): [string, boolean] => [source, canBeDeleted]);
  }

  removeAssumption (idx: number): void {
    const assumptionToRemove = idx < this.assumptions.length ? this.assumptions[idx] : undefined;
    if (assumptionToRemove === undefined) throw new Error('no such assumption');
    if (!assumptionToRemove.canBeDeleted) throw new Error('cannot remove built-in assumptions');
    this.assumptions = this.assumptions.filter(a => a !== assumptionToRemove);
  }

  assert (source: string): VerificationCondition {
    let assertion = sourceAsJavaScriptAssertion(source);
    for (const aliasedVar in this.aliases) {
      const replacement = this.aliases[aliasedVar];
      assertion = replaceVarAssertion(aliasedVar, id(replacement), id(replacement), assertion);
    }
    const maxHeap = Math.max(...this.heaps.values());
    const assumptions = this.assumptions.map(({ source }) => source);
    const vcgen = new VCGenerator(new Set([...this.classes]), maxHeap, maxHeap,
                                  new Set([...this.locs]), new Set([...this.vars]), assumptions,
                                  this.heapHints, true, this.prop);
    const [assertionP, , assertionT] = vcgen.assert(assertion);
    return new VerificationCondition(this.classes, maxHeap, this.locs, this.vars, this.prop, this.assumptions,
                                     assertionP, this.loc, source, this.freeVars, this.testBody, assertionT,
                                     this.heapHints, this.aliases);
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

  getScopes (frameIndex: number): Array<Array<[string, JSVal, JSVal | undefined]>> {
    const heap = this.guessCurrentHeap();
    return this.getInterpreter().scopes(frameIndex).map(scope =>
      scope.map(([varname, dynamicValue]): [string, JSVal, JSVal | undefined] => {
        const staticValue = this.modelValue(varname, heap);
        return [varname, this.getInterpreter().asValue(dynamicValue), staticValue];
      })
    );
  }

  getWatches (): Array<[string, JSVal | undefined, JSVal | undefined]> {
    return this.watches.map(([src, expr]): [string, JSVal | undefined, JSVal | undefined] => {
      let dynamicValue: JSVal | undefined = undefined;
      let staticValue: JSVal | undefined = undefined;
      try {
        dynamicValue = this.getInterpreter().asValue(this.getInterpreter().evalExpression(expr, []));
        staticValue = this.getInterpreter().asValue(
          this.getInterpreter().evalExpression(expr, this.currentBindingsFromModel()));
      } catch (e) { /* ignore errors */ }
      return [src, dynamicValue, staticValue];
    });
  }

  addWatch (source: string): void {
    let expr = sourceAsJavaScriptExpression(source);
    for (const aliasedVar in this.aliases) {
      const replacement = this.aliases[aliasedVar];
      expr = replaceVarExpr(aliasedVar, id(replacement), id(replacement), expr);
    }
    this.watches.push([source, expr]);
  }

  removeWatch (idx: number): void {
    const watchToRemove = idx < this.watches.length ? this.watches[idx] : undefined;
    if (watchToRemove === undefined) throw new Error('no such watch');
    this.watches = this.watches.filter(w => w !== watchToRemove);
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

  getAnnotations (): Array<[Syntax.SourceLocation, Array<JSVal>, JSVal | undefined]> {
    return this.getInterpreter().annotations
    .filter(annotation => annotation.location.file === getOptions().filename)
    .map((annotation): [Syntax.SourceLocation, Array<JSVal>, JSVal | undefined] => {
      const heap = this.guessCurrentHeap(annotation.location);
      const staticValue = this.modelValue(annotation.variableName, heap);
      return [
        annotation.location,
        annotation.values.map((v: any): JSVal => this.getInterpreter().asValue(v)),
        staticValue
      ];
    });
  }

  getResult (): Message | null {
    return this.result;
  }

  private prepareSMT (): SMTInput {
    const prop = and(this.prop, ...this.assumptions.map(({ prop }) => prop), not(this.assertion));
    const smt = vcToSMT(this.classes, this.heaps, this.locs, this.vars, this.freeVars, prop);
    if (getOptions().verbose) {
      console.log('SMT Input:');
      console.log('------------');
      console.log(smt);
      console.log('------------');
    }
    return smt;
  }

  private solveLocal (smt: SMTInput): Promise<SMTOutput> {
    if (!getOptions().quiet && getOptions().verbose) {
      console.log(`${this.description}: solving locally with ${getOptions().z3path}`);
    }
    let p = Promise.resolve('');
    if (!checkedLocalZ3Version) {
      p = p.then(() => new Promise<SMTOutput>((resolve, reject) => {
        const exec = require('child_process').exec;
        exec(getOptions().z3path + ' -version', (err: Error, out: string) => {
          if (err) {
            reject(new Error('cannot invoke z3: ' + String(err)));
          } else {
            const vstr = out.toString().match(/(\d+)\.(\d+)\.\d+/);
            if (!vstr || +vstr[1] !== 4 || +vstr[2] !== 6) {
              reject(new Error('esverify requires z3 verison 4.6'));
            } else {
              checkedLocalZ3Version = true;
              resolve('');
            }
          }
        });
      }));
    }
    if (!getOptions().quiet && getOptions().verbose) {
      p = p.then(() => new Promise<string>((resolve, reject) => {
        const writeFile = require('fs').writeFile;
        writeFile(getOptions().logsmt, smt, (err: Error, out: string) => {
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
      const p = spawn(getOptions().z3path,
                      [`-T:${getOptions().timeout}`, '-smt2', '-in'],
                      { stdio: ['pipe', 'pipe', 'ignore'] });
      let result: string = '';
      p.stdout.on('data', (data: Object) => { result += data.toString(); });
      p.on('exit', (code: number) => {
        if (!getOptions().quiet && getOptions().verbose) {
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
    if (!getOptions().quiet && getOptions().verbose) {
      console.log(`${this.description}: sending request to ${getOptions().z3url}`);
    }
    const req = await fetch(getOptions().z3url, { method: 'POST', body: smt });
    const smtout = await req.text();
    if (!getOptions().quiet && getOptions().verbose) {
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
    if (!getOptions().quiet && getOptions().verbose) {
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
    while (interpreter.canStep() && interpreter.loc().file !== getOptions().filename) {
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

  private modelValue (varname: string, currentHeap: Heap): JSVal | undefined {
    const model = this.getModel();
    if (model.mutableVariables().has(varname)) {
      try {
        return model.valueOf({ name: varname, heap: currentHeap });
      } catch (e) {
        return undefined;
      }
    } else {
      return model.valueOf(varname);
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
      const jsval = this.modelValue(varname, heap);
      if (jsval !== undefined) {
        bindings.push([varname, this.getInterpreter().fromValue(jsval)]);
      }
    }
    return bindings;
  }
}
