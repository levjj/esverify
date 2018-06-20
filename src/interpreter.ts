import { Syntax, Visitor, eqSourceLocation, nullLoc, eqEndPosition, compEndPosition,
         findSourceLocation } from './javascript';
import { sourceAsJavaScriptExpression } from './parser';
import { JSVal } from './model';
import { getOptions } from './options';

declare const console: { log: (s: string) => void };

class Scope {

  bindings: Array<[string, any, 'let' | 'const']>;
  parent: Scope | null;

  constructor (parent: Scope | null = null) {
    this.bindings = [];
    this.parent = parent;
  }

  define (name: string, val: any, kind: 'let' | 'const'): void {
    if (this.bindings.some(([n]) => n === name)) {
      throw new SyntaxError(`Identifier '${name}' has already been declared`);
    }
    this.bindings.push([name, val, kind]);
  }

  lookup (name: string): any {
    const idx = this.bindings.findIndex(([n]) => n === name);
    if (idx >= 0) {
      return this.bindings[idx][1];
    } else if (this.parent) {
      return this.parent.lookup(name);
    } else {
      throw new ReferenceError(`${name} is not defined`);
    }
  }

  assign (name: string, val: any): void {
    const idx = this.bindings.findIndex(([n]) => n === name);
    if (idx >= 0) {
      if (this.bindings[idx][2] === 'const') {
        throw new TypeError('Assignment to constant variable.');
      }
      this.bindings[idx][1] = val;
    } else if (this.parent) {
      this.parent.assign(name, val);
    } else {
      throw new ReferenceError(`ReferenceError: ${name} is not defined`);
    }
  }

  asArray (): Array<Array<[string, any]>> {
    const bindings: Array<[string, any]> = this.bindings.map(([name, val]): [string, any] => [name, val]);
    return this.parent ? [bindings].concat(this.parent.asArray()) : [bindings];
  }
}

function globalScope (): Scope {
  const scope = new Scope();
  scope.define('Object', Object, 'const');
  scope.define('Function', Function, 'const');
  scope.define('Array', Array, 'const');
  scope.define('String', String, 'const');
  scope.define('console', console, 'let');
  scope.define('parseInt', parseInt, 'const');
  scope.define('Math', Math, 'const');
  scope.define('Number', Number, 'const');

  scope.define('assert', function assert (p: any) { if (!p) throw new Error('assertion failed'); }, 'const');
  scope.define('spec', function spec (f: any, id: any, req: any, ens: any) {
    if (f._mapping) {
      f._mapping[id] = [req, ens];
      return f;
    } else {
      const mapping = { [id]: [req, ens] };
      const wrapped: any = function (this: any, ...args: any[]) {
        return Object.values(mapping).reduceRight(function (cont, [req, ens]) {
          return function (this: any, ...args2: any[]) {
            const args3 = req.apply(this, args2);
            return ens.apply(this, args3.concat([cont.apply(this, args3)]));
          };
        }, f).apply(this, args);
      };
      wrapped._mapping = mapping;
      wrapped._orig = f;
      return wrapped;
    }
  }, 'const');

  return scope;
}

interface InterpreterFunction extends Function {
  scope: Scope;
  node: Syntax.Function;
}

function isInterpreterFunction (f: any): f is InterpreterFunction {
  return typeof f === 'function' && 'scope' in f && 'node' in f;
}

interface SpecWrappedFunction extends Function {
  _mapping: { [id: number]: [InterpreterFunction, InterpreterFunction] };
  _orig: Function;
}

function isSpecWrappedFunction (f: any): f is SpecWrappedFunction {
  return typeof f === 'function' && '_mapping' in f;
}

enum StepResult { NOP, STEP, DONE, SET }

abstract class BaseStackFrame {
  scope: Scope;
  pc: Syntax.Expression | Syntax.Statement | null;
  operandStack: Array<any>;
  iteration: number;

  constructor (scope: Scope) {
    this.scope = scope;
    this.pc = null;
    this.operandStack = [];
    this.iteration = 0;
  }

  define (name: string, val: any, kind: 'let' | 'const'): void {
    this.scope.define(name, val, kind);
  }

  lookup (name: string): any {
    return this.scope.lookup(name);
  }

  assign (name: string, val: any): void {
    this.scope.assign(name, val);
  }

  loc (): Syntax.SourceLocation {
    if (this.pc === null) return nullLoc();
    return this.pc.loc;
  }

  newBlockScope (): void {
    this.scope = new Scope(this.scope);
  }

  popBlockScope (): void {
    if (this.scope.parent === null) throw new Error('no scope to pop');
    this.scope = this.scope.parent;
  }

  scopes (): Array<Array<[string, any]>> {
    return this.scope.asArray();
  }

  nextIteration (): void {
    this.iteration++;
  }

  toString (): string {
    return `${this.name()} (${this.loc().file}:${this.loc().start.line}:${this.loc().start.column})`;
  }

  asTuple (): [string, Syntax.SourceLocation, number] {
    return [this.toString(), this.loc(), this.iteration];
  }

  abstract name (): string;

  abstract entry (interpreter: InterpreterVisitor): StepResult;

}

class ProgramStackFrame extends BaseStackFrame {
  program: Syntax.Program;

  constructor (program: Syntax.Program) {
    super(globalScope());
    this.program = program;
  }

  name (): string {
    return '<program>';
  }

  entry (interpreter: InterpreterVisitor): StepResult {
    return interpreter.visitProgram(this.program);
  }
}

class FunctionStackFrame extends BaseStackFrame {
  func: InterpreterFunction;

  constructor (func: InterpreterFunction) {
    super(new Scope(func.scope));
    this.func = func;
  }

  name (): string {
    return this.func.node.id === null ? '<anonymous>' : this.func.node.id.name;
  }

  entry (interpreter: InterpreterVisitor): StepResult {
    const res = interpreter.visitBlockStatement(this.func.node.body);
    if (res === StepResult.DONE) {
      interpreter.ret(undefined);
    }
    return StepResult.STEP;
  }
}

class SpecStackFrame extends BaseStackFrame {
  func: SpecWrappedFunction;
  thisArg: any;
  args: Array<any>;
  preCheckers: Array<InterpreterFunction>;
  functionCalled: boolean;
  postCheckers: Array<InterpreterFunction>;

  constructor (func: SpecWrappedFunction, thisArg: any, args: Array<any>) {
    super(new Scope());
    this.func = func;
    this.thisArg = thisArg;
    this.args = args;
    this.operandStack.push(args);
    this.preCheckers = Object.values(func._mapping).map(([req]) => req);
    this.functionCalled = false;
    this.postCheckers = Object.values(func._mapping).map(([, ens]) => ens);
  }

  name (): string {
    return `<spec of ${this.func._orig.name || 'anonymous'}>`;
  }

  entry (interpreter: InterpreterVisitor): StepResult {
    const nextPreCheck = this.preCheckers.shift();
    if (nextPreCheck !== undefined) {
      this.args = this.operandStack.pop();
      interpreter.call(nextPreCheck, this.thisArg, this.args);
    } else if (!this.functionCalled) {
      this.args = this.operandStack.pop();
      interpreter.call(this.func._orig, this.thisArg, this.args);
      this.functionCalled = true;
    } else {
      const prevResult = this.operandStack.pop();
      const nextPostCheck = this.postCheckers.shift();
      if (nextPostCheck !== undefined) {
        interpreter.call(nextPostCheck, this.thisArg, this.args.concat([prevResult]));
      } else {
        interpreter.ret(prevResult);
      }
    }
    return StepResult.STEP;
  }
}

class EvaluationStackFrame extends BaseStackFrame {
  expression: Syntax.Expression;

  constructor (expression: Syntax.Expression, scope: Scope) {
    super(new Scope(scope));
    this.expression = expression;
  }

  name (): string {
    return '<eval>';
  }

  entry (interpreter: InterpreterVisitor): StepResult {
    return interpreter.visitExpression(this.expression);
  }
}

type StackFrame = ProgramStackFrame | FunctionStackFrame | SpecStackFrame | EvaluationStackFrame;

interface MethodCallExpression {
  type: 'CallExpression';
  callee: Syntax.MemberExpression;
  args: Array<Syntax.Expression>;
  loc: Syntax.SourceLocation;
}

function isMethodCall (expr: Syntax.CallExpression): expr is MethodCallExpression {
  return expr.callee.type === 'MemberExpression';
}

export interface Annotation {
  location: Syntax.SourceLocation;
  variableName: string;
  values: Array<any>;
}

export interface Interpreter {
  steps: number;
  annotations: Array<Annotation>;
  loc (): Syntax.SourceLocation;
  iteration (): number;
  callstack (): Array<[string, Syntax.SourceLocation, number]>;
  scopes (frameIndex: number): Array<Array<[string, any]>>;
  goto (pos: Syntax.Position, iteration: number): void;
  restart (): void;
  canStep (): boolean;
  stepInto (): void;
  stepOver (): void;
  stepOut (): void;
  run (): void;
  define (name: string, val: any, kind: 'let' | 'const'): void;
  eval (source: string, bindings: Array<[string, any]>): any;
  asValue (val: any): JSVal;
  fromValue (val: JSVal): any;
}

class InterpreterVisitor extends Visitor<void, void, StepResult, StepResult> implements Interpreter {
  program: Syntax.Program;
  steps: number;
  annotations: Array<Annotation>;
  private stack: Array<StackFrame>;
  private breakpoint: [Syntax.SourceLocation, number] | null;

  constructor (program: Syntax.Program) {
    super();
    this.program = program;
    this.steps = 0;
    this.annotations = [];
    this.stack = [new ProgramStackFrame(program)];
    this.breakpoint = null;
    this.visitProgram(program); // set initial PC
  }

  // --- Interpreter methods

  loc (): Syntax.SourceLocation {
    const pc = this.pc();
    if (pc === null) return nullLoc();
    return pc.loc;
  }

  iteration (): number {
    return this.frame().iteration;
  }

  callstack (): Array<[string, Syntax.SourceLocation, number]> {
    return this.stack.map(frame => frame.asTuple());
  }

  scopes (frameIndex: number): Array<Array<[string, any]>> {
    const idx = Math.max(0, Math.min(this.stack.length - 1, frameIndex));
    return this.stack[idx].scopes();
  }

  restart (): void {
    this.reset();
  }

  canStep (): boolean {
    if (this.steps >= getOptions().maxInterpreterSteps) {
      return false;
    }
    if (this.isBreaking()) return false;
    return this.stack.length > 0 && this.pc() !== null;
  }

  goto (pos: Syntax.Position, iteration: number = 0): void {
    this.reset();
    const loc = findSourceLocation(this.program, pos);
    this.breakpoint = [loc, iteration];
    this.run();
    if (!eqSourceLocation(loc, this.loc()) || iteration !== this.iteration()) {
      throw new Error('did not reach breakpoint');
    }
  }

  define (name: string, val: any, kind: 'let' | 'const'): void {
    this.frame().define(name, val, kind);
  }

  eval (source: string, optBindings: Array<[string, any]> = []): any {
    const expression = sourceAsJavaScriptExpression(source);
    this.stack.push(new EvaluationStackFrame(expression, this.frame().scope));
    try {
      for (const [varname, value] of optBindings) {
        this.frame().define(varname, value, 'let');
      }
      while (true) {
        const res = this.step();
        if (res === StepResult.DONE) {
          return this.popOp();
        }
      }
    } finally {
      this.stack.pop();
    }
  }

  asValue (val: any): JSVal {
    if (typeof val === 'number') {
      return { type: 'num', v: val };
    } else if (typeof val === 'boolean') {
      return { type: 'bool', v: val };
    } else if (typeof val === 'string') {
      return { type: 'str', v: val };
    } else if (val === null) {
      return { type: 'null' };
    } else if (val === undefined) {
      return { type: 'undefined' };
    } else if (isInterpreterFunction(val)) {
      return {
        type: 'fun',
        body: {
          type: 'FunctionExpression',
          body: val.node.body,
          ensures: val.node.ensures,
          freeVars: val.node.freeVars,
          id: val.node.id,
          loc: val.node.loc,
          params: val.node.params,
          requires: val.node.requires
        }
      };
    } else if (isSpecWrappedFunction(val)) {
      return this.asValue(val._orig);
    } else if (val instanceof Array) {
      return { type: 'arr', elems: val.map(e => this.asValue(e)) };
    } else if ('_cls_' in val) {
      const [cls, ...args] = val._cls_;
      return { type: 'obj-cls', cls, args: args.map((a: any) => this.asValue(a)) };
    } else if (typeof val === 'object') {
      const obj: { [key: string]: JSVal } = {};
      Object.keys(val).forEach(key => obj[key] = this.asValue(val[key]));
      return { type: 'obj', v: obj };
    } else {
      const str = String(val);
      return { type: 'str', v: `<<${str.length > 30 ? str.substr(0, 27) + '...' : str}>>` };
    }
  }

  fromValue (val: JSVal): any {
    switch (val.type) {
      case 'num':
      case 'bool':
      case 'str':
        return val.v;
      case 'null':
        return null;
      case 'undefined':
        return undefined;
      case 'fun':
        return this.evalExpression(val.body);
      case 'obj':
        const obj: { [key: string]: any } = {};
        Object.keys(val.v).forEach(key => obj[key] = this.fromValue(val.v[key]));
        return obj;
      case 'obj-cls':
        const constr = this.frame().lookup(val.cls);
        const instance = new constr(...val.args.map(arg => this.fromValue(arg)));
        instance._cls_ = [constr.name, ...val.args];
        return instance;
      case 'arr':
        return val.elems.map(elem => this.fromValue(elem));
    }
  }

  // --- other methods

  evalExpression (expression: Syntax.Expression): any {
    this.stack.push(new EvaluationStackFrame(expression, this.frame().scope));
    while (true) {
      const res = this.step();
      if (res === StepResult.DONE) {
        const retVal = this.popOp();
        this.stack.pop();
        return retVal;
      }
    }
  }

  annotate (loc: Syntax.SourceLocation, variableName: string, value: any): any {
    // find index of annotation
    const idx = this.annotations.findIndex(({ location }) => eqEndPosition(loc, location));
    if (idx >= 0) {
      this.annotations[idx].values.push(value);
    } else {
      // no such annotation yet
      // find index of first annotation that is not earlier
      const idx = this.annotations.findIndex(({ location }) => !compEndPosition(loc, location));
      const annotation = { location: loc, variableName, values: [value] };
      if (idx >= 0) {
        this.annotations.splice(idx, 0, annotation);
      } else {
        // no annotation found that are later, so append
        this.annotations.push(annotation);
      }
    }
  }

  frame (): StackFrame {
    return this.stack[this.stack.length - 1];
  }

  pc (): Syntax.Expression | Syntax.Statement | null {
    return this.frame().pc;
  }

  setPC (pc: Syntax.Expression | Syntax.Statement | null): void {
    this.frame().pc = pc;
  }

  seeking (): boolean {
    return this.frame().pc === null;
  }

  clearPC (): void {
    this.frame().pc = null;
  }

  pushOp (x: any): void {
    this.frame().operandStack.push(x);
  }

  popOp (): any {
    return this.frame().operandStack.pop();
  }

  call (callee: any, thisArg: any, args: Array<any>): void {
    if (isSpecWrappedFunction(callee)) {
      const prevPC = this.pc();
      const newFrame = new SpecStackFrame(callee, thisArg, args);
      this.stack.push(newFrame);
      this.setPC(prevPC);
    } else if (isInterpreterFunction(callee)) {
      const newFrame = new FunctionStackFrame(callee);
      newFrame.define('this', thisArg, 'const');
      for (let i = 0; i < callee.node.params.length; i++) {
        const argVal = i < args.length ? args[i] : undefined;
        newFrame.define(callee.node.params[i].name, argVal, 'let');
      }
      this.stack.push(newFrame);
      this.visitBlockStatement(callee.node.body);
    } else if (callee instanceof Function) {
      const calleeFunction: Function = callee;
      this.pushOp(calleeFunction.apply(thisArg, args));
    } else {
      throw new TypeError('is not a function');
    }
  }

  ret (retValue: any): void {
    if (this.stack.length < 2) {
      throw new SyntaxError('Illegal return statement');
    }
    this.stack.pop();
    this.pushOp(retValue);
  }

  closure (func: Syntax.Function): InterpreterFunction {
    const interpreter = this;
    const f: any = function (this: any, ...args: any[]): any {
      interpreter.call(f, this, args);
      return interpreter.stepOut();
    };
    f.node = func;
    f.scope = this.frame().scope;
    return f;
  }

  // ---- Interpreter does not evaluate assertions ----

  visitIdentifierTerm (term: Syntax.Identifier): void {
    throw new Error('Method not implemented.');
  }

  visitOldIdentifierTerm (term: Syntax.OldIdentifier): void {
    throw new Error('Method not implemented.');
  }

  visitLiteralTerm (term: Syntax.Literal): void {
    throw new Error('Method not implemented.');
  }

  visitUnaryTerm (term: Syntax.UnaryTerm): void {
    throw new Error('Method not implemented.');
  }

  visitBinaryTerm (term: Syntax.BinaryTerm): void {
    throw new Error('Method not implemented.');
  }

  visitLogicalTerm (term: Syntax.LogicalTerm): void {
    throw new Error('Method not implemented.');
  }

  visitConditionalTerm (term: Syntax.ConditionalTerm): void {
    throw new Error('Method not implemented.');
  }

  visitCallTerm (term: Syntax.CallTerm): void {
    throw new Error('Method not implemented.');
  }

  visitMemberTerm (term: Syntax.MemberTerm): void {
    throw new Error('Method not implemented.');
  }

  visitIsIntegerTerm (term: Syntax.IsIntegerTerm): void {
    throw new Error('Method not implemented.');
  }

  visitToIntegerTerm (term: Syntax.ToIntegerTerm): void {
    throw new Error('Method not implemented.');
  }

  visitTermAssertion (assertion: Syntax.Term): void {
    throw new Error('Method not implemented.');
  }

  visitPureAssertion (assertion: Syntax.PureAssertion): void {
    throw new Error('Method not implemented.');
  }

  visitSpecAssertion (assertion: Syntax.SpecAssertion): void {
    throw new Error('Method not implemented.');
  }

  visitEveryAssertion (assertion: Syntax.EveryAssertion): void {
    throw new Error('Method not implemented.');
  }

  visitInstanceOfAssertion (assertion: Syntax.InstanceOfAssertion): void {
    throw new Error('Method not implemented.');
  }

  visitInAssertion (assertion: Syntax.InAssertion): void {
    throw new Error('Method not implemented.');
  }

  visitUnaryAssertion (assertion: Syntax.UnaryAssertion): void {
    throw new Error('Method not implemented.');
  }

  visitBinaryAssertion (assertion: Syntax.BinaryAssertion): void {
    throw new Error('Method not implemented.');
  }

  // ---- Evaluation of expressions and statements ----

  visitIdentifier (expr: Syntax.Identifier): StepResult {
    if (this.seeking()) {
      this.setPC(expr);
      return StepResult.SET;
    } else if (this.pc() === expr) {
      this.pushOp(this.frame().lookup(expr.name));
      this.clearPC();
      return StepResult.DONE;
    } else {
      return StepResult.NOP;
    }
  }

  visitLiteral (expr: Syntax.Literal): StepResult {
    if (this.seeking()) {
      this.setPC(expr);
      return StepResult.SET;
    } else if (this.pc() === expr) {
      this.pushOp(expr.value);
      this.clearPC();
      return StepResult.DONE;
    } else {
      return StepResult.NOP;
    }
  }

  visitUnaryExpression (expr: Syntax.UnaryExpression): StepResult {
    if (this.seeking()) {
      return this.visitExpression(expr.argument);
    } else if (this.pc() === expr) {
      const arg = this.popOp();
      switch (expr.operator) {
        case '-':
          this.pushOp(-arg);
          break;
        case '+':
          this.pushOp(+arg);
          break;
        case '!':
          this.pushOp(!arg);
          break;
        case '~':
          this.pushOp(~arg);
          break;
        case 'typeof':
          this.pushOp(typeof arg);
          break;
        case 'void':
          this.pushOp(void(0));
          break;
      }
      this.clearPC();
      return StepResult.DONE;
    } else {
      const argRes = this.visitExpression(expr.argument);
      if (argRes === StepResult.DONE) {
        this.setPC(expr);
        return StepResult.STEP;
      } else {
        return argRes;
      }
    }
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): StepResult {
    if (this.seeking()) {
      return this.visitExpression(expr.left);
    } else if (this.pc() === expr) {
      const rightArg = this.popOp();
      const leftArg = this.popOp();
      switch (expr.operator) {
        case '===':
          this.pushOp(leftArg === rightArg);
          break;
        case '!==':
          this.pushOp(leftArg !== rightArg);
          break;
        case '<':
          this.pushOp(leftArg < rightArg);
          break;
        case '<=':
          this.pushOp(leftArg <= rightArg);
          break;
        case '>':
          this.pushOp(leftArg > rightArg);
          break;
        case '>=':
          this.pushOp(leftArg >= rightArg);
          break;
        case '<<':
          this.pushOp(leftArg << rightArg);
          break;
        case '>>':
          this.pushOp(leftArg >> rightArg);
          break;
        case '>>>':
          this.pushOp(leftArg >>> rightArg);
          break;
        case '+':
          this.pushOp(leftArg + rightArg);
          break;
        case '-':
          this.pushOp(leftArg - rightArg);
          break;
        case '*':
          this.pushOp(leftArg * rightArg);
          break;
        case '/':
          this.pushOp(leftArg / rightArg);
          break;
        case '%':
          this.pushOp(leftArg % rightArg);
          break;
        case '|':
          this.pushOp(leftArg | rightArg);
          break;
        case '^':
          this.pushOp(leftArg ^ rightArg);
          break;
        case '&':
          this.pushOp(leftArg & rightArg);
          break;
      }
      this.clearPC();
      return StepResult.DONE;
    } else {
      const leftRes = this.visitExpression(expr.left);
      if (leftRes === StepResult.NOP) {
        const rightRes = this.visitExpression(expr.right);
        if (rightRes === StepResult.DONE) {
          this.setPC(expr);
          return StepResult.STEP;
        } else {
          return rightRes;
        }
      } else if (leftRes === StepResult.STEP) {
        return StepResult.STEP;
      } else {
        this.visitExpression(expr.right);
        return StepResult.STEP;
      }
    }
  }

  visitLogicalExpression (expr: Syntax.LogicalExpression): StepResult {
    if (this.seeking()) {
      return this.visitExpression(expr.left);
    } else {
      const leftRes = this.visitExpression(expr.left);
      if (leftRes === StepResult.NOP) {
        const rightRes = this.visitExpression(expr.right);
        if (rightRes === StepResult.DONE) {
          return StepResult.DONE;
        } else {
          return rightRes;
        }
      } else if (leftRes === StepResult.STEP) {
        return StepResult.STEP;
      } else {
        const leftArg = this.popOp();
        if (expr.operator === '&&') {
          if (leftArg) {
            this.visitExpression(expr.right);
            return StepResult.STEP;
          } else {
            this.pushOp(leftArg);
            return StepResult.DONE;
          }
        } else {
          if (leftArg) {
            this.pushOp(leftArg);
            return StepResult.DONE;
          } else {
            this.visitExpression(expr.right);
            return StepResult.STEP;
          }
        }
      }
    }
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): StepResult {
    if (this.seeking()) {
      return this.visitExpression(expr.test);
    } else {
      const testRes = this.visitExpression(expr.test);
      if (testRes === StepResult.NOP) {
        const consequentRes = this.visitExpression(expr.consequent);
        if (consequentRes === StepResult.NOP) {
          return this.visitExpression(expr.alternate);
        } else {
          return consequentRes;
        }
      } else if (testRes === StepResult.STEP) {
        return StepResult.STEP;
      } else { // testRes === DONE
        const testArg = this.popOp();
        if (testArg) {
          this.visitExpression(expr.consequent);
          return StepResult.STEP;
        } else {
          this.visitExpression(expr.alternate);
          return StepResult.STEP;
        }
      }
    }
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression): StepResult {
    if (expr.left.type === 'Identifier') {
      if (this.seeking()) {
        return this.visitExpression(expr.right);
      } else {
        if (this.pc() === expr) {
          const rightArg = this.popOp();
          this.frame().assign(expr.left.name, rightArg);
          this.pushOp(rightArg);
          this.clearPC();
          return StepResult.DONE;
        } else {
          const rightRes = this.visitExpression(expr.right);
          if (rightRes === StepResult.DONE) {
            this.setPC(expr);
            return StepResult.STEP;
          } else {
            return rightRes;
          }
        }
      }
    } else {
      if (this.seeking()) {
        return this.visitExpression(expr.left.object);
      } else {
        if (this.pc() === expr) {
          const rightArg = this.popOp();
          const propertyArg = this.popOp();
          const objectArg = this.popOp();
          objectArg[propertyArg] = rightArg;
          this.pushOp(rightArg);
          this.clearPC();
          return StepResult.DONE;
        } else {
          const objectRes = this.visitExpression(expr.left.object);
          if (objectRes === StepResult.NOP) {
            const propertyRes = this.visitExpression(expr.left.property);
            if (propertyRes === StepResult.NOP) {
              const rightRes = this.visitExpression(expr.right);
              if (rightRes === StepResult.DONE) {
                this.setPC(expr);
                return StepResult.STEP;
              } else {
                return rightRes;
              }
            } else if (propertyRes === StepResult.STEP) {
              return StepResult.STEP;
            } else {
              this.visitExpression(expr.right);
              return StepResult.STEP;
            }
          } else if (objectRes === StepResult.STEP) {
            return StepResult.STEP;
          } else {
            this.visitExpression(expr.left.property);
            return StepResult.STEP;
          }
        }
      }
    }
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression): StepResult {
    if (expr.expressions.length < 1) throw new Error('empty SequenceExpression');
    if (this.seeking()) {
      return this.visitExpression(expr.expressions[0]);
    } else {
      for (let i = 0; i < expr.expressions.length; i++) {
        const res = this.visitExpression(expr.expressions[i]);
        if (res === StepResult.STEP) {
          return StepResult.STEP;
        } else if (res === StepResult.DONE) {
          if (i < expr.expressions.length - 1) {
            this.popOp();
            this.visitExpression(expr.expressions[i + 1]);
            return StepResult.STEP;
          } else {
            return StepResult.DONE;
          }
        }
      }
      return StepResult.NOP;
    }
  }

  visitMethodCallExpression (expr: MethodCallExpression): StepResult {
    if (this.seeking()) {
      return this.visitExpression(expr.callee.object);
    } else if (this.pc() === expr) {
      this.clearPC();
      return StepResult.DONE;
    } else {
      const objectRes = this.visitExpression(expr.callee.object);
      if (objectRes === StepResult.STEP) {
        return StepResult.STEP;
      } else if (objectRes === StepResult.DONE) {
        this.visitExpression(expr.callee.property);
        return StepResult.STEP;
      } else { // objectRes is NOP
        const propertyRes = this.visitExpression(expr.callee.property);
        if (propertyRes === StepResult.STEP) {
          return StepResult.STEP;
        } else if (propertyRes === StepResult.DONE) {
          if (expr.args.length > 0) {
            this.visitExpression(expr.args[0]);
          } else {
            this.setPC(expr);
            const prop = this.popOp();
            const object = this.popOp();
            this.call(object[prop], object, []);
          }
          return StepResult.STEP;
        } else { // propertyRes is NOP
          for (let i = 0; i < expr.args.length; i++) {
            const argRes = this.visitExpression(expr.args[i]);
            if (argRes === StepResult.STEP) {
              return StepResult.STEP;
            } else if (argRes === StepResult.DONE) {
              if (i < expr.args.length - 1) {
                this.visitExpression(expr.args[i + 1]);
              } else {
                this.setPC(expr);
                const args = [];
                for (let i = 0; i < expr.args.length; i++) {
                  args.unshift(this.popOp());
                }
                const prop = this.popOp();
                const object = this.popOp();
                this.call(object[prop], object, args);
              }
              return StepResult.STEP;
            }
          }
          return StepResult.NOP;
        }
      }
    }
  }

  visitCallExpression (expr: Syntax.CallExpression): StepResult {
    if (isMethodCall(expr)) {
      return this.visitMethodCallExpression(expr);
    } else if (this.seeking()) {
      return this.visitExpression(expr.callee);
    } else if (this.pc() === expr) {
      this.clearPC();
      return StepResult.DONE;
    } else {
      const calleeRes = this.visitExpression(expr.callee);
      if (calleeRes === StepResult.STEP) {
        return StepResult.STEP;
      } else if (calleeRes === StepResult.DONE) {
        if (expr.args.length > 0) {
          this.visitExpression(expr.args[0]);
        } else {
          this.setPC(expr);
          this.call(this.popOp(), undefined, []);
        }
        return StepResult.STEP;
      } else { // calleeRes is NOP
        for (let i = 0; i < expr.args.length; i++) {
          const argRes = this.visitExpression(expr.args[i]);
          if (argRes === StepResult.STEP) {
            return StepResult.STEP;
          } else if (argRes === StepResult.DONE) {
            if (i < expr.args.length - 1) {
              this.visitExpression(expr.args[i + 1]);
            } else {
              this.setPC(expr);
              const args = [];
              for (let i = 0; i < expr.args.length; i++) {
                args.unshift(this.popOp());
              }
              this.call(this.popOp(), undefined, args);
            }
            return StepResult.STEP;
          }
        }
        return StepResult.NOP;
      }
    }
  }

  visitNewExpression (expr: Syntax.NewExpression): StepResult {
    if (this.seeking()) {
      return this.visitExpression(expr.callee);
    } else if (this.pc() === expr) {
      const args = [];
      for (let i = 0; i < expr.args.length; i++) {
        args.unshift(this.popOp());
      }
      const constr = this.popOp();
      const instance = new constr(...args);
      instance._cls_ = [constr.name, ...args];
      this.pushOp(instance);
      this.clearPC();
      return StepResult.DONE;
    } else {
      const calleeRes = this.visitExpression(expr.callee);
      if (calleeRes === StepResult.STEP) {
        return StepResult.STEP;
      } else if (calleeRes === StepResult.DONE) {
        if (expr.args.length > 0) {
          this.visitExpression(expr.args[0]);
        } else {
          this.setPC(expr);
        }
        return StepResult.STEP;
      } else { // calleeRes is NOP
        for (let i = 0; i < expr.args.length; i++) {
          const argRes = this.visitExpression(expr.args[i]);
          if (argRes === StepResult.STEP) {
            return StepResult.STEP;
          } else if (argRes === StepResult.DONE) {
            if (i < expr.args.length - 1) {
              this.visitExpression(expr.args[i + 1]);
            } else {
              this.setPC(expr);
            }
            return StepResult.STEP;
          }
        }
        return StepResult.NOP;
      }
    }
  }

  visitArrayExpression (expr: Syntax.ArrayExpression): StepResult {
    if (this.seeking()) {
      if (expr.elements.length > 0) {
        return this.visitExpression(expr.elements[0]);
      } else {
        this.setPC(expr);
        return StepResult.SET;
      }
    } else if (this.pc() === expr) {
      const array = [];
      for (let i = 0; i < expr.elements.length; i++) {
        array.unshift(this.popOp());
      }
      this.pushOp(array);
      this.clearPC();
      return StepResult.DONE;
    } else {
      for (let i = 0; i < expr.elements.length; i++) {
        const elementRes = this.visitExpression(expr.elements[i]);
        if (elementRes === StepResult.STEP) {
          return StepResult.STEP;
        } else if (elementRes === StepResult.DONE) {
          if (i < expr.elements.length - 1) {
            this.visitExpression(expr.elements[i + 1]);
          } else {
            this.setPC(expr);
          }
          return StepResult.STEP;
        }
      }
      return StepResult.NOP;
    }
  }

  visitObjectExpression (expr: Syntax.ObjectExpression): StepResult {
    if (this.seeking()) {
      if (expr.properties.length > 0) {
        return this.visitExpression(expr.properties[0].value);
      } else {
        this.setPC(expr);
        return StepResult.SET;
      }
    } else if (this.pc() === expr) {
      const object: { [key: string]: any } = {};
      const propValues = [];
      for (let i = 0; i < expr.properties.length; i++) {
        propValues.unshift(this.popOp());
      }
      for (let i = 0; i < expr.properties.length; i++) {
        const { key } = expr.properties[i];
        object[key] = propValues[i];
      }
      this.pushOp(object);
      this.clearPC();
      return StepResult.DONE;
    } else {
      for (let i = 0; i < expr.properties.length; i++) {
        const elementRes = this.visitExpression(expr.properties[i].value);
        if (elementRes === StepResult.STEP) {
          return StepResult.STEP;
        } else if (elementRes === StepResult.DONE) {
          if (i < expr.properties.length - 1) {
            this.visitExpression(expr.properties[i + 1].value);
          } else {
            this.setPC(expr);
          }
          return StepResult.STEP;
        }
      }
      return StepResult.NOP;
    }
  }

  visitInstanceOfExpression (expr: Syntax.InstanceOfExpression): StepResult {
    if (this.seeking()) {
      return this.visitExpression(expr.left);
    } else if (this.pc() === expr) {
      const rightArg = this.popOp();
      const leftArg = this.popOp();
      this.pushOp(leftArg instanceof rightArg);
      this.clearPC();
      return StepResult.DONE;
    } else {
      const leftRes = this.visitExpression(expr.left);
      if (leftRes === StepResult.NOP) {
        const rightRes = this.visitExpression(expr.right);
        if (rightRes === StepResult.DONE) {
          this.setPC(expr);
          return StepResult.STEP;
        } else {
          return rightRes;
        }
      } else if (leftRes === StepResult.STEP) {
        return StepResult.STEP;
      } else { // leftRes === DONE
        this.visitExpression(expr.right);
        return StepResult.STEP;
      }
    }
  }

  visitInExpression (expr: Syntax.InExpression): StepResult {
    if (this.seeking()) {
      return this.visitExpression(expr.property);
    } else if (this.pc() === expr) {
      const objArg = this.popOp();
      const propArg = this.popOp();
      this.pushOp(propArg in objArg);
      this.clearPC();
      return StepResult.DONE;
    } else {
      const propRes = this.visitExpression(expr.property);
      if (propRes === StepResult.NOP) {
        const objRes = this.visitExpression(expr.object);
        if (objRes === StepResult.DONE) {
          this.setPC(expr);
          return StepResult.STEP;
        } else {
          return objRes;
        }
      } else if (propRes === StepResult.STEP) {
        return StepResult.STEP;
      } else { // propRes === DONE
        this.visitExpression(expr.object);
        return StepResult.STEP;
      }
    }
  }

  visitMemberExpression (expr: Syntax.MemberExpression): StepResult {
    if (this.seeking()) {
      return this.visitExpression(expr.object);
    } else if (this.pc() === expr) {
      const propArg = this.popOp();
      const objArg = this.popOp();
      this.pushOp(objArg[propArg]);
      this.clearPC();
      return StepResult.DONE;
    } else {
      const objRes = this.visitExpression(expr.object);
      if (objRes === StepResult.NOP) {
        const propRes = this.visitExpression(expr.property);
        if (propRes === StepResult.DONE) {
          this.setPC(expr);
          return StepResult.STEP;
        } else {
          return propRes;
        }
      } else if (objRes === StepResult.STEP) {
        return StepResult.STEP;
      } else { // objRes === DONE
        this.visitExpression(expr.property);
        return StepResult.STEP;
      }
    }
  }

  visitFunctionExpression (expr: Syntax.FunctionExpression): StepResult {
    if (this.seeking()) {
      this.setPC(expr);
      return StepResult.SET;
    } else if (this.pc() === expr) {
      this.pushOp(this.closure(expr));
      this.clearPC();
      return StepResult.DONE;
    } else {
      return StepResult.NOP;
    }
  }

  visitVariableDeclaration (stmt: Syntax.VariableDeclaration): StepResult {
    if (this.seeking()) {
      return this.visitExpression(stmt.init);
    } else if (this.pc() === stmt) {
      const val = this.popOp();
      this.frame().define(stmt.id.name, val, stmt.kind);
      if (stmt.id.name.startsWith('old_')) {
        this.annotate(stmt.id.loc, stmt.id.name.substr(4), val);
      }
      this.clearPC();
      return StepResult.DONE;
    } else {
      const initRes = this.visitExpression(stmt.init);
      if (initRes === StepResult.DONE) {
        this.setPC(stmt);
        return StepResult.STEP;
      } else {
        return initRes;
      }
    }
  }

  visitBlockStatement (stmt: Syntax.BlockStatement): StepResult {
    if (this.seeking()) {
      for (const substmt of stmt.body) {
        const res = this.visitStatement(substmt);
        if (res === StepResult.SET) {
          this.frame().newBlockScope();
          return StepResult.SET;
        }
      }
      return StepResult.NOP;
    } else {
      for (let i = 0; i < stmt.body.length; i++) {
        const res = this.visitStatement(stmt.body[i]);
        if (res === StepResult.STEP) {
          return StepResult.STEP;
        } else if (res === StepResult.DONE) {
          for (let j = i + 1; j < stmt.body.length; j++) {
            const res = this.visitStatement(stmt.body[j]);
            if (res === StepResult.SET) {
              return StepResult.STEP;
            }
          }
          this.frame().popBlockScope();
          return StepResult.DONE;
        }
      }
      return StepResult.NOP;
    }
  }

  visitExpressionStatement (stmt: Syntax.ExpressionStatement): StepResult {
    if (this.seeking()) {
      return this.visitExpression(stmt.expression);
    } else {
      const res = this.visitExpression(stmt.expression);
      if (res === StepResult.DONE) this.popOp();
      return res;
    }
  }

  visitAssertStatement (stmt: Syntax.AssertStatement): StepResult {
    return StepResult.NOP;
  }

  visitIfStatement (stmt: Syntax.IfStatement): StepResult {
    if (this.seeking()) {
      return this.visitExpression(stmt.test);
    } else {
      const testRes = this.visitExpression(stmt.test);
      if (testRes === StepResult.NOP) {
        const consequentRes = this.visitStatement(stmt.consequent);
        if (consequentRes === StepResult.NOP) {
          return this.visitStatement(stmt.alternate);
        } else { // STEP or DONE
          return consequentRes;
        }
      } else if (testRes === StepResult.STEP) {
        return StepResult.STEP;
      } else { // testRes === DONE
        const testArg = this.popOp();
        if (testArg) {
          const consequentRes = this.visitStatement(stmt.consequent);
          return consequentRes === StepResult.SET ? StepResult.STEP : StepResult.DONE;
        } else {
          const alternateRes = this.visitStatement(stmt.alternate);
          return alternateRes === StepResult.SET ? StepResult.STEP : StepResult.DONE;
        }
      }
    }
  }

  visitReturnStatement (stmt: Syntax.ReturnStatement): StepResult {
    if (this.seeking()) {
      return this.visitExpression(stmt.argument);
    } else if (this.pc() === stmt) {
      const retValue = this.popOp();
      this.ret(retValue);
      return StepResult.STEP;
    } else {
      const initRes = this.visitExpression(stmt.argument);
      if (initRes === StepResult.DONE) {
        this.setPC(stmt);
        return StepResult.STEP;
      } else {
        return initRes;
      }
    }
  }

  visitWhileStatement (stmt: Syntax.WhileStatement): StepResult {
    if (this.seeking()) {
      return this.visitExpression(stmt.test);
    } else {
      const testRes = this.visitExpression(stmt.test);
      if (testRes === StepResult.NOP) {
        const bodyRes = this.visitStatement(stmt.body);
        if (bodyRes === StepResult.DONE) {
          this.frame().nextIteration();
          this.visitExpression(stmt.test);
          return StepResult.STEP;
        } else { // NOP or STEP
          return bodyRes;
        }
      } else if (testRes === StepResult.STEP) {
        return StepResult.STEP;
      } else { // testRes === DONE
        const testArg = this.popOp();
        if (testArg) {
          const bodyRes = this.visitStatement(stmt.body);
          if (bodyRes !== StepResult.SET) {
            this.frame().nextIteration();
            this.visitExpression(stmt.test);
          }
          return StepResult.STEP;
        } else {
          return StepResult.DONE;
        }
      }
    }
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement): StepResult {
    return StepResult.NOP;
  }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration): StepResult {
    if (this.seeking()) {
      this.setPC(stmt);
      return StepResult.SET;
    } else if (this.pc() === stmt) {
      this.frame().define(stmt.id.name, this.closure(stmt), 'let');
      this.clearPC();
      return StepResult.DONE;
    } else {
      return StepResult.NOP;
    }
  }

  visitClassDeclaration (stmt: Syntax.ClassDeclaration): StepResult {
    if (this.seeking()) {
      this.setPC(stmt);
      return StepResult.SET;
    } else if (this.pc() === stmt) {
      /* tslint:disable:no-eval */
      const constr = eval(`(() => function ${stmt.id.name} (${stmt.fields.join(', ')}) {
${stmt.fields.map(f => `  this.${f} = ${f};\n`).join('')}
})()`);
      stmt.methods.forEach(method => {
        constr.prototype[method.id.name] = this.closure(method);
      });
      this.frame().define(stmt.id.name, constr, 'let');
      this.clearPC();
      return StepResult.DONE;
    } else {
      return StepResult.NOP;
    }
  }

  visitProgram (prog: Syntax.Program): StepResult {
    if (this.seeking()) {
      for (const substmt of prog.body) {
        const res = this.visitStatement(substmt);
        if (res === StepResult.SET) {
          return StepResult.SET;
        }
      }
      return StepResult.NOP;
    } else {
      for (let i = 0; i < prog.body.length; i++) {
        const res = this.visitStatement(prog.body[i]);
        if (res === StepResult.STEP) {
          return StepResult.STEP;
        } else if (res === StepResult.DONE) {
          for (let j = i + 1; j < prog.body.length; j++) {
            const res = this.visitStatement(prog.body[j]);
            if (res === StepResult.SET) {
              return StepResult.STEP;
            }
          }
          return StepResult.DONE;
        }
      }
      return StepResult.NOP;
    }
  }

  // --- Stepping Methods ---

  reset (): void {
    this.steps = 0;
    this.annotations = [];
    this.stack = [new ProgramStackFrame(this.program)];
    this.breakpoint = null;
    this.visitProgram(this.program);
  }

  step (): StepResult {
    const frame = this.frame();
    if (this.steps >= getOptions().maxInterpreterSteps) {
      return StepResult.DONE;
    }
    try {
      return frame.entry(this);
    } catch (e) {
      e.stack = `${e.constructor.name}: ${e.message}`;
      for (let i = this.stack.length - 1; i >= 0; i--) {
        e.stack += `\n    at ${this.stack[i].toString()}`;
      }
      throw e;
    } finally {
      this.steps++;
    }
  }

  isBreaking (): boolean {
    return this.breakpoint !== null &&
           eqSourceLocation(this.breakpoint[0], this.loc()) &&
           this.breakpoint[1] === this.iteration();
  }

  stepInto (): void {
    this.step();
  }

  stepOver (): void {
    const origStackHeight = this.stack.length;
    do {
      this.stepInto();
      if (this.isBreaking()) return;
    } while (this.stack.length > origStackHeight);
  }

  stepOut (): any { // returns stack frame return value (does not stop at breakpoints)
    const origStackHeight = this.stack.length;
    do {
      this.stepInto();
    } while (this.stack.length >= origStackHeight);
    const retVal = this.popOp();
    this.pushOp(retVal);
    return retVal;
  }

  run (): void {
    while (true) {
      const res = this.step();
      if (this.isBreaking()) return;
      if (this.stack.length === 1 && res === StepResult.DONE) return;
    }
  }
}

export function interpret (program: Syntax.Program): Interpreter {
  return new InterpreterVisitor(program);
}
