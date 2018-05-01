import { VCGenerator } from './vcgen';
import { Classes, Heap, Locs, Vars, P, tru, copy, A } from './logic';
import { Syntax, TestCode, nullLoc, id } from './javascript';
import { parseScript } from 'esprima';
import { programAsJavaScript } from './parser';
import { resolveNames } from './scopes';

export type GlobalDeclaration = { type: 'Var', decl: Syntax.VariableDeclaration }
                              | { type: 'Func', decl: Syntax.FunctionDeclaration }
                              | { type: 'Class', decl: Syntax.ClassDeclaration };

export type Preamble = { classes: Classes, heap: Heap, locs: Locs, vars: Vars, prop: P };

function builtinClass (name: string): GlobalDeclaration {
  return {
    type: 'Class',
    decl: {
      type: 'ClassDeclaration',
      id: id(name),
      fields: [],
      invariant: { type: 'Literal', value: true, loc: nullLoc() },
      methods: [],
      loc: nullLoc()
    }
  };
}

function constVar (name: string): GlobalDeclaration {
  return {
    type: 'Var',
    decl: {
      type: 'VariableDeclaration',
      id: id(name),
      init: { type: 'Literal', value: undefined, loc: nullLoc() },
      kind: 'const',
      loc: nullLoc()
    }
  };
}

let cachedGlobalDeclarations: Array<GlobalDeclaration> | null = null;

export function globalDeclarations (): Array<GlobalDeclaration> {
  if (cachedGlobalDeclarations === null) {
    cachedGlobalDeclarations = [
      builtinClass('Object'),
      builtinClass('Function'),
      builtinClass('Array'),
      builtinClass('String'),
      constVar('console')
    ];
  }
  return cachedGlobalDeclarations;
}

class PreambleGenrator extends VCGenerator {

  verify (vc: P, testBody: TestCode, loc: Syntax.SourceLocation, desc: string) {
    /* only generate preamble, do not verify */
  }

  createFunctionBodyInliner () {
    return new PreambleGenrator(this.classes,
                                this.heap + 1,
                                this.heap + 1,
                                new Set([...this.locs]),
                                new Set([...this.vars]),
                                this.prop);
  }

  visitArrayExpression (expr: Syntax.ArrayExpression): [A, Syntax.Expression] {
    if (expr.elements.length >= 2) {
      const tag = expr.elements[0];
      if (tag.type === 'Literal' && tag.value === '_builtin_') {
        const smt: Array<string | { e: A }> = [];
        for (const element of expr.elements.slice(1)) {
          if (element.type === 'Literal' && typeof element.value === 'string') {
            smt.push(element.value);
          } else {
            const [elementA] = this.visitExpression(element);
            smt.push({ e: elementA });
          }
        }
        return [{ type: 'RawSMTExpression', smt }, expr];
      }
    }
    return super.visitArrayExpression(expr);
  }
}

let cachedPreamble: Preamble | null = null;

export function generatePreamble (): Preamble {
  if (cachedPreamble === null) {
    let preambleSource = preamble.toString();
    preambleSource = preambleSource.substring(72, preambleSource.length - 2); // extract body from function
    let preambleProgram: Syntax.Program = programAsJavaScript(parseScript(preambleSource, { loc: true }));
    resolveNames(preambleProgram, false);
    const vcgen = new PreambleGenrator(new Set(), 0, 0, new Set(), new Set(), tru);
    vcgen.visitProgram(preambleProgram);
    const { classes, heap, locs, vars, prop } = vcgen;
    cachedPreamble = { classes, heap, locs, vars, prop };
  }
  return {
    classes: new Set([...cachedPreamble.classes]),
    heap: cachedPreamble.heap,
    locs: new Set([...cachedPreamble.locs]),
    vars: new Set([...cachedPreamble.vars]),
    prop: copy(cachedPreamble.prop)
  };
}

// --- javascript preamble ---

declare const requires: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const every: (a: Array<any>, b: ((x: any) => boolean) | ((x: any, y: any) => boolean)) => boolean;
declare const pure: () => boolean;

function preamble () {
  /* tslint:disable:no-unused-expression */
  /* tslint:disable:variable-name */

  class Console {
    log (arg: any) {
      ensures(y => pure() && y === undefined);
    }
  }
  // @ts-ignore: variable only initialized, never read
  const console = new Console();

    // @ts-ignore: class never used
  class Array {

    // @ts-ignore: not assigned in constructors
    length: number;

    invariant () {
      return this.length >= 0;
    }

    slice (from: number, to: number) {
      requires(typeof from === 'number');
      requires(typeof to === 'number');
      requires(from >= 0);
      requires(from < this.length);
      requires(to >= from);
      requires(to < this.length);

      // @ts-ignore: indexing this
      ensures(y => every(y, (ele, idx) => ele === this[idx + from]));
      ensures(y => y.length === to - from);
      ensures(pure());
    }

  }

  // @ts-ignore: class never used
  class String {

    _str_: string;
    // @ts-ignore: not assigned in constructors
    length: number;

    constructor (_str_: string) {
      this._str_ = _str_;
    }

    invariant () {
      return typeof this === 'string' || typeof this._str_ === 'string';
    }

    substr (from: number, len: number) {
      requires(typeof from === 'number');
      requires(typeof len === 'number');
      requires(from >= 0);
      requires(len >= 0);

      ensures(pure());

      return [
        '_builtin_',
        '(jsstr (str.substr (strv (ite (is-jsstr ', this, ') ', this, ' (String-_str_ ', this, '))) ',
        '(numv ', from, ') (numv ', len, ')))'];
    }

    substring (from: number, to: number) {
      requires(typeof from === 'number');
      requires(typeof to === 'number');
      requires(from >= 0);
      requires(from < this.length);
      requires(to >= from);
      requires(to < this.length);

      ensures(pure());

      return [
        '_builtin_',
        '(jsstr (str.substr (strv (ite (is-jsstr ', this, ') ', this, ' (String-_str_ ', this, '))) ',
        '(numv ', from, ') (numv ', to - from, ')))'];
    }
  }
}
