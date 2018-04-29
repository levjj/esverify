import { VCGenerator } from './vcgen';
import { Classes, Heap, Locs, Vars, P, tru, copy } from './logic';
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
      constVar('console')
    ];
  }
  return cachedGlobalDeclarations;
}

class PreambleGenrator extends VCGenerator {
  verify (vc: P, testBody: TestCode, loc: Syntax.SourceLocation, desc: string) {
    /* only generate preamble, do not verify */
  }

  visitFunctionBody (f: Syntax.Function, funcName: string, thisArg: string): [P, Syntax.BlockStatement] {
    return [tru, { type: 'BlockStatement', body: [], loc: nullLoc() }];
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

declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
function preamble () {
  /* tslint:disable:no-unused-expression */

  class Console {
    log (arg: any) {
      ensures(y => y === undefined);
    }
  }
  // @ts-ignore: variable only initialized, never read
  const console = new Console();
}
