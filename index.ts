import { parse } from 'lively.ast';

import { programAsJavaScript } from "./src/javascript";
import { findScopes } from './src/visitors';
import Theorem from "./src/theorems";

export type JSSource = string;
export type SMTInput = string;
export type SMTOutput = string;


export type VarName = string;
export type Vars = { [varName: string]: number; };  // latest assigned value

export default function theoremsInSource(src: JSSource): Array<Theorem> | null {
  try {
    const ast = parse(src),
          prog = programAsJavaScript(ast),
          topLevel = findScopes(ast);
    return topLevel.theorems();
  } catch (e) {
    console.error(e);
    return null;
  }
}
