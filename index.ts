import { parse } from 'lively.ast';

import { findScopes } from './src/visitors';
import Theorem from "./src/theorems";

export type JSSource = string;
export type SMTInput = string;
export type SMTOutput = string;

interface Identifier { type: "Identifier"; name: string; }
interface Literal { type: "Literal";
                    value: undefined | null | boolean | number | string; }
interface ArrayExpression { type: "ArrayExpression";
                            elements: Array<AExpression>; }
interface UnaryExpression { type: "UnaryExpression";
                            operator: "+" | "-";
                            argument: AExpression; }
interface BinaryExpression { type: "BinaryExpression";
                             operator: "=";
                             left: AExpression;
                             right: AExpression; }
interface ConditionalExpression { type: "ConditionalExpression";
                                  test: AExpression;
                                  consequent: AExpression;
                                  alternate: AExpression; }
interface CallExpression { type: "CallExpression";
                           callee: Identifier;
                           arguments: Array<Identifier>; }
export type AExpression = Identifier
                        | Literal
                        | ArrayExpression
                        | UnaryExpression
                        | BinaryExpression
                        | ConditionalExpression
                        | CallExpression;

export type VarName = string;
export type Vars = { [varName: string]: number; };  // latest assigned value

export default function theoremsInSource(src: JSSource): Array<Theorem> | null {
  try {
    const ast = parse(src),
          topLevel = findScopes(ast);
    return topLevel.theorems();
  } catch (e) {
    console.error(e);
    return null;
  }
}
