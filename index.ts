/* global console */
import { parse } from "esprima";
import { Syntax } from "spiderMonkeyParserAPI";
import { programAsJavaScript } from "./src/javascript";
import VerificationCondition from "./src/verification";
import { transformProgram } from "./src/vcgen";

declare const console: { error: any };

export function verifyAST(node: Syntax.Program): Array<VerificationCondition> | null {
  try {
    const prog = programAsJavaScript(node);
    return transformProgram(prog);
  } catch (e) {
    console.error(e);
    return null;
  }
}

export function verify(src: string): Array<VerificationCondition> | null {
  return verifyAST(parse(src));
}
