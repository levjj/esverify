import { parse } from "esprima";
import * as Syntax from "estree";
import { Message, MessageException, err, consoleLog } from "./src/message";
import { programAsJavaScript } from "./src/javascript";
import VerificationCondition from "./src/verification";
import { vcgenProgram } from "./src/vcgen";
import { Options, options, setOptions } from "./src/options";

export function verificationConditions(src: string, opts: Partial<Options> = {}): Message | Array<VerificationCondition> {
  setOptions(opts);
  let node: Syntax.Program;
  try {
    node = parse(src, { loc: true });
  } catch(e) {
    const line: number = e.lineNumber || 0;
    const column: number = 0;
    const loc = { file: options.filename, start: { line, column }, end: { line, column: column + 1 }};
    return { status: "parse-error", loc, msg: e.description || "parse error" };
  }
  try {
    const prog = programAsJavaScript(node);
    return vcgenProgram(prog);
  } catch (e) {
    return e instanceof MessageException ? e.msg : err(e);
  }
}

export async function verify(src: string, opts: Partial<Options> = {}): Promise<Array<Message>> {
  const vcs = verificationConditions(src, opts);
  if (!(vcs instanceof Array)) {
    if (options.logMessages) consoleLog(vcs);
    return [vcs];
  }
  const res: Array<Message> = [];
  for (const vc of vcs) {
    let m: Message;
    try {
      m = await vc.verify();
    } catch (e) {
      m = e instanceof MessageException ? e.msg : err(e);
    }
    if (options.logMessages) consoleLog(m);
    res.push(m);
  }
  return res;
}
