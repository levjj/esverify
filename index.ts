import { parseScript } from 'esprima';
import * as Syntax from 'estree';
import { Message, MessageException, unexpected, log } from './src/message';
import { programAsJavaScript } from './src/javascript';
import VerificationCondition from './src/verification';
import { vcgenProgram } from './src/vcgen';
import { Options, options, setOptions } from './src/options';

export function verificationConditions (src: string, opts: Partial<Options> = {}): Message | Array<VerificationCondition> {
  setOptions(opts);
  let node: Syntax.Program;
  try {
    node = parseScript(src, { loc: true });
  } catch (e) {
    const line: number = e.lineNumber || 0;
    const column: number = 0;
    const loc = { file: options.filename, start: { line, column }, end: { line, column: column + 1 }};
    return { status: 'error', type: 'parse-error', loc, description: e.description || 'parse error' };
  }
  try {
    const prog = programAsJavaScript(node);
    const vcs = vcgenProgram(prog);
    return vcs;
  } catch (e) {
    return e instanceof MessageException ? e.msg : unexpected(e);
  }
}

export async function verify (src: string, opts: Partial<Options> = {}): Promise<Array<Message>> {
  const vcs = verificationConditions(src, opts);
  if (!(vcs instanceof Array)) {
    if (!options.quiet) log(vcs);
    return [vcs];
  }
  const res: Array<Message> = [];
  for (const vc of vcs) {
    let m: Message;
    try {
      m = await vc.verify();
    } catch (e) {
      m = e instanceof MessageException ? e.msg : unexpected(e);
    }
    if (!options.quiet) log(m);
    res.push(m);
  }
  return res;
}
