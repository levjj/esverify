declare const console: { log: (s: string) => void, warn: (s: string) => void, error: (s: string) => void };

import { Model } from "./smt";
import { Syntax } from "./javascript";
import { options } from "./options";

interface ParseError { status: "parse-error", loc: Syntax.SourceLocation, msg: string }
interface Unsupported { status: "unsupported", loc: Syntax.SourceLocation }
interface UndefinedIdentifier { status: "undefined-identifier", loc: Syntax.SourceLocation }
interface AlreadyDefinedIdentifier { status: "already-defined", loc: Syntax.SourceLocation }
interface AssignmentToConst { status: "assignment-to-const", loc: Syntax.SourceLocation }
interface Verified { status: "verified", loc: Syntax.SourceLocation, description: string }
interface Incorrect { status: "incorrect", loc: Syntax.SourceLocation, description: string, model: Model, error: Error }
interface Unverified { status: "unverified", loc: Syntax.SourceLocation, description: string, model: Model }
interface ModelError { status: "unrecognized-model", loc: Syntax.SourceLocation, smt: string }
interface UnknownError { status: "error", loc: Syntax.SourceLocation, error: Error }
export type Message = ParseError | Unsupported | UndefinedIdentifier | Verified | Incorrect | Unverified | UnknownError
                    | AlreadyDefinedIdentifier | AssignmentToConst | ModelError;

function shortDescription(msg: Message): string {
  let m = msg.status;
  if (msg.status == "verified" || msg.status == "unverified" || msg.status == "incorrect") m += " " + msg.description;
  return `[${msg.loc.file}:${msg.loc.start.line}:${msg.loc.start.column}] ${m}`;
}

type Level = "bad" | "unknown" | "good";

function messageLevel(msg: Message): Level {
  switch (msg.status) {
    case "parse-error": return "bad";
    case "unsupported": return "bad";
    case "undefined-identifier": return "bad";
    case "already-defined": return "bad";
    case "assignment-to-const": return "bad";
    case "verified": return "good";
    case "incorrect": return "bad";
    case "unverified": return "unknown";
    case "unrecognized-model": return "bad";
    case "error": return "bad";
  }
}

export function consoleLog(msg: Message): void {
  const loc = `[${msg.loc.file}:${msg.loc.start.line}:${msg.loc.start.column}] `;
  let m = '';
  if (msg.status == "verified" || msg.status == "unverified" || msg.status == "incorrect") m = msg.description;
  const lvl = messageLevel(msg);
  if (lvl == "bad") {
    console.error(`${loc}\x1b[91m${msg.status}\x1b[0m ${m}`);
  } else if (lvl == "unknown") {
    console.warn(`${loc}\x1b[94m${msg.status}\x1b[0m ${m}`);
  } else {
    console.log(`${loc}\x1b[92m${msg.status}\x1b[0m ${m}`);
  }
}

export class MessageException extends Error {
  readonly msg: Message;
  constructor(msg: Message) { super(shortDescription(msg)); this.msg = msg; }
}

export function err(e: Error): Message {
  const loc = { file: options.filename, start: { line: 0, column: 0 }, end: { line: 0, column: 0 }};
  return { status: "error", loc, error: e };
}
