declare const console: { log: (s: string) => void, warn: (s: string) => void, error: (s: string) => void };

import { Model } from './smt';
import { Syntax } from './javascript';
import { options } from './options';

interface BaseMessage { status: string; loc: Syntax.SourceLocation; description: string; }

interface Verified extends BaseMessage { status: 'verified'; }

interface Unverified extends BaseMessage { status: 'unverified'; model: Model; }
interface Unknown extends BaseMessage { status: 'unknown'; }

interface BaseError extends BaseMessage { status: 'error'; type: string; }
interface Incorrect extends BaseError { type: 'incorrect'; model: Model; error: Error; }
interface ParseError extends BaseError { type: 'parse-error'; }
interface Unsupported extends BaseError { type: 'unsupported'; loc: Syntax.SourceLocation; }
interface UndefinedIdentifier extends BaseError { type: 'undefined-identifier'; }
interface AlreadyDefinedIdentifier extends BaseError { type: 'already-defined'; }
interface AssignmentToConst extends BaseError { type: 'assignment-to-const'; }
interface ModelError extends BaseError { type: 'unrecognized-model'; }
interface UnexpectedError extends BaseError { type: 'unexpected'; error: Error; }
export type Message = Verified | Unverified | Unknown | Incorrect | ParseError | Unsupported | UndefinedIdentifier
                    | AlreadyDefinedIdentifier | AssignmentToConst | ModelError | UnexpectedError;

function formatSimple (msg: Message): string {
  const loc = `${msg.loc.file}:${msg.loc.start.line}:${msg.loc.start.column}`;
  if (msg.status === 'verified') {
    return `${loc}: info: verified ${msg.description}`;
  } else if (msg.status === 'unverified' || msg.status === 'unknown') {
    return `${loc}: warning: ${msg.status} ${msg.description}`;
  } else {
    return `${loc}: error: ${msg.type} ${msg.description}`;
  }
}

function formatColored (msg: Message): string {
  const loc = `${msg.loc.file}:${msg.loc.start.line}:${msg.loc.start.column}`;
  if (msg.status === 'verified') {
    return `[${loc}] \x1b[92mverified\x1b[0m ${msg.description}`;
  } else if (msg.status === 'unverified' || msg.status === 'unknown') {
    return `[${loc}] \x1b[94m${msg.status}\x1b[0m ${msg.description}`;
  } else {
    return `[${loc}] \x1b[91m${msg.type}\x1b[0m ${msg.description}`;
  }
}

function format (msg: Message): string {
  return options.logformat === 'colored' ? formatColored(msg) : formatSimple(msg);
}

export function log (msg: Message): void {
  if (msg.status === 'verified') {
    console.log(format(msg));
  } else if (msg.status === 'unverified' || msg.status === 'unknown') {
    console.warn(format(msg));
  } else {
    console.error(format(msg));
  }
}

export class MessageException extends Error {
  readonly msg: Message;
  constructor (msg: Message) { super(formatSimple(msg)); this.msg = msg; }
}

export function unexpected (error: Error,
                           loc: Syntax.SourceLocation = {
                             file: options.filename,
                             start: { line: 0, column: 0 },
                             end: { line: 0, column: 0 }},
                            description?: string): Message {
  return {
    status: 'error',
    type: 'unexpected',
    loc,
    error,
    description: description !== undefined ? `${description}: ${error.message}` : error.message
  };
}
