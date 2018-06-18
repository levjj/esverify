import { Syntax } from './javascript';
import { Model } from './model';
import { options } from './options';

export interface BaseMessage { status: string; loc: Syntax.SourceLocation; description: string; }

export interface Verified extends BaseMessage { status: 'verified'; }

export interface Unverified extends BaseMessage { status: 'unverified'; model: Model; }
export interface Unknown extends BaseMessage { status: 'unknown'; }
export interface TimeOut extends BaseMessage { status: 'timeout'; }

export interface BaseError extends BaseMessage { status: 'error'; type: string; }
export interface Incorrect extends BaseError { type: 'incorrect'; model: Model; error: Error; }
export interface ParseError extends BaseError { type: 'parse-error'; }
export interface Unsupported extends BaseError { type: 'unsupported'; loc: Syntax.SourceLocation; }
export interface UndefinedIdentifier extends BaseError { type: 'undefined-identifier'; }
export interface AlreadyDefinedIdentifier extends BaseError { type: 'already-defined'; }
export interface AssignmentToConst extends BaseError { type: 'assignment-to-const'; }
export interface ReferenceInInvariant extends BaseError { type: 'reference-in-invariant'; }
export interface ModelError extends BaseError { type: 'unrecognized-model'; }
export interface UnexpectedError extends BaseError { type: 'unexpected'; error: Error; }
export type Message = Verified | Unverified | TimeOut | Unknown | Incorrect | ParseError | Unsupported
                    | UndefinedIdentifier | AlreadyDefinedIdentifier | AssignmentToConst | ReferenceInInvariant
                    | ModelError | UnexpectedError;

declare const console: { log: (s: string) => void, warn: (s: string) => void, error: (s: string) => void };

function formatSimple (msg: Message): string {
  const loc = `${msg.loc.file}:${msg.loc.start.line}:${msg.loc.start.column}`;
  if (msg.status === 'verified') {
    return `${loc}: info: verified ${msg.description}`;
  } else if (msg.status === 'unverified' || msg.status === 'unknown' || msg.status === 'timeout') {
    return `${loc}: warning: ${msg.status} ${msg.description}`;
  } else {
    return `${loc}: error: ${msg.type} ${msg.description}`;
  }
}

function formatColored (msg: Message): string {
  const loc = `${msg.loc.file}:${msg.loc.start.line}:${msg.loc.start.column}`;
  if (msg.status === 'verified') {
    return `[${loc}] \x1b[92mverified\x1b[0m ${msg.description}`;
  } else if (msg.status === 'unverified' || msg.status === 'unknown' || msg.status === 'timeout') {
    return `[${loc}] \x1b[94m${msg.status}\x1b[0m ${msg.description}`;
  } else {
    return `[${loc}] \x1b[91m${msg.type}\x1b[0m ${msg.description}`;
  }
}

function formatHTML (msg: Message, withLocation: boolean): string {
  function boldColored (color: string, text: string): string {
    return `<b style="color:#${color}">${text}</b>`;
  }
  function escape (text: string): string {
    const charToReplace: { [c: string]: string } = {
      '&': '&amp;',
      '<': '&lt;',
      '>': '&gt;'
    };
    return text.replace(/[&<>]/g, c => charToReplace[c] || c);
  }
  const loc = withLocation ? `[${msg.loc.file}:${msg.loc.start.line}:${msg.loc.start.column}] ` : '';
  if (msg.status === 'verified') {
    return `${loc}${boldColored('32b643', 'verified')} ${escape(msg.description)}`;
  } else if (msg.status === 'unverified' || msg.status === 'unknown' || msg.status === 'timeout') {
    return `${loc}${boldColored('ffb700', msg.status)} ${escape(msg.description)}`;
  } else {
    return `${loc}${boldColored('e85600', msg.type)} ${escape(msg.description)}`;
  }
}

export function format (msg: Message, withLocation: boolean = true): string {
  switch (options.logformat) {
    case 'simple':
      return formatSimple(msg);
    case 'colored':
      return formatColored(msg);
    case 'html':
      return formatHTML(msg, withLocation);
  }
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
