export type SExpr = string | SExprList;
export interface SExprList extends Array<SExpr> {}

export function flatMap<A,B> (a: ReadonlyArray<A>, f: (a: A) => ReadonlyArray<B>): Array<B> {
  return a.map(f).reduce((a: Array<B>, b: ReadonlyArray<B>): Array<B> => a.concat(b), []);
}

export function parseSExpr (input: string): SExpr {
  let idx = 0;

  function skipWS () {
    while (true) {
      if (input[idx] === ';') {
        while (input[idx] !== '\n') idx++;
      }
      if (input[idx] !== ' ' && input[idx] !== '\t' && input[idx] !== '\n') break;
      idx++;
    }
  }

  function sexpr (): SExpr | null {
    skipWS();
    if (input[idx] === '(') {
      idx++;
      const list: SExprList = [];
      for (let next = sexpr(); next !== null; next = sexpr()) {
        list.push(next);
      }
      skipWS();
      if (input[idx++] !== ')') {
        throw new Error(`expected s-expression: ${input.substring(idx - 10, idx + 10)}`);
      }
      return list;
    }
    const m = input.substr(idx).match(/^("[^"]*")|^[a-zA-Z0-9_\-!#=.]+/);
    if (m) {
      idx += m[0].length;
      return m[0];
    }
    return null;
  }

  const result = sexpr();
  if (result === null) {
    throw new Error(`expected s-expression: ${input}`);
  } else {
    return result;
  }
}

export type SExprPattern = string | { name: string } | { group: string } | { expr: string } | SExprPatternList;
export interface SExprPatternList extends Array<SExprPattern> {}

export function matchSExpr (expr: SExpr, pattern: SExprPattern): { [name: string]: SExpr } | null {
  const bindings: { [name: string]: SExpr } = {};
  function process (expr: SExpr, pattern: SExprPattern): boolean {
    if (typeof pattern === 'string') {
      if (expr !== pattern) return false;
    } else if (pattern instanceof Array) {
      if (!(expr instanceof Array) || pattern.length !== expr.length) return false;
      for (let i = 0; i < pattern.length; i++) {
        if (!process(expr[i], pattern[i])) return false;
      }
    } else if ('name' in pattern) {
      if (typeof expr !== 'string') return false;
      bindings[pattern.name] = expr;
    } else if ('group' in pattern) {
      if (!(expr instanceof Array)) return false;
      bindings[pattern.group] = expr;
    } else {
      bindings[pattern.expr] = expr;
    }
    return true;
  }
  return process(expr, pattern) ? bindings : null;
}
