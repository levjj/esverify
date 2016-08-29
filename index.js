import { arr } from "lively.lang";
import { parse } from "lively.ast";

import { functions, postConditions } from "./visitors.js";
import Theorem from "./theorems.js";

// type JSSource = string;
// type SMTInput = string;
// type SMTOutput = string;

export function theorems(fun) {
  // FunctionDeclaration -> Array<Theorem>
  return postConditions(fun).map(post => new Theorem(fun, post));
}

export function theoremsInSource(src) {
  // JSSource -> Array<Theorem>?
  try {
    const ast = parse(src),
          funcs = functions(ast);
    if (!funcs) return null;
    return arr.flatmap(funcs, theorems);
  } catch (e) {
    console.error(e);
    return null
  }
}
