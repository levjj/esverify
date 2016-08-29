import { arr } from "lively.lang";
import { parse } from "lively.ast";

import { functions, postConditions } from "./src/visitors.js";
import Theorem from "./src/theorems.js";

// type JSSource = string;
// type SMTInput = string;
// type SMTOutput = string;

export function theoremsInSource(src) {
  // JSSource -> Array<Theorem>?
  try {
    const ast = parse(src),
          funcs = functions(ast);
    if (!funcs) return null;
    return arr.flatmap(funcs, fun =>
            postConditions(fun).map(post => new Theorem(fun, post)));
  } catch (e) {
    console.error(e);
    return null
  }
}
