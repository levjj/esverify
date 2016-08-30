import { parse } from "lively.ast";

import { findScopes } from "./src/visitors.js";

// type JSSource = string;
// type SMTInput = string;
// type SMTOutput = string;

export function theoremsInSource(src) {
  // JSSource -> Array<Theorem>?
  try {
    const ast = parse(src),
          topLevel = findScopes(ast);
    return topLevel.theorems();
  } catch (e) {
    console.error(e);
    return null;
  }
}
