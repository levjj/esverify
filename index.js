import { arr } from "lively.lang";
import { parse } from "lively.ast";

import { theorems } from "./theorems.js";

// type JSSource = string;
// type SMTInput = string;
// type SMTOutput = string;

function functions(ast) {
  // Node -> Array<FunctionDeclaration>?
  const result = [];
  for (const node of ast.body) {
    if (node.type !== "FunctionDeclaration") return null;
    result.push(node);
  }
  return result;
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
