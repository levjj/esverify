import { arr } from "lively.lang";
import { parse } from "lively.ast";

import Theorem from "./theorems.js";

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

function postConditions(func) {
  // FunctionDeclaration -> Array<Expression>
  return func.body.body
    .filter(stmt =>
      stmt.type == "ExpressionStatement" &&
      stmt.expression.type == "CallExpression" &&
      stmt.expression.callee.type == "Identifier" &&
      stmt.expression.callee.name == "ensures"
    )
    .map(stmt => stmt.expression.arguments[0]);
}

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
