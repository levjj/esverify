import { obj } from "lively.lang";
import Visitor from "lively.ast/generated/estree-visitor.js";

class RemoveAssertions extends Visitor {
  accept(node, state, path) {
    // Node, null, Array<Node> -> Node
    const n = super.accept(node, state, path);
    if (n.type == "ExpressionStatement" &&
        n.expression.type == "CallExpression" &&
        n.expression.callee.type == "Identifier" &&
        (n.expression.callee.name == "requires" ||
         n.expression.callee.name == "ensures" ||
         n.expression.callee.name == "assert" ||
         n.expression.callee.name == "invariant") ) {
      return {type: "EmptyStatement"};
    }
    return n;
  }
}

export function removeAssertions(node) {
  // Node -> Node
  const ra = new RemoveAssertions();
  return ra.accept(obj.deepCopy(node), null, []);
}

// type Function = ArrowFunctionExpression | FunctionExpression | FunctionDeclaration;

class FindFunctions extends Visitor {
  accept(node, state, path) {
    // Node, Array<Function>, Array<Node> -> Node
    const n = super.accept(node, state, path);
    switch (node.type) {
      case "ArrowFunctionExpression":
      case "FunctionExpression":
      case "FunctionDeclaration":
        state.unshift(node);
    }
    return node;
  }
}

export function functions(node) {
  // Node -> Array<Function>
  const ff = new FindFunctions(), state = [];
  ff.accept(node, state, []);
  return state;
}

export function postConditions(func) {
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

export function preConditions(func) {
  // FunctionDeclaration -> Array<Expression>
  return func.body.body
    .filter(stmt =>
      stmt.type == "ExpressionStatement" &&
      stmt.expression.type == "CallExpression" &&
      stmt.expression.callee.type == "Identifier" &&
      stmt.expression.callee.name == "requires"
    )
    .map(stmt => stmt.expression.arguments[0]);
}
