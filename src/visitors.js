import { obj } from "lively.lang";
import Visitor from "lively.ast/generated/estree-visitor.js";

import { TopLevelScope, ClassScope, FunctionScope } from "./scopes.js";

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

class FindScopes extends Visitor {
  accept(node, state, path) {
    // Node, Array<VerificationScope>, Array<Node> -> Node
    switch (node.type) {
      case "ClassDeclaration":
      case "MethodDefinition":
      case "ArrowFunctionExpression":
      case "FunctionExpression":
        throw new Error("not supported");
      case "FunctionDeclaration":
        const newScope = new FunctionScope(state[0], node);
        state.unshift(newScope);
        super.accept(node, state, path);
        state.shift();
        break;
      default:
        super.accept(node, state, path);
    }
    return node;
  }
}

export function findScopes(node) {
  // Node -> TopLevelScope
  const fs = new FindScopes(),
        state = new TopLevelScope(node);
  fs.accept(node, [state], []);
  return state;
}

class ReplaceFunctionResult extends Visitor {
  constructor(func) {
    this.name = func.id.name;
    this.params = func.params.map(p => p.name);
  }
  accept(node, state, path) {
    // Node, null, Array<Node> -> Node
    const n = super.accept(node, state, path);
    if (n.type == "CallExpression" &&
      n.callee.type == "Identifier" &&
      n.callee.name == this.name &&
      n.arguments.length == this.params.length &&
      n.arguments.every((arg, idx) =>
        arg.type == "Identifier" && arg.name == this.params[idx])) {
      return {type: "Identifier", name: "_res"};
    }
    return n;
  }
}

export function replaceFunctionResult(func, node) {
  // Node -> Node
  const ra = new ReplaceFunctionResult(func);
  return ra.accept(obj.deepCopy(node), null, []);
}
