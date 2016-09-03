import { obj } from "lively.lang";
import { id, funcCall } from "lively.ast/lib/nodes.js";
import { declarationsOfScope } from "lively.ast/lib/query.js";
import Visitor from "lively.ast/generated/estree-visitor.js";

import { TopLevelScope, ClassScope, FunctionScope } from "./scopes.js";

class FindScopes extends Visitor {
  visitClassDeclaration(node, state, path) {
    // Node, Array<VerificationScope>, Array<Node> -> Node
    throw new Error("not supported");
  }
  visitArrowFunctionExpression(node, state, path) {
    // Node, Array<VerificationScope>, Array<Node> -> Node
    throw new Error("not supported");
  }
  visitFunctionExpression(node, state, path) {
    // Node, Array<VerificationScope>, Array<Node> -> Node
    throw new Error("not supported");
  }
  visitFunctionDeclaration(node, state, path) {
    // Node, Array<VerificationScope>, Array<Node> -> Node
    const newScope = new FunctionScope(state[0], node);
    state.unshift(newScope);
    super.visitFunctionDeclaration(node, state, path);
    state.shift();
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
    // FunctionDeclaration -> ReplaceFunctionResult
    this.name = func.id.name;
    this.params = func.params.map(p => p.name);
  }
  visitCallExpression(node, state, path) {
    // Node, null, Array<Node> -> Node
    if (node.callee.type == "Identifier" &&
        node.callee.name == this.name &&
        node.arguments.length == this.params.length &&
        node.arguments.every((arg, idx) =>
          arg.type == "Identifier" && arg.name == this.params[idx])) {
      return {type: "Identifier", name: "_res"};
    }
    return super.visitCallExpression(node, state, path);
  }
}

export function replaceFunctionResult(func, node) {
  // Node -> Node
  const ra = new ReplaceFunctionResult(func);
  return ra.accept(obj.deepCopy(node), null, []);
}

class ReplaceResultFunction extends Visitor {
  constructor(func) {
    // FunctionDeclaration -> ReplaceResultFunction
    this.id = func.id;
    this.params = func.params;
  }
  visitIdentifier(node, state, path) {
    // Node, null, Array<Node> -> Node
    if (node.name == "_res") {
      return funcCall(this.id, ...this.params);
    }
    return super.visitIdentifier(node, state, path);
  }
}

export function replaceResultFunction(func, node) {
  // Node -> Node
  const ra = new ReplaceResultFunction(func);
  return ra.accept(obj.deepCopy(node), null, []);
}

class FindDefs extends Visitor {
  
  visitVariableDeclaration(node, scope, path) {
    scope.varDecls.push(node);
    return super.visitVariableDeclaration(node, scope, path);
  }

  visitFunctionDeclaration (node, scope, path) {
    scope.funcDecls.push(node);
    if (node === scope.node) { // find defs in this function
      return super.visitFunctionDeclaration(node, scope, path);
    }
    return node; // do not enter function
  }

  visitFunctionExpression (node, scope, path) {
    return node; // do not enter function
  }

  visitArrowFunctionExpression(node, scope, path) {
    return node; // do not enter function
  }
  
  visitCatchClause (node, scope, path) {
    scope.catches.push(node.param);
    return super.visitCatchClause(node, scope, path);
  }

  visitClassDeclaration(node, scope, path) {
    scope.classDecls.push(node);
    return node;
  }
}

export function findDefs(node) {
  // Node -> Array<string>
  const fd = new FindDefs(),
        scope = {
          node,
          params: node.params || [],
          funcDecls: [],
          varDecls: [],
          catches: [],
          classDecls: [],
          importDecls: []
        };
  fd.accept(node, scope, []);
  return declarationsOfScope(scope).map(id => id.name);
}
