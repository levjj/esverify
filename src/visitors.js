import { obj } from "lively.lang";
import { declarationsOfScope } from "lively.ast/lib/query.js";
import Visitor from "lively.ast/generated/estree-visitor.js";

import { TopLevelScope, ClassScope, FunctionScope } from "./scopes.js";

class RemoveAssertions extends Visitor {
  visitExpressionStatement(node, state, path) {
    // Node, null, Array<Node> -> Node
    const expr = node.expression;
    if (expr.type == "CallExpression" &&
        expr.callee.type == "Identifier" &&
        ["requires", "ensures", "assert", "invariant"]
          .includes(expr.callee.name)) {
      return {type: "EmptyStatement"};
    }
    return super.visitExpressionStatement(node, state, path);
  }
}

export function removeAssertions(node) {
  // Node -> Node
  const ra = new RemoveAssertions();
  return ra.accept(obj.deepCopy(node), null, []);
}

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

class FindDefs extends Visitor {
  
  visitVariableDeclaration(node, scope, path) {
    scope.varDecls.push(node);
    return super.visitVariableDeclaration(node, scope, path);
  }

  visitFunctionDeclaration (node, scope, path) {
    scope.funcDecls.push(node);
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
