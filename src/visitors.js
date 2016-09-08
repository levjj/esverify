import { obj } from "lively.lang";
import { stringify } from "lively.ast";
import { id, funcCall, block, literal, exprStmt } from "lively.ast/lib/nodes.js";
import { declarationsOfScope } from "lively.ast/lib/query.js";
import Visitor from "lively.ast/generated/estree-visitor.js";

import { TopLevelScope, LoopScope, ClassScope, FunctionScope } from "./scopes.js";

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
  visitWhileStatement(node, state, path) {
    // Node, Array<VerificationScope>, Array<Node> -> Node
    const newScope = new LoopScope(state[0], node);
    state.unshift(newScope);
    super.visitWhileStatement(node, state, path);
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

class AssumesStrings extends Visitor {
  
  visitExpressionStatement(node, strings, path) {
    // ExpressionStatement, Array<String>, Array<Node> -> Node
    if (node.expression.type == "AssignmentExpression" &&
        node.expression.right.type == "Literal" &&
        typeof(node.expression.right.value) == "string" &&
        node.expression.right.value.startsWith("@assume:")) {
      strings.push(node.expression.right.value.substr(8));
    }
    return super.visitExpressionStatement(node, strings, path);
  }

  visitFunctionDeclaration(node, scope, path) {
    return node; // do not enter function
  }

  visitFunctionExpression(node, scope, path) {
    return node; // do not enter function
  }

  visitArrowFunctionExpression(node, scope, path) {
    return node; // do not enter function
  }
  
  visitWhileStatement(node, scope, path) {
    return node; // do not enter loop
  }

  visitClassDeclaration(node, scope, path) {
    return node; // do not enter class
  }
}

export function assumesStrings(node) {
  // Node -> Array<string>
  const fd = new AssumesStrings(),
        strings = [];
  fd.accept(node, strings, []);
  return strings;
}

export function isAssertion(stmt) {
  // Statement -> boolean
  return stmt.type == "ExpressionStatement" &&
         stmt.expression.type == "CallExpression" &&
         stmt.expression.callee.type == "Identifier" &&
         (["requires", "ensures", "assert", "invariant"]
           .includes(stmt.expression.callee.name)) &&
         stmt.expression.arguments.length === 1;
}

class PruneLoops extends Visitor {
  visitExpressionStatement(node, state, path) {
    if (isAssertion(node)) {
      if (node.expression.callee.name == "invariant") {
        return exprStmt(literal(`@assume:${stringify(node.expression.arguments[0])}`));
      }
      return {type: "EmptyStatement"};
    }
    return super.visitExpressionStatement(node, state, path);
  }
  visitWhileStatement(node, state, path) {
    return super.visitWhileStatement({
      type: "WhileStatement",
      test: node.test,
      body: block(exprStmt(literal(`@assume:!(${stringify(node.test)})`)), ...node.body.body)
    }, state, path);
  }
}

export function pruneLoops(stmts) {
  // Array<Statement> -> Array<Statement>
  const pl = new PruneLoops();
  return stmts.map(stmt => pl.accept(obj.deepCopy(stmt), null, []));
}
