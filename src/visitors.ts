import { obj } from "lively.lang";
import { stringify, nodes, query } from "lively.ast";
const { id, funcCall, block, literal, exprStmt } = nodes;
const { declarationsOfScope } = query;

import * as Visitor from "../generated/estree-visitor.js";

/// <reference path="../typings/mozilla-spidermonkey-parser-api.d.ts"/>
import { JSyntax } from "./javascript";
import { VerificationScope, TopLevelScope, LoopScope, ClassScope, FunctionScope } from "./scopes";

class FindScopes extends Visitor {
  visitClassDeclaration(node: JSyntax.Node, state: Array<VerificationScope>, path: Array<JSyntax.Node>): Syntax.Node {
    throw new Error("not supported");
  }
  visitArrowFunctionExpression(node: JSyntax.FunctionExpression, state: Array<VerificationScope>, path: Array<Syntax.Node>): JSyntax.Node {
    throw new Error("not supported");
  }
  visitFunctionExpression(node: JSyntax.FunctionExpression, state: Array<VerificationScope>, path: Array<Syntax.Node>): JSyntax.Node {
    throw new Error("not supported");
  }
  visitFunctionDeclaration(node: JSyntax.FunctionDeclaration, state: Array<VerificationScope>, path: Array<Syntax.Node>): JSyntax.Node {
    const newScope = new FunctionScope(state[0], node);
    state.unshift(newScope);
    super.visitFunctionDeclaration(node, state, path);
    state.shift();
    return node;
  }
  visitWhileStatement(node: JSyntax.WhileStatement, state: Array<VerificationScope>, path: Array<Syntax.Node>): JSyntax.Node {
    const newScope = new LoopScope(state[0], node);
    state.unshift(newScope);
    super.visitWhileStatement(node, state, path);
    state.shift();
    return node;
  }
}

function normalize() {
  const stmts = [exprStmt(funcExpr({}, [], ...pruneLoops(this.body)))],
        iife = program(exprStmt(funcExpr({}, [], ...stmts))),
        normalized = normalizer.normalize(iife, {unify_ret: true}),
        niife = normalized.body[0].expression.callee.body.body[1].expression.right.body.body;
  return program(...niife[1].body.body[0].expression.right.body.body);
}

export function findScopes(node: Syntax.Program): TopLevelScope {
  const fs = new FindScopes(),
        state = new TopLevelScope(node);
  fs.accept(node, [state], []);
  return state;
}

class ReplaceFunctionResult extends Visitor {
  name: string;
  params: Array<string>;

  constructor(func: Syntax.FunctionDeclaration) {
    super();
    this.name = func.id.name;
    this.params = func.params.map(p => p.name);
  }
  visitCallExpression(node: Syntax.CallExpression, state: null, path: Array<Syntax.Node>): Syntax.Node {
    if (node.callee.type == "Identifier" &&
        node.callee.name == this.name &&
        node.arguments.length == this.params.length &&
        node.arguments.every((arg, idx) =>
          arg.type == "Identifier" && arg.name == this.params[idx])) {
      const i: Syntax.Identifier = {type: "Identifier", name: "_res"};
      return i;
    }
    return super.visitCallExpression(node, state, path);
  }
}

export function replaceFunctionResult(func: Syntax.FunctionDeclaration, node: Syntax.Node): Syntax.Node {
  const ra = new ReplaceFunctionResult(func);
  return ra.accept(obj.deepCopy(node), null, []);
}

class ReplaceResultFunction extends Visitor {
  id: Syntax.Identifier;
  params: Array<string>;

  constructor(func: Syntax.FunctionDeclaration) {
    super();
    this.id = func.id;
    this.params = func.params;
  }
  visitIdentifier(node: Syntax.Identifier, state: null, path: Array<Syntax.Node>): Syntax.Node {
    if (node.name == "_res") {
      return funcCall(this.id, ...this.params);
    }
    return super.visitIdentifier(node, state, path);
  }
}

export function replaceResultFunction(func: Syntax.FunctionDeclaration, node: Syntax.Node): Syntax.Node {
  const ra = new ReplaceResultFunction(func);
  return ra.accept(obj.deepCopy(node), null, []);
}

interface Scope {
  node: Syntax.Node;
  params: Array<Syntax.Identifier>;
  funcDecls: Array<Syntax.FunctionDeclaration>;
  varDecls: Array<Syntax.VariableDeclaration>;
  catches: Array<Syntax.Statement>;
  classDecls: Array<Syntax.ClassDeclaration>;
  importDecls: Array<Syntax.Node>;
}

class FindDefs extends Visitor {
  
  visitVariableDeclaration(node: Syntax.VariableDeclaration, scope: Scope, path: Array<Syntax.Node>): Syntax.Node {
    scope.varDecls.push(node);
    return super.visitVariableDeclaration(node, scope, path);
  }

  visitFunctionDeclaration(node: Syntax.FunctionDeclaration, scope: Scope, path: Array<Syntax.Node>): Syntax.Node {
    scope.funcDecls.push(node);
    if (node === scope.node) { // find defs in this function
      return super.visitFunctionDeclaration(node, scope, path);
    }
    return node; // do not enter function
  }

  visitFunctionExpression(node: Syntax.FunctionExpression, scope: Scope, path: Array<Syntax.Node>): Syntax.Node {
    return node; // do not enter function
  }

  visitArrowFunctionExpression(node: Syntax.FunctionExpression, scope: Scope, path: Array<Syntax.Node>): Syntax.Node {
    return node; // do not enter function
  }
  
  visitCatchClause(node: Syntax.CatchClause, scope: Scope, path: Array<Syntax.Node>): Syntax.Node {
    scope.catches.push(node.param);
    return super.visitCatchClause(node, scope, path);
  }

  visitClassDeclaration(node: Syntax.ClassDeclaration, scope: Scope, path: Array<Syntax.Node>): Syntax.Node {
    scope.classDecls.push(node);
    return node;
  }
}

export function findDefs(node: Syntax.Node) {
  // Node -> Array<string>
  const fd = new FindDefs(),
        scope: Scope = {
          node,
          params: node.params || [],
          funcDecls: [],
          varDecls: [],
          catches: [],
          classDecls: [],
          importDecls: []
        };
  fd.accept(node, scope, []);
  return declarationsOfScope(scope).map((id: Syntax.Identifier) => id.name);
}

export function isAssertion(stmt: Syntax.Statement): boolean {
  return stmt.type == "ExpressionStatement" &&
         stmt.expression.type == "CallExpression" &&
         stmt.expression.callee.type == "Identifier" &&
         (["requires", "ensures", "assert", "invariant"]
           .includes(stmt.expression.callee.name)) &&
         stmt.expression.arguments.length === 1;
}

class FindInvariants extends Visitor {
  visitExpressionStatement(node: JSyntax.ExpressionStatement, state: Array<JSyntax.CallExpression>, path: Array<Syntax.Node>): Syntax.Node {
    if (isAssertion(node)) {
      if (node.expression.callee.name == "invariant") {
        return exprStmt(literal(`@assume:${stringify(node.expression.arguments[0])}`));
      }
      return {type: "EmptyStatement"};
    }
    return super.visitExpressionStatement(node, state, path);
  }
  visitWhileStatement(node: Syntax.WhileStatement, state: null, path: Array<Syntax.Node>): Syntax.Node {
    return super.visitWhileStatement({
      type: "WhileStatement",
      test: node.test,
      body: block(exprStmt(literal(`@assume:!(${stringify(node.test)})`)), ...node.body.body)
    }, state, path);
  }
}

export function findInvariants(stmt: JSyntax.Statement): Array<JSyntax.CallExpression> {
  const fi = new FindInvariants(),
        inv = [];
  fi.accept(stmt, inv, []);
  return inv;
}