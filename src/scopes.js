import { stringify } from "lively.ast";
import { exprStmt, funcExpr, funcDecl, funcCall, program, varDecl } from "lively.ast/lib/nodes.js";
import { arr } from "lively.lang";

import normalizer from "../generated/jswala.js";
import Theorem from "./theorems.js";
import { removeAssertions, replaceFunctionResult, replaceResultFunction, findDefs } from "./visitors.js";

class VerificationScope {
  
  constructor(parent, node) {
    // VerificationScope?, Node -> VerificationScope
    if (parent) {
      parent.scopes.push(this);
      this.parent = parent;
    }
    this.scopes = []; // Array<VerificationScope>
    this.node = node;
  }
  
  assumes() {
    // -> Array<Expression>
    throw new Error("not implemented");
  }
  
  body() {
    // -> Array<Statement>
    throw new Error("not implemented");
  }
  
  bodySource() {
    // -> JSSource
    throw new Error("not implemented");
  }
  
  toProve() {
    // -> Array<Expression>
    return this.invariants();
  }
  
  describe(post) {
    // Expression -> string
    throw new Error("not implemented");
  }
  
  theorems() {
    // -> Array<Theorem>
    const vars = this.surroundingVars(),
          pre = this.assumes(),
          body = program(...this.normalizedNode()),
          theorems = this.toProve().map(pc =>
            new Theorem(this, vars, pre, body, pc, this.describe(pc)));
    return theorems.concat(arr.flatmap(this.scopes, s => s.theorems()));
  }
  
  vars() {
    // -> Array<string>
    return findDefs(this.node).concat(this.surroundingVars());
  }
  
  surroundingVars() {
    // -> Array<string>
    return this.parent ? this.parent.vars() : [];
  }
  
  normalizedNode() {
    // -> Array<Statement>
    // normalize function body to SSA-like language
    const decls = this.surroundingVars().map(v => varDecl(v)),
          stmts = decls.concat([exprStmt(funcExpr({}, [], ...this.statements()))]),
          iife = program(exprStmt(funcExpr({}, [], ...stmts))),
          normalized = normalizer.normalize(iife, {unify_ret: true}),
          niife = normalized.body[0].expression.callee.body.body[1].expression.right.body.body;
    return niife[1].body.body[0].expression.right.body.body;
  }
  
  statements() {
    // -> Array<Statement>
    return this.body()
      .filter(stmt =>
        stmt.type != "ExpressionStatement" ||
        stmt.expression.type != "CallExpression" ||
        stmt.expression.callee.type != "Identifier" ||
        !(["requires", "ensures", "assert", "invariant"]
          .includes(stmt.expression.callee.name)));
  }
  
  assertions() {
    // -> Array<Expression>
    return this.body()
      .filter(stmt =>
        stmt.type == "ExpressionStatement" &&
        stmt.expression.type == "CallExpression" &&
        stmt.expression.callee.type == "Identifier" &&
        (["requires", "ensures", "assert", "invariant"]
          .includes(stmt.expression.callee.name)) &&
        stmt.expression.arguments.length === 1)
      .map(stmt => stmt.expression);
  }

  immediate() {
    // -> Array<Expression>
    return this.assertions()
      .filter(expr => expr.callee.name == "assert")
      .map(expr => expr.arguments[0]);
  }
  
  invariants() {
    // -> Array<Expression>
    const pi = this.parent ? this.parent.invariants() : null;
    return pi.concat(this.assertions()
      .filter(expr => expr.callee.name == "invariant")
      .map(expr => expr.arguments[0]));
  }
  
}

export class FunctionScope extends VerificationScope {
  
  assumes() {
    // -> Array<Expression>
    return this.preConditions().concat(this.parent.invariants());
  }

  body() {
    // -> Array<Statement>
    return this.node.body.body;
  }
  
  bodySource() {
    // -> JSSource
    const {id, params} = this.node;
    return stringify(funcExpr({id}, params, ...this.normalizedNode()));
  }
  
  toProve() {
    // -> Array<Expression>
    return super.toProve().concat(this.postConditions().map(pc => {
      return replaceFunctionResult(this.node, pc);
    }));
  }
  
  describe(post) {
    // Expression -> string
    const replaced = replaceResultFunction(this.node, post);
    return `${this.node.id.name}:\n${stringify(replaced)}`;
  }

  surroundingVars() {
    // -> Array<string>
    return super.surroundingVars().concat(this.node.params.map(p => p.name));
  }

  preConditions() {
    // -> Array<Expression>
    return this.assertions()
      .filter(expr => expr.callee.name == "requires")
      .map(expr => expr.arguments[0]);
  }
  
  postConditions() {
    // -> Array<Expression>
    return this.assertions()
      .filter(expr => expr.callee.name == "ensures")
      .map(expr => expr.arguments[0]);
  }
  
}

export class ClassScope extends VerificationScope {
}

export class TopLevelScope extends VerificationScope {
  
  constructor(node) {
    // Program -> VerificationScope
    super(null, node);
  }
  
  describe(post) {
    // Expression -> string
    return `initially:\n${stringify(post)}`;
  }

  assumes() {
    // -> Array<Expression>
    return [];
  }
  
  body() {
    // -> Array<Statement>
    return this.node.body;
  }

  bodySource() {
    // -> JSSource
    return stringify(program(...this.normalizedNode()));
  }
}
