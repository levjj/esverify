import { stringify } from "lively.ast";
import { exprStmt, funcExpr, funcDecl, funcCall, program, varDecl } from "lively.ast/lib/nodes.js";
import { arr } from "lively.lang";

import normalizer from "../generated/jswala.js";
import Theorem from "./theorems.js";
import { removeAssertions, replaceFunctionResult, findDefs } from "./visitors.js";

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
  
  ownTheorems() {
    // -> Array<Theorem>
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

  theorems() {
    // -> Array<Theorem>
    return this.ownTheorems().concat(arr.flatmap(this.scopes, s => s.theorems()));
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
  
  body() {
    // -> Array<Statement>
    return this.node.body.body;
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
  
  bodySource() {
    // -> JSSource
    const {id, params} = this.node;
    return stringify(funcExpr({id}, params, ...this.normalizedNode()));
  }

  ownTheorems() {
    // -> Array<Theorem>
    const vars = this.surroundingVars(),
          pre = this.preConditions().concat(this.parent.invariants()),
          body = program(...this.normalizedNode()),
          toProve = this.postConditions().concat(this.invariants());
    return toProve.map(pc => {
      const pc2 = replaceFunctionResult(this.node, pc),
            desc = this.describe(pc);
      return new Theorem(this, vars, pre, body, pc2, desc);
    });
  }
  
  describe(post) {
    // Expression -> string
    return `${this.node.id.name}:\n${stringify(post)}`;
  }

}

export class ClassScope extends VerificationScope {
}

export class TopLevelScope extends VerificationScope {
  
  constructor(node) {
    // Program -> VerificationScope
    super(null, node);
  }
  
  body() {
    // -> Array<Statement>
    return this.node.body;
  }

  ownTheorems() {
    // -> Array<Theorem>
    const body = program(...this.normalizedNode());
    return this.invariants().map(pc =>
      new Theorem(this, [], [], body, pc, `initially:\n${stringify(pc)}`));
  }
  
  bodySource() {
    // -> JSSource
    return stringify(program(...this.normalizedNode()));
  }
}
