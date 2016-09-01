import { stringify } from "lively.ast";
import { exprStmt, funcExpr, funcCall, program, varDecl } from "lively.ast/lib/nodes.js";
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
  
  invariants() {
    // -> Array<Expression>
    return this.parent.invariants();
  }
  
  theorems() {
    // -> Array<Theorem>
    return arr.flatmap(this.scopes, s => s.theorems());
  }
  
  nodeAsProgram() {
    // -> Node
    return this.node;
  }
  
  bodySource() {
    // -> JSSource
    throw new Error("not implemented");
  }

  vars() {
    // -> Array<string>
    return findDefs(this.node).concat(this.surroundingVars());
  }
  
  surroundingVars() {
    // -> Array<string>
    return this.parent.vars();
  }
  
  normalizedNode() {
    // -> Array<Statement>
    // normalize function body to SSA-like language
    const prog = removeAssertions(this.nodeAsProgram()),
          stmts = this.surroundingVars().map(v => varDecl(v)).concat(prog.body),
          iife = program(exprStmt(funcCall(funcExpr({}, [], ...stmts)))),
          normalized = normalizer.normalize(iife, {unify_ret: true}),
          origProg = normalized.body[0].expression.callee.body;
    // extract statements in function
    return origProg.body[1].expression.right;
  }
  
}

export class FunctionScope extends VerificationScope {

  assertions() {
    // -> Array<Expression>
    return this.node.body.body
      .filter(stmt =>
        stmt.type == "ExpressionStatement" &&
        stmt.expression.type == "CallExpression" &&
        stmt.expression.callee.type == "Identifier" &&
        (["requires", "ensures", "assert", "invariant"]
          .includes(stmt.expression.callee.name)));
  }
  
  preConditions() {
    // -> Array<Expression>
    return this.assertions()
      .filter(stmt => stmt.expression.callee.name == "requires")
      .map(stmt => stmt.expression.arguments[0])
      .map(expr => replaceFunctionResult(this.node, expr));
  }
  
  nodeAsProgram() {
    // -> Node
    // TODO add surrounding vars
    return program(this.node);
  }
  
  normalizedNode() {
    // -> Node
    return super.normalizedNode().body.body[1].expression.right;
  }
  
  postConditions() {
    // -> Array<Expression>
    return this.assertions()
      .filter(stmt => stmt.expression.callee.name == "ensures")
      .map(stmt => stmt.expression.arguments[0]);
  }
  
  bodySource() {
    // -> JSSource
    const body = this.normalizedNode();
    body.id = this.node.id;
    return stringify(body);
  }

  theorems() {
    // -> Array<Theorem>
    const params = this.node.params.map(p => p.name).concat(this.surroundingVars()),
          pre = this.preConditions().concat(this.parent.invariants()),
          body = this.normalizedNode().body,
          toProve = this.postConditions().concat(this.invariants()),
          theorems = toProve.map(pc => {
            const pc2 = replaceFunctionResult(this.node, pc),
                  desc = this.describe(pc);
            return new Theorem(this, params, pre, body, pc2, desc);
          });
    return theorems.concat(super.theorems());
  }
  
  invariants() {
    // -> Array<Expression>
    return super.invariants().concat(this.assertions()
      .filter(stmt => stmt.expression.callee.name == "invariant")
      .map(stmt => stmt.expression.arguments[0]));
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
    // Node -> VerificationScope
    super(null, node);
  }
  
  theorems() {
    // -> Array<Theorem>
    const stmts = this.normalizedNode().body.body,
          body = { type: "BlockStatement", body: stmts.slice(0, -1)},
          theorems = this.invariants().map(pc =>
            new Theorem(this, [], [], body, pc, `initially:\n${stringify(pc)}`));
    return theorems.concat(super.theorems());
  }
  
  invariants() {
    // -> Array<Expression>
    return this.node.body
      .filter(stmt =>
        stmt.type == "ExpressionStatement" &&
        stmt.expression.type == "CallExpression" &&
        stmt.expression.callee.type == "Identifier" &&
        stmt.expression.callee.name == "invariant")
      .map(stmt => stmt.expression.arguments[0]);
  }
  
  surroundingVars() {
    // -> Array<string>
    return [];
  }
  
  bodySource() {
    // -> JSSource
    return stringify(program(...this.normalizedNode().body.body));
  }
}
