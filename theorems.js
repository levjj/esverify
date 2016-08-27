/* global fetch */

import { stringify } from "lively.ast";
import Visitor from "lively.ast/generated/estree-visitor.js";

import normalizer from "./jswala.js";
import assertionToSMT from "./assertions.js";
import statementToSMT from "./javascript.js";
import { preamble } from "./defs-smt.js";

class RemoveAssertions extends Visitor {
  accept(node, state, path) {
    const n = super.accept(node, state, path);
    if (n.type == "ExpressionStatement" &&
        n.expression.type == "CallExpression" &&
        n.expression.callee.type == "Identifier" &&
        (n.expression.callee.name == "requires" ||
         n.expression.callee.name == "ensures") ) {
      return {type: "EmptyStatement"};
    }
    return n;
  }
}

function funcBody(func) {
  // FunctionDeclaration -> Array<Statement>
  
  // normalize function body to SSA-like language
  const ra = new RemoveAssertions(),
      replaced = ra.accept(func, null, []),
      normalized = normalizer.normalize(replaced,
        {unify_ret: true, unfold_ifs: true});
  return normalized.body.body;
}

function preConditions(func) {
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

export class Theorem {
  constructor(func, postcondition) {
    this.func = func;
    this.postcondition = postcondition;
  }
  
  description() {
    // -> string
    return `${this.func.name}:\n${stringify(this.postcondition)}`;
  }
  
  csystem() {
    // -> SMTInput
    if (this._csystem) return this._csystem;

    const parameters = this.func.params.map(p =>
            `(declare-const ${p.name} JSVal)`).join('\n'),
          requirements = preConditions(this.func).map(c =>
            `(assert (_js-truthy ${assertionToSMT(c)}))`).join('\n'),
          body = funcBody(this.func).map(stmt => statementToSMT(stmt)).join('\n'),
          post = `(assert (not (_js-truthy ${assertionToSMT(this.postcondition)})))`;

    return this._csystem = `
      ${preamble}
      ${parameters}
      (declare-const _res JSVal)
      ${requirements}
      ${body}
      ${post}
      (check-sat)
      (get-model)`;
  }
  
  async solve() {
    // -> SMTOutput
    if (this._results) return this._results;
    const req = await fetch("/nodejs/Z3server/", {
      method: "POST",
      body: this.csystem()
    });
    return this._results = await req.text();
  }
  
  async isSatisfied() {
    // -> Bool
    const res = await this.solve();
    return res.startsWith("unsat");
  }
}

export function theorems(fun) {
  // FunctionDeclaration -> Array<Theorem>
  return postConditions(fun).map(post => new Theorem(fun, post));
}
