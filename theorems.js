/* global fetch */

import { stringify } from "lively.ast";
import Visitor from "lively.ast/generated/estree-visitor.js";

import normalizer from "./jswala.js";
import { assertionToSMT } from "./assertions.js";
import { statementToSMT, smtToValue } from "./javascript.js";
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
  // FunctionDeclaration -> BlockStatement
  
  // normalize function body to SSA-like language
  const ra = new RemoveAssertions(),
      replaced = ra.accept(func, null, []),
      prog = {type: "Program", body: [replaced]},
      normalized = normalizer.normalize(prog,
        {unify_ret: true});
  // extract statements in function
  const nFunc = normalized.body[0].expression.callee;
  return {
    type: "BlockStatement",
    body: nFunc.body.body[1].expression.right.body.body
  };
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
    // FunctionDeclaration, Expression -> Theorem
    this.func = func;
    this.postcondition = postcondition;
  }
  
  description() {
    // -> string
    return `${this.func.id.name}:\n${stringify(this.postcondition)}`;
  }
  
  csystem() {
    // -> SMTInput
    if (this._csystem) return this._csystem;

    const parameters = this.func.params.map(p =>
            `(declare-const ${p.name} JSVal)`).join('\n'),
          requirements = preConditions(this.func).map(c =>
            `(assert (_truthy ${assertionToSMT(c, this.func)}))`).join('\n'),
          [body] = statementToSMT(funcBody(this.func)),
          post = `(assert (not (_truthy ${assertionToSMT(this.postcondition, this.func)})))`;
    
    console.log(stringify(funcBody(this.func)));

    return this._csystem = `
${preamble}

; parameters
${parameters}
(declare-const _res JSVal)

; requirements
${requirements}

; body
${body}

; post condition
${post}

(check-sat)
(get-value (${this.func.params.map(p => p.name).join(' ')} _res))`;
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
    if (res.startsWith("unsat")) return true;
    if (res.startsWith("sat")) return false;
    throw new Error("z3 failed to solve problem");
  }
  
  async getModel() {
    // -> { [string]: any }
    if (this._model) return this._model;
    let res = await this.solve();
    if (!res.startsWith("sat")) throw new Error("no model available");
    // remove "sat"
    res = res.slice(3, res.length);
    // remove outer parens
    res = res.trim().slice(2, res.length - 4);
    const model = {};
    res.split(/\)\s+\(/m).forEach(str => {
      // these are now just pairs of varname value
      const both = str.trim().split(" ");
      if (both.length < 2) return;
      const name = both[0].trim(),
            value = both.slice(1, both.length).join(" ").trim();
      model[name] = smtToValue(value);
    });
    return this._model = model;
  }
}

export function theorems(fun) {
  // FunctionDeclaration -> Array<Theorem>
  return postConditions(fun).map(post => new Theorem(fun, post));
}
