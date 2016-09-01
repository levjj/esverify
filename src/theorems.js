/* global fetch */

import { stringify } from "lively.ast";

import { assertionToSMT } from "./assertions.js";
import { statementToSMT, smtToValue, createVars, varsToSMT } from "./javascript.js";
import { preamble } from "./defs-smt.js";

export default class Theorem {
  constructor(vars, pre, body, post, description) {
    // Array<string>, Array<Expression>, Statement, Expression, string -> Theorem
    this.vars = vars;
    this.pre = pre;
    this.body = body;
    this.post = post;
    this.description = description;
    this._result = null;
  }
  
  csystem() {
    // -> SMTInput
    if (this._csystem) return this._csystem;
    const vars = createVars(this.vars),
          [body, nvars] = statementToSMT(this.body, vars),
          declarations = varsToSMT(nvars),
          requirements = this.pre.map(c =>
            `(assert (_truthy ${assertionToSMT(c, vars)}))`).join('\n'),
          post = `(assert (not (_truthy ${assertionToSMT(this.post, nvars)})))`;
    
    return this._csystem =
`${preamble}

; declarations
${declarations}

; body
${body}

; requirements
${requirements}

; post condition
${post}

(check-sat)
(get-value (${this.vars.map(v => `${v}_0`).join(' ')} _res_0))`;
  }
  
  result() {
    return this._result;
  }
  
  async solve() {
    // -> SMTOutput
    if (this._result) return this._result;
    const req = await fetch("/nodejs/Z3server/", {
      method: "POST",
      body: this.csystem()
    });
    return this._result = await req.text();
  }
  
  isSatisfiable() {
    // -> Bool?
    const res = this.result();
    if (!res) return null;
    if (res.startsWith("unsat")) return true;
    if (res.startsWith("sat")) return false;
    throw new Error("z3 failed to solve problem");
  }
  
  getModel() {
    // -> { [string]: any }?
    if (this._model) return this._model;
    let res = this.result();
    if (!res) return null;
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
      model[name.substr(0, name.length - 2)] = smtToValue(value);
    });
    return this._model = model;
  }
}
