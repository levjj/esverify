/* global fetch */

import { stringify } from "lively.ast";
import { id, literal, exprStmt, funcExpr, program, varDecl, ifStmt } from "lively.ast/lib/nodes.js";

import normalizer from "../generated/jswala.js";
import { pruneLoops } from "./visitors.js";
import { assertionToSMT } from "./assertions.js";
import { statementToSMT, smtToValue, createVars, varsToSMT } from "./javascript.js";
import { preamble } from "./defs-smt.js";

// type Model = { [string]: any }?

// type Result = { status: "inprogress" }
//             | { status: "sat" }
//             | { status: "unsat", error: Exception }
//             | { status: "failed", reason: ("smt" | "test") }

function valueToNode(v) {
  // any -> Node
  if (v === null || v === undefined || typeof(v) == "boolean" || typeof(v) == "string") {
    return literal(v);
  }
  if (typeof(v) == "number") {
    if (v >= 0) {
      return literal(v);
    } else {
      return { type: "UnaryExpression", operator: "-", argument: literal(-v) }
    }
  }
  // TODO: arrays, objects
}

export default class Theorem {
  constructor(vars, pre, body, post, description) {
    // Array<string>, Array<Expression>, Array<Statement>, Expression, string -> Theorem
    this.vars = vars;
    this.pre = pre;
    this.body = body;
    this.post = post;
    this.description = description;
    this._smtin = null;
    this._smtout = null;
    this._testresult = null;
  }
  
  normalizedBody() {
    // () -> Program
    // normalize function body to SSA-like language
    const decls = this.vars.map(v => varDecl(v)),
          stmts = decls.concat([exprStmt(funcExpr({}, [], ...pruneLoops(this.body)))]),
          iife = program(exprStmt(funcExpr({}, [], ...stmts))),
          normalized = normalizer.normalize(iife, {unify_ret: true}),
          niife = normalized.body[0].expression.callee.body.body[1].expression.right.body.body;
    return program(...niife[1].body.body[0].expression.right.body.body);
  }
  
  testBody() {
    // () -> Program
    const model = this.getModel(),
          decls = this.vars.map(v => varDecl(v, valueToNode(model[v]))),
          check = ifStmt({type: "UnaryExpression", operator: "!", argument: this.post},
                         {type: "ThrowStatement", argument: {
                           type: "NewExpression",
                           callee: id("Error"),
                           arguments: [literal("AssertionError")]
                         }});
    return program(...decls, ...this.body, check);
  }

  bodySource() {
    // -> JSSource
    return stringify(this.normalizedBody());
  }
  
  smtInput() {
    // -> SMTInput
    if (this._smtin) return this._smtin;
    const vars = createVars(this.vars),
          [body, nvars] = statementToSMT(this.normalizedBody(), vars),
          declarations = varsToSMT(nvars),
          requirements = this.pre.map(c =>
            `(assert (_truthy ${assertionToSMT(c, vars)}))`).join('\n'),
          post = `(assert (not (_truthy ${assertionToSMT(this.post, nvars)})))`;
    
    return this._smtin =
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
(get-value (${Object.keys(nvars).map(v => `${v}_0`).join(' ')}))`;
  }
  
  smtOutput() {
    return this._smtout;
  }
  
  getModel() {
    // -> Model?
    let res = this._smtout;
    if (!res || !res.startsWith("sat")) throw new Error("no model available");
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
    return model;
  }
  
  runTest() {
    // -> ()
    eval(stringify(this.testBody()));
  }
  
  result() {
    // -> Result
    if (!this._smtout) return { status: "inprogress" };
    if (this._smtout.startsWith("unsat")) return { status: "sat" };
    if (!this._smtout.startsWith("sat")) return { status: "failed", reason: "smt" };
    if (!this._testresult) return { status: "failed", reason: "test" };
    return { status: "unsat", error: this._testresult };
  }

  async solve() {
    // -> ()
    const req = await fetch("/nodejs/Z3server/", {
      method: "POST",
      body: this.smtInput()
    });
    this._smtout = await req.text();
    if (this._smtout.startsWith("sat")) {
      try {
        this.runTest();
        this._testresult = null;
      } catch (e) {
        this._testresult = e;
      }
    }
  }

}
