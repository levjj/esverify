/* global fetch */

import { arr } from "lively.lang";
import { parse, stringify } from "lively.ast";
import normalizer from "./jswala.js";

// type JSSource = string;
// type SMTInput = string;
// type SMTOutput = string;

function funcBody(func) {
  // FunctionDeclaration -> Array<Statement>
  // return function body in SSA-like language
  // TODO remove conditions
  const normalized = normalizer.normalize(func,
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

const preamble = `
; Values in JavaScript
(declare-datatypes () (
  (JSVal
    (jsnum (numv Int))
    (jsbool (boolv Bool))
    (jsstring (stringv (List Int)))
    jsnull
    jsundefined
    (jsarray (items JSValList))
    (jsobj (props JSPropList)))
  (JSValList empty (cons (car JSVal) (cdr JSValList)))
  (JSProp (prop (key (List Int)) (val JSVal)))
  (JSPropList empty (cons (car JSProp) (cdr JSPropList)))))

; Types in JavaScript
(declare-datatypes () ((JSType JSNum JSBool JSString JSUndefined JSArray JSObj)))

(define-fun _js-typeof ((a JSVal)) JSType
  (ite (is-jsnum a) JSNum
  (ite (is-jsbool a) JSBool
  (ite (is-jsstring a) JSString
  (ite (is-jsnull a) JSObj
  (ite (is-jsundefined a) JSUndefined
  (ite (is-jsarray a) JSArray
  JSObj)))))))

; a >= b
(define-fun _js-geq ((a JSVal) (b JSVal)) JSVal
  (ite (is-jsnum a)
    (ite (is-jsnum b)
      (ite (>= (numv a) (numv b)) (jsbool true) (jsbool false))
      (jsbool false))
    (jsbool false)))

; !!x
(define-fun _js-truthy ((x JSVal)) Bool
  (ite (is-jsnum x)
    (not (= (numv x) 0))
    (boolv x)))
`;

function assertionToSMT(expr) {
  // Expression -> SMTInput
  return `(jsbool true)`;
}

function statementToSMT(stmt) {
  // Statement -> SMTInput
  return "";
}

class Theorem {
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

function functions(ast) {
  // Node -> Array<FunctionDeclaration>?
  const result = [];
  for (const node of ast.body) {
    if (node.type !== "FunctionDeclaration") return null;
    result.push(node);
  }
  return result;
}

function theorems(fun) {
  // FunctionDeclaration -> Array<Theorem>
  return postConditions(fun).map(post => new Theorem(fun, post));
}

export function theoremsInSource(src) {
  // JSSource -> Array<Theorem>?
  try {
    const ast = parse(src),
          funcs = functions(ast);
    if (!funcs) return null;
    return arr.flatmap(funcs, theorems);
  } catch (e) {
    console.error(e);
    return null
  }
}
