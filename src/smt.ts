import { flatMap } from "./util";
import { Syntax, A, P, Classes, Vars, Locs, Heap, Heaps, Visitor, implies } from "./logic";
import { instantiateQuantifiers } from "./qi";
import { MessageException } from "./message";
import { options } from "./options";

export type SMTInput = string;
export type SMTOutput = string;

const unOpToSMT: {[unop: string]: SMTInput} = {
  "-": "_js-negative",
  "+":"_js-positive",
  "!": "_js-not",
  "~": "_js-bnot",
  "typeof": "_js-typeof",
  "void": "_js-void"
};

const binOpToSMT: {[binop: string]: SMTInput} = {
  "==": "_js-eq", // non-standard
  "!=": "_js-neq", // non-standard
  "===": "_js-eq", // non-standard
  "!==": "_js-neq", // non-standard
  "<": "_js_lt",
  "<=": "_js_leq",
  ">": "_js_gt",
  ">=": "_js-geq",
  "+": "_js-plus",
  "-": "_js-minus",
  "*": "_js-multiply",
  "/": "_js-divide",
  "%": "_js-mod",
  "<<": "_js-lshift",
  ">>": "_js-rshift",
  ">>>": "_js-rzshift",
  "|": "_js-bor",
  "^": "_js-bxor",
  "&": "_js-band",
  "in": "_js-in", // unsupported
  "instanceof": "_js-instanceof" // unsupported
};

class SMTGenerator extends Visitor<SMTInput, SMTInput, SMTInput, SMTInput> {

  visitLocation(loc: Syntax.Location): SMTInput {
    return "l_" + loc;
  }

  visitHeap(heap: Heap): SMTInput {
    return "h_" + heap;
  }

  visitClassName(cls: Syntax.ClassName): SMTInput {
    return "c_" + cls;
  }

  visitHeapStore(expr: Syntax.HeapStore): SMTInput {
    return `(store ${this.visitHeapExpr(expr.target)} ${this.visitLocation(expr.loc)} ${this.visitExpr(expr.expr)})`;
  }
  
  visitHeapEffect(expr: Syntax.HeapEffect): SMTInput {
    const {callee, heap, args} = expr;
    return `(eff${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")})`;
  }

  visitVariable(expr: Syntax.Variable): SMTInput {
    return "v_" + expr;
  }

  visitHeapReference(expr: Syntax.HeapReference): SMTInput {
    return `(select ${this.visitHeapExpr(expr.heap)} ${this.visitLocation(expr.loc)})`;
  }
  
  visitLiteral(expr: Syntax.Literal): SMTInput {
    if (expr.value === undefined) return `jsundefined`;
    if (expr.value === null) return `jsnull`;
    switch (typeof expr.value) {
      case "boolean": return `(jsbool ${expr.value})`;
      case "number": return `(jsnum ${expr.value})`;
      case "string": return `(jsstr "${expr.value}")`;
      default: throw new Error("unreachable");
    }
  }
  
  visitArrayExpression(expr: Syntax.ArrayExpression): SMTInput {
    const arrayToSMT = (elements: Array<A>): SMTInput => {
      if (elements.length === 0) return `empty`;
      const [head, ...tail] = elements;
      const h = head || {type: "Literal", value: "undefined"};
      return `(cons ${this.visitExpr(h)} ${arrayToSMT(tail)})`;
    };
    return `(jsarr ${arrayToSMT(expr.elements)})`;
  }
  
  visitUnaryExpression(expr: Syntax.UnaryExpression): SMTInput {
    const arg = this.visitExpr(expr.argument),
          op = unOpToSMT[expr.operator];
    return `(${op} ${arg})`;
  }
  
  visitBinaryExpression(expr: Syntax.BinaryExpression): SMTInput {
    const left = this.visitExpr(expr.left),
          right = this.visitExpr(expr.right),
          binop = binOpToSMT[expr.operator];
    return `(${binop} ${left} ${right})`;
  }
  
  visitConditionalExpression(expr: Syntax.ConditionalExpression): SMTInput {
    const test = this.visitProp(expr.test),
          then = this.visitExpr(expr.consequent),
          elze = this.visitExpr(expr.alternate);
    return `(ite ${test} ${then} ${elze})`;
  }
  
  visitCallExpression(expr: Syntax.CallExpression): SMTInput {
    const {callee, heap, args} = expr;
    return `(app${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")})`;
  }

  visitMemberExpression(expr: Syntax.MemberExpression): SMTInput {
    return `(field ${this.visitExpr(expr.object)} "${expr.property}")`;
  }

  visitTruthy(prop: Syntax.Truthy): SMTInput {
    if (typeof(prop.expr) == "object" &&
        prop.expr.type == "ConditionalExpression" &&
        typeof(prop.expr.consequent) == "object" &&
        prop.expr.consequent.type == "Literal" &&
        prop.expr.consequent.value === true &&
        typeof(prop.expr.alternate) == "object" &&
        prop.expr.alternate.type == "Literal" &&
        prop.expr.alternate.value === false) {
      return this.visitProp(prop.expr.test);
    }
    return `(_truthy ${this.visitExpr(prop.expr)})`;
  }
  
  visitAnd(prop: Syntax.And): SMTInput {
    const clauses: Array<SMTInput> = flatMap(prop.clauses,
      c => c.type == "And" ? c.clauses : [c]) 
      .map(p => this.visitProp(p))
      .filter(s => s != `true`);
    if (clauses.find(s => s == `false`)) return `false`;
    if (clauses.length == 0) return `true`;
    if (clauses.length == 1) return clauses[0];
    return `(and ${clauses.join(' ')})`;
  }
  
  visitOr(prop: Syntax.Or): SMTInput {
    const clauses: Array<SMTInput> = flatMap(prop.clauses,
      c => c.type == "Or" ? c.clauses : [c]) 
      .map(p => this.visitProp(p))
      .filter(s => s != `false`);
    if (clauses.find(s => s == `true`)) return `true`;
    if (clauses.length == 0) return `false`;
    if (clauses.length == 1) return clauses[0];
    return `(or ${clauses.join(' ')})`;
  }
  
  visitEq(prop: Syntax.Eq): SMTInput {
    const left: SMTInput = this.visitExpr(prop.left);
    const right: SMTInput = this.visitExpr(prop.right);
    if (left == right) return `true`;
    return `(= ${left} ${right})`;
  }
  
  visitHeapEq(prop: Syntax.HeapEq): SMTInput {
    const left: SMTInput = this.visitHeapExpr(prop.left);
    const right: SMTInput = this.visitHeapExpr(prop.right);
    if (left == right) return `true`;
    return `(= ${left} ${right})`;
  }
  
  visitNot(prop: Syntax.Not): SMTInput {
    const arg: SMTInput = this.visitProp(prop.arg);
    if (arg == "true") return `false`;
    if (arg == "false") return `true`;
    return `(not ${arg})`;
  }
  
  visitTrue(prop: Syntax.True): SMTInput {
    return `true`;
  }
  
  visitFalse(prop: Syntax.False): SMTInput {
    return `false`;
  }
  
  visitPrecondition(prop: Syntax.Precondition): SMTInput {
    const {callee, heap, args} = prop;
    return `(pre${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")})`;
  }
  
  visitPostcondition(prop: Syntax.Postcondition): SMTInput {
    const {callee, heap, args} = prop;
    return `(post${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")})`;
  }
  
  visitForAllCalls(prop: Syntax.ForAllCalls): SMTInput {
    const {callee, heap, args} = prop;
    const params = `${args.map(a => `(${this.visitVariable(a)} JSVal)`).join(' ')}`;
    const callP: P = { type: "CallTrigger", callee, heap, args: args };
    let p = this.visitProp(implies(callP, prop.prop));
    if (prop.existsLocs.size + prop.existsHeaps.size + prop.existsVars.size > 0) {
      p = `(exists (${[...prop.existsHeaps].map(h => `(${this.visitHeap(h)} Heap)`).join(' ')} `
                 + `${[...prop.existsLocs].map(l => `(${this.visitLocation(l)} Loc)`).join(' ')} `
                 + `${[...prop.existsVars].map(v => `(${this.visitVariable(v)} JSVal)`).join(' ')})\n  ${p})`;
    }
    const trigger: SMTInput = this.visitProp(callP);
    return `(forall ((${this.visitHeap(heap)} Heap) ${params}) (!\n  ${p}\n  :pattern (${trigger})))`;
  }
  
  visitCallTrigger(prop: Syntax.CallTrigger): SMTInput {
    const {callee, heap, args} = prop;
    return `(call${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")})`;
  }

  visitForAllAccess(prop: Syntax.ForAllAccess): SMTInput {
    const accessP: P = { type: "AccessTrigger", object: "this" };
    let p = this.visitProp(implies(accessP, prop.prop));
    const trigger: SMTInput = this.visitProp(accessP);
    return `(forall ((${this.visitVariable("this")} JSVal)) (!\n  ${p}\n  :pattern (${trigger})))`;
  }

  visitInstanceOf(prop: Syntax.InstanceOf): SMTInput {
    return `(instanceof ${this.visitExpr(prop.left)} ${this.visitClassName(prop.right)})`;
  }

  visitHasProperty(prop: Syntax.HasProperty): SMTInput {
    return `(has ${this.visitExpr(prop.object)} "${prop.property}")`;
  }

  visitAccessTrigger(prop: Syntax.AccessTrigger): SMTInput {
    return `(access ${this.visitExpr(prop.object)})`;
  }
}

function propositionToSMT(prop: P): SMTInput {
  const v = new SMTGenerator();
  return v.visitProp(prop);
}

function propositionToAssert(prop: P): SMTInput {
  if (prop.type == "And") {
    return prop.clauses.map(propositionToAssert).join("");
  }
  return `(assert ${propositionToSMT(prop)})\n`;
}

export function vcToSMT(classes: Classes, heaps: Heaps, locs: Locs, vars: Vars, freeVars: Vars, p: P): SMTInput {
  const prop = options.qi ? instantiateQuantifiers(heaps, locs, vars, p) : p;
  return `(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

; Values in JavaScript
(declare-datatypes () (
  (JSVal
    (jsnum (numv Int))
    (jsbool (boolv Bool))
    (jsstr (strv String))
    jsnull
    jsundefined
    (jsarr (items JSValList))
    (jsobj (oidx Int))
    (jsfun (fidx Int)))
  (JSValList empty (cons (car JSVal) (cdr JSValList)))))

; Types in JavaScript
(declare-datatypes () ((JSType JSNum JSBool JSString JSUndefined JSArray JSObj JSFunction)))

(define-fun _type ((x JSVal)) JSType
  (ite (is-jsnum x) JSNum
  (ite (is-jsbool x) JSBool
  (ite (is-jsstr x) JSString
  (ite (is-jsnull x) JSObj
  (ite (is-jsundefined x) JSUndefined
  (ite (is-jsarr x) JSArray
  (ite (is-jsfun x) JSFunction
  JSObj))))))))

(define-fun _falsy ((x JSVal)) Bool
  (or (is-jsnull x)
      (is-jsundefined x)
      (and (is-jsnum x) (= (numv x) 0))
      (and (is-jsbool x) (not (boolv x)))
      (and (is-jsstr x) (= (strv x) ""))))

(define-fun _truthy ((x JSVal)) Bool
  (not (_falsy x)))

; typeof
(define-fun _js-typeof ((x JSVal)) JSVal
  (ite (is-jsnum x) (jsstr "number")
  (ite (is-jsbool x) (jsstr "boolean")
  (ite (is-jsstr x) (jsstr "string")
  (ite (is-jsundefined x) (jsstr "undefined")
  (ite (is-jsfun x) (jsstr "function")
  (jsstr "object")))))))

; -
(define-fun _js-negative ((x JSVal)) JSVal
  (ite (is-jsnum x) (jsnum (- (numv x)))
  jsundefined)) ; non-standard!

; +
(define-fun _js-positive ((x JSVal)) JSVal
  (ite (is-jsnum x) x
  jsundefined)) ; non-standard!

; !
(define-fun _js-not ((x JSVal)) JSVal
  (jsbool (_falsy x)))

; ~
(define-fun _js-bnot ((x JSVal)) JSVal
  (ite (is-jsnum x) (jsnum (bv2int (bvneg ((_ int2bv 32) (numv x)))))
  jsundefined)) ; non-standard!

; void
(define-fun _js-void ((x JSVal)) JSVal
  jsundefined)

; ==
(define-fun _js-eq ((a JSVal) (b JSVal)) JSVal
  (jsbool (= a b))) ; non-standard!

; !=
(define-fun _js-neq ((a JSVal) (b JSVal)) JSVal
  (jsbool (not (= a b)))) ; non-standard!

; <
(define-fun _js_lt ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsbool (< (numv a) (numv b)))
    (jsbool false))) ; non-standard!

; <=
(define-fun _js_leq ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsbool (<= (numv a) (numv b)))
    (jsbool false))) ; non-standard!

; >
(define-fun _js_gt ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsbool (> (numv a) (numv b)))
    (jsbool false))) ; non-standard!

; >=
(define-fun _js-geq ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsbool (>= (numv a) (numv b)))
    (jsbool false))) ; non-standard!

; +
(define-fun _js-plus ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (+ (numv a) (numv b)))
  (ite (and (is-jsstr a) (is-jsstr b))
    (jsstr (str.++ (strv a) (strv b)))
  jsundefined))) ; non-standard!

; -
(define-fun _js-minus ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (- (numv a) (numv b)))
  jsundefined)) ; non-standard!

; *
(define-fun _js-multiply ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (* (numv a) (numv b)))
  jsundefined)) ; non-standard!

; /
(define-fun _js-divide ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (div (numv a) (numv b)))
  jsundefined)) ; non-standard!

; %
(define-fun _js-mod ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (rem (numv a) (numv b)))
  jsundefined)) ; non-standard!

; <<
(define-fun _js-lshift ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (bv2int (bvshl ((_ int2bv 32) (numv a)) ((_ int2bv 32) (numv b)))))
  jsundefined)) ; non-standard!

; >>
(define-fun _js-rshift ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (bv2int (bvashr ((_ int2bv 32) (numv a)) ((_ int2bv 32) (numv b)))))
  jsundefined)) ; non-standard!

; >>>
(define-fun _js-rzshift ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (bv2int (bvlshr ((_ int2bv 32) (numv a)) ((_ int2bv 32) (numv b)))))
  jsundefined)) ; non-standard!

; |
(define-fun _js-bor ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (bv2int (bvor ((_ int2bv 32) (numv a)) ((_ int2bv 32) (numv b)))))
  jsundefined)) ; non-standard!

; ^
(define-fun _js-bxor ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (bv2int (bvxor ((_ int2bv 32) (numv a)) ((_ int2bv 32) (numv b)))))
  jsundefined)) ; non-standard!

; &
(define-fun _js-band ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (bv2int (bvand ((_ int2bv 32) (numv a)) ((_ int2bv 32) (numv b)))))
  jsundefined)) ; non-standard!

; Heap

(declare-sort Loc)
(define-sort Heap () (Array Loc JSVal))

; Functions
${[...Array(10).keys()].map(i => `
(declare-fun pre${i} (JSVal Heap ${[...Array(i).keys()].map(_ => ' JSVal').join('')}) Bool)
(declare-fun post${i} (JSVal Heap ${[...Array(i).keys()].map(_ => ' JSVal').join('')}) Bool)
(declare-fun app${i} (JSVal Heap ${[...Array(i).keys()].map(_ => ' JSVal').join('')}) JSVal)
(declare-fun eff${i} (JSVal Heap ${[...Array(i).keys()].map(_ => ' JSVal').join('')}) Heap)
(declare-fun call${i} (JSVal Heap ${[...Array(i).keys()].map(_ => ' JSVal').join('')}) Bool)`).join('')}

; Objects
(declare-sort ClassName)
(declare-fun has (JSVal String) Bool)
(declare-fun field (JSVal String) JSVal)
(declare-fun instanceof (JSVal ClassName) Bool)
(declare-fun access (JSVal) Bool)

; Declarations

${[...classes].map(c => `(declare-const c_${c} ClassName)\n`).join('')}
${classes.size == 0 ? '' : `(assert (distinct ${[...classes].map(c => 'c_'+c).join(' ')}))`}
${[...heaps].map(h => `(declare-const h_${h} Heap)\n`).join('')}
${[...locs].map(l => `(declare-const l_${l} Loc)\n`).join('')}
${locs.size == 0 ? '' : `(assert (distinct ${[...locs].map(l => 'l_'+l).join(' ')}))`}
${[...vars].map(v => `(declare-const v_${v} JSVal)\n`).join('')}

; Verification condition

${propositionToAssert(prop)}

(check-sat)
(get-value (${[...freeVars].map(v => `v_${v}`).join(' ')}))`;
}

function modelError(smt: SMTOutput): MessageException {
  const loc = { file: options.filename, start: { line: 0, column: 0}, end: { line: 0, column: 0} };
  return new MessageException({ status: "error", type: "unrecognized-model", loc, description: `cannot parse ${smt}` });
}

function smtToArray(smt: SMTOutput): Array<any> {
  const s = smt.trim();
  if (s == "empty") return [];
  const m = s.match(/^\(cons (\w+|\(.*\))\ (.*)\)$/);
  if (!m) throw modelError(s);
  const [, h, t] = m;
  return [smtToValue(h)].concat(smtToArray(t));
}

function smtToValue(smt: SMTOutput): any {
  const s = smt.trim();
  if (s == "jsundefined") return undefined;
  if (s == "jsnull") return null;
  const m = s.match(/^\((\w+)\ (.*)\)$/);
  if (!m) throw modelError(s);
  const [, tag, v] = m;
  if (tag.startsWith("jsfun")) return ()=>0;
  switch (tag) {
    case "jsbool": return v == "true";
    case "jsnum": const neg = v.match(/\(- ([0-9]+)\)/); return neg ? -neg[1] : +v;
    case "jsstr": return v.substr(1, v.length - 2);
    case "jsarr": return smtToArray(v);
    case "jsobj": return {};
    default: throw modelError(tag);
  }
}

export type Model = { [varName: string]: any };

export function smtToModel(smt: SMTOutput): Model {
  // assumes smt starts with "sat", so remove "sat"
  smt = smt.slice(3, smt.length);
  if (smt.trim().startsWith("(error")) return {};

  // remove outer parens
  smt = smt.trim().slice(2, smt.length - 4);
  const model: Model = {};
  smt.split(/\)\s+\(/m).forEach(str => {
    // these are now just pairs of varname value
    const both = str.trim().split(" ");
    if (both.length < 2) return;
    const name = both[0].trim(),
          value = both.slice(1, both.length).join(" ").trim();
    const val = smtToValue(value);
    model[name.substr(2)] = val;
  });
  return model;
}