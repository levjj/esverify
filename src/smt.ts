import { P, Vars, Locs, Heap, SMTInput, propositionToAssert, propositionToSMT } from "./propositions";

export default function smt(heap: Heap, locs: Locs, vars: Vars, prop: P, vc: P): SMTInput {
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
    (jsarray (items JSValList))
    (jsobj (props JSPropList))
    (jsfun (idx Int)))
  (JSValList empty (cons (car JSVal) (cdr JSValList)))
  (JSProp (prop (key (List Int)) (val JSVal)))
  (JSPropList empty (cons (car JSProp) (cdr JSPropList)))))

; Types in JavaScript
(declare-datatypes () ((JSType JSNum JSBool JSString JSUndefined JSArray JSObj JSFunction)))

(define-fun _type ((x JSVal)) JSType
  (ite (is-jsnum x) JSNum
  (ite (is-jsbool x) JSBool
  (ite (is-jsstr x) JSString
  (ite (is-jsnull x) JSObj
  (ite (is-jsundefined x) JSUndefined
  (ite (is-jsarray x) JSArray
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

(declare-fun pre0 (JSVal Heap) Bool)
(declare-fun pre1 (JSVal Heap JSVal) Bool)
(declare-fun pre2 (JSVal Heap JSVal JSVal) Bool)
(declare-fun post0 (JSVal Heap Heap) Bool)
(declare-fun post1 (JSVal Heap Heap JSVal) Bool)
(declare-fun post2 (JSVal Heap Heap JSVal JSVal) Bool)
(declare-fun app0 (JSVal Heap) JSVal)
(declare-fun app1 (JSVal Heap JSVal) JSVal)
(declare-fun app2 (JSVal Heap JSVal JSVal) JSVal)
(declare-fun eff0 (JSVal Heap) Heap)
(declare-fun eff1 (JSVal Heap JSVal) Heap)
(declare-fun eff2 (JSVal Heap JSVal JSVal) Heap)
(declare-fun call0 (JSVal Heap Heap) Bool)
(declare-fun call1 (JSVal Heap Heap JSVal) Bool)
(declare-fun call2 (JSVal Heap Heap JSVal JSVal) Bool)

; Declarations

${[...vars].map(v => `(declare-const v_${v} JSVal)\n`).join('')}
${[...locs].map(v => `(declare-const l_${v} Loc)\n`).join('')}
${locs.size == 0 ? '' : `(assert (distinct ${[...locs].map(l => 'l_'+l).join(' ')}))`}

${[...Array(heap+1).keys()].map(h => `(declare-const h_${h} Heap)\n`).join('')}

; Antecedents

${propositionToAssert(prop)}

; Verification condition

(assert (not ${propositionToSMT(vc)}))

(check-sat)
(get-value (${[...vars].map(v => `v_${v}`).join(' ')}))`;
}
