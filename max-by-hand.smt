; -----------------------------------------
; JavaScript Preamble
; -----------------------------------------

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

; -----------------------------------------
; Example Code: max()
; -----------------------------------------

;function max(a, b) {
;  requires(typeof(a) == "number");
;  requires(typeof(b) == "number");
;  ensures(max(a,b) >= a);
;  if (a >= b) {
;    return a;
;  } else {
;    return b;
;  }
;}

; Encoded as a function

(define-fun _max ((a JSVal) (b JSVal)) JSVal
  (ite (_js-truthy (_js-geq a b)) a b))

; Specification as single constraint

(assert (forall ((a JSVal) (b JSVal)) (=> (and (= (_js-typeof a) JSNum)
                                               (= (_js-typeof b) JSNum))
                                          (_js-truthy (_js-geq (_max a b) a)))))

; Encoded as a method

;function max(a, b) {
;  t1 = a >= b;
;  if (t1) {
;    t2 = a;
;  }
;  if (!t1) {
;    t2 = b;
;  }
;  return t2;
;}

; Specification as constraint system over free variables a and b

(declare-const a JSVal)
(declare-const b JSVal)

(assert (= (_js-typeof a) JSNum))
(assert (= (_js-typeof b) JSNum))

(declare-const t1 JSVal)
(declare-const t2 JSVal)

(assert (= t1 (_js-geq a b)))
(assert (= t1 (_js-geq a b)))
(assert (=> (_js-truthy t1) (= t2 a)))
(assert (=> (not (_js-truthy t1)) (= t2 b)))

(assert (not (_js-truthy (_js-geq t2 a))))

(check-sat)
(get-model)
