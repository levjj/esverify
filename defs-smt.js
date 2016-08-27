export const preamble = `

; Values in JavaScript
(declare-datatypes () (
  (JSVal
    (jsnum (numv Int))
    (jsbool (boolv Bool))
    (jsstr (strv String))
    jsnull
    jsundefined
    (jsarray (items JSValList))
    (jsobj (props JSPropList)))
  (JSValList empty (cons (car JSVal) (cdr JSValList)))
  (JSProp (prop (key (List Int)) (val JSVal)))
  (JSPropList empty (cons (car JSProp) (cdr JSPropList)))))

; Types in JavaScript
(declare-datatypes () ((JSType JSNum JSBool JSString JSUndefined JSArray JSObj)))

(define-fun _type ((x JSVal)) JSType
  (ite (is-jsnum x) JSNum
  (ite (is-jsbool x) JSBool
  (ite (is-jsstring x) JSString
  (ite (is-jsnull x) JSObj
  (ite (is-jsundefined x) JSUndefined
  (ite (is-jsarray x) JSArray
  JSObj)))))))

(define-fun _falsy ((x JSVal)) Bool
  (or (is-jsnull x)
      (is-jsundefined x)
      (and (is-jsnum x) (= (numv x) 0))
      (and (is-jsbool x) (not (boolv x)))
      (and (is-jsstring x) (= (strval x) ""))))

(define-fun _truthy ((x JSVal)) Bool
  (not (_falsy x)))

; typeof
(define-fun _js-typeof ((x JSVal)) JSVal
  (ite (is-jsnum x) (jsstr "number")
  (ite (is-jsbool x) (jsstr "boolean")
  (ite (is-jsstring x) (jsstr "string")
  (ite (is-jsundefined x) (jsstr "undefined")
  (jsstr "object"))))))

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
  (ite (is-jsnum x) (jsnum (bv2int (bvneg (int2bv (numv x)))))
  jsundefined)) ; non-standard!

; void
(define-fun _js-void ((x JSVal)) JSVal
  jsundefined)

; ==
(define-fun _js-eq ((a JSVal) (b JSVal)) JSVal
  (= a b)) ; non-standard!

; !=
(define-fun _js-neq ((a JSVal) (b JSVal)) JSVal
  (not (= a b))) ; non-standard!

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
    (jsnum (/ (numv a) (numv b)))
  jsundefined)) ; non-standard!

; %
(define-fun _js-mod ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsnum a) (is-jsnum b))
    (jsnum (rem (numv a) (numv b)))
  jsundefined)) ; non-standard!

; <<
(define-fun _js-lshift ((a JSVal) (b JSVal)) JSVal

; >>
(define-fun _js-rshift ((a JSVal) (b JSVal)) JSVal

; >>>
(define-fun _js-rzshift ((a JSVal) (b JSVal)) JSVal

; |
(define-fun _js-bor ((a JSVal) (b JSVal)) JSVal

; ^
(define-fun _js-bxor ((a JSVal) (b JSVal)) JSVal

; &
(define-fun _js-band ((a JSVal) (b JSVal)) JSVal


`;
