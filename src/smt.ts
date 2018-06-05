import { Classes, FreeVars, Heap, Heaps, Locs, P, Syntax, Vars, Visitor, implies } from './logic';
import { options } from './options';
import { instantiateQuantifiers } from './qi';
import { flatMap } from './util';

export type SMTInput = string;
export type SMTOutput = string;

const unOpToSMT: {[unop: string]: SMTInput} = {
  '-': '_js-negative',
  '+': '_js-positive',
  '!': '_js-not',
  '~': '_js-bnot',
  'typeof': '_js-typeof',
  'void': '_js-void'
};

const binOpToSMT: {[binop: string]: SMTInput} = {
  '===': '_js-eq',
  '!==': '_js-neq',
  '<': '_js_lt',
  '<=': '_js_leq',
  '>': '_js_gt',
  '>=': '_js-geq',
  '+': '_js-plus',
  '-': '_js-minus',
  '*': '_js-multiply',
  '/': '_js-divide',
  '%': '_js-mod',
  '<<': '_js-lshift',
  '>>': '_js-rshift',
  '>>>': '_js-rzshift',
  '|': '_js-bor',
  '^': '_js-bxor',
  '&': '_js-band',
  'in': '_js-in', // unsupported
  'instanceof': '_js-instanceof' // unsupported
};

class SMTGenerator extends Visitor<SMTInput, SMTInput, SMTInput, SMTInput> {

  visitLocation (loc: Syntax.Location): SMTInput {
    return 'l_' + loc;
  }

  visitHeap (heap: Heap): SMTInput {
    return 'h_' + heap;
  }

  visitClassName (cls: Syntax.ClassName): SMTInput {
    return 'c_' + cls;
  }

  visitHeapStore (expr: Syntax.HeapStore): SMTInput {
    return `(store ${this.visitHeapExpr(expr.target)} ${this.visitLocation(expr.loc)} ${this.visitExpr(expr.expr)})`;
  }

  visitHeapEffect (expr: Syntax.HeapEffect): SMTInput {
    const { callee, heap, thisArg, args } = expr;
    return `(eff${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)} ` +
             `${this.visitExpr(thisArg)}${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitVariable (expr: Syntax.Variable): SMTInput {
    return 'v_' + expr;
  }

  visitHeapReference (expr: Syntax.HeapReference): SMTInput {
    return `(select ${this.visitHeapExpr(expr.heap)} ${this.visitLocation(expr.loc)})`;
  }

  visitLiteral (expr: Syntax.Literal): SMTInput {
    if (expr.value === undefined) return `jsundefined`;
    if (expr.value === null) return `jsnull`;
    if (typeof expr.value === 'boolean') {
      return `(jsbool ${expr.value})`;
    } else if (typeof expr.value === 'number') {
      return Number.isInteger(expr.value) ? `(jsint ${expr.value})` : `(jsreal ${expr.value})`;
    } else {
      return `(jsstr "${expr.value}")`;
    }
  }

  visitUnaryExpression (expr: Syntax.UnaryExpression): SMTInput {
    const arg = this.visitExpr(expr.argument);
    const op = unOpToSMT[expr.operator];
    return `(${op} ${arg})`;
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): SMTInput {
    const left = this.visitExpr(expr.left);
    const right = this.visitExpr(expr.right);
    const binop = binOpToSMT[expr.operator];
    return `(${binop} ${left} ${right})`;
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): SMTInput {
    if (expr.test.type === 'True') {
      return this.visitExpr(expr.consequent);
    } else if (expr.test.type === 'False') {
      return this.visitExpr(expr.alternate);
    } else {
      const test = this.visitProp(expr.test);
      const then = this.visitExpr(expr.consequent);
      const elze = this.visitExpr(expr.alternate);
      return `(ite ${test} ${then} ${elze})`;
    }
  }

  visitCallExpression (expr: Syntax.CallExpression): SMTInput {
    const { callee, heap, thisArg, args } = expr;
    return `(app${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)} ` +
            `${this.visitExpr(thisArg)}${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitNewExpression (expr: Syntax.NewExpression): SMTInput {
    if (expr.args.length === 0) {
      return `jsobj_${expr.className}`;
    } else {
      return `(jsobj_${expr.className}${expr.args.map(a => ' ' + this.visitExpr(a)).join('')})`;
    }
  }

  visitMemberExpression (expr: Syntax.MemberExpression): SMTInput {
    return `(field ${this.visitExpr(expr.object)} ${this.visitExpr(expr.property)})`;
  }

  visitArrayIndexExpression (expr: Syntax.ArrayIndexExpression): SMTInput {
    return `(arrelems (arrv ${this.visitExpr(expr.array)}) (intv ${this.visitExpr(expr.index)}))`;
  }

  visitRawSMTExpression (expr: Syntax.RawSMTExpression): SMTInput {
    let result = '';
    for (const e of expr.smt) {
      if (typeof e === 'string') {
        result += e;
      } else {
        result += this.visitExpr(e.e);
      }
    }
    return result;
  }

  visitIsIntegerExpression (expr: Syntax.IsIntegerExpression): SMTInput {
    return `(jsbool (is-jsint ${this.visitExpr(expr.expression)}))`;
  }

  visitToIntegerExpression (expr: Syntax.ToIntegerExpression): SMTInput {
    return `(jsint (_toint ${this.visitExpr(expr.expression)}))`;
  }

  visitTruthy (prop: Syntax.Truthy): SMTInput {
    if (typeof(prop.expr) === 'object' &&
        prop.expr.type === 'ConditionalExpression' &&
        typeof(prop.expr.consequent) === 'object' &&
        prop.expr.consequent.type === 'Literal' &&
        prop.expr.consequent.value === true &&
        typeof(prop.expr.alternate) === 'object' &&
        prop.expr.alternate.type === 'Literal' &&
        prop.expr.alternate.value === false) {
      return this.visitProp(prop.expr.test);
    }
    return `(_truthy ${this.visitExpr(prop.expr)})`;
  }

  visitAnd (prop: Syntax.And): SMTInput {
    const clauses: Array<SMTInput> = flatMap(prop.clauses,
      c => c.type === 'And' ? c.clauses : [c])
      .map(p => this.visitProp(p))
      .filter(s => s !== `true`);
    if (clauses.find(s => s === `false`)) return `false`;
    if (clauses.length === 0) return `true`;
    if (clauses.length === 1) return clauses[0];
    return `(and ${clauses.join(' ')})`;
  }

  visitOr (prop: Syntax.Or): SMTInput {
    const clauses: Array<SMTInput> = flatMap(prop.clauses,
      c => c.type === 'Or' ? c.clauses : [c])
      .map(p => this.visitProp(p))
      .filter(s => s !== `false`);
    if (clauses.find(s => s === `true`)) return `true`;
    if (clauses.length === 0) return `false`;
    if (clauses.length === 1) return clauses[0];
    return `(or ${clauses.join(' ')})`;
  }

  visitEq (prop: Syntax.Eq): SMTInput {
    const left: SMTInput = this.visitExpr(prop.left);
    const right: SMTInput = this.visitExpr(prop.right);
    if (left === right) return `true`;
    return `(= ${left} ${right})`;
  }

  visitHeapEq (prop: Syntax.HeapEq): SMTInput {
    const left: SMTInput = this.visitHeapExpr(prop.left);
    const right: SMTInput = this.visitHeapExpr(prop.right);
    if (left === right) return `true`;
    return `(= ${left} ${right})`;
  }

  visitNot (prop: Syntax.Not): SMTInput {
    const arg: SMTInput = this.visitProp(prop.arg);
    if (arg === 'true') return `false`;
    if (arg === 'false') return `true`;
    return `(not ${arg})`;
  }

  visitTrue (prop: Syntax.True): SMTInput {
    return `true`;
  }

  visitFalse (prop: Syntax.False): SMTInput {
    return `false`;
  }

  visitPrecondition (prop: Syntax.Precondition): SMTInput {
    const { callee, heap, thisArg, args } = prop;
    return `(pre${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)} ` +
             `${this.visitExpr(thisArg)}${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitPostcondition (prop: Syntax.Postcondition): SMTInput {
    const { callee, heap, thisArg, args } = prop;
    return `(post${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)} ` +
            `${this.visitExpr(thisArg)}${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): SMTInput {
    const { callee, heap, args, fuel } = prop;
    const params = `${args.map(a => `(${this.visitVariable(a)} JSVal)`).join(' ')}`;
    const callP: P = { type: 'CallTrigger', callee, heap, thisArg: prop.thisArg, args, fuel };
    let p = this.visitProp(implies(callP, prop.prop));
    if (prop.existsLocs.size + prop.existsHeaps.size + prop.existsVars.size > 0) {
      p = `(exists (${[...prop.existsHeaps].map(h => `(${this.visitHeap(h)} Heap)`).join(' ')} `
                 + `${[...prop.existsLocs].map(l => `(${this.visitLocation(l)} Loc)`).join(' ')} `
                 + `${[...prop.existsVars].map(v => `(${this.visitVariable(v)} JSVal)`).join(' ')})\n  ${p})`;
    }
    const trigger: SMTInput = this.visitProp(callP);
    return `(forall ((${this.visitHeap(heap)} Heap) `
                  + `(${this.visitVariable(prop.thisArg)} JSVal) `
                  + `${params}) (!\n  ${p}\n  :pattern ${trigger}))`;
  }

  visitCallTrigger (prop: Syntax.CallTrigger): SMTInput {
    const { callee, heap, thisArg, args } = prop;
    return `(call${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)} ` +
            `${this.visitExpr(thisArg)}${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): SMTInput {
    const { heap, fuel } = prop;
    const accessP: P = { type: 'AccessTrigger', object: prop.thisArg, property: 'thisProp', heap, fuel };
    let p = this.visitProp(implies(accessP, prop.prop));
    const trigger: SMTInput = this.visitProp(accessP);
    return `(forall ((${this.visitVariable(prop.thisArg)} JSVal) `
                  + `(${this.visitVariable('thisProp')} JSVal) `
                  + `(${this.visitHeap(heap)} Heap)) (!\n  ${p}\n  :pattern ${trigger}))`;
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): SMTInput {
    const { heap, fuel } = prop;
    const accessP: P = { type: 'AccessTrigger', object: prop.object, property: prop.property, heap, fuel };
    let p = this.visitProp(implies(accessP, prop.prop));
    const trigger: SMTInput = this.visitProp(accessP);
    return `(forall ((${this.visitVariable(prop.property)} JSVal) `
                  + `(${this.visitHeap(heap)} Heap)) (!\n  ${p}\n  :pattern ${trigger}))`;
  }

  visitInstanceOf (prop: Syntax.InstanceOf): SMTInput {
    const instCheck = `(instanceof ${this.visitExpr(prop.left)} ${this.visitClassName(prop.right)})`;
    if (prop.right === 'String') {
      return `(or (is-jsstr ${this.visitExpr(prop.left)}) ${instCheck})`;
    } else {
      return instCheck;
    }
  }

  visitHasProperty (prop: Syntax.HasProperty): SMTInput {
    return `(has ${this.visitExpr(prop.object)} ${this.visitExpr(prop.property)})`;
  }

  visitHasProperties (prop: Syntax.HasProperties): SMTInput {
    const empty = '((as const (Array String Bool)) false)';
    const str = prop.properties.reduceRight((prev, curr) => `(store ${prev} "${curr}" true)`, empty);
    return `(= (objproperties (objv ${this.visitExpr(prop.object)})) ${str})`;
  }

  visitInBounds (prop: Syntax.InBounds): SMTInput {
    const indexExpr = this.visitExpr(prop.index);
    return `(and (is-jsint ${indexExpr}) `
              + `(>= (intv ${indexExpr}) 0) `
              + `(< (intv ${indexExpr}) (arrlength (arrv ${this.visitExpr(prop.array)}))))`;
  }

  visitAccessTrigger (prop: Syntax.AccessTrigger): SMTInput {
    return `(access ${this.visitExpr(prop.object)} ${this.visitExpr(prop.property)} ${this.visitHeapExpr(prop.heap)})`;
  }
}

export function propositionToSMT (prop: P): SMTInput {
  const v = new SMTGenerator();
  return v.visitProp(prop);
}

function propositionToAssert (prop: P): SMTInput {
  if (prop.type === 'And') {
    return prop.clauses.map(propositionToAssert).join('');
  }
  return `(assert ${propositionToSMT(prop)})\n`;
}

export function vcToSMT (classes: Classes, heaps: Heaps, locs: Locs, vars: Vars, freeVars: FreeVars, p: P): SMTInput {
  const prop = options.qi ? instantiateQuantifiers(heaps, locs, vars, freeVars, p) : p;
  const regClasses: Classes = new Set([...classes].filter(c => c.cls !== 'Array'));
  const strClass = [...classes].find(({ cls }) => cls === 'String');
  if (strClass === undefined) throw new Error('cannot find String class');
  return `(set-option :produce-models true)
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-sort Func 0) ; function reference
(declare-sort Obj 0) ; object reference
(declare-sort Arr 0) ; array reference

; Values in JavaScript
(declare-datatypes () ((JSVal
  (jsint (intv Int))
  (jsreal (realv Real))
  (jsbool (boolv Bool))
  (jsstr (strv String))
  (jsnull)
  (jsundefined)
  (jsfun (funv Func))
  (jsobj (objv Obj))
  (jsobj_Array (arrv Arr))
${[...regClasses].map(({ cls, fields }) =>
  fields.length === 0
  ? `    jsobj_${cls}\n`
  : `    (jsobj_${cls} ${fields.map(field => `(${cls}-${field} JSVal)`).join(' ')})\n`
).join('')})))

(define-fun _tostring ((x JSVal)) String
  (ite (is-jsint x) (int.to.str (intv x))
  (ite (is-jsreal x) (int.to.str (to_int (realv x)))
  (ite (is-jsbool x) (ite (boolv x) "true" "false")
  (ite (is-jsstr x) (strv x)
  (ite (is-jsnull x) "null"
  (ite (is-jsundefined x) "undefined"
  (ite (is-jsfun x) "function () { ... }"
${[...classes].map(({ cls }) =>
  `  (ite (is-jsobj_${cls} x) "[object ${cls}]"`).join('\n')}
  "[object Object]"${[...classes].map(c => ')').join('')}))))))))

(define-fun _toint ((x JSVal)) Int
  (ite (is-jsint x) (intv x)
  (ite (is-jsreal x) (to_int (realv x))
  (ite (is-jsbool x) (ite (boolv x) 1 0)
  (ite (is-jsstr x) (str.to.int (strv x))
  -1)))))

(define-fun _falsy ((x JSVal)) Bool
  (or (is-jsnull x)
      (is-jsundefined x)
      (and (is-jsint x) (= (intv x) 0))
      (and (is-jsreal x) (= (realv x) 0))
      (and (is-jsbool x) (not (boolv x)))
      (and (is-jsstr x) (= (strv x) ""))))

(define-fun _truthy ((x JSVal)) Bool
  (not (_falsy x)))

; typeof
(define-fun _js-typeof ((x JSVal)) JSVal
  (ite (is-jsint x) (jsstr "number")
  (ite (is-jsreal x) (jsstr "number")
  (ite (is-jsbool x) (jsstr "boolean")
  (ite (is-jsstr x) (jsstr "string")
  (ite (is-jsundefined x) (jsstr "undefined")
  (ite (is-jsfun x) (jsstr "function")
  (jsstr "object"))))))))

; -
(define-fun _js-negative ((x JSVal)) JSVal
  (ite (is-jsint x) (jsint (- (intv x)))
  (ite (is-jsreal x) (jsreal (- (realv x)))
  jsundefined)))

; +
(define-fun _js-positive ((x JSVal)) JSVal
  (ite (is-jsint x) x
  (ite (is-jsreal x) x
  jsundefined)))

; !
(define-fun _js-not ((x JSVal)) JSVal
  (jsbool (_falsy x)))

; ~
(define-fun _js-bnot ((x JSVal)) JSVal
  (ite (is-jsint x) (jsint (bv2int (bvneg ((_ int2bv 32) (intv x)))))
  jsundefined))

; void
(define-fun _js-void ((x JSVal)) JSVal
  jsundefined)

; ==
(define-fun _js-eq ((a JSVal) (b JSVal)) JSVal
  (jsbool (= a b)))

; !=
(define-fun _js-neq ((a JSVal) (b JSVal)) JSVal
  (jsbool (not (= a b))))

; <
(define-fun _js_lt ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b)) (jsbool (< (intv a) (intv b)))
  (ite (and (is-jsint a) (is-jsreal b)) (jsbool (< (intv a) (realv b)))
  (ite (and (is-jsreal a) (is-jsint b)) (jsbool (< (realv a) (intv b)))
  (ite (and (is-jsreal a) (is-jsreal b)) (jsbool (< (realv a) (realv b)))
  (jsbool false))))))

; <=
(define-fun _js_leq ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b)) (jsbool (<= (intv a) (intv b)))
  (ite (and (is-jsint a) (is-jsreal b)) (jsbool (<= (intv a) (realv b)))
  (ite (and (is-jsreal a) (is-jsint b)) (jsbool (<= (realv a) (intv b)))
  (ite (and (is-jsreal a) (is-jsreal b)) (jsbool (<= (realv a) (realv b)))
  (jsbool false))))))

; >
(define-fun _js_gt ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b)) (jsbool (> (intv a) (intv b)))
  (ite (and (is-jsint a) (is-jsreal b)) (jsbool (> (intv a) (realv b)))
  (ite (and (is-jsreal a) (is-jsint b)) (jsbool (> (realv a) (intv b)))
  (ite (and (is-jsreal a) (is-jsreal b)) (jsbool (> (realv a) (realv b)))
  (jsbool false))))))

; >=
(define-fun _js-geq ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b)) (jsbool (>= (intv a) (intv b)))
  (ite (and (is-jsint a) (is-jsreal b)) (jsbool (>= (intv a) (realv b)))
  (ite (and (is-jsreal a) (is-jsint b)) (jsbool (>= (realv a) (intv b)))
  (ite (and (is-jsreal a) (is-jsreal b)) (jsbool (>= (realv a) (realv b)))
  (jsbool false))))))

; +
(define-fun _js-plus ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b)) (jsint (+ (intv a) (intv b)))
  (ite (and (is-jsint a) (is-jsreal b)) (jsreal (+ (intv a) (realv b)))
  (ite (and (is-jsreal a) (is-jsint b)) (jsreal (+ (realv a) (intv b)))
  (ite (and (is-jsreal a) (is-jsreal b)) (jsreal (+ (realv a) (realv b)))
  (ite (and (is-jsstr a) (is-jsstr b)) (jsstr (str.++ (strv a) (strv b)))
  jsundefined))))))

; -
(define-fun _js-minus ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b)) (jsint (- (intv a) (intv b)))
  (ite (and (is-jsint a) (is-jsreal b)) (jsreal (- (intv a) (realv b)))
  (ite (and (is-jsreal a) (is-jsint b)) (jsreal (- (realv a) (intv b)))
  (ite (and (is-jsreal a) (is-jsreal b)) (jsreal (- (realv a) (realv b)))
  jsundefined)))))

; *
(define-fun _js-multiply ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b)) (jsint (* (intv a) (intv b)))
  (ite (and (is-jsint a) (is-jsreal b)) (jsreal (* (intv a) (realv b)))
  (ite (and (is-jsreal a) (is-jsint b)) (jsreal (* (realv a) (intv b)))
  (ite (and (is-jsreal a) (is-jsreal b)) (jsreal (* (realv a) (realv b)))
  jsundefined)))))

; /
(define-fun _js-divide ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b))
    (ite (is_int (/ (intv a) (intv b))) (jsint (/ (intv a) (intv b)))
                                        (jsreal (/ (intv a) (intv b))))
  (ite (and (is-jsint a) (is-jsreal b)) (jsreal (/ (intv a) (realv b)))
  (ite (and (is-jsreal a) (is-jsint b)) (jsreal (/ (realv a) (intv b)))
  (ite (and (is-jsreal a) (is-jsreal b)) (jsreal (/ (realv a) (realv b)))
  jsundefined)))))

; %
(define-fun _js-mod ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b)) (jsint (rem (intv a) (intv b)))
  (ite (and (is-jsint a) (is-jsreal b)) (jsreal (rem (intv a) (realv b)))
  (ite (and (is-jsreal a) (is-jsint b)) (jsreal (rem (realv a) (intv b)))
  (ite (and (is-jsreal a) (is-jsreal b)) (jsreal (rem (realv a) (realv b)))
  jsundefined)))))

; <<
(define-fun _js-lshift ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b))
    (jsint (bv2int (bvshl ((_ int2bv 32) (intv a)) ((_ int2bv 32) (intv b)))))
  jsundefined))

; >>
(define-fun _js-rshift ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b))
    (jsint (bv2int (bvashr ((_ int2bv 32) (intv a)) ((_ int2bv 32) (intv b)))))
  jsundefined))

; >>>
(define-fun _js-rzshift ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b))
    (jsint (bv2int (bvlshr ((_ int2bv 32) (intv a)) ((_ int2bv 32) (intv b)))))
  jsundefined))

; |
(define-fun _js-bor ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b))
    (jsint (bv2int (bvor ((_ int2bv 32) (intv a)) ((_ int2bv 32) (intv b)))))
  jsundefined))

; ^
(define-fun _js-bxor ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b))
    (jsint (bv2int (bvxor ((_ int2bv 32) (intv a)) ((_ int2bv 32) (intv b)))))
  jsundefined))

; &
(define-fun _js-band ((a JSVal) (b JSVal)) JSVal
  (ite (and (is-jsint a) (is-jsint b))
    (jsint (bv2int (bvand ((_ int2bv 32) (intv a)) ((_ int2bv 32) (intv b)))))
  jsundefined))

; Heap

(declare-sort Loc 0)
(define-sort Heap () (Array Loc JSVal))

; Functions
${[...Array(10).keys()].map(i => `
(declare-fun pre${i} (JSVal Heap JSVal${[...Array(i).keys()].map(_ => ' JSVal').join('')}) Bool)
(declare-fun post${i} (JSVal Heap JSVal${[...Array(i).keys()].map(_ => ' JSVal').join('')}) Bool)
(declare-fun app${i} (JSVal Heap JSVal${[...Array(i).keys()].map(_ => ' JSVal').join('')}) JSVal)
(declare-fun eff${i} (JSVal Heap JSVal${[...Array(i).keys()].map(_ => ' JSVal').join('')}) Heap)
${options.qi ? '' : `(declare-fun call${i} (JSVal Heap JSVal${[...Array(i).keys()].map(_ => ' JSVal').join('')}) Bool)`}
`).join('')}
; Objects
(declare-datatypes () ((ClassName
  (c_Object)
  (c_Function)
  (c_ObjectLiteral)${[...classes].map(({ cls }) => `\n  (c_${cls})`).join('')})))

(declare-fun objproperties (Obj) (Array String Bool))
(declare-fun objfield (Obj String) JSVal)
(declare-fun arrlength (Arr) Int)
(declare-fun arrelems (Arr Int) JSVal)
${options.qi ? '' : '(declare-fun access (JSVal JSVal Heap) Bool)'}

(define-fun instanceof ((obj JSVal) (cls ClassName)) Bool
  (or (and (is-jsobj obj) (= cls c_Object))
      (and (is-jsobj obj) (= cls c_ObjectLiteral))
      (and (is-jsfun obj) (= cls c_Object))
      (and (is-jsfun obj) (= cls c_Function))
${[...classes].map(({ cls }) =>
`      (and (is-jsobj_${cls} obj) (= cls c_Object))
      (and (is-jsobj_${cls} obj) (= cls c_${cls}))`).join('\n')}
))

; Methods
${flatMap([...classes], ({ cls, methods }) => methods.map(method => ({ cls, method }))).map(({ cls, method }) =>
`(declare-fun v_${cls}.${method} () JSVal)\n`).join('')}

(define-fun has ((obj JSVal) (prop JSVal)) Bool
  (or (and (is-jsobj obj) (select (objproperties (objv obj)) (_tostring prop)))
      (and (is-jsstr obj) (= (_tostring prop) "length"))
      (and (is-jsstr obj) (is-jsint prop) (>= (intv prop) 0) (< (intv prop) (str.len (strv obj))))
      (and (is-jsstr obj) (is-jsreal prop) (is_int (realv prop))
                          (>= (realv prop) 0) (< (realv prop) (str.len (strv obj))))
      (and (is-jsstr obj) (>= (str.to.int (_tostring prop)) 0)
                          (< (str.to.int (_tostring prop)) (str.len (strv obj))))
${strClass.methods.map(method =>
`      (and (is-jsstr obj) (= (_tostring prop) "${method}"))`).join('\n')}
      (and (is-jsobj_String obj) (= (_tostring prop) "length"))
      (and (is-jsobj_String obj) (is-jsint prop) (>= (intv prop) 0) (< (intv prop) (str.len (strv (String-_str_ obj)))))
      (and (is-jsobj_String obj) (is-jsreal prop) (is_int (realv prop))
                                 (>= (realv prop) 0) (< (realv prop) (str.len (strv (String-_str_ obj)))))
      (and (is-jsobj_String obj) (>= (str.to.int (_tostring prop)) 0)
                                 (< (str.to.int (_tostring prop)) (str.len (strv (String-_str_ obj)))))
      (and (is-jsobj_Array obj) (= (_tostring prop) "length"))
      (and (is-jsobj_Array obj) (is-jsint prop) (>= (intv prop) 0) (< (intv prop) (arrlength (arrv obj))))
      (and (is-jsobj_Array obj) (is-jsreal prop) (is_int (realv prop))
                                (>= (realv prop) 0) (< (realv prop) (arrlength (arrv obj))))
      (and (is-jsobj_Array obj) (>= (str.to.int (_tostring prop)) 0)
                                (< (str.to.int (_tostring prop)) (arrlength (arrv obj))))
${flatMap([...classes], ({ cls, fields }) => fields.map(field => ({ cls, field }))).map(({ cls, field }) =>
`      (and (is-jsobj_${cls} obj) (= (_tostring prop) "${field}"))`).join('\n')}
${flatMap([...classes], ({ cls, methods }) => methods.map(method => ({ cls, method }))).map(({ cls, method }) =>
`      (and (is-jsobj_${cls} obj) (= (_tostring prop) "${method}"))`).join('\n')}
))

(define-fun field ((obj JSVal) (prop JSVal)) JSVal
  (ite (and (is-jsobj obj) (select (objproperties (objv obj)) (_tostring prop)))
       (objfield (objv obj) (_tostring prop))
  (ite (and (is-jsstr obj) (= (_tostring prop) "length")) (jsint (str.len (strv obj)))
  (ite (and (is-jsstr obj) (is-jsint prop) (>= (intv prop) 0) (< (intv prop) (str.len (strv obj))))
       (jsstr (str.at (strv obj) (intv prop)))
  (ite (and (is-jsstr obj) (is-jsreal prop) (is_int (realv prop))
       (>= (realv prop) 0) (< (realv prop) (str.len (strv obj))))
       (jsstr (str.at (strv obj) (to_int (realv prop))))
  (ite (and (is-jsstr obj)
            (>= (str.to.int (_tostring prop)) 0)
            (< (str.to.int (_tostring prop)) (str.len (strv obj))))
       (jsstr (str.at (strv obj) (str.to.int (_tostring prop))))
${strClass.methods.map(method =>
`  (ite (and (is-jsstr obj) (= (_tostring prop) "${method}")) v_String.${method}`).join('\n')}
  (ite (and (is-jsobj_String obj) (= (_tostring prop) "length")) (jsint (str.len (strv (String-_str_ obj))))
  (ite (and (is-jsobj_String obj) (is-jsint prop)
            (>= (intv prop) 0)
            (< (intv prop) (str.len (strv (String-_str_ obj)))))
       (jsstr (str.at (strv (String-_str_ obj)) (intv prop)))
  (ite (and (is-jsobj_String obj) (is-jsreal prop) (is_int (realv prop))
            (>= (realv prop) 0)
            (< (realv prop) (str.len (strv (String-_str_ obj)))))
       (jsstr (str.at (strv (String-_str_ obj)) (to_int (realv prop))))
  (ite (and (is-jsobj_String obj)
            (>= (str.to.int (_tostring prop)) 0)
            (< (str.to.int (_tostring prop)) (str.len (strv (String-_str_ obj)))))
       (jsstr (str.at (strv (String-_str_ obj)) (str.to.int (_tostring prop))))
  (ite (and (is-jsobj_Array obj) (= (_tostring prop) "length")) (jsint (arrlength (arrv obj)))
  (ite (and (is-jsobj_Array obj) (is-jsint prop)
       (>= (intv prop) 0) (< (intv prop) (arrlength (arrv obj))))
       (arrelems (arrv obj) (intv prop))
  (ite (and (is-jsobj_Array obj) (is-jsreal prop) (is_int (realv prop))
       (>= (realv prop) 0) (< (realv prop) (arrlength (arrv obj))))
       (arrelems (arrv obj) (to_int (realv prop)))
  (ite (and (is-jsobj_Array obj)
            (>= (str.to.int (_tostring prop)) 0)
            (< (str.to.int (_tostring prop)) (arrlength (arrv obj))))
       (arrelems (arrv obj) (str.to.int (_tostring prop)))
${flatMap([...classes], ({ cls, fields }) => fields.map(field => ({ cls, field }))).map(({ cls, field }) =>
`  (ite (and (is-jsobj_${cls} obj) (= (_tostring prop) "${field}")) (${cls}-${field} obj)`).join('\n')}
${flatMap([...classes], ({ cls, methods }) => methods.map(method => ({ cls, method }))).map(({ cls, method }) =>
`  (ite (and (is-jsobj_${cls} obj) (= (_tostring prop) "${method}")) v_${cls}.${method}`).join('\n')}
  jsundefined
${flatMap([strClass,...classes], ({ fields, methods }) => fields.concat(methods).map(_ => ')')).join('')})))))))))))))

; Declarations
${[...heaps].map(h => `(declare-fun h_${h} () Heap)\n`).join('')}
${[...locs].map(l => `(declare-fun l_${l} () Loc)\n`).join('')}
${locs.size === 0 ? '' : `(assert (distinct ${[...locs].map(l => 'l_' + l).join(' ')}))`}
${[...vars].map(v => `(declare-fun v_${v} () JSVal)\n`).join('')}

; Verification condition

${propositionToAssert(prop)}

(check-sat)
(get-model)`;
}
