import { flatMap } from './util';
import { Syntax, P, Classes, Vars, FreeVars, Locs, Heap, Heaps, Visitor, implies } from './logic';
import { instantiateQuantifiers } from './qi';
import { MessageException } from './message';
import { options } from './options';

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
    const { callee, heap, args } = expr;
    return `(eff${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}` +
             `${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
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
    switch (typeof expr.value) {
      case 'boolean': return `(jsbool ${expr.value})`;
      case 'number': return `(jsnum ${expr.value})`;
      case 'string': return `(jsstr "${expr.value}")`;
      default: throw new Error('unreachable');
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
    const test = this.visitProp(expr.test);
    const then = this.visitExpr(expr.consequent);
    const elze = this.visitExpr(expr.alternate);
    return `(ite ${test} ${then} ${elze})`;
  }

  visitCallExpression (expr: Syntax.CallExpression): SMTInput {
    const { callee, heap, args } = expr;
    return `(app${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}` +
            `${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitNewExpression (expr: Syntax.NewExpression): SMTInput {
    return `(jsobj_${expr.className}${expr.args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitMemberExpression (expr: Syntax.MemberExpression): SMTInput {
    return `(field ${this.visitExpr(expr.object)} ${this.visitExpr(expr.property)})`;
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
    const { callee, heap, args } = prop;
    return `(pre${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}` +
             `${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitPostcondition (prop: Syntax.Postcondition): SMTInput {
    const { callee, heap, args } = prop;
    return `(post${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}` +
            `${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): SMTInput {
    const { callee, heap, args, fuel } = prop;
    const params = `${args.map(a => `(${this.visitVariable(a)} JSVal)`).join(' ')}`;
    const callP: P = { type: 'CallTrigger', callee, heap, args: args, fuel };
    let p = this.visitProp(implies(callP, prop.prop));
    if (prop.existsLocs.size + prop.existsHeaps.size + prop.existsVars.size > 0) {
      p = `(exists (${[...prop.existsHeaps].map(h => `(${this.visitHeap(h)} Heap)`).join(' ')} `
                 + `${[...prop.existsLocs].map(l => `(${this.visitLocation(l)} Loc)`).join(' ')} `
                 + `${[...prop.existsVars].map(v => `(${this.visitVariable(v)} JSVal)`).join(' ')})\n  ${p})`;
    }
    const trigger: SMTInput = this.visitProp(callP);
    return `(forall ((${this.visitHeap(heap)} Heap) ${params}) (!\n  ${p}\n  :pattern (${trigger})))`;
  }

  visitCallTrigger (prop: Syntax.CallTrigger): SMTInput {
    const { callee, heap, args } = prop;
    return `(call${args.length} ${this.visitExpr(callee)} ${this.visitHeapExpr(heap)}` +
            `${args.map(a => ' ' + this.visitExpr(a)).join('')})`;
  }

  visitForAllAccess (prop: Syntax.ForAllAccess): SMTInput {
    const { heap, fuel } = prop;
    const accessP: P = { type: 'AccessTrigger', object: 'this', heap, fuel };
    let p = this.visitProp(implies(accessP, prop.prop));
    const trigger: SMTInput = this.visitProp(accessP);
    return `(forall ((${this.visitVariable('this')} JSVal) `
                  + `(${this.visitHeap(heap)} Heap)) (!\n  ${p}\n  :pattern (${trigger})))`;
  }

  visitInstanceOf (prop: Syntax.InstanceOf): SMTInput {
    return `(instanceof ${this.visitExpr(prop.left)} ${this.visitClassName(prop.right)})`;
  }

  visitHasProperty (prop: Syntax.HasProperty): SMTInput {
    return `(has ${this.visitExpr(prop.object)} ${this.visitExpr(prop.property)})`;
  }

  visitAccessTrigger (prop: Syntax.AccessTrigger): SMTInput {
    return `(access ${this.visitExpr(prop.object)} ${this.visitHeapExpr(prop.heap)})`;
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
  const prop = options.qi ? instantiateQuantifiers(heaps, locs, vars, p) : p;
  return `(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-sort Func) ; unspecified function
(declare-sort Obj) ; unspecified object

; Values in JavaScript
(declare-datatypes () ((JSVal
  (jsnum (numv Int))
  (jsbool (boolv Bool))
  (jsstr (strv String))
  jsnull
  jsundefined
  (jsfun (funv Func))
  (jsobj (objv Obj))
${[...classes].map(({ cls, fields }) =>
  fields.length === 0
  ? `  jsobj_${cls}\n`
  : `  (jsobj_${cls} ${fields.map(field => `(${cls}-${field} JSVal)`).join(' ')})\n`
).join('')})))

; Types in JavaScript
(declare-datatypes () ((JSType JSNum JSBool JSString JSUndefined JSObj JSFunction)))

(define-fun _type ((x JSVal)) JSType
  (ite (is-jsnum x) JSNum
  (ite (is-jsbool x) JSBool
  (ite (is-jsstr x) JSString
  (ite (is-jsnull x) JSObj
  (ite (is-jsundefined x) JSUndefined
  (ite (is-jsfun x) JSFunction
  JSObj)))))))

(define-fun _tostring ((x JSVal)) String
  (ite (is-jsnum x) (int.to.str (numv x))
  (ite (is-jsbool x) (ite (boolv x) "true" "false")
  (ite (is-jsstr x) (strv x)
  (ite (is-jsnull x) "null"
  (ite (is-jsundefined x) "undefined"
  (ite (is-jsfun x) "function () { ... }"
${[...classes].map(({ cls }) =>
  `  (ite (is-jsobj_${cls} x) "[object ${cls}]"`).join('\n')}
  "[object Object]"${[...classes].map(c => ')').join('')})))))))

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
(declare-const c_Object ClassName)
(declare-const c_Function ClassName)
${[...classes].map(({ cls }) => `(declare-const c_${cls} ClassName)\n`).join('')}
(assert (distinct c_Object c_Function ${[...classes].map(({ cls }) => 'c_' + cls).join(' ')}))

(declare-fun objhas (Obj String) Bool)
(declare-fun objfield (Obj String) JSVal)

(define-fun has ((obj JSVal) (prop JSVal)) Bool
  (or (and (is-jsobj obj) (objhas (objv obj) (_tostring prop)))
${flatMap([...classes], ({ cls, fields }) => fields.map(field => ({ cls, field }))).map(({ cls, field }) =>
`      (and (is-jsobj_${cls} obj) (= (_tostring prop) "${field}"))`).join('\n')}
))

(define-fun field ((obj JSVal) (prop JSVal)) JSVal
  (ite (is-jsobj obj) (objfield (objv obj) (_tostring prop))
${flatMap([...classes], ({ cls, fields }) => fields.map(field => ({ cls, field }))).map(({ cls, field }) =>
`  (ite (and (is-jsobj_${cls} obj) (= (_tostring prop) "${field}")) (${cls}-${field} obj)`).join('\n')}
  jsundefined
${flatMap([...classes], ({ cls, fields }) => fields.map(field => ')')).join('')}))

(define-fun instanceof ((obj JSVal) (cls ClassName)) Bool
  (or (and (is-jsfun obj) (= cls c_Object))
      (and (is-jsfun obj) (= cls c_Function))
      (and (is-jsobj obj) (= cls c_Object))
${[...classes].map(({ cls }) =>
`      (and (is-jsobj_${cls} obj) (= cls c_Object))
      (and (is-jsobj_${cls} obj) (= cls c_${cls}))`).join('\n')}
))

(declare-fun access (JSVal Heap) Bool)

; Declarations
${[...heaps].map(h => `(declare-const h_${h} Heap)\n`).join('')}
${[...locs].map(l => `(declare-const l_${l} Loc)\n`).join('')}
${locs.size === 0 ? '' : `(assert (distinct ${[...locs].map(l => 'l_' + l).join(' ')}))`}
${[...vars].map(v => `(declare-const v_${v} JSVal)\n`).join('')}

; Verification condition

${propositionToAssert(prop)}

(check-sat)
(get-value (${[...freeVars].map(v => typeof v === 'string' ? `v_${v}` : `(select h_${v.heap} l_${v.name})`)
                           .join(' ')}))`;
}

export namespace Model {
  /* tslint:disable:ter-indent */

  export interface Num { type: 'num'; v: number; }
  export interface Bool { type: 'bool'; v: boolean; }
  export interface Str { type: 'str'; v: string; }
  export interface Null { type: 'null'; }
  export interface Undefined { type: 'undefined'; }
  export interface Fun { type: 'fun'; v: string; }
  export interface Obj { type: 'obj'; v: string; }
  export interface ObjCls { type: 'obj-cls'; cls: string; args: Array<Value>; }
  export type Value = Num | Bool | Str | Null | Undefined | Fun | Obj | ObjCls;
}

export type Model = { [varName: string]: Model.Value };

function modelError (smt: SMTOutput): MessageException {
  const loc = { file: options.filename, start: { line: 0, column: 0 }, end: { line: 0, column: 0 } };
  return new MessageException({ status: 'error', type: 'unrecognized-model', loc, description: `cannot parse ${smt}` });
}

type SExpr = string | SExprList;
interface SExprList extends Array<SExpr> {}

function parseSExpr (input: string): SExpr {
  let idx = 0;

  function skipWS () {
    while (input[idx] === ' ' || input[idx] === '\t' || input[idx] === '\n') idx++;
  }

  function sexpr (): SExpr | null {
    skipWS();
    if (input[idx] === '(') {
      idx++;
      const list: SExprList = [];
      for (let next = sexpr(); next !== null; next = sexpr()) {
        list.push(next);
      }
      skipWS();
      if (input[idx++] !== ')') throw modelError(input);
      return list;
    }
    const m = input.substr(idx).match(/^("[^"]*")|^\w+/);
    if (m) {
      idx += m[0].length;
      return m[0];
    }
    return null;
  }

  const result = sexpr();
  if (result === null) {
    throw modelError(input);
  } else {
    return result;
  }
}

function smtToValue (s: SExpr): Model.Value {
  if (typeof s === 'string') {
    if (s === 'jsundefined') {
      return { type: 'undefined' };
    } else if (s === 'jsnull') {
      return { type: 'null' };
    } else if (s.startsWith('jsobj_')) {
      return { type: 'obj-cls', cls: s.substr(6), args: [] };
    } else {
      throw modelError(s);
    }
  } else {
    if (s.length < 1) throw modelError(s.toString());
    const tag = s[0];
    if (typeof tag !== 'string') throw modelError(tag.toString());
    if (tag === 'jsbool') {
      if (s.length !== 2) throw modelError(s.toString());
      const v = s[1];
      if (typeof v !== 'string') throw modelError(s.toString());
      return { type: 'bool', v: v === 'true' };
    } else if (tag === 'jsnum') {
      if (s.length !== 2) throw modelError(s.toString());
      const v = s[1];
      if (typeof v !== 'string') throw modelError(s.toString());
      const neg = v.match(/\(- ([0-9]+)\)/);
      return { type: 'num', v: neg ? -neg[1] : +v };
    } else if (tag === 'jsstr') {
      if (s.length !== 2) throw modelError(s.toString());
      const v = s[1];
      if (typeof v !== 'string') throw modelError(s.toString());
      return { type: 'str', v: v.substr(1, v.length - 2) };
    } else if (tag === 'jsfun') {
      if (s.length !== 2) throw modelError(s.toString());
      const v = s[1];
      if (typeof v !== 'string') throw modelError(s.toString());
      return { type: 'fun', v };
    } else if (tag === 'jsobj') {
      if (s.length !== 2) throw modelError(s.toString());
      const v = s[1];
      if (typeof v !== 'string') throw modelError(s.toString());
      return { type: 'obj', v };
    } else if (tag.startsWith('jsobj_')) {
      return {
        type: 'obj-cls',
        cls: tag.substr(6),
        args: s.slice(1).map(smtToValue)
      };
    } else {
      throw modelError(tag);
    }
  }
}

export function smtToModel (smt: SMTOutput): Model {
  // assumes smt starts with "sat", so remove "sat"
  const smt2 = smt.slice(3, smt.length);
  // return empty model if there was an error
  if (smt2.trim().startsWith('(error')) return {};

  const data = parseSExpr(smt2.trim());
  const model: Model = {};
  if (typeof data === 'string') throw modelError(data);
  data.forEach(nameAndValue => {
    if (typeof nameAndValue === 'string') throw modelError(nameAndValue);
    if (nameAndValue.length !== 2) throw modelError(smt);
    const nameExpr: SExpr = nameAndValue[0];
    let name: string;
    if (typeof nameExpr === 'string') { // v_x
      name = nameExpr.substr(2);
    } else { // (select h_i l_x)
      if (nameExpr.length !== 3) throw modelError(smt);
      if (nameExpr[0] !== 'select') throw modelError(smt);
      const loc = nameExpr[2];
      if (typeof loc !== 'string') throw modelError(smt);
      name = loc.substr(2);
    }
    model[name] = smtToValue(nameAndValue[1]);
  });
  return model;
}
