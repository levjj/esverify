import { flatMap } from './util';

export namespace Syntax {
  /* tslint:disable:ter-indent */

  export type ClassName = string;

  export type Location = string;

  export type Heap = number;
  export interface HeapStore { type: 'HeapStore';
                               target: HeapExpression;
                               loc: Location;
                               expr: Expression; }
  export interface HeapEffect { type: 'HeapEffect';
                                callee: Expression;
                                heap: HeapExpression;
                                args: Array<Expression>; }
  export type HeapExpression = Heap
                             | HeapStore
                             | HeapEffect;

  export type Variable = string;
  export interface HeapReference { type: 'HeapReference';
                                   loc: Location;
                                   heap: HeapExpression; }
  export interface Literal { type: 'Literal';
                             value: undefined | null | boolean | number | string; }
  export type UnaryOperator = '-' | '+' | '!' | '~' | 'typeof' | 'void';
  export interface UnaryExpression { type: 'UnaryExpression';
                                     operator: UnaryOperator;
                                     argument: Expression; }
  export type BinaryOperator = '===' | '!==' | '<' | '<=' | '>' | '>='
                             | '<<' | '>>' | '>>>' | '+' | '-' | '*' | '/' | '%'
                             | '|' | '^' | '&';
  export interface BinaryExpression { type: 'BinaryExpression';
                                      operator: BinaryOperator;
                                      left: Expression;
                                      right: Expression; }
  export interface ConditionalExpression { type: 'ConditionalExpression';
                                           test: Proposition;
                                           consequent: Expression;
                                           alternate: Expression; }
  export interface CallExpression { type: 'CallExpression';
                                    callee: Expression;
                                    heap: HeapExpression;
                                    args: Array<Expression>; }
  export interface NewExpression { type: 'NewExpression';
                                   className: ClassName;
                                   args: Array<Expression>; }
  export interface MemberExpression { type: 'MemberExpression';
                                      object: Expression;
                                      property: Expression; }
  export interface ArrayIndexExpression { type: 'ArrayIndexExpression';
                                          array: Expression; // assumes JSVal(Array)
                                          index: Expression; } // assumes in-bounds JSVal(num)
  export type Expression = Variable
                         | HeapReference
                         | Literal
                         | UnaryExpression
                         | BinaryExpression
                         | ConditionalExpression
                         | CallExpression
                         | NewExpression
                         | MemberExpression
                         | ArrayIndexExpression;

  export interface Truthy { type: 'Truthy';
                            expr: Expression; }
  export interface And { type: 'And';
                         clauses: Array<Proposition>; }
  export interface Or { type: 'Or';
                        clauses: Array<Proposition>; }
  export interface Eq { type: 'Eq';
                        left: Expression;
                        right: Expression; }
  export interface HeapEq { type: 'HeapEq';
                            left: HeapExpression;
                            right: HeapExpression; }
  export interface Not { type: 'Not';
                         arg: Proposition; }
  export interface True { type: 'True'; }
  export interface False { type: 'False'; }
  export interface Precondition { type: 'Precondition';
                                  callee: Expression;
                                  heap: HeapExpression;
                                  args: Array<Expression>; }
  export interface Postcondition { type: 'Postcondition';
                                   callee: Expression;
                                   heap: HeapExpression;
                                   args: Array<Expression>; }
  export interface ForAllCalls { type: 'ForAllCalls';
                                 callee: Expression;
                                 heap: Heap;
                                 args: Array<Variable>;
                                 existsHeaps: Set<Heap>;
                                 existsLocs: Locs;
                                 existsVars: Vars;
                                 prop: Proposition;
                                 instantiations: Array<CallTrigger>;
                                 fuel: number;
                                 liftCallback: (renamedArgs: Array<Variable>) => void; }
  export interface CallTrigger { type: 'CallTrigger';
                                 callee: Expression;
                                 heap: HeapExpression;
                                 args: Array<Expression>;
                                 fuel: number; }
  export interface ForAllAccessObject { type: 'ForAllAccessObject';
                                        heap: Heap;
                                        prop: Proposition;
                                        instantiations: Array<AccessTrigger>;
                                        fuel: number; }
  export interface ForAllAccessProperty { type: 'ForAllAccessProperty';
                                          heap: Heap;
                                          object: Expression;
                                          property: Variable;
                                          prop: Proposition;
                                          instantiations: Array<AccessTrigger>;
                                          fuel: number; }
  export interface InstanceOf { type: 'InstanceOf';
                                left: Expression;
                                right: ClassName; }
  export interface HasProperty { type: 'HasProperty';
                                 object: Expression;
                                 property: Expression; }
  export interface InBounds { type: 'InBounds';
                              array: Expression;
                              index: Expression; }
  export interface HasProperties { type: 'HasProperties';
                                   object: Expression;
                                   properties: Array<string>; }
  export interface AccessTrigger { type: 'AccessTrigger';
                                   object: Expression;
                                   property: Expression;
                                   heap: HeapExpression;
                                   fuel: number; }
  export type Proposition = Truthy
                          | And
                          | Or
                          | Eq
                          | HeapEq
                          | Not
                          | True
                          | False
                          | Precondition
                          | Postcondition
                          | ForAllCalls
                          | CallTrigger
                          | ForAllAccessObject
                          | ForAllAccessProperty
                          | InstanceOf
                          | HasProperty
                          | HasProperties
                          | InBounds
                          | AccessTrigger;
}

export type A = Syntax.Expression;
export type P = Syntax.Proposition;
export type Heap = Syntax.Heap;
export type Heaps = Set<Syntax.Heap>;
export type Locs = Set<Syntax.Location>;
export type Vars = Set<Syntax.Variable>;
export type Classes = Set<{ cls: Syntax.ClassName, fields: Array<string> }>;
export type FreeVar = Syntax.Variable | { name: Syntax.Variable, heap: Heap };
export type FreeVars = Array<FreeVar>;

export const und: A = { type: 'Literal', value: undefined };
export const tru: P = { type: 'True' };
export const fls: P = { type: 'False' };

export function truthy (expr: A): P {
  if (typeof expr !== 'string' && expr.type === 'Literal') {
    return expr.value ? tru : fls;
  } else {
  return { type: 'Truthy', expr };
}
}

export function falsy (expr: A): P {
  return not(truthy(expr));
}

export function implies (cond: P, cons: P): P {
  return or(not(cond), cons);
}

export function and (...props: Array<P>): P {
  const clauses: Array<P> = flatMap(props,
    c => c.type === 'And' ? c.clauses : [c])
    .filter(c => c.type !== 'True');
  if (clauses.find(c => c.type === 'False')) return fls;
  if (clauses.length === 0) return tru;
  if (clauses.length === 1) return clauses[0];
  return { type: 'And', clauses };
}

export function or (...props: Array<P>): P {
  const clauses: Array<P> = flatMap(props,
    c => c.type === 'Or' ? c.clauses : [c])
    .filter(c => c.type !== 'False');
  if (clauses.find(c => c.type === 'True')) return tru;
  if (clauses.length === 0) return fls;
  if (clauses.length === 1) return clauses[0];
  return { type: 'Or', clauses };
}

export function eq (left: A, right: A): P {
  if (eqExpr(left, right)) return tru;
  return { type: 'Eq', left, right };
}

export function not (arg: P): P {
  if (arg.type === 'True') return fls;
  if (arg.type === 'False') return tru;
  if (arg.type === 'Not') return arg.arg;
  return { type: 'Not', arg };
}

export function heapStore (target: Heap, loc: string, expr: A): P {
  return { type: 'HeapEq', left: target + 1, right: { type: 'HeapStore', target, loc, expr } };
}

export function heapEq (left: Syntax.HeapExpression, right: Syntax.HeapExpression): P {
  if (eqHeap(left, right)) return tru;
  return { type: 'HeapEq', left, right };
}

function eqHeap (exprA: Syntax.HeapExpression, exprB: Syntax.HeapExpression): boolean {
  if (exprA === exprB) return true;
  if (typeof(exprA) === 'number') {
    return typeof(exprB) === 'number' && exprA === exprB;
  }
  if (typeof(exprB) === 'number') return false;
  switch (exprA.type) {
    case 'HeapEffect':
      return exprA.type === exprB.type &&
             eqExpr(exprA.callee, exprB.callee) &&
             eqHeap(exprA.heap, exprB.heap) &&
             exprA.args.length === exprB.args.length &&
             exprA.args.every((e,idx) => eqExpr(e, exprB.args[idx]));
    case 'HeapStore':
      return exprA.type === exprB.type &&
             eqHeap(exprA.target, exprB.target) &&
             exprA.loc === exprB.loc &&
             eqExpr(exprA.expr, exprB.expr);
  }
}

function eqExpr (exprA: A, exprB: A): boolean {
  if (exprA === exprB) return true;
  if (typeof(exprA) === 'string') {
    return typeof(exprB) === 'string' && exprA === exprB;
  }
  if (typeof(exprB) === 'string') return false;
  switch (exprA.type) {
    case 'HeapReference':
      return exprA.type === exprB.type &&
             eqHeap(exprA.heap, exprB.heap) &&
             exprA.loc === exprB.loc;
    case 'Literal':
      return exprA.type === exprB.type &&
             exprA.value === exprB.value;
    case 'UnaryExpression':
      return exprA.type === exprB.type &&
             exprA.operator === exprB.operator &&
             eqExpr(exprA.argument, exprB.argument);
    case 'BinaryExpression':
      return exprA.type === exprB.type &&
             exprA.operator === exprB.operator &&
             eqExpr(exprA.left, exprB.left) &&
             eqExpr(exprA.right, exprB.right);
    case 'ConditionalExpression':
      return exprA.type === exprB.type &&
             eqProp(exprA.test, exprB.test) &&
             eqExpr(exprA.consequent, exprB.consequent) &&
             eqExpr(exprA.alternate, exprB.alternate);
    case 'CallExpression':
      return exprA.type === exprB.type &&
             eqHeap(exprA.heap, exprB.heap) &&
             eqExpr(exprA.callee, exprB.callee) &&
             exprA.args.length === exprB.args.length &&
             exprA.args.every((e,idx) => eqExpr(e, exprB.args[idx]));
    case 'NewExpression':
      return exprA.type === exprB.type &&
             exprA.className === exprB.className &&
             exprA.args.length === exprB.args.length &&
             exprA.args.every((e,idx) => eqExpr(e, exprB.args[idx]));
    case 'MemberExpression':
      return exprA.type === exprB.type &&
             eqExpr(exprA.object, exprB.object) &&
             eqExpr(exprA.property, exprB.property);
    case 'ArrayIndexExpression':
      return exprA.type === exprB.type &&
             eqExpr(exprA.array, exprB.array) &&
             eqExpr(exprA.index, exprB.index);
  }
}

export function eqProp (propA: P, propB: P): boolean {
  if (propA === propB) return true;
  switch (propA.type) {
    case 'Truthy':
      return propA.type === propB.type &&
             eqExpr(propA.expr, propB.expr);
    case 'And':
    case 'Or':
      return propA.type === propB.type &&
             propA.clauses.length === propB.clauses.length &&
             propA.clauses.every((c,idx) => eqProp(c, propB.clauses[idx]));
    case 'Eq':
      return propA.type === propB.type &&
             eqExpr(propA.left, propB.left) &&
             eqExpr(propA.right, propB.right);
    case 'HeapEq':
      return propA.type === propB.type &&
             eqHeap(propA.left, propB.left) &&
             eqHeap(propA.right, propB.right);
    case 'Not':
      return propA.type === propB.type &&
             eqProp(propA.arg, propB.arg);
    case 'True':
    case 'False':
      return propA.type === propB.type;
    case 'CallTrigger':
    case 'Precondition':
    case 'Postcondition':
      return propA.type === propB.type &&
             eqHeap(propA.heap, propB.heap) &&
             eqExpr(propA.callee, propB.callee) &&
             propA.args.length === propB.args.length &&
             propA.args.every((e,idx) => eqExpr(e, propB.args[idx]));
    case 'ForAllCalls':
      return propA.type === propB.type &&
             eqExpr(propA.callee, propB.callee) &&
             propA.args.length === propB.args.length &&
             propA.args.every((e,idx) => e === propB.args[idx]) &&
             propA.existsHeaps.size === propB.existsHeaps.size &&
             [...propA.existsHeaps].every(h => propB.existsHeaps.has(h)) &&
             propA.existsLocs.size === propB.existsLocs.size &&
             [...propA.existsLocs].every(l => propB.existsLocs.has(l)) &&
             propA.existsVars.size === propB.existsVars.size &&
             [...propA.existsVars].every(v => propB.existsVars.has(v)) &&
             eqProp(propA.prop, propB.prop);
    case 'ForAllAccessObject':
      return propA.type === propB.type &&
             eqHeap(propA.heap, propB.heap) &&
             eqProp(propA.prop, propB.prop);
    case 'ForAllAccessProperty':
      return propA.type === propB.type &&
             eqHeap(propA.heap, propB.heap) &&
             eqExpr(propA.object, propB.object) &&
             propA.property === propB.property &&
             eqProp(propA.prop, propB.prop);
    case 'InstanceOf':
      return propA.type === propB.type &&
             eqExpr(propA.left, propB.left) &&
             propA.right === propB.right;
    case 'HasProperty':
      return propA.type === propB.type &&
             eqExpr(propA.object, propB.object) &&
             eqExpr(propA.property, propB.property);
    case 'HasProperties':
      return propA.type === propB.type &&
             eqExpr(propA.object, propB.object) &&
             propA.properties.length === propB.properties.length &&
             propA.properties.every((p, idx) => p === propB.properties[idx]);
    case 'InBounds':
      return propA.type === propB.type &&
             eqExpr(propA.array, propB.array) &&
             eqExpr(propA.index, propB.index);
    case 'AccessTrigger':
      return propA.type === propB.type &&
             eqHeap(propA.heap, propB.heap) &&
             eqExpr(propA.object, propB.object) &&
             eqExpr(propA.property, propB.property);
  }
}

export abstract class Visitor<L,H,R,S> {

  abstract visitLocation (loc: Syntax.Location): L;

  abstract visitHeap (heap: Heap): H;
  abstract visitHeapStore (prop: Syntax.HeapStore): H;
  abstract visitHeapEffect (prop: Syntax.HeapEffect): H;

  abstract visitVariable (expr: Syntax.Variable): R;
  abstract visitHeapReference (expr: Syntax.HeapReference): R;
  abstract visitLiteral (expr: Syntax.Literal): R;
  abstract visitUnaryExpression (expr: Syntax.UnaryExpression): R;
  abstract visitBinaryExpression (expr: Syntax.BinaryExpression): R;
  abstract visitConditionalExpression (expr: Syntax.ConditionalExpression): R;
  abstract visitCallExpression (expr: Syntax.CallExpression): R;
  abstract visitNewExpression (expr: Syntax.NewExpression): R;
  abstract visitMemberExpression (expr: Syntax.MemberExpression): R;
  abstract visitArrayIndexExpression (expr: Syntax.ArrayIndexExpression): R;

  abstract visitTruthy (prop: Syntax.Truthy): S;
  abstract visitAnd (prop: Syntax.And): S;
  abstract visitOr (prop: Syntax.Or): S;
  abstract visitEq (prop: Syntax.Eq): S;
  abstract visitHeapEq (prop: Syntax.HeapEq): S;
  abstract visitNot (prop: Syntax.Not): S;
  abstract visitTrue (prop: Syntax.True): S;
  abstract visitFalse (prop: Syntax.False): S;
  abstract visitPrecondition (prop: Syntax.Precondition): S;
  abstract visitPostcondition (prop: Syntax.Postcondition): S;
  abstract visitForAllCalls (prop: Syntax.ForAllCalls): S;
  abstract visitCallTrigger (prop: Syntax.CallTrigger): S;
  abstract visitForAllAccessObject (prop: Syntax.ForAllAccessObject): S;
  abstract visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): S;
  abstract visitInstanceOf (prop: Syntax.InstanceOf): S;
  abstract visitHasProperty (prop: Syntax.HasProperty): S;
  abstract visitHasProperties (prop: Syntax.HasProperties): S;
  abstract visitInBounds (prop: Syntax.InBounds): S;
  abstract visitAccessTrigger (prop: Syntax.AccessTrigger): S;

  visitHeapExpr (heap: Syntax.HeapExpression): H {
    if (typeof(heap) === 'number') return this.visitHeap(heap);
    switch (heap.type) {
      case 'HeapStore': return this.visitHeapStore(heap);
      case 'HeapEffect': return this.visitHeapEffect(heap);
    }
  }

  visitExpr (expr: A): R {
    if (typeof(expr) === 'string') return this.visitVariable(expr);
    switch (expr.type) {
      case 'HeapReference': return this.visitHeapReference(expr);
      case 'Literal': return this.visitLiteral(expr);
      case 'UnaryExpression': return this.visitUnaryExpression(expr);
      case 'BinaryExpression': return this.visitBinaryExpression(expr);
      case 'ConditionalExpression': return this.visitConditionalExpression(expr);
      case 'CallExpression': return this.visitCallExpression(expr);
      case 'NewExpression': return this.visitNewExpression(expr);
      case 'MemberExpression': return this.visitMemberExpression(expr);
      case 'ArrayIndexExpression': return this.visitArrayIndexExpression(expr);
    }
  }

  visitProp (prop: P): S {
    switch (prop.type) {
      case 'Truthy': return this.visitTruthy(prop);
      case 'And': return this.visitAnd(prop);
      case 'Or': return this.visitOr(prop);
      case 'Eq': return this.visitEq(prop);
      case 'HeapEq': return this.visitHeapEq(prop);
      case 'Not': return this.visitNot(prop);
      case 'True': return this.visitTrue(prop);
      case 'False': return this.visitFalse(prop);
      case 'Precondition': return this.visitPrecondition(prop);
      case 'Postcondition': return this.visitPostcondition(prop);
      case 'ForAllCalls': return this.visitForAllCalls(prop);
      case 'CallTrigger': return this.visitCallTrigger(prop);
      case 'ForAllAccessObject': return this.visitForAllAccessObject(prop);
      case 'ForAllAccessProperty': return this.visitForAllAccessProperty(prop);
      case 'InstanceOf': return this.visitInstanceOf(prop);
      case 'HasProperty': return this.visitHasProperty(prop);
      case 'HasProperties': return this.visitHasProperties(prop);
      case 'InBounds': return this.visitInBounds(prop);
      case 'AccessTrigger': return this.visitAccessTrigger(prop);
    }
  }
}

export abstract class Reducer<R> extends Visitor<R,R,R,R> {

  abstract empty (): R;

  abstract reduce (x: R, y: R): R;

  r (...r: R[]) {
    return r.reduce((res,r) => this.reduce(res, r), this.empty());
  }

  visitLocation (loc: Syntax.Location) { return this.empty(); }

  visitHeap (heap: Heap): R { return this.empty(); }

  visitHeapStore (prop: Syntax.HeapStore): R {
    return this.r(this.visitHeapExpr(prop.target),
                  this.visitLocation(prop.loc),
                  this.visitExpr(prop.expr));
  }

  visitHeapEffect (prop: Syntax.HeapEffect): R {
    return this.r(this.visitHeapExpr(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }

  visitVariable (expr: Syntax.Variable) { return this.empty(); }

  visitHeapReference (expr: Syntax.HeapReference) {
    return this.r(this.visitHeapExpr(expr.heap), this.visitLocation(expr.loc));
  }

  visitLiteral (expr: Syntax.Literal) { return this.empty(); }

  visitUnaryExpression (expr: Syntax.UnaryExpression) {
    return this.visitExpr(expr.argument);
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression) {
    return this.r(this.visitExpr(expr.left), this.visitExpr(expr.right));
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): R {
    return this.r(this.visitProp(expr.test), this.visitExpr(expr.consequent), this.visitExpr(expr.alternate));
  }

  visitCallExpression (expr: Syntax.CallExpression): R {
    return this.r(this.visitHeapExpr(expr.heap),
                  this.visitExpr(expr.callee),
                  ...expr.args.map(a => this.visitExpr(a)));
  }

  visitNewExpression (expr: Syntax.NewExpression): R {
    return this.r(...expr.args.map(a => this.visitExpr(a)));
  }

  visitMemberExpression (expr: Syntax.MemberExpression): R {
    return this.r(this.visitExpr(expr.object), this.visitExpr(expr.property));
  }

  visitArrayIndexExpression (expr: Syntax.ArrayIndexExpression): R {
    return this.r(this.visitExpr(expr.array), this.visitExpr(expr.index));
  }

  visitTruthy (prop: Syntax.Truthy): R {
    return this.visitExpr(prop.expr);
  }

  visitAnd (prop: Syntax.And): R {
    return this.r(...prop.clauses.map(c => this.visitProp(c)));
  }

  visitOr (prop: Syntax.Or): R {
    return this.r(...prop.clauses.map(c => this.visitProp(c)));
  }

  visitEq (prop: Syntax.Eq): R {
    return this.r(this.visitExpr(prop.left), this.visitExpr(prop.right));
  }

  visitNot (prop: Syntax.Not): R {
    return this.visitProp(prop.arg);
  }

  visitTrue (prop: Syntax.True): R { return this.empty(); }

  visitFalse (prop: Syntax.False): R { return this.empty(); }

  visitPrecondition (prop: Syntax.Precondition): R {
    return this.r(this.visitHeapExpr(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }

  visitPostcondition (prop: Syntax.Postcondition): R {
    return this.r(this.visitHeapExpr(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): R {
    return this.r(this.visitExpr(prop.callee),
                  this.visitProp(prop.prop));
  }

  visitCallTrigger (prop: Syntax.CallTrigger): R {
    return this.r(this.visitHeapExpr(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }

  visitHeapEq (prop: Syntax.HeapEq): R {
    return this.r(this.visitHeapExpr(prop.left),
                  this.visitHeapExpr(prop.right));
  }

  visitInstanceOf (prop: Syntax.InstanceOf): R {
    return this.visitExpr(prop.left);
  }

  visitHasProperty (prop: Syntax.HasProperty): R {
    return this.r(this.visitExpr(prop.object), this.visitExpr(prop.property));
  }

  visitHasProperties (prop: Syntax.HasProperties): R {
    return this.visitExpr(prop.object);
  }

  visitInBounds (expr: Syntax.InBounds): R {
    return this.r(this.visitExpr(expr.array), this.visitExpr(expr.index));
  }

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): R {
    return this.visitProp(prop.prop);
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): R {
    return this.r(this.visitExpr(prop.object), this.visitProp(prop.prop));
  }

  visitAccessTrigger (prop: Syntax.AccessTrigger): R {
    return this.visitExpr(prop.object);
  }
}

export class Traverser extends Reducer<void> {
  empty (): void { /* empty */ }
  reduce (x: void, y: void): void { /* empty */ }
}

export class Transformer extends Visitor<Syntax.Location, Syntax.HeapExpression, A, P> {

  visitLocation (loc: Syntax.Location): Syntax.Location {
    return loc;
  }

  visitHeap (heap: Heap): Syntax.HeapExpression {
    return heap;
  }

  visitHeapStore (expr: Syntax.HeapStore): Syntax.HeapExpression {
    return {
      type: 'HeapStore',
      target: this.visitHeapExpr(expr.target),
      loc: this.visitLocation(expr.loc),
      expr: this.visitExpr(expr.expr)
    };
  }

  visitHeapEffect (expr: Syntax.HeapEffect): Syntax.HeapExpression {
    return {
     type: 'HeapEffect',
     callee: this.visitExpr(expr.callee),
     heap: this.visitHeapExpr(expr.heap),
     args: expr.args.map(a => this.visitExpr(a))
    };
  }

  visitVariable (expr: Syntax.Variable): A {
    return expr;
  }

  visitHeapReference (expr: Syntax.HeapReference): A {
    return {
      type: 'HeapReference',
      heap: this.visitHeapExpr(expr.heap),
      loc: this.visitLocation(expr.loc)
    };
  }

  visitLiteral (expr: Syntax.Literal): A {
    return expr;
  }

  visitUnaryExpression (expr: Syntax.UnaryExpression): A {
    return {
      type: 'UnaryExpression',
      operator: expr.operator,
      argument: this.visitExpr(expr.argument)
    };
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): A {
    return {
     type: 'BinaryExpression',
     operator: expr.operator,
     left: this.visitExpr(expr.left),
     right: this.visitExpr(expr.right)
    };
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): A {
    return {
     type: 'ConditionalExpression',
     test: this.visitProp(expr.test),
     consequent: this.visitExpr(expr.consequent),
     alternate: this.visitExpr(expr.alternate)
    };
  }

  visitCallExpression (expr: Syntax.CallExpression): A {
    return {
     type: 'CallExpression',
     callee: this.visitExpr(expr.callee),
     heap: this.visitHeapExpr(expr.heap),
     args: expr.args.map(a => this.visitExpr(a))
    };
  }

  visitNewExpression (expr: Syntax.NewExpression): A {
    return {
     type: 'NewExpression',
     className: expr.className,
     args: expr.args.map(a => this.visitExpr(a))
    };
  }

  visitMemberExpression (expr: Syntax.MemberExpression): A {
    return {
      type: 'MemberExpression',
      object: this.visitExpr(expr.object),
      property: this.visitExpr(expr.property)
    };
  }

  visitArrayIndexExpression (expr: Syntax.ArrayIndexExpression): A {
    return {
      type: 'ArrayIndexExpression',
      array: this.visitExpr(expr.array),
      index: this.visitExpr(expr.index)
    };
  }

  visitTruthy (prop: Syntax.Truthy): P {
    return { type: 'Truthy', expr: this.visitExpr(prop.expr) };
  }

  visitAnd (prop: Syntax.And): P {
    return and(...prop.clauses.map(c => this.visitProp(c)));
  }

  visitOr (prop: Syntax.Or): P {
    return or(...prop.clauses.map(c => this.visitProp(c)));
  }

  visitEq (prop: Syntax.Eq): P {
    return eq(this.visitExpr(prop.left), this.visitExpr(prop.right));
  }

  visitHeapEq (prop: Syntax.HeapEq): P {
    return heapEq(this.visitHeapExpr(prop.left), this.visitHeapExpr(prop.right));
  }

  visitNot (prop: Syntax.Not): P {
    return not(this.visitProp(prop.arg));
  }

  visitTrue (prop: Syntax.True): P {
    return prop;
  }

  visitFalse (prop: Syntax.False): P {
    return prop;
  }

  visitPrecondition (prop: Syntax.Precondition): P {
    return {
      type: 'Precondition',
      callee: this.visitExpr(prop.callee),
      heap: this.visitHeapExpr(prop.heap),
      args: prop.args.map(a => this.visitExpr(a))
    };
  }

  visitPostcondition (prop: Syntax.Postcondition): P {
    return {
      type: 'Postcondition',
      callee: this.visitExpr(prop.callee),
      heap: this.visitHeapExpr(prop.heap),
      args: prop.args.map(a => this.visitExpr(a))
    };
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): P {
    return {
      type: 'ForAllCalls',
      callee: this.visitExpr(prop.callee),
      heap: prop.heap,
      args: prop.args,
      existsHeaps: new Set([...prop.existsHeaps]),
      existsLocs: new Set([...prop.existsLocs]),
      existsVars: new Set([...prop.existsVars]),
      prop: this.visitProp(prop.prop),
      instantiations: [...prop.instantiations], // shallow copy, do not process
      fuel: prop.fuel,
      liftCallback: prop.liftCallback
    };
  }

  visitCallTrigger (prop: Syntax.CallTrigger): P {
    return {
      type: 'CallTrigger',
      callee: this.visitExpr(prop.callee),
      heap: this.visitHeapExpr(prop.heap),
      args: prop.args.map(a => this.visitExpr(a)),
      fuel: prop.fuel
    };
  }

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): P {
    return {
      type: 'ForAllAccessObject',
      heap: prop.heap,
      prop: this.visitProp(prop.prop),
      instantiations: [...prop.instantiations], // shallow copy, do not process
      fuel: prop.fuel
    };
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): P {
    return {
      type: 'ForAllAccessProperty',
      heap: prop.heap,
      object: this.visitExpr(prop.object),
      property: prop.property,
      prop: this.visitProp(prop.prop),
      instantiations: [...prop.instantiations], // shallow copy, do not process
      fuel: prop.fuel
    };
  }

  visitInstanceOf (prop: Syntax.InstanceOf): P {
    return {
      type: 'InstanceOf',
      left: this.visitExpr(prop.left),
      right: prop.right
    };
  }

  visitHasProperty (prop: Syntax.HasProperty): P {
    return {
      type: 'HasProperty',
      object: this.visitExpr(prop.object),
      property: prop.property
    };
  }

  visitHasProperties (prop: Syntax.HasProperties): P {
    return {
      type: 'HasProperties',
      object: this.visitExpr(prop.object),
      properties: prop.properties
    };
  }

  visitInBounds (expr: Syntax.InBounds): P {
    return {
      type: 'InBounds',
      array: this.visitExpr(expr.array),
      index: this.visitExpr(expr.index)
    };
  }

  visitAccessTrigger (prop: Syntax.AccessTrigger): P {
    return {
      type: 'AccessTrigger',
      object: this.visitExpr(prop.object),
      property: this.visitExpr(prop.property),
      heap: this.visitHeapExpr(prop.heap),
      fuel: prop.fuel
    };
  }
}

export function copy (prop: P): P {
  return (new Transformer()).visitProp(prop);
}

export class Substituter extends Transformer {
  thetaHeap: { [heap: number]: Syntax.HeapExpression } = {};
  thetaLoc: { [lname: string]: Syntax.Location } = {};
  thetaVar: { [vname: string]: Syntax.Expression } = {};

  visitHeap (heap: Heap): Syntax.HeapExpression {
    return heap in this.thetaHeap ? this.thetaHeap[heap] : heap;
  }

  visitLocation (l: Syntax.Location): Syntax.Location {
    return l in this.thetaLoc ? this.thetaLoc[l] : l;
  }

  visitVariable (v: Syntax.Variable): Syntax.Expression {
    return v in this.thetaVar ? this.thetaVar[v] : v;
  }

  replaceHeap (orig: number, expr: Syntax.HeapExpression): Substituter {
    this.thetaHeap[orig] = expr;
    return this;
  }

  replaceLoc (orig: Syntax.Location, expr: Syntax.Location): Substituter {
    this.thetaLoc[orig] = expr;
    return this;
  }

  replaceVar (orig: Syntax.Variable, expr: Syntax.Expression): Substituter {
    this.thetaVar[orig] = expr;
    return this;
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): P {
    const origThetaHeap = Object.assign({}, this.thetaHeap);
    const origThetaLoc = Object.assign({}, this.thetaLoc);
    const origThetaVar = Object.assign({}, this.thetaVar);
    try {
      delete this.thetaHeap[prop.heap];
      prop.args.forEach(a => { delete this.thetaVar[a]; });
      prop.existsHeaps.forEach(h => { delete this.thetaHeap[h]; });
      prop.existsLocs.forEach(l => { delete this.thetaLoc[l]; });
      prop.existsVars.forEach(v => { delete this.thetaVar[v]; });
      return super.visitForAllCalls(prop);
    } finally {
      this.thetaHeap = origThetaHeap;
      this.thetaLoc = origThetaLoc;
      this.thetaVar = origThetaVar;
    }
  }

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): P {
    const origThetaHeap = Object.assign({}, this.thetaHeap);
    const origThetaVar = Object.assign({}, this.thetaVar);
    try {
      delete this.thetaHeap[prop.heap];
      delete this.thetaVar['this'];
      return super.visitForAllAccessObject(prop);
    } finally {
      this.thetaHeap = origThetaHeap;
      this.thetaVar = origThetaVar;
    }
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): P {
    const origThetaHeap = Object.assign({}, this.thetaHeap);
    const origThetaVar = Object.assign({}, this.thetaVar);
    try {
      delete this.thetaHeap[prop.heap];
      delete this.thetaVar[prop.property];
      return super.visitForAllAccessProperty(prop);
    } finally {
      this.thetaHeap = origThetaHeap;
      this.thetaVar = origThetaVar;
    }
  }
}

export function replaceVar (v: string, subst: A, prop: P): P {
  const sub = new Substituter();
  sub.replaceVar(v, subst);
  return sub.visitProp(prop);
}

export function replaceResultWithCall (callee: A, heap: Heap, args: Array<string>,
                                       result: { name: string } | null, post: P): P {
  if (!result) return post;
    // replace result argument with orig. function invocation
  const sub = new Substituter();
  sub.replaceVar(result.name, { type: 'CallExpression', callee, heap, args });
  return sub.visitProp(post);
}

export function removePrefix (prefix: P, prop: P): P {
  if (prefix.type !== 'And' || prop.type !== 'And') return prop;
  let prefixLength = 0;
  while (prefix.clauses.length > prefixLength &&
         prop.clauses.length > prefixLength &&
         eqProp(prefix.clauses[prefixLength], prop.clauses[prefixLength])) {
    prefixLength++;
  }
  return and(...prop.clauses.slice(prefixLength));
}

export function transformSpec (callee: A, args: Array<string>, req: P, ens: P, heap: Heap, toHeap: Heap = heap + 1,
                               existsLocs: Locs = new Set(), existsVars: Vars = new Set()): P {
  const numHeaps = Math.max(0, toHeap - heap - 1);
  const existsHeaps: Set<Heap> = new Set([...Array(numHeaps).keys()].map(i => i + heap + 1));
  const preP: P = { type: 'Precondition', callee, heap, args };
  const postP: P = { type: 'Postcondition', callee, heap, args };
  let s;
  if (heap !== toHeap) {
    const sub = new Substituter();
    sub.replaceHeap(toHeap, { type: 'HeapEffect', callee, heap, args });
    s = sub.visitProp(ens);
  } else {
    s = and(ens, heapEq(heap, { type: 'HeapEffect', callee, heap, args }));
  }
  const prop = and(implies(req, preP), implies(and(req, postP), s));
  const forAll: P = {
    type: 'ForAllCalls',
    callee,
    heap,
    args,
    existsHeaps,
    existsLocs,
    existsVars,
    prop,
    instantiations: [],
    fuel: 0,
    liftCallback: () => undefined
  };
  const fnCheck: A = {
    type: 'BinaryExpression',
    left: {
      type: 'UnaryExpression',
      operator: 'typeof',
      argument: callee
    },
    operator: '===',
    right: { type: 'Literal', value: 'function' }
  };
  return and(truthy(fnCheck), forAll);
}

export function transformClassInvariant (className: string, fields: Array<string>, inv: P, heap: Heap): P {
  const instP: P = { type: 'InstanceOf', left: 'this', right: className };
  return { type: 'ForAllAccessObject', heap, prop: implies(instP, inv), instantiations: [], fuel: 0 };
}

export function transformEveryInvariant (array: A, elemName: string, index: string | null, inv: P, heap: Heap): P {
  const instP: P = { type: 'InstanceOf', left: array, right: 'Array' };
  const inBounds: P = { type: 'InBounds', array, index: elemName };
  const sub = new Substituter();
  sub.replaceVar(elemName, { type: 'ArrayIndexExpression', array, index: elemName });
  if (index !== null) {
    sub.replaceVar(index, elemName);
  }
  const forAllP: P = {
    type: 'ForAllAccessProperty',
    heap,
    object: array,
    property: elemName,
    prop: implies(inBounds, sub.visitProp(inv)),
    instantiations: [],
    fuel: 0
  };
  return and(instP, forAllP);
}
