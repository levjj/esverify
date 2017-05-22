import { flatMap } from "./util";

export namespace Syntax {

  export type Location = string;

  export type Heap = number;
  export interface HeapStore { type: "HeapStore",
                               target: HeapExpression,
                               loc: Location,
                               expr: Expression }
  export interface HeapEffect { type: "HeapEffect",
                                callee: Expression,
                                heap: HeapExpression,
                                args: Array<Expression> }
  export type HeapExpression = Heap
                             | HeapStore
                             | HeapEffect;

  export type Variable = string;
  export interface HeapReference { type: "HeapReference",
                                   loc: Location,
                                   heap: HeapExpression }
  export interface Literal { type: "Literal",
                             value: undefined | null | boolean | number | string }
  export interface ArrayExpression { type: "ArrayExpression",
                                     elements: Array<Expression> }
  export type UnaryOperator = "-" | "+" | "!" | "~" | "typeof" | "void";
  export interface UnaryExpression { type: "UnaryExpression",
                                     operator: UnaryOperator,
                                     argument: Expression }
  export type BinaryOperator = "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">="
                      | "<<" | ">>" | ">>>" | "+" | "-" | "*" | "/" | "%"
                      | "|" | "^" | "&";
  export interface BinaryExpression { type: "BinaryExpression",
                                      operator: BinaryOperator,
                                      left: Expression,
                                      right: Expression }
  export interface ConditionalExpression { type: "ConditionalExpression",
                                           test: Proposition,
                                           consequent: Expression,
                                           alternate: Expression }
  export interface CallExpression { type: "CallExpression",
                                    callee: Expression,
                                    heap: HeapExpression,
                                    args: Array<Expression> }
  export type Expression = Variable
                         | HeapReference
                         | Literal
                         | ArrayExpression
                         | UnaryExpression
                         | BinaryExpression
                         | ConditionalExpression
                         | CallExpression;

  export interface Truthy { type: "Truthy",
                            expr: Expression }
  export interface And { type: "And",
                         clauses: Array<Proposition> }
  export interface Or { type: "Or",
                        clauses: Array<Proposition> }
  export interface Eq { type: "Eq",
                        left: Expression,
                        right: Expression }
  export interface HeapEq { type: "HeapEq",
                            left: HeapExpression,
                            right: HeapExpression }
  export interface Not { type: "Not",
                         arg: Proposition }
  export interface True { type: "True" }
  export interface False { type: "False" }
  export interface Precondition { type: "Precondition",
                                  callee: Expression,
                                  heap: HeapExpression,
                                  args: Array<Expression> }
  export interface Postcondition { type: "Postcondition",
                                   callee: Expression,
                                   heap: HeapExpression,
                                   args: Array<Expression> }
  export interface ForAll { type: "ForAll",
                            callee: Expression,
                            args: Array<string>,
                            existsHeaps: Set<Heap>,
                            existsLocs: Locs,
                            existsVars: Vars,
                            prop: Proposition,
                            instantiations: Array<CallTrigger> }
  export interface CallTrigger { type: "CallTrigger",
                                 callee: Expression,
                                 heap: HeapExpression,
                                 args: Array<Expression> }
  export type Proposition = Truthy
                          | And
                          | Or
                          | Eq
                          | Not
                          | True
                          | False
                          | Precondition
                          | Postcondition
                          | ForAll
                          | CallTrigger
                          | HeapEq;
}

export type A = Syntax.Expression;
export type P = Syntax.Proposition;
export type Heap = Syntax.Heap;
export type Heaps = Set<Syntax.Heap>;
export type Locs = Set<Syntax.Location>;
export type Vars = Set<Syntax.Variable>;

export const und: A = { type: "Literal", value: undefined };
export const tru: P = { type: "True" };
export const fls: P = { type: "False" };

export function truthy(expr: A): P {
  return { type: "Truthy", expr };
}

export function falsy(expr: A): P {
  return not(truthy(expr));
}

export function implies(cond: P, cons: P): P {
  return or(not(cond), cons);
}

export function and(...props: Array<P>): P {
  const clauses: Array<P> = flatMap(props,
    c => c.type == "And" ? c.clauses : [c]) 
    .filter(c => c.type != "True");
  if (clauses.find(c => c.type == "False")) return fls;
  if (clauses.length == 0) return tru;
  if (clauses.length == 1) return clauses[0];
  return { type: "And", clauses };
}

export function or(...props: Array<P>): P {
  const clauses: Array<P> = flatMap(props,
    c => c.type == "Or" ? c.clauses : [c]) 
    .filter(c => c.type != "False");
  if (clauses.find(c => c.type == "True")) return tru;
  if (clauses.length == 0) return fls;
  if (clauses.length == 1) return clauses[0];
  return { type: "Or", clauses };
}

export function eq(left: A, right: A): P {
  if (eqExpr(left, right)) return tru;
  return { type: "Eq", left, right };
}

export function not(arg: P): P {
  if (arg.type == "True") return fls;
  if (arg.type == "False") return tru;
  if (arg.type == "Not") return arg.arg;
  return { type: "Not", arg };
}

export function heapStore(target: Heap, loc: string, expr: A): P {
  return { type: "HeapEq", left: target + 1, right: { type: "HeapStore", target, loc, expr }};
}

export function heapEq(left: Syntax.HeapExpression, right: Syntax.HeapExpression): P {
  return { type: "HeapEq", left, right };
}

export function forAllCalls(callee: Syntax.Variable, args: Array<string>, existsHeaps: Set<Heap>, existsLocs: Locs, existsVars: Vars, r: P, s: P): P {
  const preP: P = { type: "Precondition", callee, heap: 0, args };
  const postP: P = { type: "Postcondition", callee, heap: 0, args };
  const resHeap: Syntax.HeapExpression = { type: "HeapEffect", callee, heap: 0, args };
  const sub = (new Substituter()).replaceHeap(1, resHeap).visitProp(s);
  const prop = and(implies(r, preP), implies(and(r, postP), sub));
  return { type: "ForAll", callee, args, existsHeaps, existsLocs, existsVars, prop, instantiations: [] };
}

function eqHeap(exprA: Syntax.HeapExpression, exprB: Syntax.HeapExpression): boolean {
  if (typeof(exprA) == "number") {
    return typeof(exprB) == "number" && exprA == exprB;
  }
  if (typeof(exprB) == "number") return false;
  switch (exprA.type) {
    case "HeapEffect":
      return exprA.type == exprB.type &&
             eqExpr(exprA.callee, exprB.callee) &&
             eqHeap(exprA.heap, exprB.heap) &&
             exprA.args.length == exprB.args.length &&
             exprA.args.every((e,idx) => eqExpr(e, exprB.args[idx]));
    case "HeapStore":
      return exprA.type == exprB.type &&
             eqHeap(exprA.target, exprB.target) &&
             exprA.loc == exprB.loc &&
             eqExpr(exprA.expr, exprB.expr);
  }
}

function eqExpr(exprA: A, exprB: A): boolean {
  if (typeof(exprA) == "string") {
    return typeof(exprB) == "string" && exprA == exprB;
  }
  if (typeof(exprB) == "string") return false;
  switch (exprA.type) {
    case "HeapReference":
      return exprA.type == exprB.type &&
             eqHeap(exprA.heap, exprB.heap) &&
             exprA.loc == exprB.loc;
    case "Literal":
      return exprA.type == exprB.type &&
             exprA.value === exprB.value;
    case 'ArrayExpression':
      return exprA.type == exprB.type &&
             exprA.elements.length == exprB.elements.length &&
             exprA.elements.every((e,idx) => eqExpr(e, exprB.elements[idx]));
    case "UnaryExpression":
      return exprA.type == exprB.type &&
             exprA.operator == exprB.operator &&
             eqExpr(exprA.argument, exprB.argument);
    case "BinaryExpression":
      return exprA.type == exprB.type &&
             exprA.operator == exprB.operator &&
             eqExpr(exprA.left, exprB.left) &&
             eqExpr(exprA.right, exprB.right);
    case "ConditionalExpression":
      return exprA.type == exprB.type &&
             eqProp(exprA.test, exprB.test) &&
             eqExpr(exprA.consequent, exprB.consequent) &&
             eqExpr(exprA.alternate, exprB.alternate);
    case "CallExpression":
      return exprA.type == exprB.type &&
             eqHeap(exprA.heap, exprB.heap) &&
             eqExpr(exprA.callee, exprB.callee) &&
             exprA.args.length == exprB.args.length &&
             exprA.args.every((e,idx) => eqExpr(e, exprB.args[idx]));
  }
}

export function eqProp(propA: P, propB: P): boolean {
  switch (propA.type) {
    case "Truthy":
      return propA.type == propB.type &&
             eqExpr(propA.expr, propB.expr);
    case "And":
    case "Or":
      return propA.type == propB.type &&
             propA.clauses.length == propB.clauses.length &&
             propA.clauses.every((c,idx) => eqProp(c, propB.clauses[idx]));
    case "Eq":
      return propA.type == propB.type &&
             eqExpr(propA.left, propB.left) &&
             eqExpr(propA.right, propB.right);
    case "HeapEq":
      return propA.type == propB.type &&
             eqHeap(propA.left, propB.left) &&
             eqHeap(propA.right, propB.right);
    case "Not":
      return propA.type == propB.type &&
             eqProp(propA.arg, propB.arg);
    case "True":
    case "False":
      return propA.type == propB.type;
    case "CallTrigger":
    case "Precondition":
    case "Postcondition":
      return propA.type == propB.type &&
             eqHeap(propA.heap, propB.heap) &&
             eqExpr(propA.callee, propB.callee) &&
             propA.args.length == propB.args.length &&
             propA.args.every((e,idx) => eqExpr(e, propB.args[idx]));
    case "ForAll":
      return propA.type == propB.type &&
             eqExpr(propA.callee, propB.callee) &&
             propA.args.length == propB.args.length &&
             propA.args.every((e,idx) => e == propB.args[idx]) &&
             propA.existsHeaps.size == propB.existsHeaps.size &&
             [...propA.existsHeaps].every(h => propB.existsHeaps.has(h)) &&
             propA.existsLocs.size == propB.existsLocs.size &&
             [...propA.existsLocs].every(l => propB.existsLocs.has(l)) &&
             propA.existsVars.size == propB.existsVars.size &&
             [...propA.existsVars].every(v => propB.existsVars.has(v)) &&
             eqProp(propA.prop, propB.prop);
  }
}

export abstract class PropVisitor<L,H,R,S> {

  abstract visitLocation(loc: Syntax.Location): L;

  abstract visitHeap(heap: Heap): H;
  abstract visitHeapStore(prop: Syntax.HeapStore): H;
  abstract visitHeapEffect(prop: Syntax.HeapEffect): H;

  abstract visitVariable(expr: Syntax.Variable): R;
  abstract visitHeapReference(expr: Syntax.HeapReference): R;
  abstract visitLiteral(expr: Syntax.Literal): R;
  abstract visitArrayExpression(expr: Syntax.ArrayExpression): R;
  abstract visitUnaryExpression(expr: Syntax.UnaryExpression): R;
  abstract visitBinaryExpression(expr: Syntax.BinaryExpression): R;
  abstract visitConditionalExpression(expr: Syntax.ConditionalExpression): R;
  abstract visitCallExpression(expr: Syntax.CallExpression): R;

  abstract visitTruthy(prop: Syntax.Truthy): S;
  abstract visitAnd(prop: Syntax.And): S;
  abstract visitOr(prop: Syntax.Or): S;
  abstract visitEq(prop: Syntax.Eq): S;
  abstract visitHeapEq(prop: Syntax.HeapEq): S;
  abstract visitNot(prop: Syntax.Not): S;
  abstract visitTrue(prop: Syntax.True): S;
  abstract visitFalse(prop: Syntax.False): S;
  abstract visitPrecondition(prop: Syntax.Precondition): S;
  abstract visitPostcondition(prop: Syntax.Postcondition): S;
  abstract visitForAll(prop: Syntax.ForAll): S;
  abstract visitCallTrigger(prop: Syntax.CallTrigger): S;

  visitHeapExpr(heap: Syntax.HeapExpression): H {
    if (typeof(heap) == "number") return this.visitHeap(heap);
    switch (heap.type) {
      case "HeapStore": return this.visitHeapStore(heap);
      case "HeapEffect": return this.visitHeapEffect(heap);
    }
  }

  visitExpr(expr: A): R {
    if (typeof(expr) == "string") return this.visitVariable(expr);
    switch (expr.type) {
      case "HeapReference": return this.visitHeapReference(expr);
      case "Literal": return this.visitLiteral(expr);
      case 'ArrayExpression': return this.visitArrayExpression(expr);
      case "UnaryExpression": return this.visitUnaryExpression(expr);
      case "BinaryExpression": return this.visitBinaryExpression(expr);
      case "ConditionalExpression": return this.visitConditionalExpression(expr);
      case "CallExpression": return this.visitCallExpression(expr);
    }
  }

  visitProp(prop: P): S {
    switch (prop.type) {
      case "Truthy": return this.visitTruthy(prop);
      case "And": return this.visitAnd(prop);
      case "Or": return this.visitOr(prop);
      case "Eq": return this.visitEq(prop);
      case "HeapEq": return this.visitHeapEq(prop);
      case "Not": return this.visitNot(prop);
      case "True": return this.visitTrue(prop);
      case "False": return this.visitFalse(prop);
      case "Precondition": return this.visitPrecondition(prop);
      case "Postcondition": return this.visitPostcondition(prop);
      case "ForAll": return this.visitForAll(prop);
      case "CallTrigger": return this.visitCallTrigger(prop);
    }
  }
}

export abstract class PropReducer<R> extends PropVisitor<R,R,R,R> {

  abstract empty(): R;

  abstract reduce(x: R, y: R): R;

  r(...r: R[]) {
    return r.reduce((res,r) => this.reduce(res, r), this.empty());
  }

  visitLocation(loc: Syntax.Location) { return this.empty(); }

  visitHeap(heap: Heap): R { return this.empty(); }

  visitHeapStore(prop: Syntax.HeapStore): R {
    return this.r(this.visitHeapExpr(prop.target),
                  this.visitLocation(prop.loc),
                  this.visitExpr(prop.expr));
  }

  visitHeapEffect(prop: Syntax.HeapEffect): R {
    return this.r(this.visitHeapExpr(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }

  visitVariable(expr: Syntax.Variable) { return this.empty(); }

  visitHeapReference(expr: Syntax.HeapReference) {
    return this.r(this.visitHeapExpr(expr.heap), this.visitLocation(expr.loc));
  }

  visitLiteral(expr: Syntax.Literal) { return this.empty(); }

  visitArrayExpression(expr: Syntax.ArrayExpression) {
    return this.r(...expr.elements.map(e => this.visitExpr(e)));
  }

  visitUnaryExpression(expr: Syntax.UnaryExpression) {
    return this.visitExpr(expr.argument);
  }

  visitBinaryExpression(expr: Syntax.BinaryExpression) {
    return this.r(this.visitExpr(expr.left), this.visitExpr(expr.right));
  }

  visitConditionalExpression(expr: Syntax.ConditionalExpression): R {
    return this.r(this.visitProp(expr.test), this.visitExpr(expr.consequent), this.visitExpr(expr.alternate));
  }

  visitCallExpression(expr: Syntax.CallExpression): R {
    return this.r(this.visitHeapExpr(expr.heap),
                  this.visitExpr(expr.callee),
                  ...expr.args.map(a => this.visitExpr(a)));
  }

  visitTruthy(prop: Syntax.Truthy): R {
    return this.visitExpr(prop.expr);
  }

  visitAnd(prop: Syntax.And): R {
    return this.r(...prop.clauses.map(c => this.visitProp(c)));
  }

  visitOr(prop: Syntax.Or): R {
    return this.r(...prop.clauses.map(c => this.visitProp(c)));
  }

  visitEq(prop: Syntax.Eq): R {
    return this.r(this.visitExpr(prop.left), this.visitExpr(prop.right));
  }

  visitNot(prop: Syntax.Not): R {
    return this.visitProp(prop.arg);
  }

  visitTrue(prop: Syntax.True): R { return this.empty(); }

  visitFalse(prop: Syntax.False): R { return this.empty(); }

  visitPrecondition(prop: Syntax.Precondition): R {
    return this.r(this.visitHeapExpr(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }

  visitPostcondition(prop: Syntax.Postcondition): R {
    return this.r(this.visitHeapExpr(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }

  visitForAll(prop: Syntax.ForAll): R {
    return this.r(this.visitExpr(prop.callee),
                  this.visitProp(prop.prop));
  }

  visitCallTrigger(prop: Syntax.CallTrigger): R {
    return this.r(this.visitHeapExpr(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }

  visitHeapEq(prop: Syntax.HeapEq): R {
    return this.r(this.visitHeapExpr(prop.left),
                  this.visitHeapExpr(prop.right));
  }
}

export class PropTransformer extends PropVisitor<Syntax.Location, Syntax.HeapExpression, A, P> {

  visitLocation(loc: Syntax.Location): Syntax.Location {
    return loc;
  }

  visitHeap(heap: Heap): Syntax.HeapExpression {
    return heap;
  }

  visitHeapStore(expr: Syntax.HeapStore): Syntax.HeapExpression {
    return {
      type: "HeapStore",
      target: this.visitHeapExpr(expr.target),
      loc: this.visitLocation(expr.loc),
      expr: this.visitExpr(expr.expr)
    };
  }
  
  visitHeapEffect(expr: Syntax.HeapEffect): Syntax.HeapExpression {
    return {
     type: "HeapEffect",
     callee: this.visitExpr(expr.callee),
     heap: this.visitHeapExpr(expr.heap),
     args: expr.args.map(a => this.visitExpr(a))
    };
  }
  
  visitVariable(expr: Syntax.Variable): A {
    return expr;
  }

  visitHeapReference(expr: Syntax.HeapReference): A {
    return {
      type: "HeapReference",
      heap: this.visitHeapExpr(expr.heap),
      loc: this.visitLocation(expr.loc)
    }
  }

  visitLiteral(expr: Syntax.Literal): A {
    return expr;
  }
  
  visitArrayExpression(expr: Syntax.ArrayExpression): A {
    return { type: "ArrayExpression", elements: expr.elements.map(e => this.visitExpr(e)) };
  }
  
  visitUnaryExpression(expr: Syntax.UnaryExpression): A {
    return {
      type: "UnaryExpression",
      operator: expr.operator,
      argument: this.visitExpr(expr.argument)
    };
  }
  
  visitBinaryExpression(expr: Syntax.BinaryExpression): A {
    return {
     type: "BinaryExpression",
     operator: expr.operator,
     left: this.visitExpr(expr.left),
     right: this.visitExpr(expr.right)
    };
  }
  
  visitConditionalExpression(expr: Syntax.ConditionalExpression): A {
    return {
     type: "ConditionalExpression",
     test: this.visitProp(expr.test),
     consequent: this.visitExpr(expr.consequent),
     alternate: this.visitExpr(expr.alternate)
    };
  }
  
  visitCallExpression(expr: Syntax.CallExpression): A {
    return {
     type: "CallExpression",
     callee: this.visitExpr(expr.callee),
     heap: this.visitHeapExpr(expr.heap),
     args: expr.args.map(a => this.visitExpr(a))
    };
  }

  visitTruthy(prop: Syntax.Truthy): P {
    return { type: "Truthy", expr: this.visitExpr(prop.expr) };
  }
  
  visitAnd(prop: Syntax.And): P {
    return and(...prop.clauses.map(c => this.visitProp(c)));
  }
  
  visitOr(prop: Syntax.Or): P {
    return or(...prop.clauses.map(c => this.visitProp(c)));
  }
  
  visitEq(prop: Syntax.Eq): P {
    return eq(this.visitExpr(prop.left), this.visitExpr(prop.right));
  }
  
  visitHeapEq(prop: Syntax.HeapEq): P {
    return heapEq(this.visitHeapExpr(prop.left), this.visitHeapExpr(prop.right));
  }
  
  visitNot(prop: Syntax.Not): P {
    return not(this.visitProp(prop.arg));
  }
  
  visitTrue(prop: Syntax.True): P {
    return prop;
  }
  
  visitFalse(prop: Syntax.False): P {
    return prop;
  }
  
  visitPrecondition(prop: Syntax.Precondition): P {
    return {
      type: "Precondition",
      callee: this.visitExpr(prop.callee),
      heap: this.visitHeapExpr(prop.heap),
      args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitPostcondition(prop: Syntax.Postcondition): P {
    return {
      type: "Postcondition",
      callee: this.visitExpr(prop.callee),
      heap: this.visitHeapExpr(prop.heap),
      args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitForAll(prop: Syntax.ForAll): P {
    return {
      type: "ForAll",
      callee: this.visitExpr(prop.callee),
      args: prop.args,
      existsHeaps: new Set([...prop.existsHeaps]),
      existsLocs: new Set([...prop.existsLocs]),
      existsVars: new Set([...prop.existsVars]),
      prop: this.visitProp(prop.prop),
      instantiations: [...prop.instantiations] // shallow copy, do not process
    };
  }
  
  visitCallTrigger(prop: Syntax.CallTrigger): P {
    return {
      type: "CallTrigger",
      callee: this.visitExpr(prop.callee),
      heap: this.visitHeapExpr(prop.heap),
      args: prop.args.map(a => this.visitExpr(a))
    };
  }
}

export function copy(prop: P): P {
  return (new PropTransformer()).visitProp(prop);
}

export class Substituter extends PropTransformer {
  thetaHeap: { [heap: number]: Syntax.HeapExpression } = {};
  thetaLoc: { [lname: string]: Syntax.Location } = {};
  thetaVar: { [vname: string]: Syntax.Expression } = {};

  visitHeap(heap: Heap): Syntax.HeapExpression {
    return heap in this.thetaHeap ? this.thetaHeap[heap] : heap;
  }

  visitLocation(l: Syntax.Location): Syntax.Location {
    return l in this.thetaLoc ? this.thetaLoc[l] : l;
  }
  
  visitVariable(v: Syntax.Variable): Syntax.Expression {
    return v in this.thetaVar ? this.thetaVar[v] : v;
  }

  replaceHeap(orig: number, expr: Syntax.HeapExpression): Substituter {
    this.thetaHeap[orig] = expr;
    return this;
  }
  
  replaceLoc(orig: Syntax.Location, expr: Syntax.Location): Substituter {
    this.thetaLoc[orig] = expr;
    return this;
  }
  
  replaceVar(orig: Syntax.Variable, expr: Syntax.Expression): Substituter {
    this.thetaVar[orig] = expr;
    return this;
  }
  
  visitForAll(prop: Syntax.ForAll): P {
    const origAlphaHeap = Object.assign({}, this.thetaHeap);
    const origAlphaLoc = Object.assign({}, this.thetaLoc);
    const origAlphaVar = Object.assign({}, this.thetaVar);
    try {
      delete this.thetaHeap[0];
      prop.args.forEach(a => { delete this.thetaVar[a]; });
      prop.existsHeaps.forEach(h => { delete this.thetaHeap[h]; });
      prop.existsLocs.forEach(l => { delete this.thetaLoc[l]; });
      prop.existsVars.forEach(v => { delete this.thetaVar[v]; });
      return super.visitForAll(prop);
    } finally {
      this.thetaHeap = origAlphaHeap;
      this.thetaLoc = origAlphaLoc;
      this.thetaVar = origAlphaVar;
    }
  }
}
