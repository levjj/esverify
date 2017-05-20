import { flatMap } from "./util";

export namespace ASyntax {

  export type Heap = number;
  export type Location = string;
  export type Variable = string;
  export interface HeapReference { type: "HeapReference", loc: Location, heap: Heap }
  export interface Literal { type: "Literal", value: undefined | null | boolean | number | string }
  export interface ArrayExpression { type: "ArrayExpression", elements: Array<Expression> }
  type UnaryOperator = "-" | "+" | "!" | "~" | "typeof" | "void";
  export interface UnaryExpression { type: "UnaryExpression",
                                     operator: UnaryOperator,
                                     argument: Expression }
  type BinaryOperator = "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">="
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
                                    heap: Heap,
                                    args: Array<Expression> }
  export type Expression = Variable
                         | HeapReference
                         | Literal
                         | ArrayExpression
                         | UnaryExpression
                         | BinaryExpression
                         | ConditionalExpression
                         | CallExpression;

  export interface Truthy { type: "Truthy", expr: Expression }
  export interface And { type: "And", clauses: Array<Proposition> }
  export interface Or { type: "Or", clauses: Array<Proposition> }
  export interface Eq { type: "Eq", left: Expression, right: Expression }
  export interface Iff { type: "Iff", left: Proposition, right: Proposition }
  export interface Not { type: "Not", arg: Proposition }
  export interface True { type: "True" }
  export interface False { type: "False" }
  export interface Precondition { type: "Precondition",
                                  callee: Expression,
                                  heap: Heap,
                                  args: Array<Expression> }
  export interface Postcondition { type: "Postcondition",
                                   callee: Expression,
                                   heap: Heap,
                                   args: Array<Expression> }
  export interface ForAll { type: "ForAll",
                            callee: Expression,
                            args: Array<string>,
                            existsHeaps: Set<Heap>,
                            existsLocs: Locs,
                            existsVars: Vars,
                            prop: Proposition,
                            instantiations: Array<CallTrigger>
                           }
  export interface CallTrigger { type: "CallTrigger",
                                 callee: Expression,
                                 heap: Heap,
                                 args: Array<Expression> }
  export interface HeapStore { type: "HeapStore",
                               heap: Heap,
                               loc: Location,
                               expr: Expression }
  export interface HeapEffect { type: "HeapEffect",
                                callee: Expression,
                                heap: Heap,
                                args: Array<Expression> }
  export interface HeapPromote { type: "HeapPromote",
                                 from: Heap,
                                 to: Heap }
  export type Proposition = Truthy
                          | And
                          | Or
                          | Iff
                          | Eq
                          | Not
                          | True
                          | False
                          | Precondition
                          | Postcondition
                          | ForAll
                          | CallTrigger
                          | HeapStore
                          | HeapEffect
                          | HeapPromote;
}

export type Heap = ASyntax.Heap;
export type A = ASyntax.Expression;
export type P = ASyntax.Proposition;
export type Heaps = Set<ASyntax.Heap>;
export type Locs = Set<ASyntax.Location>;
export type Vars = Set<ASyntax.Variable>;
export type SMTInput = string;
export type SMTOutput = string;

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

export function iff(left: P, right: P): P {
  if (left.type == "True") return right;
  if (right.type == "True") return left;
  if (eqProp(left, right)) return tru;
  return { type: "Iff", left, right };
}

export function not(arg: P): P {
  if (arg.type == "True") return fls;
  if (arg.type == "False") return tru;
  if (arg.type == "Not") return arg.arg;
  return { type: "Not", arg };
}

export function heapStore(heap: Heap, loc: string, expr: A): P {
  return { type: "HeapStore", heap, loc, expr };
}

export function heapPromote(from: Heap, to: Heap): P {
  return { type: "HeapPromote", from, to };
}


function eqExpr(exprA: A, exprB: A): boolean {
  if (typeof(exprA) == "string") {
    return typeof(exprB) == "string" && exprA == exprB;
  }
  if (typeof(exprB) == "string") return false;
  switch (exprA.type) {
    case "HeapReference":
      return exprA.type == exprB.type &&
             exprA.heap == exprB.heap &&
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
             exprA.heap == exprB.heap &&
             eqExpr(exprA.callee, exprB.callee) &&
             exprA.args.length == exprB.args.length &&
             exprA.args.every((e,idx) => eqExpr(e, exprB.args[idx]));
  }
}

function eqProp(propA: P, propB: P): boolean {
  switch (propA.type) {
    case "Truthy":
      return propA.type == propB.type &&
             eqExpr(propA.expr, propB.expr);
    case "And":
    case "Or":
      return propA.type == propB.type &&
             propA.clauses.length == propB.clauses.length &&
             propA.clauses.every((c,idx) => eqProp(c, propB.clauses[idx]));
    case "Iff":
      return propA.type == propB.type &&
             eqProp(propA.left, propB.left) &&
             eqProp(propA.right, propB.right);
    case "Eq":
      return propA.type == propB.type &&
             eqExpr(propA.left, propB.left) &&
             eqExpr(propA.right, propB.right);
    case "Not":
      return propA.type == propB.type &&
             eqProp(propA.arg, propB.arg);
    case "True":
    case "False":
      return propA.type == propB.type;
    case "CallTrigger":
    case "Precondition":
    case "Postcondition":
    case "HeapEffect":
      return propA.type == propB.type &&
             propA.heap == propB.heap &&
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
    case "HeapStore":
      return propA.type == propB.type &&
             propA.heap == propB.heap &&
             propA.loc == propB.loc &&
             eqExpr(propA.expr, propB.expr);
    case "HeapPromote":
      return propA.type == propB.type &&
             propA.from == propB.from &&
             propA.to == propB.to;
  }
}

abstract class PropVisitor<H,L,R,S> {

  abstract visitHeap(heap: Heap): H;

  abstract visitLocation(loc: ASyntax.Location): L;

  abstract visitVariable(expr: ASyntax.Variable): R;
  abstract visitHeapReference(expr: ASyntax.HeapReference): R;
  abstract visitLiteral(expr: ASyntax.Literal): R;
  abstract visitArrayExpression(expr: ASyntax.ArrayExpression): R;
  abstract visitUnaryExpression(expr: ASyntax.UnaryExpression): R;
  abstract visitBinaryExpression(expr: ASyntax.BinaryExpression): R;
  abstract visitConditionalExpression(expr: ASyntax.ConditionalExpression): R;
  abstract visitCallExpression(expr: ASyntax.CallExpression): R;

  abstract visitTruthy(prop: ASyntax.Truthy): S;
  abstract visitAnd(prop: ASyntax.And): S;
  abstract visitOr(prop: ASyntax.Or): S;
  abstract visitIff(prop: ASyntax.Iff): S;
  abstract visitEq(prop: ASyntax.Eq): S;
  abstract visitNot(prop: ASyntax.Not): S;
  abstract visitTrue(prop: ASyntax.True): S;
  abstract visitFalse(prop: ASyntax.False): S;
  abstract visitPrecondition(prop: ASyntax.Precondition): S;
  abstract visitPostcondition(prop: ASyntax.Postcondition): S;
  abstract visitForAll(prop: ASyntax.ForAll): S;
  abstract visitCallTrigger(prop: ASyntax.CallTrigger): S;
  abstract visitHeapStore(prop: ASyntax.HeapStore): S;
  abstract visitHeapEffect(prop: ASyntax.HeapEffect): S;
  abstract visitHeapPromote(prop: ASyntax.HeapPromote): S;

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
      case "Iff": return this.visitIff(prop);
      case "Eq": return this.visitEq(prop);
      case "Not": return this.visitNot(prop);
      case "True": return this.visitTrue(prop);
      case "False": return this.visitFalse(prop);
      case "Precondition": return this.visitPrecondition(prop);
      case "Postcondition": return this.visitPostcondition(prop);
      case "ForAll": return this.visitForAll(prop);
      case "CallTrigger": return this.visitCallTrigger(prop);
      case "HeapStore": return this.visitHeapStore(prop);
      case "HeapEffect": return this.visitHeapEffect(prop);
      case "HeapPromote": return this.visitHeapPromote(prop);
    }
  }
}

abstract class PropReducer<R> extends PropVisitor<R,R,R,R> {

  abstract empty(): R;
  abstract reduce(x: R, y: R): R;

  r(...r: R[]) {
    return r.reduce((res,r) => this.reduce(res, r), this.empty());
  }

  visitHeap(heap: Heap): R { return this.empty(); }
  visitLocation(loc: ASyntax.Location) { return this.empty(); }

  visitVariable(expr: ASyntax.Variable) { return this.empty(); }
  visitHeapReference(expr: ASyntax.HeapReference) {
    return this.r(this.visitHeap(expr.heap), this.visitLocation(expr.loc));
  }
  visitLiteral(expr: ASyntax.Literal) { return this.empty(); }
  visitArrayExpression(expr: ASyntax.ArrayExpression) {
    return this.r(...expr.elements.map(e => this.visitExpr(e)));
  }
  visitUnaryExpression(expr: ASyntax.UnaryExpression) {
    return this.visitExpr(expr.argument);
  }
  visitBinaryExpression(expr: ASyntax.BinaryExpression) {
    return this.r(this.visitExpr(expr.left), this.visitExpr(expr.right));
  }
  visitConditionalExpression(expr: ASyntax.ConditionalExpression): R {
    return this.r(this.visitProp(expr.test), this.visitExpr(expr.consequent), this.visitExpr(expr.alternate));
  }
  visitCallExpression(expr: ASyntax.CallExpression): R {
    return this.r(this.visitHeap(expr.heap),
                  this.visitExpr(expr.callee),
                  ...expr.args.map(a => this.visitExpr(a)));
  }

  visitTruthy(prop: ASyntax.Truthy): R {
    return this.visitExpr(prop.expr);
  }
  visitAnd(prop: ASyntax.And): R {
    return this.r(...prop.clauses.map(c => this.visitProp(c)));
  }
  visitOr(prop: ASyntax.Or): R {
    return this.r(...prop.clauses.map(c => this.visitProp(c)));
  }
  visitIff(prop: ASyntax.Iff): R {
    return this.r(this.visitProp(prop.left), this.visitProp(prop.right));
  }
  visitEq(prop: ASyntax.Eq): R {
    return this.r(this.visitExpr(prop.left), this.visitExpr(prop.right));
  }
  visitNot(prop: ASyntax.Not): R {
    return this.visitProp(prop.arg);
  }
  visitTrue(prop: ASyntax.True): R { return this.empty(); }
  visitFalse(prop: ASyntax.False): R { return this.empty(); }
  visitPrecondition(prop: ASyntax.Precondition): R {
    return this.r(this.visitHeap(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }
  visitPostcondition(prop: ASyntax.Postcondition): R {
    return this.r(this.visitHeap(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }
  visitForAll(prop: ASyntax.ForAll): R {
    return this.r(...[...prop.existsHeaps].map(h => this.visitHeap(h)),
                  ...[...prop.existsLocs].map(l => this.visitLocation(l)),
                  ...[...prop.existsVars].map(v => this.visitVariable(v)),
                  this.visitExpr(prop.callee),
                  this.visitProp(prop.prop));
  }
  visitCallTrigger(prop: ASyntax.CallTrigger): R {
    return this.r(this.visitHeap(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }
  visitHeapStore(prop: ASyntax.HeapStore): R {
    return this.r(this.visitHeap(prop.heap),
                  this.visitLocation(prop.loc),
                  this.visitExpr(prop.expr));
  }
  visitHeapEffect(prop: ASyntax.HeapEffect): R {
    return this.r(this.visitHeap(prop.heap),
                  this.visitExpr(prop.callee),
                  ...prop.args.map(a => this.visitExpr(a)));
  }
  visitHeapPromote(prop: ASyntax.HeapPromote): R {
    return this.r(this.visitHeap(prop.from), this.visitHeap(prop.to));
  }
}

const unOpToSMT: {[unop: string]: string} = {
  "-": "_js-negative",
  "+":"_js-positive",
  "!": "_js-not",
  "~": "_js-bnot",
  "typeof": "_js-typeof",
  "void": "_js-void"
};

const binOpToSMT: {[binop: string]: string} = {
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

class SMTGenerator extends PropVisitor<SMTInput, SMTInput, SMTInput, SMTInput> {

  visitHeap(heap: Heap): SMTInput {
    return "h_" + heap;
  }

  visitLocation(loc: ASyntax.Location): SMTInput {
    return "l_" + loc;
  }

  visitVariable(expr: ASyntax.Variable): SMTInput {
    return "v_" + expr;
  }

  visitHeapReference(expr: ASyntax.HeapReference): SMTInput {
    return `(select ${this.visitHeap(expr.heap)} ${this.visitLocation(expr.loc)})`;
  }
  
  visitLiteral(expr: ASyntax.Literal): SMTInput {
    if (expr.value === undefined) return `jsundefined`;
    if (expr.value === null) return `jsnull`;
    switch (typeof expr.value) {
      case "boolean": return `(jsbool ${expr.value})`;
      case "number": return `(jsnum ${expr.value})`;
      case "string": return `(jsstr "${expr.value}")`;
      default: throw new Error("unsupported");
    }
  }
  
  visitArrayExpression(expr: ASyntax.ArrayExpression): SMTInput {
    const arrayToSMT = (elements: Array<A>): SMTInput => {
      if (elements.length === 0) return `empty`;
      const [head, ...tail] = elements;
      const h = head || {type: "Literal", value: "undefined"};
      return `(cons ${this.visitExpr(h)} ${arrayToSMT(tail)})`;
    };
    return `(jsarray ${arrayToSMT(expr.elements)})`;
  }
  
  visitUnaryExpression(expr: ASyntax.UnaryExpression): SMTInput {
    const arg = this.visitExpr(expr.argument),
          op = unOpToSMT[expr.operator];
    return `(${op} ${arg})`;
  }
  
  visitBinaryExpression(expr: ASyntax.BinaryExpression): SMTInput {
    const left = this.visitExpr(expr.left),
          right = this.visitExpr(expr.right),
          binop = binOpToSMT[expr.operator];
    return `(${binop} ${left} ${right})`;
  }
  
  visitConditionalExpression(expr: ASyntax.ConditionalExpression): SMTInput {
    const test = this.visitProp(expr.test),
          then = this.visitExpr(expr.consequent),
          elze = this.visitExpr(expr.alternate);
    return `(ite ${test} ${then} ${elze})`;
  }
  
  visitCallExpression(expr: ASyntax.CallExpression): SMTInput {
    const {callee, heap, args} = expr;
    if (args.length > 9) {
      throw new Error("unsupported");
    }
    return `(app${args.length} ${this.visitExpr(callee)} ${this.visitHeap(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")})`;
  }

  visitTruthy(prop: ASyntax.Truthy): SMTInput {
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
  
  visitAnd(prop: ASyntax.And): SMTInput {
    const clauses: Array<SMTInput> = flatMap(prop.clauses,
      c => c.type == "And" ? c.clauses : [c]) 
      .map(p => this.visitProp(p))
      .filter(s => s != `true`);
    if (clauses.find(s => s == `false`)) return `false`;
    if (clauses.length == 0) return `true`;
    if (clauses.length == 1) return clauses[0];
    return `(and ${clauses.join(' ')})`;
  }
  
  visitOr(prop: ASyntax.Or): SMTInput {
    const clauses: Array<SMTInput> = flatMap(prop.clauses,
      c => c.type == "Or" ? c.clauses : [c]) 
      .map(p => this.visitProp(p))
      .filter(s => s != `false`);
    if (clauses.find(s => s == `true`)) return `true`;
    if (clauses.length == 0) return `false`;
    if (clauses.length == 1) return clauses[0];
    return `(or ${clauses.join(' ')})`;
  }
  
  visitIff(prop: ASyntax.Iff): SMTInput {
    const left: SMTInput = this.visitProp(prop.left);
    const right: SMTInput = this.visitProp(prop.right);
    if (left == `true`) return right;
    if (right == `true`) return left;
    if (left == right) return `true`;
    return `(= ${left} ${right})`;
  }
  
  visitEq(prop: ASyntax.Eq): SMTInput {
    const left: SMTInput = this.visitExpr(prop.left);
    const right: SMTInput = this.visitExpr(prop.right);
    if (left == right) return `true`;
    return `(= ${left} ${right})`;
  }
  
  visitNot(prop: ASyntax.Not): SMTInput {
    const arg: SMTInput = this.visitProp(prop.arg);
    if (arg == "true") return `false`;
    if (arg == "false") return `true`;
    return `(not ${arg})`;
  }
  
  visitTrue(prop: ASyntax.True): SMTInput {
    return `true`;
  }
  
  visitFalse(prop: ASyntax.False): SMTInput {
    return `false`;
  }
  
  visitPrecondition(prop: ASyntax.Precondition): SMTInput {
    const {callee, heap, args} = prop;
    if (args.length > 9) {
      throw new Error("unsupported");
    }
    return `(pre${args.length} ${this.visitExpr(callee)} ${this.visitHeap(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")})`;
  }
  
  visitPostcondition(prop: ASyntax.Postcondition): SMTInput {
    const {callee, heap, args} = prop;
    if (args.length > 9) {
      throw new Error("unsupported");
    }
    return `(post${args.length} ${this.visitExpr(callee)} ${this.visitHeap(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")})`;
  }
  
  visitForAll(prop: ASyntax.ForAll): SMTInput {
    const {args, callee} = prop;
    const params = `${args.map(a => `(v_${a} JSVal)`).join(' ')}`;
    if (args.length > 9) throw new Error("Not supported");
    const callP: P = { type: "CallTrigger", callee, heap: 0, args: args };
    const effP: P = { type: "HeapEffect", callee, heap: 0, args: args };
    let p = this.visitProp(implies(callP, and(effP, prop.prop)));
    if (prop.existsLocs.size > 0 || prop.existsHeaps.size > 0) {
      p = `(exists (${[1, ...prop.existsHeaps].map(h => `(${this.visitHeap(h)} Heap)`).join(' ')} `
                 + `${[...prop.existsLocs].map(l => `(${this.visitLocation(l)} Loc)`).join(' ')} `
                 + `${[...prop.existsVars].map(v => `(${this.visitVariable(v)} JSVal)`).join(' ')})\n  ${p})`;
    }
    const trigger = this.visitProp(callP);
    return `(forall ((${this.visitHeap(0)} Heap) ${params}) (!\n  ${p}\n  :pattern ((${trigger}))))`;
  }
  
  visitCallTrigger(prop: ASyntax.CallTrigger): SMTInput {
    const {callee, heap, args} = prop;
    if (args.length > 9) {
      throw new Error("unsupported");
    }
    return `(call${args.length} ${this.visitExpr(callee)} ${this.visitHeap(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")})`;
  }
  
  visitHeapStore(prop: ASyntax.HeapStore): SMTInput {
    return `(= ${this.visitHeap(prop.heap + 1)} (store ${this.visitHeap(prop.heap)} ${this.visitLocation(prop.loc)} ${this.visitExpr(prop.expr)}))`
  }
  
  visitHeapEffect(prop: ASyntax.HeapEffect): SMTInput {
    const {callee, heap, args} = prop;
    if (args.length > 9) {
      throw new Error("unsupported");
    }
    return `(= ${this.visitHeap(prop.heap + 1)} (eff${args.length} ${this.visitExpr(callee)} ${this.visitHeap(heap)}${args.map(a => ' ' + this.visitExpr(a)).join("")}))`;
  }
  
  visitHeapPromote(prop: ASyntax.HeapPromote): SMTInput {
    if (prop.from == prop.to) return `true`;
    return `(= ${this.visitHeap(prop.from)} ${this.visitHeap(prop.to)})`;
  }
}

export function propositionToSMT(prop: P): SMTInput {
  const v = new SMTGenerator();
  return v.visitProp(prop);
}

export function propositionToAssert(prop: P): SMTInput {
  if (prop.type == "And") {
    return prop.clauses.map(propositionToAssert).join("");
  }
  return `(assert ${propositionToSMT(prop)})\n`;
}

class PropTransformer extends PropVisitor<Heap, ASyntax.Location, A, P> {

  visitHeap(heap: Heap): Heap {
    return heap;
  }

  visitLocation(loc: ASyntax.Location): ASyntax.Location {
    return loc;
  }

  visitVariable(expr: ASyntax.Variable): ASyntax.Variable {
    return expr;
  }

  visitHeapReference(expr: ASyntax.HeapReference): A {
    return {
      type: "HeapReference",
      heap: this.visitHeap(expr.heap),
      loc: this.visitLocation(expr.loc)
    }
  }
  
  visitLiteral(expr: ASyntax.Literal): A {
    return expr;
  }
  
  visitArrayExpression(expr: ASyntax.ArrayExpression): A {
    return { type: "ArrayExpression", elements: expr.elements.map(e => this.visitExpr(e)) };
  }
  
  visitUnaryExpression(expr: ASyntax.UnaryExpression): A {
    return {
      type: "UnaryExpression",
      operator: expr.operator,
      argument: this.visitExpr(expr.argument)
    };
  }
  
  visitBinaryExpression(expr: ASyntax.BinaryExpression): A {
    return {
     type: "BinaryExpression",
     operator: expr.operator,
     left: this.visitExpr(expr.left),
     right: this.visitExpr(expr.right)
    };
  }
  
  visitConditionalExpression(expr: ASyntax.ConditionalExpression): A {
    return {
     type: "ConditionalExpression",
     test: this.visitProp(expr.test),
     consequent: this.visitExpr(expr.consequent),
     alternate: this.visitExpr(expr.alternate)
    };
  }
  
  visitCallExpression(expr: ASyntax.CallExpression): A {
    return {
     type: "CallExpression",
     callee: this.visitExpr(expr.callee),
     heap: this.visitHeap(expr.heap),
     args: expr.args.map(a => this.visitExpr(a))
    };
  }

  visitTruthy(prop: ASyntax.Truthy): P {
    return { type: "Truthy", expr: this.visitExpr(prop.expr) };
  }
  
  visitAnd(prop: ASyntax.And): P {
    return and(...prop.clauses.map(c => this.visitProp(c)));
  }
  
  visitOr(prop: ASyntax.Or): P {
    return or(...prop.clauses.map(c => this.visitProp(c)));
  }
  
  visitIff(prop: ASyntax.Iff): P {
    return iff(this.visitProp(prop.left), this.visitProp(prop.right));
  }
  
  visitEq(prop: ASyntax.Eq): P {
    return eq(this.visitExpr(prop.left), this.visitExpr(prop.right));
  }
  
  visitNot(prop: ASyntax.Not): P {
    return not(this.visitProp(prop.arg));
  }
  
  visitTrue(prop: ASyntax.True): P {
    return prop;
  }
  
  visitFalse(prop: ASyntax.False): P {
    return prop;
  }
  
  visitPrecondition(prop: ASyntax.Precondition): P {
    return {
      type: "Precondition",
      callee: this.visitExpr(prop.callee),
      heap: this.visitHeap(prop.heap),
      args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitPostcondition(prop: ASyntax.Postcondition): P {
    return {
      type: "Postcondition",
      callee: this.visitExpr(prop.callee),
      heap: this.visitHeap(prop.heap),
      args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitForAll(prop: ASyntax.ForAll): P {
    return {
      type: "ForAll",
      callee: this.visitExpr(prop.callee),
      args: prop.args,
      existsHeaps: new Set([...prop.existsHeaps].map(h => this.visitHeap(h))),
      existsLocs: new Set([...prop.existsLocs].map(l => this.visitLocation(l))),
      existsVars: new Set([...prop.existsVars].map(v => this.visitVariable(v))),
      prop: this.visitProp(prop.prop),
      instantiations: [...prop.instantiations] // shallow copy, do not process
    };
  }
  
  visitCallTrigger(prop: ASyntax.CallTrigger): P {
    return {
      type: "CallTrigger",
      callee: this.visitExpr(prop.callee),
      heap: this.visitHeap(prop.heap),
      args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitHeapStore(prop: ASyntax.HeapStore): P {
    return {
      type: "HeapStore",
      heap: this.visitHeap(prop.heap),
      loc: this.visitLocation(prop.loc),
      expr: this.visitExpr(prop.expr)
    };
  }
  
  visitHeapEffect(prop: ASyntax.HeapEffect): P {
    return {
     type: "HeapEffect",
     callee: this.visitExpr(prop.callee),
     heap: this.visitHeap(prop.heap),
     args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitHeapPromote(prop: ASyntax.HeapPromote): P {
    return {
      type: "HeapPromote",
      from: this.visitHeap(prop.from),
      to: this.visitHeap(prop.to)
    };
  }
}

class TriggerEraser extends PropTransformer {
  visitCallTrigger(prop: ASyntax.CallTrigger): P {
    return tru;
  }
  
  visitForAll(prop: ASyntax.ForAll): P {
    // do not erase under quantifier -> leave unchanged
    return prop;
  }
}

export function eraseTriggersProp(prop: P): P {
  const v = new TriggerEraser();
  return v.visitProp(prop);
}

class AlphaRenamer extends PropTransformer {
  alphaHeap: { [heap: number]: Heap } = {};
  alphaLoc: { [lname: string]: ASyntax.Location } = {};
  alphaVar: { [vname: string]: ASyntax.Variable } = {};

  visitHeap(heap: Heap): Heap {
    return heap in this.alphaHeap ? this.alphaHeap[heap] : heap;
  }

  visitLocation(l: ASyntax.Location): ASyntax.Location {
    return l in this.alphaLoc ? this.alphaLoc[l] : l;
  }
  
  visitVariable(v: ASyntax.Variable): ASyntax.Variable {
    return v in this.alphaVar ? this.alphaVar[v] : v;
  }

  renameHeap(orig: number, num: number) {
    this.alphaHeap[orig] = num;
  }
  
  renameLoc(orig: ASyntax.Location, name: ASyntax.Location) {
    this.alphaLoc[orig] = name;
  }
  
  renameVar(orig: ASyntax.Variable, name: ASyntax.Variable) {
    this.alphaVar[orig] = name;
  }
  
  visitForAll(prop: ASyntax.ForAll): P {
    const origAlphaHeap = Object.assign({}, this.alphaHeap);
    const origAlphaLoc = Object.assign({}, this.alphaLoc);
    const origAlphaVar = Object.assign({}, this.alphaVar);
    try {
      prop.args.forEach(a => { delete this.alphaVar[a]; });
      prop.existsHeaps.forEach(h => { delete this.alphaHeap[h]; });
      prop.existsLocs.forEach(l => { delete this.alphaLoc[l]; });
      prop.existsVars.forEach(v => { delete this.alphaVar[v]; });
      return super.visitForAll(prop);
    } finally {
      this.alphaHeap = origAlphaHeap;
      this.alphaLoc = origAlphaLoc;
      this.alphaVar = origAlphaVar;
    }
  }
}

class QuantifierTransformer extends PropTransformer {
  readonly heaps: Heaps;
  readonly locs: Locs;
  readonly vars: Vars;

  constructor(heaps: Heaps, locs: Locs, vars: Vars) {
    super();
    this.heaps = heaps;
    this.locs = locs;
    this.vars = vars;
  }

  freshHeap(num: number): Heap {
    let n = num;
    while (this.heaps.has(n)) n++;
    this.heaps.add(n);
    return n;
  }
  
  freshLoc(name: string): ASyntax.Location {
    let n = name;
    while (this.locs.has(n)) n = n + "_";
    this.locs.add(n);
    return n;
  }
  
  freshVar(name: string): ASyntax.Variable {
    let n = name;
    while (this.vars.has(n)) n = n + "_";
    this.vars.add(n);
    return n;
  }

  liftExistantials(prop: ASyntax.ForAll): AlphaRenamer {
    const renamer = new AlphaRenamer();
    prop.existsHeaps.forEach(h => renamer.renameHeap(h, this.freshHeap(h)));
    prop.existsLocs.forEach(l => renamer.renameLoc(l, this.freshLoc(l)));
    prop.existsVars.forEach(v => renamer.renameVar(v, this.freshVar(v)));
    return renamer;
  }
}

class QuantifierLifter extends QuantifierTransformer {
  position: boolean;

  constructor(heaps: Heaps, locs: Locs, vars: Vars, position: boolean = false) {
    super(heaps, locs, vars);
    this.position = position;
  }

  visitNot(prop: ASyntax.Not): P {
    this.position = !this.position;
    try {
      return super.visitNot(prop);
    } finally {
      this.position = !this.position;
    }
  }

  visitForAll(prop: ASyntax.ForAll): P {
    if (!this.position) return prop;
    const renamer = this.liftExistantials(prop);
    prop.args.forEach(a => renamer.renameVar(a, this.freshVar(a)));
    const lifted = renamer.visitProp(prop);
    return this.visitProp(lifted);
  }
}

class TriggerCollector extends PropReducer<Array<ASyntax.CallTrigger>> {

  empty(): Array<ASyntax.CallTrigger> { return []; }

  reduce(a: Array<ASyntax.CallTrigger>, b: Array<ASyntax.CallTrigger>) {
    return a.concat(b);
  }

  visitCallTrigger(prop: ASyntax.CallTrigger): Array<ASyntax.CallTrigger> {
    return this.r([prop], super.visitCallTrigger(prop));
  }
  
  visitForAll(prop: ASyntax.ForAll): Array<ASyntax.CallTrigger>  {
    return []; // do not collect under quantifier
  }
}

class QuantifierInstantiator extends QuantifierTransformer {
  readonly triggers: Array<ASyntax.CallTrigger>;
  instantiations: number;

  constructor(triggers: Array<ASyntax.CallTrigger>, heaps: Heaps, locs: Locs, vars: Vars) {
    super(heaps, locs, vars);
    this.triggers = triggers;
    this.instantiations = 0;
  }

  instantiate(prop: ASyntax.ForAll, trigger: ASyntax.CallTrigger) {
    const match = eq(prop.callee, trigger.callee);
    const renamer = this.liftExistantials(prop);
    let body: P = tru;
    // substitute H0 and H1
    const h0 = this.freshHeap(0);
    body = and(body, heapPromote(trigger.heap, h0));
    renamer.renameHeap(0, h0);
    const h1 = this.freshHeap(1);
    body = and(body, heapPromote(trigger.heap + 1, h1));
    renamer.renameHeap(1, h1);
    // substitute arguments
    prop.args.forEach((a, idx) => {
      const a2 = this.freshVar(a);
      body = and(body, eq(a2, trigger.args[idx]));
      renamer.renameVar(a, a2);
    });
    body = and(body, renamer.visitProp(prop.prop));
    return implies(match, body);
  }

  visitForAll(prop: ASyntax.ForAll): P {
    const clauses: Array<P> = [prop];
    for (const t of this.triggers) {
      debugger;
      if (prop.args.length != t.args.length || prop.instantiations.some(trigger => eqProp(t, trigger))) {
        continue;
      }
      const instantiated: P = this.instantiate(prop, t);
      clauses.push(instantiated);
      prop.instantiations.push(t);
      this.instantiations++;
    }
    return and(...clauses);
  }
}

class QuantifierEraser extends PropTransformer {
  visitCallTrigger(prop: ASyntax.CallTrigger): P {
    return tru;
  }
  
  visitForAll(prop: ASyntax.ForAll): P {
    return tru;
  }
}

export function instantiateQuantifiers(heaps: Heaps, locs: Locs, vars: Vars, p: P): P {
  let prop = (new QuantifierLifter(heaps, locs, vars)).visitProp(p);
  const triggers: Array<ASyntax.CallTrigger> = (new TriggerCollector()).visitProp(prop);
  const instantiator = new QuantifierInstantiator(triggers, heaps, locs, vars);
  let num = -1;
  while (instantiator.instantiations> num) {
    num = instantiator.instantiations;
    prop = instantiator.visitProp(prop);
  }
  prop = (new QuantifierEraser()).visitProp(prop);
  return prop;
}

