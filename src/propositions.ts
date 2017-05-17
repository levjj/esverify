import { flatMap } from "./util";

export namespace ASyntax {
  export interface Variable { type: "Variable", name: string }
  export interface HeapReference { type: "HeapReference", name: string, heap: Heap }
  export interface Literal { type: "Literal",
                             value: undefined | null | boolean | number | string }
  export interface FunctionLiteral { type: "FunctionLiteral",
                                     id: number }
  export interface ArrayExpression { type: "ArrayExpression",
                                     elements: Array<Expression> }
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
                         | FunctionLiteral
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
                            args: Array<Variable>,
                            existsHeaps: Set<Heap>,
                            existsLocs: Locs,
                            existsVars: Vars,
                            prop: Proposition }
  export interface CallTrigger { type: "CallTrigger",
                                 callee: Expression,
                                 heap: Heap,
                                 args: Array<Expression> }
  export interface HeapStore { type: "HeapStore",
                               heap: Heap,
                               name: string,
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

export type A = ASyntax.Expression;
export type P = ASyntax.Proposition;
export type Vars = Set<string>;
export type Locs = Set<string>;
export type Heap = number;
export type SMTInput = string;
export type SMTOutput = string;

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
  return { type: "Eq", left, right };
}

export function iff(left: P, right: P): P {
  return { type: "Iff", left, right };
}

export function not(arg: P): P {
  if (arg.type == "True") return fls;
  if (arg.type == "False") return tru;
  if (arg.type == "Not") return arg.arg;
  return { type: "Not", arg };
}

export function heapStore(heap: Heap, name: string, expr: A): P {
  return { type: "HeapStore", heap, name, expr };
}

export function heapPromote(from: Heap, to: Heap): P {
  return { type: "HeapPromote", from, to };
}

abstract class PropVisitor<R,S> {

  abstract visitVariable(expr: ASyntax.Variable): R;
  abstract visitHeapReference(expr: ASyntax.HeapReference): R;
  abstract visitLiteral(expr: ASyntax.Literal): R;
  abstract visitFunctionLiteral(expr: ASyntax.FunctionLiteral): R;
  abstract visitArrayExpression(expr: ASyntax.ArrayExpression): R;
  abstract visitUnaryExpression(expr: ASyntax.UnaryExpression): R;
  abstract visitBinaryExpression(expr: ASyntax.BinaryExpression): R;
  abstract visitConditionalExpression(expr: ASyntax.ConditionalExpression): R;
  abstract visitCallExpression(expr: ASyntax.CallExpression): R;

  abstract visitTruthy(stmt: ASyntax.Truthy): S;
  abstract visitAnd(stmt: ASyntax.And): S;
  abstract visitOr(stmt: ASyntax.Or): S;
  abstract visitIff(stmt: ASyntax.Iff): S;
  abstract visitEq(stmt: ASyntax.Eq): S;
  abstract visitNot(stmt: ASyntax.Not): S;
  abstract visitTrue(stmt: ASyntax.True): S;
  abstract visitFalse(stmt: ASyntax.False): S;
  abstract visitPrecondition(stmt: ASyntax.Precondition): S;
  abstract visitPostcondition(stmt: ASyntax.Postcondition): S;
  abstract visitForAll(stmt: ASyntax.ForAll): S;
  abstract visitCallTrigger(stmt: ASyntax.CallTrigger): S;
  abstract visitHeapStore(stmt: ASyntax.HeapStore): S;
  abstract visitHeapEffect(stmt: ASyntax.HeapEffect): S;
  abstract visitHeapPromote(stmt: ASyntax.HeapPromote): S;

  visitExpr(expr: A): R {
    switch (expr.type) {
      case "Variable": return this.visitVariable(expr);
      case "HeapReference": return this.visitHeapReference(expr);
      case "Literal": return this.visitLiteral(expr);
      case "FunctionLiteral": return this.visitFunctionLiteral(expr);
      case 'ArrayExpression': return this.visitArrayExpression(expr);
      case "UnaryExpression": return this.visitUnaryExpression(expr);
      case "BinaryExpression": return this.visitBinaryExpression(expr);
      case "ConditionalExpression": return this.visitConditionalExpression(expr);
      case "CallExpression": return this.visitCallExpression(expr);
    }
  }

  visitProp(stmt: P): S {
    switch (stmt.type) {
      case "Truthy": return this.visitTruthy(stmt);
      case "And": return this.visitAnd(stmt);
      case "Or": return this.visitOr(stmt);
      case "Iff": return this.visitIff(stmt);
      case "Eq": return this.visitEq(stmt);
      case "Not": return this.visitNot(stmt);
      case "True": return this.visitTrue(stmt);
      case "False": return this.visitFalse(stmt);
      case "Precondition": return this.visitPrecondition(stmt);
      case "Postcondition": return this.visitPostcondition(stmt);
      case "ForAll": return this.visitForAll(stmt);
      case "CallTrigger": return this.visitCallTrigger(stmt);
      case "HeapStore": return this.visitHeapStore(stmt);
      case "HeapEffect": return this.visitHeapEffect(stmt);
      case "HeapPromote": return this.visitHeapPromote(stmt);
    }
  }
}

class SMTGenerator extends PropVisitor<SMTInput, SMTInput> {

  visitVariable(expr: ASyntax.Variable): SMTInput {
    return "v_" + expr.name;
  }

  visitHeapReference(expr: ASyntax.HeapReference): SMTInput {
    return `(select h_${expr.heap} l_${expr.name})`;
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
  
  visitFunctionLiteral(expr: ASyntax.FunctionLiteral): SMTInput {
    return `(jsfun ${expr.id})`;
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
    if (expr.args.length == 0) {
      return `(app0 ${this.visitExpr(expr.callee)} h_${expr.heap})`;
    } else if (expr.args.length == 1) {
      return `(app1 ${this.visitExpr(expr.callee)} h_${expr.heap} ${expr.args.map(e => this.visitExpr(e)).join(" ")})`;
    } else if (expr.args.length == 2) {
      return `(app2 ${this.visitExpr(expr.callee)} h_${expr.heap} ${expr.args.map(e => this.visitExpr(e)).join(" ")})`;
    } else {
      throw new Error("unsupported");
    }
  }

  visitTruthy(prop: ASyntax.Truthy): SMTInput {
    if (prop.expr.type == "ConditionalExpression" &&
        prop.expr.consequent.type == "Literal" &&
        prop.expr.consequent.value === true &&
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
    if (prop.args.length == 0) {
      return `(pre0 ${this.visitExpr(prop.callee)} h_${prop.heap})`;
    } else if (prop.args.length == 1) {
      return `(pre1 ${this.visitExpr(prop.callee)} h_${prop.heap} ${prop.args.map(a => this.visitExpr(a)).join(" ")})`;
    } else if (prop.args.length == 2) {
      return `(pre2 ${this.visitExpr(prop.callee)} h_${prop.heap} ${prop.args.map(a => this.visitExpr(a)).join(" ")})`;
    } else {
      throw new Error("unsupported");
    }
  }
  
  visitPostcondition(prop: ASyntax.Postcondition): SMTInput {
    if (prop.args.length == 0) {
      return `(post0 ${this.visitExpr(prop.callee)} h_${prop.heap} h_${prop.heap+1})`;
    } else if (prop.args.length == 1) {
      return `(post1 ${this.visitExpr(prop.callee)} h_${prop.heap} h_${prop.heap+1} ${prop.args.map(a => this.visitExpr(a)).join(" ")})`;
    } else if (prop.args.length == 2) {
      return `(post2 ${this.visitExpr(prop.callee)} h_${prop.heap} h_${prop.heap+1} ${prop.args.map(a => this.visitExpr(a)).join(" ")})`;
    } else {
      throw new Error("unsupported");
    }
  }
  
  visitForAll(prop: ASyntax.ForAll): SMTInput {
    const params = `${prop.args.map(p => `(${this.visitExpr(p)} JSVal)`).join(' ')}`;
    const triggerArgs = `${this.visitExpr(prop.callee)} h_0 h_1 ${prop.args.map(a => this.visitExpr(a)).join(' ')}`;
    if (prop.args.length > 2) throw new Error("Not supported");
    const trigger = `call${prop.args.length} ${triggerArgs}`;
    let p = this.visitProp(prop.prop);
    if (prop.existsLocs.size > 0 || prop.existsHeaps.size > 0) {
      p = `(exists (${[...prop.existsHeaps].map(h => `(h_${h} Heap)`).join(' ')} `
                 + `${[...prop.existsLocs].map(l => `(l_${l} Loc)`).join(' ')} `
                 + `${[...prop.existsVars].map(v => `(v_${v} JSVal)`).join(' ')})\n  ${p})`;
    }
    return `(forall ((h_0 Heap) (h_1 Heap) ${params}) (!\n  ${p}\n  :pattern ((${trigger}))))`;
  }
  
  visitCallTrigger(prop: ASyntax.CallTrigger): SMTInput {
    if (prop.args.length == 0) {
      return `(call0 ${this.visitExpr(prop.callee)} h_${prop.heap} h_${prop.heap+1})`;
    } else if (prop.args.length == 1) {
      return `(call1 ${this.visitExpr(prop.callee)} h_${prop.heap} h_${prop.heap+1} ${prop.args.map(a => this.visitExpr(a)).join(" ")})`;
    } else if (prop.args.length == 2) {
      return `(call2 ${this.visitExpr(prop.callee)} h_${prop.heap} h_${prop.heap+1} ${prop.args.map(a => this.visitExpr(a)).join(" ")})`;
    } else {
      throw new Error("unsupported");
    }
  }
  
  visitHeapStore(prop: ASyntax.HeapStore): SMTInput {
    return `(= h_${prop.heap + 1} (store h_${prop.heap} l_${prop.name} ${this.visitExpr(prop.expr)}))`
  }
  
  visitHeapEffect(prop: ASyntax.HeapEffect): SMTInput {
    if (prop.args.length == 0) {
      return `(= h_${prop.heap + 1} (eff0 ${this.visitExpr(prop.callee)} h_${prop.heap}))`;
    } else if (prop.args.length == 1) {
      return `(= h_${prop.heap + 1} (eff1 ${this.visitExpr(prop.callee)} h_${prop.heap} ${prop.args.map(a => this.visitExpr(a)).join(" ")}))`;
    } else if (prop.args.length == 2) {
      return `(= h_${prop.heap + 1} (eff2 ${this.visitExpr(prop.callee)} h_${prop.heap} ${prop.args.map(a => this.visitExpr(a)).join(" ")}))`;
    } else {
      throw new Error("unsupported");
    }
  }
  
  visitHeapPromote(prop: ASyntax.HeapPromote): SMTInput {
    if (prop.from == prop.to) return `true`;
    return `(= h_${prop.from} h_${prop.to})`;
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

function smtToArray(smt: SMTOutput): Array<any> {
  const s = smt.trim();
  if (s == "empty") return [];
  const m = s.match(/^\(cons (\w+|\(.*\))\ (.*)\)$/);
  if (!m) throw new Error("Cannot parse output!");
  const [, h, t] = m;
  return [smtToValue(h)].concat(smtToArray(t));
}

export function smtToValue(smt: SMTOutput): any {
  const s = smt.trim();
  if (s == "jsundefined") return undefined;
  if (s == "jsnull") return null;
  const m = s.match(/^\((\w+)\ (.*)\)$/);
  if (!m) throw new Error("Cannot parse output!");
  const [, tag, v] = m;
  if (tag.startsWith("jsfun_")) return null;
  switch (tag) {
    case "jsbool": return v == "true";
    case "jsnum": const neg = v.match(/\(- ([0-9]+)\)/); return neg ? -neg[1] : +v;
    case "jsstr": return v.substr(1, v.length - 2);
    case "jsarr": return smtToArray(v);
    default: throw new Error("unsupported");
  }
}

class PropTransformer extends PropVisitor<A, P> {

  visitVariable(expr: ASyntax.Variable): A {
    return expr;
  }

  visitHeapReference(expr: ASyntax.HeapReference): A {
    return expr;
  }
  
  visitLiteral(expr: ASyntax.Literal): A {
    return expr;
  }
  
  visitFunctionLiteral(expr: ASyntax.FunctionLiteral): A {
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
     heap: expr.heap,
     args: expr.args.map(a => this.visitExpr(a))
    };
  }

  visitTruthy(prop: ASyntax.Truthy): P {
    return { type: "Truthy", expr: this.visitExpr(prop.expr) };
  }
  
  visitAnd(prop: ASyntax.And): P {
    return { type: "And", clauses: prop.clauses.map(c => this.visitProp(c)) };
  }
  
  visitOr(prop: ASyntax.Or): P {
    return { type: "Or", clauses: prop.clauses.map(c => this.visitProp(c)) };
  }
  
  visitIff(prop: ASyntax.Iff): P {
    return {
      type: "Iff",
      left: this.visitProp(prop.left),
      right: this.visitProp(prop.right)
    };
  }
  
  visitEq(prop: ASyntax.Eq): P {
    return {
      type: "Eq",
      left: this.visitExpr(prop.left),
      right: this.visitExpr(prop.right)
    };
  }
  
  visitNot(prop: ASyntax.Not): P {
    return { type: "Not", arg: this.visitProp(prop.arg) };
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
      heap: prop.heap,
      args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitPostcondition(prop: ASyntax.Postcondition): P {
    return {
      type: "Postcondition",
      callee: this.visitExpr(prop.callee),
      heap: prop.heap,
      args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitForAll(prop: ASyntax.ForAll): P {
    return {
      type: "ForAll",
      callee: this.visitExpr(prop.callee),
      args: prop.args,
      existsHeaps: prop.existsHeaps,
      existsLocs: prop.existsLocs,
      existsVars: prop.existsVars,
      prop: this.visitProp(prop.prop)
    };
  }
  
  visitCallTrigger(prop: ASyntax.CallTrigger): P {
    return {
      type: "CallTrigger",
      callee: this.visitExpr(prop.callee),
      heap: prop.heap,
      args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitHeapStore(prop: ASyntax.HeapStore): P {
    return {
      type: "HeapStore",
      heap: prop.heap,
      name: prop.name,
      expr: this.visitExpr(prop.expr)
    };
  }
  
  visitHeapEffect(prop: ASyntax.HeapEffect): P {
    return {
     type: "HeapEffect",
     callee: this.visitExpr(prop.callee),
     heap: prop.heap,
     args: prop.args.map(a => this.visitExpr(a))
    };
  }
  
  visitHeapPromote(prop: ASyntax.HeapPromote): P {
    return prop;
  }
}

class TriggerRemoval extends PropTransformer {
  readonly triggers: Array<ASyntax.CallTrigger> = [];

  visitCallTrigger(prop: ASyntax.CallTrigger): P {
    this.triggers.push(prop);
    return tru;
  }
  
  visitForAll(prop: ASyntax.ForAll): P {
    // do not erase under quantifier -> leave unchanged
    return prop;
  }
}

export function eraseTriggersProp(prop: P): P {
  const v = new TriggerRemoval();
  return v.visitProp(prop);
}

