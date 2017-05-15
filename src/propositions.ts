import { flatMap } from "./util";

export namespace ASyntax {
  export interface Variable { type: "Variable", name: string }
  export interface HeapReference { type: "HeapReference", name: string, heap: Heap }
  interface Literal { type: "Literal",
                      value: undefined | null | boolean | number | string }
  interface FunctionLiteral { type: "FunctionLiteral",
                              id: number }
  interface ArrayExpression { type: "ArrayExpression",
                              elements: Array<Expression> }
  type UnaryOperator = "-" | "+" | "!" | "~" | "typeof" | "void";
  interface UnaryExpression { type: "UnaryExpression",
                              operator: UnaryOperator,
                              argument: Expression }
  type BinaryOperator = "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">="
                      | "<<" | ">>" | ">>>" | "+" | "-" | "*" | "/" | "%"
                      | "|" | "^" | "&";
  interface BinaryExpression { type: "BinaryExpression",
                               operator: BinaryOperator,
                               left: Expression,
                               right: Expression }
  interface ConditionalExpression { type: "ConditionalExpression",
                                    test: Proposition,
                                    consequent: Expression,
                                    alternate: Expression }
  interface CallExpression { type: "CallExpression",
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

function arrayToSMT(elements: Array<A>): SMTInput {
  if (elements.length === 0) return `empty`;
  const [head, ...tail] = elements;
  const h = head || {type: "Literal", value: "undefined"};
  return `(cons ${expressionToSMT(h)} ${arrayToSMT(tail)})`;
}

export function expressionToSMT(expr: A): SMTInput {
  switch (expr.type) {
    case "Variable":
      return "v_" + expr.name;
    case "HeapReference":
      return `(select h_${expr.heap} l_${expr.name})`;
    case "Literal":
      if (expr.value === undefined) return `jsundefined`;
      if (expr.value === null) return `jsnull`;
      switch (typeof expr.value) {
        case "boolean": return `(jsbool ${expr.value})`;
        case "number": return `(jsnum ${expr.value})`;
        case "string": return `(jsstr "${expr.value}")`;
        default: throw new Error("unsupported");
      }
    case "FunctionLiteral": {
      return `(jsfun ${expr.id})`;
    }
    case 'ArrayExpression':
      return `(jsarray ${arrayToSMT(expr.elements)})`;
    case "UnaryExpression":
      const arg = expressionToSMT(expr.argument),
            op = unOpToSMT[expr.operator];
      return `(${op} ${arg})`;
    case "BinaryExpression": {
      const left = expressionToSMT(expr.left),
            right = expressionToSMT(expr.right),
            binop = binOpToSMT[expr.operator];
      return `(${binop} ${left} ${right})`;
    }
    case "ConditionalExpression":
      const test = propositionToSMT(expr.test),
            then = expressionToSMT(expr.consequent),
            elze = expressionToSMT(expr.alternate);
      return `(ite ${test} ${then} ${elze})`;
    case "CallExpression": {
      if (expr.args.length == 0) {
        return `(app0 ${expressionToSMT(expr.callee)} h_${expr.heap})`;
      } else if (expr.args.length == 1) {
        return `(app1 ${expressionToSMT(expr.callee)} h_${expr.heap} ${expr.args.map(expressionToSMT).join(" ")})`;
      } else if (expr.args.length == 2) {
        return `(app2 ${expressionToSMT(expr.callee)} h_${expr.heap} ${expr.args.map(expressionToSMT).join(" ")})`;
      } else {
        throw new Error("unsupported");
      }
    }
  }
}

export function propositionToSMT(prop: P): SMTInput {
  switch (prop.type) {
    case "Truthy": {
      if (prop.expr.type == "ConditionalExpression" &&
          prop.expr.consequent.type == "Literal" &&
          prop.expr.consequent.value === true &&
          prop.expr.alternate.type == "Literal" &&
          prop.expr.alternate.value === false) {
        return propositionToSMT(prop.expr.test);
      }
      return `(_truthy ${expressionToSMT(prop.expr)})`;
    }
    case "And": {
      const clauses: Array<SMTInput> = flatMap(prop.clauses,
        c => c.type == "And" ? c.clauses : [c]) 
        .map(propositionToSMT)
        .filter(s => s != `true`);
      if (clauses.find(s => s == `false`)) return `false`;
      if (clauses.length == 0) return `true`;
      if (clauses.length == 1) return clauses[0];
      return `(and ${clauses.join(' ')})`;
    }
    case "Or": {
      const clauses: Array<SMTInput> = flatMap(prop.clauses,
        c => c.type == "Or" ? c.clauses : [c]) 
        .map(propositionToSMT)
        .filter(s => s != `false`);
      if (clauses.find(s => s == `true`)) return `true`;
      if (clauses.length == 0) return `false`;
      if (clauses.length == 1) return clauses[0];
      return `(or ${clauses.join(' ')})`;
    }
    case "Iff": {
      const left: SMTInput = propositionToSMT(prop.left);
      const right: SMTInput = propositionToSMT(prop.right);
      if (left == `true`) return right;
      if (right == `true`) return left;
      if (left == right) return `true`;
      return `(= ${left} ${right})`;
    }
    case "Eq": {
      const left: SMTInput = expressionToSMT(prop.left);
      const right: SMTInput = expressionToSMT(prop.right);
      if (left == right) return `true`;
      return `(= ${left} ${right})`;
    }
    case "Not": {
      const arg: SMTInput = propositionToSMT(prop.arg);
      if (arg == "true") return `false`;
      if (arg == "false") return `true`;
      return `(not ${arg})`;
    }
    case "True": return `true`;
    case "False": return `false`;
    case "Precondition":
      if (prop.args.length == 0) {
        return `(pre0 ${expressionToSMT(prop.callee)} h_${prop.heap})`;
      } else if (prop.args.length == 1) {
        return `(pre1 ${expressionToSMT(prop.callee)} h_${prop.heap} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else if (prop.args.length == 2) {
        return `(pre2 ${expressionToSMT(prop.callee)} h_${prop.heap} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else {
        throw new Error("unsupported");
      }
    case "Postcondition":
      if (prop.args.length == 0) {
        return `(post0 ${expressionToSMT(prop.callee)} h_${prop.heap} h_${prop.heap+1})`;
      } else if (prop.args.length == 1) {
        return `(post1 ${expressionToSMT(prop.callee)} h_${prop.heap} h_${prop.heap+1} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else if (prop.args.length == 2) {
        return `(post2 ${expressionToSMT(prop.callee)} h_${prop.heap} h_${prop.heap+1} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else {
        throw new Error("unsupported");
      }
    case "ForAll": {
      const params = `${prop.args.map(p => `(${expressionToSMT(p)} JSVal)`).join(' ')}`;
      const triggerArgs = `${expressionToSMT(prop.callee)} h_0 h_1 ${prop.args.map(expressionToSMT).join(' ')}`;
      if (prop.args.length > 2) throw new Error("Not supported");
      const trigger = `call${prop.args.length} ${triggerArgs}`;
      let p = propositionToSMT(prop.prop);
      if (prop.existsLocs.size > 0 || prop.existsHeaps.size > 0) {
        p = `(exists (${[...prop.existsHeaps].map(h => `(h_${h} Heap)`).join(' ')} `
                   + `${[...prop.existsLocs].map(l => `(l_${l} Loc)`).join(' ')} `
                   + `${[...prop.existsVars].map(v => `(v_${v} JSVal)`).join(' ')})\n  ${p})`;
      }
      return `(forall ((h_0 Heap) (h_1 Heap) ${params}) (!\n  ${p}\n  :pattern ((${trigger}))))`;
    }
    case "CallTrigger":
      if (prop.args.length == 0) {
        return `(call0 ${expressionToSMT(prop.callee)} h_${prop.heap} h_${prop.heap+1})`;
      } else if (prop.args.length == 1) {
        return `(call1 ${expressionToSMT(prop.callee)} h_${prop.heap} h_${prop.heap+1} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else if (prop.args.length == 2) {
        return `(call2 ${expressionToSMT(prop.callee)} h_${prop.heap} h_${prop.heap+1} ${prop.args.map(expressionToSMT).join(" ")})`;
      } else {
        throw new Error("unsupported");
      }
    case "HeapStore":
      return `(= h_${prop.heap + 1} (store h_${prop.heap} l_${prop.name} ${expressionToSMT(prop.expr)}))`
    case "HeapPromote":
      if (prop.from == prop.to) return `true`;
      return `(= h_${prop.from} h_${prop.to})`;
  }
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
