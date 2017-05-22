import * as JSyntax from "estree";
import { flatMap } from "./util";
import { MessageException, err } from "./message";
import { options } from "./options";

export namespace Syntax {

  export type Declaration = { type: "Unresolved" }
                          | { type: "Var", decl: Syntax.VariableDeclaration }
                          | { type: "Func", decl: Syntax.FunctionDeclaration }
                          | { type: "SpecArg", decl: Syntax.SpecExpression, argIdx: number }
                          | { type: "Param",
                              func: Syntax.FunctionDeclaration;
                              decl: Syntax.Identifier };

  interface Position { line: number, column: number }
  export interface SourceLocation { file: string, start: Position, end: Position }

  export interface Identifier { type: "Identifier", name: string,
                                decl: Declaration, refs: Array<Identifier>, isWrittenTo: boolean,
                                loc: SourceLocation }
  export interface OldIdentifier { type: "OldIdentifier", id: Identifier, loc: SourceLocation }
  export interface Literal { type: "Literal",
                             value: undefined | null | boolean | number | string,
                             loc: SourceLocation }
  export interface ArrayExpression { type: "ArrayExpression",
                                     elements: Array<Expression>,
                                     loc: SourceLocation }
  export type UnaryOperator = "-" | "+" | "!" | "~" | "typeof" | "void";
  export interface UnaryExpression { type: "UnaryExpression",
                                     operator: UnaryOperator,
                                     argument: Expression,
                                     loc: SourceLocation }
  export type BinaryOperator = "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">="
                             | "<<" | ">>" | ">>>" | "+" | "-" | "*" | "/" | "%"
                             | "|" | "^" | "&";
  export interface BinaryExpression { type: "BinaryExpression",
                                      operator: BinaryOperator,
                                      left: Expression,
                                      right: Expression,
                                      loc: SourceLocation }
  export type LogicalOperator = "||" | "&&";
  export interface LogicalExpression { type: "LogicalExpression",
                                       operator: LogicalOperator,
                                       left: Expression,
                                       right: Expression,
                                       loc: SourceLocation }
  export interface ConditionalExpression { type: "ConditionalExpression",
                                           test: Expression,
                                           consequent: Expression,
                                           alternate: Expression,
                                           loc: SourceLocation }
  export interface AssignmentExpression { type: "AssignmentExpression",
                                          left: Identifier,
                                          right: Expression,
                                          loc: SourceLocation }
  export interface SequenceExpression { type: "SequenceExpression",
                                        expressions: Expression[],
                                        loc: SourceLocation }
  export interface CallExpression { type: "CallExpression",
                                    callee: Expression,
                                    args: Array<Expression>,
                                    loc: SourceLocation }
  export interface PureExpression { type: "PureExpression",
                                    loc: SourceLocation }
  export interface SpecExpression { type: "SpecExpression",
                                    callee: Identifier, // not mutable
                                    args: Array<string>,
                                    pre: Expression,
                                    post: Expression,
                                    loc: SourceLocation }
  export type Expression = Identifier
                         | OldIdentifier
                         | Literal
                         | ArrayExpression
                         | UnaryExpression
                         | BinaryExpression
                         | LogicalExpression
                         | ConditionalExpression
                         | AssignmentExpression
                         | SequenceExpression
                         | CallExpression
                         | SpecExpression
                         | PureExpression;
  export interface VariableDeclaration { type: "VariableDeclaration",
                                         id: Identifier,
                                         init: Expression,
                                         kind: "let" | "const",
                                         loc: SourceLocation  }
  export interface BlockStatement { type: "BlockStatement",
                                    body: Statement[],
                                    loc: SourceLocation  }
  export interface ExpressionStatement { type: "ExpressionStatement",
                                         expression: Expression,
                                         loc: SourceLocation  }
  export interface AssertStatement { type: "AssertStatement",
                                     expression: Expression,
                                     loc: SourceLocation  }
  export interface IfStatement { type: "IfStatement",
                                 test: Expression,
                                 consequent: BlockStatement,
                                 alternate: BlockStatement,
                                 loc: SourceLocation }
  export interface ReturnStatement { type: "ReturnStatement",
                                     argument: Expression,
                                     loc: SourceLocation }
  export interface WhileStatement { type: "WhileStatement",
                                    invariants: Array<Expression>,
                                    test: Expression,
                                    body: BlockStatement,
                                    loc: SourceLocation }
  export interface DebuggerStatement { type: "DebuggerStatement",
                                       loc: SourceLocation }
  export interface FunctionDeclaration { type: "FunctionDeclaration",
                                         id: Identifier,
                                         params: Array<Identifier>,
                                         requires: Array<Expression>,
                                         ensures: Array<Expression>,
                                         body: BlockStatement,
                                         freeVars: Array<Declaration>,
                                         loc: SourceLocation }
 
  export type Statement = VariableDeclaration
                        | BlockStatement
                        | ExpressionStatement
                        | AssertStatement
                        | IfStatement
                        | ReturnStatement
                        | WhileStatement
                        | DebuggerStatement
                        | FunctionDeclaration;

  export type Program = { body: Array<Statement>,
                          invariants: Array<Expression> };
}

function unsupported(node: JSyntax.Node): MessageException {
  return new MessageException({
    status: "unsupported",
    loc: loc(node)
  });
}

function findPseudoCalls(type: string, stmts: Array<JSyntax.Statement>): Array<Syntax.Expression> {
  return flatMap(stmts, stmt => {
    if (stmt.type == "ExpressionStatement" &&
        stmt.expression.type == "CallExpression" &&
        stmt.expression.callee.type == "Identifier" &&
        stmt.expression.callee.name == type) {
      if (stmt.expression.arguments.length != 1) throw unsupported(stmt.expression);
      const arg = stmt.expression.arguments[0];
      if (arg.type == "SpreadElement") throw unsupported(arg);
      return [expressionAsJavaScript(arg)];
    }
    return [];
  });
}

function withoutPseudoCalls(type: string, stmts: Array<JSyntax.Statement>): Array<JSyntax.Statement> {
  return flatMap(stmts, stmt => {
    if (stmt.type == "ExpressionStatement" &&
        stmt.expression.type == "CallExpression" &&
        stmt.expression.callee.type == "Identifier" &&
        stmt.expression.callee.name == type &&
        stmt.expression.arguments.length == 1) {
      return [];
    }
    return [stmt];
  });
}

function loc(n: JSyntax.Node): Syntax.SourceLocation {
  if (!n.loc) {
    debugger;
    throw new MessageException(err(new Error("No location information available on nodes")));
  }
  return { file: options.filename, start: n.loc.start, end: n.loc.end };
}

function patternAsIdentifier(node: JSyntax.Pattern): Syntax.Identifier {
  if (node.type != "Identifier") throw unsupported(node);
  return {
    type: "Identifier",
    name: node.name,
    refs: [],
    decl: { type: "Unresolved" },
    isWrittenTo: false,
    loc: loc(node)
  };
}

function unaryOp(unop: JSyntax.UnaryExpression): Syntax.UnaryOperator {
  switch (unop.operator) {
    case "-":
    case "+":
    case "!":
    case "~":
    case "typeof":
    case "void":
      return unop.operator;
    default:
      throw unsupported(unop);
  }
}

function binaryOp(binop: JSyntax.BinaryExpression): Syntax.BinaryOperator {
  switch (binop.operator) {
    case "==":
    case "!=":
    case "===":
    case "!==":
    case "<":
    case "<=":
    case ">":
    case ">=":
    case "<<":
    case ">>":
    case ">>>":
    case "+":
    case "-":
    case "*":
    case "/":
    case "%":
    case "|":
    case "^":
    case "&":
      return binop.operator;
    default:
      throw unsupported(binop);
  }
}

export function programAsJavaScript(program: JSyntax.Program): Syntax.Program {
  let stmts: Array<JSyntax.Statement> = [];
  for (const s of program.body) {
    if (s.type == "ImportDeclaration" ||
        s.type == "ExportAllDeclaration" ||
        s.type == "ExportNamedDeclaration" ||
        s.type == "ExportDefaultDeclaration" ||
        s.type == "ReturnStatement") {
      throw unsupported(s);
    } 
    stmts.push(s);
  }
  const body = flatMap(withoutPseudoCalls("invariant", stmts), statementAsJavaScript);
  const prog: Syntax.Program = {
    body,
    invariants: findPseudoCalls("invariant", stmts)
  };
  resolveProgram(prog);
  return prog;
}

function statementAsJavaScript(stmt: JSyntax.Statement): Array<Syntax.Statement> {
  function assert(cond: boolean) { if (!cond) throw unsupported(stmt); }
  switch (stmt.type) {
    case "EmptyStatement":
      return [];
    case "VariableDeclaration":
      assert(stmt.kind == "let" || stmt.kind == "const");
      return stmt.declarations.map(decl => {
        assert(decl.id.type == "Identifier");
        const d: Syntax.VariableDeclaration = {
          type: "VariableDeclaration",
          kind: stmt.kind == "let" ? "let" : "const",
          id: patternAsIdentifier(decl.id),
          init: decl.init ? expressionAsJavaScript(decl.init) : {type: "Literal", value: undefined, loc: loc(stmt)},
          loc: loc(stmt)
        };
        return d;
      });
    case "BlockStatement":
      return [{
        type: "BlockStatement",
        body: flatMap(stmt.body, statementAsJavaScript),
        loc: loc(stmt)
      }];
    case "ExpressionStatement":
      if (stmt.expression.type == "CallExpression" &&
          stmt.expression.callee.type == "Identifier" &&
          stmt.expression.callee.name == "assert" &&
          stmt.expression.arguments.length == 1) {
        const arg = stmt.expression.arguments[0];
        if (arg.type != "SpreadElement") {
          return [{ type: "AssertStatement", expression: expressionAsJavaScript(arg), loc: loc(stmt) }];
        }
      }
      return [{ type: "ExpressionStatement", expression: expressionAsJavaScript(stmt.expression), loc: loc(stmt) }]
    case "IfStatement":
      return [{
        type: "IfStatement",
        test: expressionAsJavaScript(stmt.test),
        consequent: {
          type: "BlockStatement",
          body: stmt.consequent.type == "BlockStatement"
                ? flatMap(stmt.consequent.body, statementAsJavaScript)
                : statementAsJavaScript(stmt.consequent),
          loc: loc(stmt.consequent)
        },
        alternate: {
          type: "BlockStatement",
          body: stmt.alternate ? (stmt.alternate.type == "BlockStatement"
                ? flatMap(stmt.alternate.body, statementAsJavaScript)
                : statementAsJavaScript(stmt.alternate)) : [],
          loc: loc(stmt.alternate || stmt)
        },
        loc: loc(stmt)
      }];
    case "WhileStatement":
      const stmts: Array<JSyntax.Statement> = stmt.body.type == "BlockStatement" ? stmt.body.body : [stmt];
      return [{
        type: "WhileStatement",
        invariants: findPseudoCalls("invariant", stmts),
        test: expressionAsJavaScript(stmt.test),
        body: {
          type: "BlockStatement",
          body: flatMap(withoutPseudoCalls("invariant", stmts), statementAsJavaScript),
          loc: loc(stmt.body)
        },
        loc: loc(stmt)
      }];
    case "DebuggerStatement":
      return [{ type: "DebuggerStatement", loc: loc(stmt) }];
    case "ReturnStatement":
      return [{
        type: "ReturnStatement",
        argument: stmt.argument ? expressionAsJavaScript(stmt.argument) : { type: "Literal", value: undefined, loc: loc(stmt) },
        loc: loc(stmt)
      }];
    case "FunctionDeclaration": {
      if (stmt.body.type != "BlockStatement") throw unsupported(stmt.body);
      assert(!stmt.generator);
      const params: Array<Syntax.Identifier> = stmt.params.map(patternAsIdentifier);
      assert(distinct(params));
      const id: Syntax.Identifier = { type: "Identifier", name: stmt.id.name,
        refs: [], isWrittenTo: false, decl: { type: "Unresolved" }, loc: loc(stmt.id) };
      const fd: Syntax.FunctionDeclaration = {
        type: "FunctionDeclaration",
        id,
        params,
        requires: findPseudoCalls("requires", stmt.body.body),
        ensures: findPseudoCalls("ensures", stmt.body.body),
        body: {
          type: "BlockStatement",
          body: flatMap(withoutPseudoCalls("requires",
                        withoutPseudoCalls("ensures", stmt.body.body)), statementAsJavaScript),
          loc: loc(stmt.body)
        },
        freeVars: [],
        loc: loc(stmt)
      };
      fd.id.decl = { type: "Func", decl: fd };
      return [fd];
    }
    default:
      throw unsupported(stmt);
  }
}

function assignUpdate(left: Syntax.Identifier, op: Syntax.BinaryOperator, right: JSyntax.Expression, stmt: JSyntax.Expression): Syntax.AssignmentExpression {
  return {
    type: "AssignmentExpression",
    left,
    right: {
      type: "BinaryExpression",
      left,
      operator: op,
      right: expressionAsJavaScript(right),
      loc: loc(stmt)
    },
    loc: loc(stmt)
  };
}

function distinct(params: Array<Syntax.Identifier>): boolean {
  for (let i = 0; i < params.length - 1; i++) {
    for (let j = i + 1; j < params.length; j++) {
      if (params[i].name == params[j].name) return false;      
    }
  }
  return true;
}

function expressionAsJavaScript(expr: JSyntax.Expression): Syntax.Expression {
  switch (expr.type) {
    case "ThisExpression":
    case "ObjectExpression":
      throw unsupported(expr);
    case "ArrayExpression":
      return {
        type: "ArrayExpression",
        elements: expr.elements.map(expressionAsJavaScript),
        loc: loc(expr)
      };
    case "SequenceExpression":
      return {
        type: "SequenceExpression",
        expressions: expr.expressions.map(expressionAsJavaScript),
        loc: loc(expr)
      };
    case "UnaryExpression":
      return {
        type: "UnaryExpression",
        operator: unaryOp(expr),
        argument: expressionAsJavaScript(expr.argument),
        loc: loc(expr)
      };
    case "BinaryExpression":
      return {
        type: "BinaryExpression",
        operator: binaryOp(expr),
        left: expressionAsJavaScript(expr.left),
        right: expressionAsJavaScript(expr.right),
        loc: loc(expr)
      };
    case "AssignmentExpression":
      if (expr.left.type != "Identifier") throw unsupported(expr.left);
      const to: Syntax.Identifier = { type: "Identifier", name: expr.left.name,
        refs: [], isWrittenTo: true, decl: { type: "Unresolved" }, loc: loc(expr) };
      switch (expr.operator) {
        case "=":
          return {
            type: "AssignmentExpression",
            left: to,
            right: expressionAsJavaScript(expr.right),
            loc: loc(expr)
          };
        case "+=": return assignUpdate(to, "+", expr.right, expr);
        case "-=": return assignUpdate(to, "-", expr.right, expr);
        case "*=": return assignUpdate(to, "*", expr.right, expr);
        case "/=": return assignUpdate(to, "/", expr.right, expr);
        case "%=": return assignUpdate(to, "%", expr.right, expr);
        case "<<=": return assignUpdate(to, "<<", expr.right, expr);
        case ">>=": return assignUpdate(to, ">>", expr.right, expr);
        case ">>>=": return assignUpdate(to, ">>>", expr.right, expr);
        case "|=": return assignUpdate(to, "|", expr.right, expr);
        case "^=": return assignUpdate(to, "^", expr.right, expr);
        case "&=": return assignUpdate(to, "&", expr.right, expr);
        default: throw unsupported(expr);
      }
    case "UpdateExpression": {
      if (expr.argument.type != "Identifier") throw unsupported(expr.argument);
      const to: Syntax.Identifier = { type: "Identifier", name: expr.argument.name, refs: [],
                                      isWrittenTo: true, decl: { type: "Unresolved" }, loc: loc(expr.argument) },
            one: JSyntax.SimpleLiteral = { type: "Literal", value: 1, raw: "1", loc: loc(expr) },
            oneE: Syntax.Literal = { type: "Literal", value: 1, loc: loc(expr) };
      if (expr.prefix) {
        if (expr.operator == "++") {
          return assignUpdate(to, "+", one, expr);
        }
        return assignUpdate(to, "-", one, expr);
      } else {
        if (expr.operator == "++") {
          return {
            type: "SequenceExpression",
            expressions: [
              assignUpdate(to, "+", one, expr),
              { type: "BinaryExpression", operator: "-", left: to, right: oneE, loc: loc(expr) }
            ],
            loc: loc(expr)
          };
        };
        return {
          type: "SequenceExpression",
          expressions: [
            assignUpdate(to, "-", one, expr),
            { type: "BinaryExpression", operator: "+", left: to, right: oneE, loc: loc(expr) }
          ],
          loc: loc(expr)
        };
      }
    }
    case "LogicalExpression":
      return {
        type: "LogicalExpression",
        operator: expr.operator == "||" ? "||" : "&&",
        left: expressionAsJavaScript(expr.left),
        right: expressionAsJavaScript(expr.right),
        loc: loc(expr)
      };
    case "ConditionalExpression":
      return {
        type: "ConditionalExpression",
        test: expressionAsJavaScript(expr.test),
        consequent: expressionAsJavaScript(expr.consequent),
        alternate: expressionAsJavaScript(expr.alternate),
        loc: loc(expr)
      };
    case "CallExpression":
      if (expr.callee.type == "Identifier" &&
          expr.callee.name == "pure") {
        if (expr.arguments.length != 0) throw unsupported(expr);
        return { type: "PureExpression", loc: loc(expr) };
      }
      if (expr.callee.type == "Identifier" &&
          expr.callee.name == "old") {
        if (expr.arguments.length != 1 || expr.arguments[0].type != "Identifier") {
          throw unsupported(expr);
        }
        return {
          type: "OldIdentifier",
          id: { type: "Identifier", name: (<JSyntax.Identifier>expr.arguments[0]).name,
                refs: [], isWrittenTo: false, decl: { type: "Unresolved" }, loc: loc(expr.arguments[0]) },
          loc: loc(expr)
        };
      }
      if (expr.callee.type == "Identifier" &&
          expr.callee.name == "spec") {
        if (expr.arguments.length != 3) throw unsupported(expr);
        const [callee, arg1, arg2] = expr.arguments;
        if (callee.type != "Identifier" ||
            arg1.type != "ArrowFunctionExpression" ||
            arg2.type != "ArrowFunctionExpression") throw unsupported(expr);
        const r: JSyntax.ArrowFunctionExpression = arg1;
        const s: JSyntax.ArrowFunctionExpression = arg2;
        if (r.body.type == "BlockStatement" ||
            s.body.type == "BlockStatement" ||
            r.params.length != s.params.length &&
            !r.params.every((p, idx) => {
              const otherP = s.params[idx];
              return p.type == "Identifier" && otherP.type == "Identifier" && p.name == otherP.name; })) {
          throw unsupported(expr);
        }
        return {
          type: "SpecExpression",
          callee: { type: "Identifier", name: callee.name, refs: [],
                    isWrittenTo: false, decl: { type: "Unresolved" }, loc: loc(callee) },
          args: r.params.map(p => (p as JSyntax.Identifier).name),
          pre: expressionAsJavaScript(r.body),
          post: expressionAsJavaScript(s.body),
          loc: loc(expr)
        };
      }
      if (expr.callee.type == "Super") throw unsupported(expr.callee);
      if (expr.arguments.length > 9) throw unsupported(expr);
      return {
        type: "CallExpression",
        callee: expressionAsJavaScript(expr.callee),
        args: expr.arguments.map(expressionAsJavaScript),
        loc: loc(expr)
      };
    case "Identifier":
      if (expr.name == "undefined") {
        return { type: "Literal", value: undefined, loc: loc(expr) };
      }
      return { type: "Identifier", name: expr.name, refs: [],
               isWrittenTo: false, decl: { type: "Unresolved" }, loc: loc(expr) };
    case "Literal":
      if (expr.value instanceof RegExp) throw unsupported(expr);
      return {
        type: "Literal",
        value: expr.value,
        loc: loc(expr)
      };
    default:
      throw unsupported(expr);
  }
}

function unsupportedLoc(loc: Syntax.SourceLocation) {return new MessageException({status:"unsupported",loc})}
function undefinedId(loc: Syntax.SourceLocation) {return new MessageException({status:"undefined-identifier",loc})}
function alreadyDefined(loc: Syntax.SourceLocation) {return new MessageException({status:"already-defined",loc})}
function assignToConst(loc: Syntax.SourceLocation) {return new MessageException({status:"assignment-to-const",loc})}

export function isMutable(id: Syntax.Identifier): boolean {
  if (id.decl.type == "Unresolved") throw undefinedId(id.loc);
  return isWrittenTo(id.decl);
}

function isWrittenTo(decl: Syntax.Declaration): boolean {
  return decl.type == "Var" && decl.decl.kind == "let";
}

class Scope {
  func: Syntax.FunctionDeclaration | null;
  ids: { [varname: string]: Syntax.Declaration } = {};
  parent: Scope | null;
  constructor(parent: Scope | null = null, fn: Syntax.FunctionDeclaration | null = null) {
    this.parent = parent;
    this.func = fn;
  }

  lookupDef(sym: Syntax.Identifier) {
    if (sym.name in this.ids) throw alreadyDefined(sym.loc);
    if (this.parent) this.parent.lookupDef(sym);
  }

  defSymbol(sym: Syntax.Identifier, decl: Syntax.Declaration) {
    // TODO enable shadowing
    this.lookupDef(sym);
    this.ids[sym.name] = decl;
  }

  lookupUse(sym: Syntax.Identifier): Syntax.Declaration {
    if (sym.name in this.ids) return this.ids[sym.name];
    if (this.parent) {
      let decl: Syntax.Declaration = this.parent.lookupUse(sym);
      if (this.func && !this.func.freeVars.includes(decl) && isWrittenTo(decl)) {
        this.func.freeVars.push(decl); // a free variable
      }
      return decl;
    }
    throw undefinedId(sym.loc);
  }

  useSymbol(sym: Syntax.Identifier, write: boolean = false) {
    const decl = this.lookupUse(sym);
    sym.decl = decl;
    switch (decl.type) {
      case "Var":
        decl.decl.id.refs.push(sym);
        if (write) {
          if (decl.decl.kind == "const") {
            throw assignToConst(sym.loc);
          }
          decl.decl.id.isWrittenTo = true;
        }
        break;
      case "Func":
        decl.decl.id.refs.push(sym);
        if (write) {
          throw assignToConst(sym.loc);
        }
        break;
      case "Param":
        decl.decl.refs.push(sym);
        if (write) {
          throw assignToConst(sym.loc);
        }
        break;
    }
  }
}

function resolveProgram(prog: Syntax.Program) {
  const root: Scope = new Scope();
  prog.body.forEach(stmt => resolveStament(root, stmt));
  prog.invariants.forEach(inv => resolveExpression(root, inv));
}

function resolveStament(scope: Scope, stmt: Syntax.Statement) {
  switch (stmt.type) {
    case "VariableDeclaration":
      scope.defSymbol(stmt.id, { type: "Var", decl: stmt });
      resolveExpression(scope, stmt.init);
      break;
    case "BlockStatement":
      const blockScope = new Scope(scope, scope.func);
      stmt.body.forEach(s => resolveStament(blockScope, s));
      break;
    case "ExpressionStatement":
      resolveExpression(scope, stmt.expression);
      break;
    case "AssertStatement":
      resolveExpression(scope, stmt.expression);
      break;
    case "IfStatement":
      resolveExpression(scope, stmt.test);
      const thenScope = new Scope(scope, scope.func);
      stmt.consequent.body.forEach(s => resolveStament(thenScope, s));
      const elseScope = new Scope(scope, scope.func);
      stmt.alternate.body.forEach(s => resolveStament(elseScope, s));
      break;
    case "ReturnStatement":
      resolveExpression(scope, stmt.argument);
      break;
    case "WhileStatement":
      resolveExpression(scope, stmt.test);
      const loopScope = new Scope(scope, scope.func);
      stmt.invariants.forEach(i => resolveExpression(loopScope, i));
      stmt.body.body.forEach(s => resolveStament(loopScope, s));
      break;
    case "DebuggerStatement":
      break;
    case "FunctionDeclaration": {
      const funScope = new Scope(scope, stmt);
      funScope.defSymbol(stmt.id, { type: "Func", decl: stmt });
      stmt.params.forEach(p => funScope.defSymbol(p, { type: "Param", func: stmt, decl: p }));
      stmt.requires.forEach(r => resolveExpression(funScope, r));
      stmt.ensures.forEach(r => resolveExpression(funScope, r, true));
      stmt.body.body.forEach(s => resolveStament(funScope, s));
      scope.defSymbol(stmt.id, { type: "Func", decl: stmt });
      break;
    }
  }
}

function stringAsIdentifier(name: string): Syntax.Identifier {
  const loc = { file: options.filename, start: { line: 0, column: 0}, end: { line: 0, column: 0}};
  return { type: "Identifier", name, refs: [], decl: { type: "Unresolved" }, isWrittenTo: false, loc };
}

function resolveExpression(scope: Scope, expr: Syntax.Expression, allowOld: boolean = false) {
  switch (expr.type) {
    case "Identifier":
      scope.useSymbol(expr);
      break;
    case "OldIdentifier":
      if (!allowOld) throw unsupportedLoc(expr.loc);
      scope.useSymbol(expr.id);
    case "Literal":
      break;
    case "ArrayExpression":
      expr.elements.forEach(e => resolveExpression(scope, e, allowOld));
      break;
    case "UnaryExpression":
      resolveExpression(scope, expr.argument, allowOld);
      break;
    case "BinaryExpression":
      resolveExpression(scope, expr.left, allowOld);
      resolveExpression(scope, expr.right, allowOld);
      break;
    case "LogicalExpression":
      resolveExpression(scope, expr.left, allowOld);
      resolveExpression(scope, expr.right, allowOld);
      break;
    case "ConditionalExpression":
      resolveExpression(scope, expr.test, allowOld);
      resolveExpression(scope, expr.consequent, allowOld);
      resolveExpression(scope, expr.alternate, allowOld);
      break;
    case "AssignmentExpression":
      resolveExpression(scope, expr.right, allowOld);
      scope.useSymbol(expr.left, true);
      break;
    case "SequenceExpression":
      expr.expressions.forEach(e => resolveExpression(scope, e, allowOld));
      break;
    case "CallExpression":
      expr.args.forEach(e => resolveExpression(scope, e, allowOld));
      resolveExpression(scope, expr.callee);
      break;
    case "SpecExpression":
      resolveExpression(scope, expr.callee);
      if (isMutable(expr.callee)) throw unsupportedLoc(expr.callee.loc);
      const preScope = new Scope(scope, scope.func);
      const postScope = new Scope(scope, scope.func);
      expr.args.forEach((a, argIdx) => {
        preScope.defSymbol(stringAsIdentifier(a), { type: "SpecArg", decl: expr, argIdx });
        postScope.defSymbol(stringAsIdentifier(a), { type: "SpecArg", decl: expr, argIdx });
      });
      resolveExpression(preScope, expr.pre);
      resolveExpression(postScope, expr.post, true);
      break;
  }
}

export function stringifyExpr(expr: Syntax.Expression): string {
  switch (expr.type) {
    case "Identifier":
      return expr.name;
    case "OldIdentifier":
      return `old(${expr.id.name})`;
    case "Literal":
      return expr.value === undefined ? "undefined" : JSON.stringify(expr.value);
    case "ArrayExpression":
      return `[${expr.elements.map(stringifyExpr).join(', ')}]`;
    case "UnaryExpression":
      switch (expr.operator) {
        case "typeof":
        case "void":
          return `${expr.operator}(${stringifyExpr(expr.argument)})`;
        default: 
          return `${expr.operator}${stringifyExpr(expr.argument)}`;
      }
    case "BinaryExpression":
      return `(${stringifyExpr(expr.left)} ${expr.operator} ${stringifyExpr(expr.right)})`;
    case "LogicalExpression":
      return `${stringifyExpr(expr.left)} ${expr.operator} ${stringifyExpr(expr.right)}`;
    case "ConditionalExpression":
      return `${stringifyExpr(expr.test)} ? ${stringifyExpr(expr.consequent)} : ${stringifyExpr(expr.alternate)}`;
    case "AssignmentExpression":
      return `${expr.left.name} = ${stringifyExpr(expr.right)}`;
    case "SequenceExpression":
      return `${expr.expressions.map(stringifyExpr).join(', ')}`;
    case "CallExpression":
      return `${stringifyExpr(expr.callee)}(${expr.args.map(stringifyExpr).join(', ')})`;
    case "SpecExpression":
      return `spec(${stringifyExpr(expr.callee)}, (${expr.args.join(", ")}) => (${stringifyExpr(expr.pre)}), (${expr.args.join(", ")}) => (${stringifyExpr(expr.post)}))`;
    case "PureExpression":
      return `pure()`;
  }
}

export function stringifyStmt(stmt: Syntax.Statement, indent: number = 0): string {
  function ind(s: string):string { let d = ""; for (let i = 0; i < indent; i++) d += "  "; return d + s; }
  switch (stmt.type) {
    case "VariableDeclaration":
      return ind(`${stmt.kind} ${stmt.id.name} = ${stringifyExpr(stmt.init)};\n`);
    case "BlockStatement":
      return ind("{\n") + stmt.body.map(s => stringifyStmt(s, indent + 1)).join("") + ind("}\n");
    case "ExpressionStatement":
      return ind(`${stringifyExpr(stmt.expression)};\n`);
    case "AssertStatement":
      return ind(`assert(${stringifyExpr(stmt.expression)});\n`);
    case "IfStatement":
      return ind(`if (${stringifyExpr(stmt.test)}) {\n`) +
             stmt.consequent.body.map(s => stringifyStmt(s, indent + 1)).join("") +
             ind("} else {\n") +
             stmt.alternate.body.map(s => stringifyStmt(s, indent + 1)).join("") +
             ind("}\n");
    case "ReturnStatement":
      return ind(`return ${stringifyExpr(stmt.argument)};\n`);
    case "WhileStatement":
      return ind(`while (${stringifyExpr(stmt.test)}) {\n`) +
             stmt.body.body.map(s => stringifyStmt(s, indent + 1)).join("") +
             ind("}\n");
    case "DebuggerStatement":
      return ind(`debugger;\n`);
    case "FunctionDeclaration":
      return ind(`function ${stmt.id.name} (${stmt.params.map(p => p.name).join(", ")}) {\n`) +
             stmt.body.body.map(s => stringifyStmt(s, indent + 1)).join("") +
             ind("}\n");
  }
}

function callMatchesParams(expr: Syntax.CallExpression, f: Syntax.FunctionDeclaration): boolean {
  if (expr.args.length != f.params.length) return false;
  for (let i = 0; i < expr.args.length; i++) {
    const arg: Syntax.Expression = expr.args[i];
    if (arg.type != "Identifier" ||
        arg.decl.type != "Param" ||
        arg.decl.func != f ||
        arg.decl.decl != f.params[i]) {
     return false;
    }
  }
  return true;
}

export function replaceFunctionResult(f: Syntax.FunctionDeclaration, expr: Syntax.Expression): Syntax.Expression {
  switch (expr.type) {
    case "Identifier":
    case "OldIdentifier":
    case "Literal":
    case "PureExpression":
      return expr;
    case "ArrayExpression":
      return {
        type: "ArrayExpression",
        elements: expr.elements.map(e => replaceFunctionResult(f, e)),
        loc: expr.loc
      };
    case "UnaryExpression":
      return {
        type: "UnaryExpression",
        operator: expr.operator,
        argument: replaceFunctionResult(f, expr.argument),
        loc: expr.loc
      };
    case "BinaryExpression":
      return {
        type: "BinaryExpression",
        operator: expr.operator,
        left: replaceFunctionResult(f, expr.left),
        right: replaceFunctionResult(f, expr.right),
        loc: expr.loc
      };
    case "LogicalExpression":
      return {
        type: "LogicalExpression",
        operator: expr.operator,
        left: replaceFunctionResult(f, expr.left),
        right: replaceFunctionResult(f, expr.right),
        loc: expr.loc
      };
    case "ConditionalExpression":
      return {
        type: "ConditionalExpression",
        test: replaceFunctionResult(f, expr.test),
        consequent: replaceFunctionResult(f, expr.consequent),
        alternate: replaceFunctionResult(f, expr.alternate),
        loc: expr.loc
      };
    case "AssignmentExpression":
      return {
        type: "AssignmentExpression",
        left: expr.left, 
        right: replaceFunctionResult(f, expr.right),
        loc: expr.loc
      };
    case "SequenceExpression":
      return {
        type: "SequenceExpression",
        expressions: expr.expressions.map(e => replaceFunctionResult(f, e)),
        loc: expr.loc
      };
    case "CallExpression":
      if (expr.callee.type == "Identifier" &&
          expr.callee.decl.type == "Func" &&
          expr.callee.decl.decl == f &&
          callMatchesParams(expr, f)) {
        return {
          type: "Identifier",
          name: "_res_",
          decl: { type: "Unresolved" },
          refs: [],
          isWrittenTo: false,
          loc: expr.loc
        };
      }
      return {
        type: "CallExpression",
        callee: replaceFunctionResult(f, expr.callee),
        args: expr.args.map(e => replaceFunctionResult(f, e)),
        loc: expr.loc
      };
    case "SpecExpression":
      return {
        type: "SpecExpression",
        callee: expr.callee,
        args: expr.args,
        pre: replaceFunctionResult(f, expr.pre),
        post: replaceFunctionResult(f, expr.post),
        loc: expr.loc
      };
  }
}

export function checkInvariants(whl: Syntax.WhileStatement): Syntax.FunctionDeclaration {
  return {
    type: "FunctionDeclaration",
    id: { type: "Identifier", name: "test", decl: {type: "Unresolved"}, refs: [], isWrittenTo: false, loc: whl.loc },
    params: [],
    requires: [],
    ensures: [],
    body: {
      type: "BlockStatement",
      body: whl.invariants
      .map((inv): Syntax.Statement =>
        ({ type: "AssertStatement", expression: inv, loc: inv.loc }))
      .concat(whl.body.body),
      loc: whl.loc
    },
    freeVars: [],
    loc: whl.loc
  };
}

export function checkPreconditions(f: Syntax.FunctionDeclaration): Syntax.FunctionDeclaration {
  return {
    type: "FunctionDeclaration",
    id: f.id,
    params: f.params,
    requires: f.requires,
    ensures: f.ensures,
    body: {
      type: "BlockStatement",
      body: f.requires
        .map((r): Syntax.Statement =>
          ({ type: "AssertStatement", expression: r, loc: r.loc }))
        .concat(f.body.body),
      loc: f.loc
    },
    freeVars: f.freeVars,
    loc: f.loc
  };
}