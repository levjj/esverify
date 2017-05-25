import * as JSyntax from "estree";
import { flatMap } from "./util";
import { MessageException, unexpected } from "./message";
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

function unsupported(node: JSyntax.Node, description: string = "unsupported syntax"): MessageException {
  return new MessageException({
    status: "error",
    type: "unsupported",
    loc: loc(node),
    description
  });
}

function findPseudoCalls(type: string, stmts: Array<JSyntax.Statement>): Array<Syntax.Expression> {
  return flatMap(stmts, stmt => {
    if (stmt.type == "ExpressionStatement" &&
        stmt.expression.type == "CallExpression" &&
        stmt.expression.callee.type == "Identifier" &&
        stmt.expression.callee.name == type) {
      if (stmt.expression.arguments.length != 1) throw unsupported(stmt.expression, `${type} expects proposition as one single argument`);
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
    throw new MessageException(unexpected(new Error("No location information available on nodes")));
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

function distinct(params: Array<Syntax.Identifier>): boolean {
  for (let i = 0; i < params.length - 1; i++) {
    for (let j = i + 1; j < params.length; j++) {
      if (params[i].name == params[j].name) return false;      
    }
  }
  return true;
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
        if (expr.arguments.length != 0) throw unsupported(expr, "pure modifier has no arguments");
        return { type: "PureExpression", loc: loc(expr) };
      }
      if (expr.callee.type == "Identifier" &&
          expr.callee.name == "old") {
        if (expr.arguments.length != 1 || expr.arguments[0].type != "Identifier") {
          throw unsupported(expr, "old modifier has exactly one argument");
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
        if (expr.arguments.length != 3) throw unsupported(expr, "spec(f,req,ens) has three arguments");
        const [callee, arg1, arg2] = expr.arguments;
        if (callee.type != "Identifier") throw unsupported(expr, "spec(f, req, ens) requires f to be an identifier");
        if (arg1.type != "ArrowFunctionExpression") throw unsupported(expr, "spec(f, req, ens) requires req to be an arrow function");
        if (arg2.type != "ArrowFunctionExpression") throw unsupported(expr, "spec(f, req, ens) requires ens to be an arrow function");
        const r: JSyntax.ArrowFunctionExpression = arg1;
        const s: JSyntax.ArrowFunctionExpression = arg2;
        if (r.body.type == "BlockStatement") throw unsupported(expr, "spec(f, req, ens) requires req to be an arrow function with an expression as body");
        if (s.body.type == "BlockStatement") throw unsupported(expr, "spec(f, req, ens) requires ens to be an arrow function with an expression as body");
        if ( r.params.length != s.params.length &&
            !r.params.every((p, idx) => {
              const otherP = s.params[idx];
              return p.type == "Identifier" && otherP.type == "Identifier" && p.name == otherP.name; })) {
          throw unsupported(expr, "spec(f, req, ens) requires req and ens to have same parameters");
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
      if (expr.arguments.length > 9) throw unsupported(expr, "more than 9 arguments not supported yet");
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
  const resolver = new NameResolver();
  resolver.visitProgram(prog);
  return prog;
}

export abstract class Visitor<E,S> {

  abstract visitIdentifier(expr: Syntax.Identifier): E;
  abstract visitOldIdentifier(expr: Syntax.OldIdentifier): E;
  abstract visitLiteral(expr: Syntax.Literal): E;
  abstract visitArrayExpression(expr: Syntax.ArrayExpression): E;
  abstract visitUnaryExpression(expr: Syntax.UnaryExpression): E;
  abstract visitBinaryExpression(expr: Syntax.BinaryExpression): E;
  abstract visitLogicalExpression(expr: Syntax.LogicalExpression): E;
  abstract visitConditionalExpression(expr: Syntax.ConditionalExpression): E;
  abstract visitAssignmentExpression(expr: Syntax.AssignmentExpression): E;
  abstract visitSequenceExpression(expr: Syntax.SequenceExpression): E;
  abstract visitCallExpression(expr: Syntax.CallExpression): E;
  abstract visitPureExpression(expr: Syntax.PureExpression): E;
  abstract visitSpecExpression(expr: Syntax.SpecExpression): E;

  visitExpression(expr: Syntax.Expression): E {
    switch (expr.type) {
      case "Identifier": return this.visitIdentifier(expr);
      case "OldIdentifier": return this.visitOldIdentifier(expr);
      case "Literal": return this.visitLiteral(expr);
      case "ArrayExpression": return this.visitArrayExpression(expr);
      case "UnaryExpression": return this.visitUnaryExpression(expr);
      case "BinaryExpression": return this.visitBinaryExpression(expr);
      case "LogicalExpression": return this.visitLogicalExpression(expr);
      case "ConditionalExpression": return this.visitConditionalExpression(expr);
      case "AssignmentExpression": return this.visitAssignmentExpression(expr);
      case "SequenceExpression": return this.visitSequenceExpression(expr);
      case "CallExpression": return this.visitCallExpression(expr);
      case "SpecExpression": return this.visitSpecExpression(expr);
      case "PureExpression": return this.visitPureExpression(expr);
    }
  }

  abstract visitVariableDeclaration(stmt: Syntax.VariableDeclaration): S;
  abstract visitBlockStatement(stmt: Syntax.BlockStatement): S;
  abstract visitExpressionStatement(stmt: Syntax.ExpressionStatement): S;
  abstract visitAssertStatement(stmt: Syntax.AssertStatement): S;
  abstract visitIfStatement(stmt: Syntax.IfStatement): S;
  abstract visitReturnStatement(stmt: Syntax.ReturnStatement): S;
  abstract visitWhileStatement(stmt: Syntax.WhileStatement): S;
  abstract visitDebuggerStatement(stmt: Syntax.DebuggerStatement): S;
  abstract visitFunctionDeclaration(stmt: Syntax.FunctionDeclaration): S;
  
  visitStatement(stmt: Syntax.Statement): S {
    switch (stmt.type) {
      case "VariableDeclaration": return this.visitVariableDeclaration(stmt);
      case "BlockStatement": return this.visitBlockStatement(stmt);
      case "ExpressionStatement": return this.visitExpressionStatement(stmt);
      case "AssertStatement": return this.visitAssertStatement(stmt);
      case "IfStatement": return this.visitIfStatement(stmt);
      case "ReturnStatement": return this.visitReturnStatement(stmt);
      case "WhileStatement": return this.visitWhileStatement(stmt);
      case "DebuggerStatement": return this.visitDebuggerStatement(stmt);
      case "FunctionDeclaration": return this.visitFunctionDeclaration(stmt);
    }
  }

  abstract visitProgram(prog: Syntax.Program): S;

}

function unsupportedLoc(loc: Syntax.SourceLocation, description: string = "") {
  return new MessageException({ status: "error", type:"unsupported", loc, description });
}

function undefinedId(loc: Syntax.SourceLocation) {
  return new MessageException({ status: "error", type:"undefined-identifier", loc, description: ""});
}

function alreadyDefined(loc: Syntax.SourceLocation, decl: Syntax.Declaration) {
  if (decl.type == "Unresolved") throw unexpected(new Error("decl should be resolved"));
  const { file, start } = decl.decl.loc;
  return new MessageException({ status: "error", type:"already-defined", loc,
                                description: `at ${file}:${start.line}:${start.column}` });
}

function assignToConst(loc: Syntax.SourceLocation) {
  return new MessageException({ status: "error", type: "assignment-to-const", loc, description: "" });
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
    if (sym.name in this.ids) throw alreadyDefined(sym.loc, this.ids[sym.name]);
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

class NameResolver extends Visitor<void,void> {

  scope: Scope = new Scope();
  allowOld: boolean = false;

  stringAsIdentifier(name: string): Syntax.Identifier {
    const loc = { file: options.filename, start: { line: 0, column: 0}, end: { line: 0, column: 0}};
    return { type: "Identifier", name, refs: [], decl: { type: "Unresolved" }, isWrittenTo: false, loc };
  }

  scoped(action: () => void, allowsOld: boolean = this.allowOld, fn: null | Syntax.FunctionDeclaration = this.scope.func) {
    const { scope, allowOld } = this;
    try {
      this.scope = new Scope(scope, fn);
      this.allowOld = allowsOld;
      action();
    } finally {
      this.scope = scope;
      this.allowOld = allowOld;
    }
  }

  visitIdentifier(expr: Syntax.Identifier) {
    this.scope.useSymbol(expr);
  }

  visitOldIdentifier(expr: Syntax.OldIdentifier) {
    if (!this.allowOld) throw unsupportedLoc(expr.loc, "old() not allowed in this context");
    this.scope.useSymbol(expr.id);
  }

  visitLiteral(expr: Syntax.Literal) { }

  visitArrayExpression(expr: Syntax.ArrayExpression) {
    expr.elements.forEach(e => this.visitExpression(e));
  }

  visitUnaryExpression(expr: Syntax.UnaryExpression) {
    this.visitExpression(expr.argument);
  }

  visitBinaryExpression(expr: Syntax.BinaryExpression) {
    this.visitExpression(expr.left);
    this.visitExpression(expr.right);
  }

  visitLogicalExpression(expr: Syntax.LogicalExpression) {
    this.visitExpression(expr.left);
    this.visitExpression(expr.right);
  }

  visitConditionalExpression(expr: Syntax.ConditionalExpression) {
    this.visitExpression(expr.test);
    this.visitExpression(expr.consequent);
    this.visitExpression(expr.alternate);
  }

  visitAssignmentExpression(expr: Syntax.AssignmentExpression) {
    this.visitExpression(expr.right);
    this.scope.useSymbol(expr.left, true);
  }

  visitSequenceExpression(expr: Syntax.SequenceExpression) {
    expr.expressions.forEach(e => this.visitExpression(e));
  }

  visitCallExpression(expr: Syntax.CallExpression) {
    expr.args.forEach(e => this.visitExpression(e));
    this.visitExpression(expr.callee);
  }

  visitSpecExpression(expr: Syntax.SpecExpression) {
    this.visitExpression(expr.callee);
    if (isMutable(expr.callee)) throw unsupportedLoc(expr.callee.loc, "spec(f,req,ens) requires f to be const");
    this.scoped(() => {
      expr.args.forEach((a, argIdx) => {
        this.scope.defSymbol(this.stringAsIdentifier(a), { type: "SpecArg", decl: expr, argIdx });
      });
      this.visitExpression(expr.pre);
    }, false);
    this.scoped(() => {
      expr.args.forEach((a, argIdx) => {
        this.scope.defSymbol(this.stringAsIdentifier(a), { type: "SpecArg", decl: expr, argIdx });
      });
      this.visitExpression(expr.post);
    }, true);
  }

  visitPureExpression(expr: Syntax.PureExpression) { }

  visitVariableDeclaration(stmt: Syntax.VariableDeclaration) {
    this.scope.defSymbol(stmt.id, { type: "Var", decl: stmt });
    this.visitExpression(stmt.init);
  }

  visitBlockStatement(stmt: Syntax.BlockStatement) {
    this.scoped(() => {
      stmt.body.forEach(s => this.visitStatement(s));
    });
  }

  visitExpressionStatement(stmt: Syntax.ExpressionStatement) {
    this.visitExpression(stmt.expression);
  }

  visitAssertStatement(stmt: Syntax.AssertStatement) {
    this.visitExpression(stmt.expression);
  }

  visitIfStatement(stmt: Syntax.IfStatement) {
    this.visitExpression(stmt.test);
    this.scoped(() => {
      stmt.consequent.body.forEach(s => this.visitStatement(s));
    })
    this.scoped(() => {
      stmt.alternate.body.forEach(s => this.visitStatement(s));
    })
  }

  visitReturnStatement(stmt: Syntax.ReturnStatement) {
    this.visitExpression(stmt.argument);
  }

  visitWhileStatement(stmt: Syntax.WhileStatement) {
    this.visitExpression(stmt.test);
    this.scoped(() => {
      stmt.invariants.forEach(i => this.visitExpression(i));
      stmt.body.body.forEach(s => this.visitStatement(s));
    });
  }

  visitDebuggerStatement(stmt: Syntax.DebuggerStatement) { }

  visitFunctionDeclaration(stmt: Syntax.FunctionDeclaration) {
    this.scoped(() => {
      this.scope.defSymbol(stmt.id, { type: "Func", decl: stmt });
      stmt.params.forEach(p => this.scope.defSymbol(p, { type: "Param", func: stmt, decl: p }));
      stmt.requires.forEach(r => this.visitExpression(r));
      stmt.body.body.forEach(s => this.visitStatement(s));
      this.allowOld = true;
      stmt.ensures.forEach(r => this.visitExpression(r));
    }, false, stmt);
    this.scope.defSymbol(stmt.id, { type: "Func", decl: stmt });
  }

  visitProgram(prog: Syntax.Program) {
    prog.body.forEach(stmt => this.visitStatement(stmt));
    prog.invariants.forEach(inv => this.visitExpression(inv));
  }
}

export function isMutable(id: Syntax.Identifier): boolean {
  if (id.decl.type == "Unresolved") throw undefinedId(id.loc);
  return isWrittenTo(id.decl);
}

class Stringifier extends Visitor<string,string> {

  depth: number = 0;

  visitIdentifier(expr: Syntax.Identifier): string {
    return expr.name;
  }

  visitOldIdentifier(expr: Syntax.OldIdentifier): string {
    return `old(${expr.id.name})`;
  }
  
  visitLiteral(expr: Syntax.Literal): string {
    return expr.value === undefined ? "undefined" : JSON.stringify(expr.value);
  }
  
  visitArrayExpression(expr: Syntax.ArrayExpression): string {
    return `[${expr.elements.map(e => this.visitExpression(e)).join(', ')}]`;
    }
  
  visitUnaryExpression(expr: Syntax.UnaryExpression): string {
    switch (expr.operator) {
      case "typeof":
      case "void":
        return `${expr.operator}(${this.visitExpression(expr.argument)})`;
      default:
        return `${expr.operator}${this.visitExpression(expr.argument)}`;
    }
  }
  
  visitBinaryExpression(expr: Syntax.BinaryExpression): string {
    return `(${this.visitExpression(expr.left)} ${expr.operator} ${this.visitExpression(expr.right)})`;
  }
  
  visitLogicalExpression(expr: Syntax.LogicalExpression): string {
    return `${this.visitExpression(expr.left)} ${expr.operator} ${this.visitExpression(expr.right)}`;
  }
  
  visitConditionalExpression(expr: Syntax.ConditionalExpression): string {
    return `${this.visitExpression(expr.test)} ? ${this.visitExpression(expr.consequent)} : ${this.visitExpression(expr.alternate)}`;
  }
 
  visitAssignmentExpression(expr: Syntax.AssignmentExpression): string {
    return `${expr.left.name} = ${this.visitExpression(expr.right)}`;
  }
  
  visitSequenceExpression(expr: Syntax.SequenceExpression): string {
    return `${expr.expressions.map(e => this.visitExpression(e)).join(', ')}`;
  }
  
  visitCallExpression(expr: Syntax.CallExpression): string {
    return `${this.visitExpression(expr.callee)}(${expr.args.map(a => this.visitExpression(a)).join(', ')})`;
  }
  
  visitSpecExpression(expr: Syntax.SpecExpression): string {
    return `spec(${this.visitExpression(expr.callee)}, (${expr.args.join(", ")}) => (${this.visitExpression(expr.pre)}), (${expr.args.join(", ")}) => (${this.visitExpression(expr.post)}))`;
  }
  
  visitPureExpression(expr: Syntax.PureExpression): string {
    return `pure()`;
  }

  indent(f: () => void) {
    this.depth++;
    try {
      f();
    } finally {
      this.depth--;
    }
  }

  i(s: string):string {
    let d = "";
    for (let i = 0; i < this.depth; i++) d += "  ";
    return d + s;
  }

  visitVariableDeclaration(stmt: Syntax.VariableDeclaration): string {
    return this.i(`${stmt.kind} ${stmt.id.name} = ${this.visitExpression(stmt.init)};\n`);
  }
  
  visitStatements(stmts: Array<Syntax.Statement>): string {
    let res = "{\n";
    this.indent(() => {
      for (const s of stmts) {
        res += this.visitStatement(s);
      }
    });
    return res + this.i("}");
  }
  
  visitBlockStatement(stmt: Syntax.BlockStatement): string {
    return this.i(this.visitStatements(stmt.body)) + "\n";
  }
  
  visitExpressionStatement(stmt: Syntax.ExpressionStatement): string {
    return this.i(`${this.visitExpression(stmt.expression)};\n`);
  }
  
  visitAssertStatement(stmt: Syntax.AssertStatement): string {
    return this.i(`assert(${this.visitExpression(stmt.expression)});\n`);
  }
  
  visitIfStatement(stmt: Syntax.IfStatement): string {
    return this.i(`if (${this.visitExpression(stmt.test)}) ${this.visitStatements(stmt.consequent.body)} else ${this.visitStatements(stmt.alternate.body)}\n`);
  }
  
  visitReturnStatement(stmt: Syntax.ReturnStatement): string {
    return this.i(`return ${this.visitExpression(stmt.argument)};\n`);
  }
  
  visitWhileStatement(stmt: Syntax.WhileStatement): string {
    return this.i(`while (${this.visitExpression(stmt.test)}) ${this.visitStatements(stmt.body.body)}\n`);
  }
  
  visitDebuggerStatement(stmt: Syntax.DebuggerStatement): string {
    return this.i(`debugger;\n`);
  }
  
  visitFunctionDeclaration(stmt: Syntax.FunctionDeclaration): string {
    return this.i(`function ${stmt.id.name} (${stmt.params.map(p => p.name).join(", ")}) ${this.visitStatements(stmt.body.body)}\n`);
  }

  visitProgram(prog: Syntax.Program) {
    return prog.body.map(s => this.visitStatement(s)).join("");
  }
}

export function stringifyExpr(expr: Syntax.Expression): string {
  return (new Stringifier()).visitExpression(expr);
}

export function stringifyStmt(stmt: Syntax.Statement): string {
  return (new Stringifier()).visitStatement(stmt);
}

class FunctionResultSubstituter extends Visitor<Syntax.Expression, void> {

  f: Syntax.FunctionDeclaration;

  constructor(f: Syntax.FunctionDeclaration) {
    super();
    this.f = f;
  }

  callMatchesParams(expr: Syntax.CallExpression): boolean {
    if (expr.args.length != this.f.params.length) return false;
    for (let i = 0; i < expr.args.length; i++) {
      const arg: Syntax.Expression = expr.args[i];
      if (arg.type != "Identifier" ||
          arg.decl.type != "Param" ||
          arg.decl.func != this.f ||
          arg.decl.decl != this.f.params[i]) {
      return false;
      }
    }
    return true;
  }

  visitIdentifier(expr: Syntax.Identifier): Syntax.Expression {
    return expr;
  }
  
  visitOldIdentifier(expr: Syntax.OldIdentifier): Syntax.Expression {
    return expr;
  }
  
  visitLiteral(expr: Syntax.Literal): Syntax.Expression {
    return expr;
  }
  
  visitPureExpression(expr: Syntax.PureExpression): Syntax.Expression {
    return expr;
  }
  
  visitArrayExpression(expr: Syntax.ArrayExpression): Syntax.Expression {
    return {
      type: "ArrayExpression",
      elements: expr.elements.map(e => this.visitExpression(e)),
      loc: expr.loc
    };
  }
  
  visitUnaryExpression(expr: Syntax.UnaryExpression): Syntax.Expression {
    return {
      type: "UnaryExpression",
      operator: expr.operator,
      argument: this.visitExpression(expr.argument),
      loc: expr.loc
    };
  }
  
  visitBinaryExpression(expr: Syntax.BinaryExpression): Syntax.Expression {
    return {
      type: "BinaryExpression",
      operator: expr.operator,
      left: this.visitExpression(expr.left),
      right: this.visitExpression(expr.right),
      loc: expr.loc
    };
  }
  
  visitLogicalExpression(expr: Syntax.LogicalExpression): Syntax.Expression {
    return {
      type: "LogicalExpression",
      operator: expr.operator,
      left: this.visitExpression(expr.left),
      right: this.visitExpression(expr.right),
      loc: expr.loc
    };
  }
  
  visitConditionalExpression(expr: Syntax.ConditionalExpression): Syntax.Expression {
    return {
      type: "ConditionalExpression",
      test: this.visitExpression(expr.test),
      consequent: this.visitExpression(expr.consequent),
      alternate: this.visitExpression(expr.alternate),
      loc: expr.loc
    };
  }
  
  visitAssignmentExpression(expr: Syntax.AssignmentExpression): Syntax.Expression {
    return {
      type: "AssignmentExpression",
      left: expr.left, 
      right: this.visitExpression(expr.right),
      loc: expr.loc
    };
  }
  
  visitSequenceExpression(expr: Syntax.SequenceExpression): Syntax.Expression {
    return {
      type: "SequenceExpression",
      expressions: expr.expressions.map(e => this.visitExpression(e)),
      loc: expr.loc
    };
  }
  
  visitCallExpression(expr: Syntax.CallExpression): Syntax.Expression {
    if (expr.callee.type == "Identifier" &&
        expr.callee.decl.type == "Func" &&
        expr.callee.decl.decl == this.f &&
        this.callMatchesParams(expr)) {
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
      callee: this.visitExpression(expr.callee),
      args: expr.args.map(e => this.visitExpression(e)),
      loc: expr.loc
    };
  }
  
  visitSpecExpression(expr: Syntax.SpecExpression): Syntax.Expression {
    return {
      type: "SpecExpression",
      callee: expr.callee,
      args: expr.args,
      pre: this.visitExpression(expr.pre),
      post: this.visitExpression(expr.post),
      loc: expr.loc
    };
  }

  visitVariableDeclaration(stmt: Syntax.VariableDeclaration) {}
  visitBlockStatement(stmt: Syntax.BlockStatement) {}
  visitExpressionStatement(stmt: Syntax.ExpressionStatement) {}
  visitAssertStatement(stmt: Syntax.AssertStatement) {}
  visitIfStatement(stmt: Syntax.IfStatement) {}
  visitReturnStatement(stmt: Syntax.ReturnStatement) {}
  visitWhileStatement(stmt: Syntax.WhileStatement) {}
  visitDebuggerStatement(stmt: Syntax.DebuggerStatement) {}
  visitFunctionDeclaration(stmt: Syntax.FunctionDeclaration) {}
  visitProgram(prog: Syntax.Program) {}
}

export function replaceFunctionResult(f: Syntax.FunctionDeclaration, expr: Syntax.Expression): Syntax.Expression {
  const sub = new FunctionResultSubstituter(f);
  return sub.visitExpression(expr);
}

export function loopTestingCode(whl: Syntax.WhileStatement): Array<Syntax.Statement> {
  return [{
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
  },
  {
    type: "ExpressionStatement",
    expression: {
      type: "CallExpression",
      args: [],
      callee: {
        type: "Identifier", name: "test", decl: {type: "Unresolved"},
        refs: [], isWrittenTo: false, loc: whl.loc
      },
      loc: whl.loc
    },
    loc: whl.loc
  }];
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

export function convertToAssignment(decl: Syntax.VariableDeclaration): Syntax.ExpressionStatement {
  return {
    type: "ExpressionStatement",
    expression: {
      type: "AssignmentExpression",
      left: decl.id,
      right: decl.init,
      loc: decl.loc
    },
    loc: decl.loc
  }
}
