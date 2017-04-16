/// <reference path="../typings/mozilla-spidermonkey-parser-api.d.ts"/>
import { Syntax } from "spiderMonkeyParserAPI";
import { flatMap } from "./util";

export namespace JSyntax {
  export type Declaration = { type: "Unresolved" }
                          | { type: "Var"; decl: JSyntax.VariableDeclaration }
                          | { type: "Func"; decl: JSyntax.FunctionDeclaration }
                          | { type: "Param";
                              func: JSyntax.FunctionDeclaration;
                              decl: JSyntax.Identifier };

  export interface Identifier { type: "Identifier"; name: string;
                                decl: Declaration; refs: Array<Identifier>; isWrittenTo: boolean }
  export interface OldIdentifier { type: "OldIdentifier"; id: Identifier; version?: number }
  export interface Literal { type: "Literal";
                             value: undefined | null | boolean | number | string; }
  export interface ArrayExpression { type: "ArrayExpression";
                                     elements: Array<Expression>; }
  export type UnaryOperator = "-" | "+" | "!" | "~" | "typeof" | "void";
  export interface UnaryExpression { type: "UnaryExpression";
                                     operator: UnaryOperator;
                                     argument: Expression; }
  export type BinaryOperator = "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">="
                             | "<<" | ">>" | ">>>" | "+" | "-" | "*" | "/" | "%"
                             | "|" | "^" | "&";
  export interface BinaryExpression { type: "BinaryExpression";
                                      operator: BinaryOperator;
                                      left: Expression;
                                      right: Expression; }
  export type LogicalOperator = "||" | "&&";
  export interface LogicalExpression { type: "LogicalExpression";
                                       operator: LogicalOperator;
                                       left: Expression;
                                       right: Expression; }
  export interface ConditionalExpression { type: "ConditionalExpression";
                                           test: Expression;
                                           consequent: Expression;
                                           alternate: Expression; }
  export interface AssignmentExpression { type: "AssignmentExpression";
                                          left: Identifier;
                                          right: Expression; }
  export interface SequenceExpression { type: "SequenceExpression";
                                        expressions: Expression[]; }
  export interface CallExpression { type: "CallExpression";
                                    callee: Expression;
                                    arguments: Array<Expression>; }
  // export interface FunctionExpression { type: "FunctionExpression";
  //                                       params: Array<Identifier>;
  //                                       body: Statement[]; }
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
                        //  | FunctionExpression
                         | CallExpression;
  export interface VariableDeclaration { type: "VariableDeclaration";
                                         id: Identifier;
                                         init: Expression;
                                         kind: "let" | "const"; }
  export interface BlockStatement { type: "BlockStatement";
                                    body: Statement[]; }
  export interface ExpressionStatement { type: "ExpressionStatement";
                                         expression: Expression; }
  export interface AssertStatement { type: "AssertStatement";
                                     expression: Expression; }
  export interface IfStatement { type: "IfStatement";
                                 test: Expression;
                                 consequent: BlockStatement;
                                 alternate: BlockStatement; }
  export interface ReturnStatement { type: "ReturnStatement";
                                     argument: Expression; }
  export interface WhileStatement { type: "WhileStatement";
                                    invariants: Array<Expression>;
                                    test: Expression;
                                    body: BlockStatement; }
  export interface DebuggerStatement { type: "DebuggerStatement"; }
  export interface FunctionDeclaration { type: "FunctionDeclaration";
                                         id: Identifier;
                                         params: Array<Identifier>;
                                         requires: Array<Expression>;
                                         ensures: Array<Expression>;
                                         body: BlockStatement;
                                         freeVars: Array<Declaration>; }
 
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
                          invariants: Array<Expression>,
                          functions: Array<FunctionDeclaration> };
}

function findPseudoCalls(type: string, stmts: Array<Syntax.Statement>): Array<JSyntax.Expression> {
  return flatMap(stmts, stmt => {
    if (stmt.type == "ExpressionStatement" &&
        stmt.expression.type == "CallExpression" &&
        stmt.expression.callee.type == "Identifier" &&
        stmt.expression.callee.name == type &&
        stmt.expression.arguments.length == 1) {
      return [expressionAsJavaScript(stmt.expression.arguments[0])];
    }
    return [];
  });
}

function withoutPseudoCalls(type: string, stmts: Array<Syntax.Statement>): Array<Syntax.Statement> {
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

function patternAsIdentifier(node: Syntax.Pattern): JSyntax.Identifier {
  if (node.type != "Identifier") throw new Error("Identifier expected:\n" + JSON.stringify(node));
  return {
    type: "Identifier",
    name: node.name,
    refs: [],
    decl: { type: "Unresolved" },
    isWrittenTo: false
  };
}

function unaryOp(op: Syntax.UnaryOperator): JSyntax.UnaryOperator {
  switch (op) {
    case "-":
    case "+":
    case "!":
    case "~":
    case "typeof":
    case "void":
      return op;
    default:
      throw new Error("unsupported");
  }
}

function binaryOp(op: Syntax.BinaryOperator): JSyntax.BinaryOperator {
  switch (op) {
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
      return op;
    default:
      throw new Error("unsupported");
  }
}

export function programAsJavaScript(program: Syntax.Program): JSyntax.Program {
  const body = flatMap(withoutPseudoCalls("invariant", program.body), statementAsJavaScript);
  if (body.some(stmt => stmt.type == "ReturnStatement")) {
    throw new Error("Top level return not allowed");
  }
  const prog: JSyntax.Program = {
    body,
    invariants: findPseudoCalls("invariant", program.body),
    functions: findFunctions({ type: "BlockStatement", body })
  };
  resolveProgram(prog);
  return prog;
}

function findFunctions(stmt: JSyntax.Statement): Array<JSyntax.FunctionDeclaration> {
  switch (stmt.type) {
    case "VariableDeclaration":
    case "ExpressionStatement":
    case "AssertStatement":
    case "ReturnStatement":
    case "DebuggerStatement":
      return [];
    case "BlockStatement":
      return flatMap(stmt.body, findFunctions);
    case "IfStatement":
      return findFunctions(stmt.consequent).concat(findFunctions(stmt.alternate));
    case "WhileStatement":
      return findFunctions(stmt.body);
    case "FunctionDeclaration":
      return [stmt].concat(findFunctions(stmt.body));
  }
}

function statementAsJavaScript(stmt: Syntax.Statement): Array<JSyntax.Statement> {
  function assert(cond: boolean) { if (!cond) throw new Error("Not supported:\n" + JSON.stringify(stmt)); }
  switch (stmt.type) {
    case "EmptyStatement":
      return [];
    case "VariableDeclaration":
      assert(stmt.kind == "let" || stmt.kind == "const");
      return stmt.declarations.map(decl => {
        assert(decl.id.type == "Identifier");
        const d: JSyntax.VariableDeclaration = {
          type: "VariableDeclaration",
          kind: stmt.kind == "let" ? "let" : "const",
          id: patternAsIdentifier(decl.id),
          init: decl.init ? expressionAsJavaScript(decl.init) : {type: "Literal", value: undefined}
        };
        return d;
      });
    case "BlockStatement":
      return [{
        type: "BlockStatement",
        body: flatMap(stmt.body, statementAsJavaScript)
      }];
    case "ExpressionStatement":
      if (stmt.expression.type == "CallExpression" &&
          stmt.expression.callee.type == "Identifier" &&
          stmt.expression.callee.name == "assert" &&
          stmt.expression.arguments.length == 1) {
        return [{
          type: "AssertStatement", expression: expressionAsJavaScript(stmt.expression.arguments[0])
        }];
      }
      return [{
        type: "ExpressionStatement", expression: expressionAsJavaScript(stmt.expression)
      }]
    case "IfStatement":
      return [{
        type: "IfStatement",
        test: expressionAsJavaScript(stmt.test),
        consequent: {
          type: "BlockStatement",
          body: stmt.consequent.type == "BlockStatement"
                ? flatMap(stmt.consequent.body, statementAsJavaScript)
                : statementAsJavaScript(stmt.consequent)
        },
        alternate: {
          type: "BlockStatement",
          body: stmt.alternate ? (stmt.alternate.type == "BlockStatement"
                ? flatMap(stmt.alternate.body, statementAsJavaScript)
                : statementAsJavaScript(stmt.alternate)) : []
        }
      }];
    case "WhileStatement":
      const stmts: Array<Syntax.Statement> = stmt.body.type == "BlockStatement" ? stmt.body.body : [stmt];
      return [{
        type: "WhileStatement",
        invariants: findPseudoCalls("invariant", stmts),
        test: expressionAsJavaScript(stmt.test),
        body: {
          type: "BlockStatement",
          body: flatMap(withoutPseudoCalls("invariant", stmts), statementAsJavaScript)
        }
      }];
    case "DebuggerStatement":
      return [stmt];
    case "ReturnStatement":
      return [{
        type: "ReturnStatement",
        argument: stmt.argument ? expressionAsJavaScript(stmt.argument) : { type: "Literal", value: undefined }}];
    case "FunctionDeclaration": {
      if (stmt.defaults && stmt.defaults.length > 0) throw new Error("defaults not supported");
      if (stmt.rest) throw new Error("Rest arguments not supported");
      if (stmt.body.type != "BlockStatement") throw new Error("unsupported");
      if (stmt.generator) throw new Error("generators not supported");
      const params: Array<JSyntax.Identifier> = stmt.params.map(patternAsIdentifier);
      if (!distinct(params)) throw new Error("parameter names must be distinct");
      const id: JSyntax.Identifier = { type: "Identifier", name: stmt.id.name,
        refs: [], isWrittenTo: false, decl: { type: "Unresolved" } };
      const fd: JSyntax.FunctionDeclaration = {
        type: "FunctionDeclaration",
        id,
        params,
        requires: findPseudoCalls("requires", stmt.body.body),
        ensures: findPseudoCalls("ensures", stmt.body.body),
        body: {
          type: "BlockStatement",
          body: flatMap(withoutPseudoCalls("requires",
                        withoutPseudoCalls("ensures", stmt.body.body)), statementAsJavaScript)
        },
        freeVars: []
      };
      fd.id.decl = { type: "Func", decl: fd };
      return [fd];
    }
    default:
      throw new Error("Not supported:\n" + JSON.stringify(stmt));
  }
}

function assignUpdate(left: JSyntax.Identifier, op: JSyntax.BinaryOperator, right: Syntax.Expression): JSyntax.AssignmentExpression {
  return {
    type: "AssignmentExpression",
    left,
    right: {
      type: "BinaryExpression",
      left,
      operator: op,
      right: expressionAsJavaScript(right)
    }
  };
}

function distinct(params: Array<JSyntax.Identifier>): boolean {
  for (let i = 0; i < params.length - 1; i++) {
    for (let j = i + 1; j < params.length; j++) {
      if (params[i].name == params[j].name) return false;      
    }
  }
  return true;
}

function expressionAsJavaScript(expr: Syntax.Expression): JSyntax.Expression {
  function assert(cond: boolean) { if (!cond) throw new Error("Not supported:\n" + JSON.stringify(expr)); }
  switch (expr.type) {
    case "ThisExpression":
    case "ObjectExpression":
      throw new Error("not supported");
    case "ArrayExpression":
      return {
        type: "ArrayExpression",
        elements: expr.elements.map(expressionAsJavaScript)
      };
    // case "FunctionExpression":
    //   if (expr.id) throw new Error("named function expressions not supported");
    //   if (expr.defaults && expr.defaults.length > 0) throw new Error("defaults not supported");
    //   if (expr.rest) throw new Error("Rest arguments not supported");
    //   if (expr.body.type != "BlockStatement") throw new Error("unsupported");
    //   if (expr.generator) throw new Error("generators not supported");
    //   const params: Array<JSyntax.Identifier> = expr.params.map(patternAsIdentifier);
    //   if (!distinct(params)) throw new Error("parameter names must be distinct");
    //   return {
    //     type: "FunctionExpression",
    //     params,
    //     body: flatMap(expr.body.body, statementAsJavaScript)
    //   };
    // case "ArrowExpression":
    //   if (expr.defaults && expr.defaults.length > 0) throw new Error("defaults not supported");
    //   if (expr.rest) throw new Error("Rest arguments not supported");
    //   if (expr.body.type != "BlockStatement") throw new Error("unsupported");
    //   if (expr.generator) throw new Error("generators not supported");
    //   return {
    //     type: "FunctionExpression",
    //     params: expr.params.map(patternAsIdentifier),
    //     body: flatMap(expr.body.body, statementAsJavaScript)
    //   };
    case "SequenceExpression":
      return {
        type: "SequenceExpression",
        expressions: expr.expressions.map(expressionAsJavaScript)
      };
    case "UnaryExpression":
      return {
        type: "UnaryExpression",
        operator: unaryOp(expr.operator),
        argument: expressionAsJavaScript(expr.argument)
      };
    case "BinaryExpression":
      return {
        type: "BinaryExpression",
        operator: binaryOp(expr.operator),
        left: expressionAsJavaScript(expr.left),
        right: expressionAsJavaScript(expr.right)
      };
    case "AssignmentExpression":
      if (expr.left.type != "Identifier") throw new Error("only identifiers can be assigned");
      const to: JSyntax.Identifier = { type: "Identifier", name: expr.left.name,
        refs: [], isWrittenTo: true, decl: { type: "Unresolved" } };
      switch (expr.operator) {
        case "=":
          return {
            type: "AssignmentExpression",
            left: to,
            right: expressionAsJavaScript(expr.right)
          };
        case "+=": return assignUpdate(to, "+", expr.right);
        case "-=": return assignUpdate(to, "-", expr.right);
        case "*=": return assignUpdate(to, "*", expr.right);
        case "/=": return assignUpdate(to, "/", expr.right);
        case "%=": return assignUpdate(to, "%", expr.right);
        case "<<=": return assignUpdate(to, "<<", expr.right);
        case ">>=": return assignUpdate(to, ">>", expr.right);
        case ">>>=": return assignUpdate(to, ">>>", expr.right);
        case "|=": return assignUpdate(to, "|", expr.right);
        case "^=": return assignUpdate(to, "^", expr.right);
        case "&=": return assignUpdate(to, "&", expr.right);
        default: throw new Error("unknown operator");
      }
    case "UpdateExpression": {
      if (expr.argument.type != "Identifier") throw new Error("only identifiers can be assigned");
      const to: JSyntax.Identifier = { type: "Identifier", name: expr.argument.name, refs: [],
                                       isWrittenTo: true, decl: { type: "Unresolved" } },
            one: Syntax.Literal = { type: "Literal", value: 1 },
            oneE: JSyntax.Literal = { type: "Literal", value: 1 };
      if (expr.prefix) {
        if (expr.operator == "++") {
          return assignUpdate(to, "+", one);
        }
        return assignUpdate(to, "-", one);
      } else {
        if (expr.operator == "++") {
          return {
            type: "SequenceExpression",
            expressions: [
              assignUpdate(to, "+", one),
              { type: "BinaryExpression", operator: "-", left: to, right: oneE }
            ]
          };
        };
        return {
          type: "SequenceExpression",
          expressions: [
            assignUpdate(to, "-", one),
            { type: "BinaryExpression", operator: "+", left: to, right: oneE }
          ]
        };
      }
    }
    case "LogicalExpression":
      return {
        type: "LogicalExpression",
        operator: expr.operator == "||" ? "||" : "&&",
        left: expressionAsJavaScript(expr.left),
        right: expressionAsJavaScript(expr.right)
      };
    case "ConditionalExpression":
      return {
        type: "ConditionalExpression",
        test: expressionAsJavaScript(expr.test),
        consequent: expressionAsJavaScript(expr.consequent),
        alternate: expressionAsJavaScript(expr.alternate)
      };
    case "CallExpression":
      if (expr.callee.type == "Identifier" &&
          expr.callee.name == "old" &&
          expr.arguments.length == 1 &&
          expr.arguments[0].type == "Identifier") {
        return {
          type: "OldIdentifier",
          id: { type: "Identifier", name: (<Syntax.Identifier>expr.arguments[0]).name,
                refs: [], isWrittenTo: false, decl: { type: "Unresolved" } }
        };
      }
      return {
        type: "CallExpression",
        callee: expressionAsJavaScript(expr.callee),
        arguments: expr.arguments.map(expressionAsJavaScript)
      };
    case "Identifier":
      if (expr.name == "undefined") {
        return { type: "Literal", value: undefined };
      }
      return { type: "Identifier", name: expr.name, refs: [],
               isWrittenTo: false, decl: { type: "Unresolved" } };
    case "Literal":
      if (expr.value instanceof RegExp) throw new Error("regular expressions not supported");
      return {
        type: "Literal",
        value: expr.value
      };
    default:
      throw new Error("unsupported");
  }
}

function isWrittenTo(decl: JSyntax.Declaration): boolean {
  return decl.type == "Var" && decl.decl.kind == "let";
}

export function declName(decl: JSyntax.Declaration): string {
  if (decl.type == "Unresolved") throw new Error("Unresolved variable");
  return decl.type == "Param" ? decl.decl.name : decl.decl.id.name;
}

class Scope {
  func: JSyntax.FunctionDeclaration | null;
  ids: { [varname: string]: JSyntax.Declaration } = {};
  parent: Scope | null;
  constructor(parent: Scope | null = null, fn: JSyntax.FunctionDeclaration | null = null) {
    this.parent = parent;
    this.func = fn;
  }

  lookupDef(sym: string) {
    if (sym in this.ids) throw new Error(`${sym} already defined`);
    if (this.parent) this.parent.lookupDef(sym);
  }

  defSymbol(sym: JSyntax.Identifier, decl: JSyntax.Declaration) {
    // TODO enable shadowing
    this.lookupDef(sym.name);
    this.ids[sym.name] = decl;
  }

  lookupUse(sym: string): JSyntax.Declaration {
    if (sym in this.ids) return this.ids[sym];
    if (this.parent) {
      const decl = this.parent.lookupUse(sym);
      if (this.func && !this.func.freeVars.includes(decl) && isWrittenTo(decl)) {
        this.func.freeVars.push(decl); // a free variable
      }
      return decl;
    }
    throw new Error("undefined variable " + sym);
  }

  useSymbol(sym: JSyntax.Identifier, write: boolean = false) {
    const decl = this.lookupUse(sym.name);
    sym.decl = decl;
    switch (decl.type) {
      case "Var":
        decl.decl.id.refs.push(sym);
        if (write) {
          if (decl.decl.kind == "const") {
            throw new Error("assignment to const");
          }
          decl.decl.id.isWrittenTo = true;
        }
        break;
      case "Func":
        decl.decl.id.refs.push(sym);
        if (write) {
          throw new Error("assignment to function declaration");
        }
        break;
      case "Param":
        decl.decl.refs.push(sym);
        if (write) {
          throw new Error("assignment to function parameter");
        }
        break;
    }
  }
}

function resolveProgram(prog: JSyntax.Program) {
  const root: Scope = new Scope();
  prog.body.forEach(stmt => resolveStament(root, stmt));
  prog.invariants.forEach(inv => resolveExpression(root, inv));
}

function resolveStament(scope: Scope, stmt: JSyntax.Statement) {
  switch (stmt.type) {
    case "VariableDeclaration":
      scope.defSymbol(stmt.id, { type: "Var", decl: stmt });
      resolveExpression(scope, stmt.init);
      break;
    case "BlockStatement":
      const blockScope = new Scope(scope);
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
      const thenScope = new Scope(scope);
      stmt.consequent.body.forEach(s => resolveStament(thenScope, s));
      const elseScope = new Scope(scope);
      stmt.alternate.body.forEach(s => resolveStament(elseScope, s));
      break;
    case "ReturnStatement":
      resolveExpression(scope, stmt.argument);
      break;
    case "WhileStatement":
      resolveExpression(scope, stmt.test);
      const loopScope = new Scope(scope);
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

function resolveExpression(scope: Scope, expr: JSyntax.Expression, allowOld: boolean = false) {
  switch (expr.type) {
    case "Identifier":
      scope.useSymbol(expr);
      break;
    case "OldIdentifier":
      if (!allowOld) throw new Error("old() is only allows in function post conditions");
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
      expr.arguments.forEach(e => resolveExpression(scope, e, allowOld));
      resolveExpression(scope, expr.callee);
      break;
    // case "FunctionExpression":
    //   const funScope = new Scope(scope);
    //   expr.params.forEach(p => funScope.defSymbol(p, { type: "Param", func: expr, decl: p }));
    //   expr.body.forEach(s => resolveStament(funScope, s));
    //   break;
  }
}

export function stringifyExpr(expr: JSyntax.Expression): string {
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
      return `${stringifyExpr(expr.callee)}(${expr.arguments.map(stringifyExpr).join(', ')})`;
    // case "FunctionExpression":
    //   throw new Error("not implemented yet");
  }
}

export function stringifyStmt(stmt: JSyntax.Statement, indent: number = 0): string {
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

function callMatchesParams(expr: JSyntax.CallExpression, f: JSyntax.FunctionDeclaration): boolean {
  if (expr.arguments.length != f.params.length) return false;
  for (let i = 0; i < expr.arguments.length; i++) {
    const arg: JSyntax.Expression = expr.arguments[i];
    if (arg.type != "Identifier" ||
        arg.decl.type != "Param" ||
        arg.decl.func != f ||
        arg.decl.decl != f.params[i]) {
     return false;
    }
  }
  return true;
}

export function replaceFunctionResult(f: JSyntax.FunctionDeclaration, expr: JSyntax.Expression): JSyntax.Expression {
  switch (expr.type) {
    case "Identifier":
    case "OldIdentifier":
    case "Literal":
      return expr;
    case "ArrayExpression":
      return { type: "ArrayExpression", elements: expr.elements.map(e => replaceFunctionResult(f, e)) };
    case "UnaryExpression":
      return { type: "UnaryExpression", operator: expr.operator, argument: replaceFunctionResult(f, expr.argument)};
    case "BinaryExpression":
      return {
        type: "BinaryExpression",
        operator: expr.operator,
        left: replaceFunctionResult(f, expr.left),
        right: replaceFunctionResult(f, expr.right)
      };
    case "LogicalExpression":
      return {
        type: "LogicalExpression",
        operator: expr.operator,
        left: replaceFunctionResult(f, expr.left),
        right: replaceFunctionResult(f, expr.right)
      };
    case "ConditionalExpression":
      return {
        type: "ConditionalExpression",
        test: replaceFunctionResult(f, expr.test),
        consequent: replaceFunctionResult(f, expr.consequent),
        alternate: replaceFunctionResult(f, expr.alternate)
      };
    case "AssignmentExpression":
      return {
        type: "AssignmentExpression",
        left: expr.left, 
        right: replaceFunctionResult(f, expr.right)
      };
    case "SequenceExpression":
      return { type: "SequenceExpression", expressions: expr.expressions.map(e => replaceFunctionResult(f, e)) };
    case "CallExpression":
      if (expr.callee.type == "Identifier" &&
          expr.callee.decl.type == "Func" &&
          expr.callee.decl.decl == f &&
          callMatchesParams(expr, f)) {
        return { type: "Identifier", name: "_res_", decl: { type: "Unresolved" }, refs: [], isWrittenTo: false };
      }
      return {
        type: "CallExpression",
        callee: replaceFunctionResult(f, expr.callee),
        arguments: expr.arguments.map(e => replaceFunctionResult(f, e))
      }
    // case "FunctionExpression":
    //   throw new Error("not implemented yet"); 
  }
}

export function checkInvariants(whl: JSyntax.WhileStatement): JSyntax.FunctionDeclaration {
  return {
    type: "FunctionDeclaration",
    id: { type: "Identifier", name: "test", decl: {type: "Unresolved"}, refs: [], isWrittenTo: false},
    params: [],
    requires: [],
    ensures: [],
    body: { type: "BlockStatement", body:
      whl.invariants.map((inv): JSyntax.Statement => ({ type: "AssertStatement", expression: inv })).concat(whl.body.body)},
    freeVars: []
  }
}

export function checkPreconditions(f: JSyntax.FunctionDeclaration): JSyntax.FunctionDeclaration {
  return {
    type: "FunctionDeclaration",
    id: f.id,
    params: f.params,
    requires: f.requires,
    ensures: f.ensures,
    body: {
      type: "BlockStatement",
      body: f.requires.map((r): JSyntax.Statement =>
        ({ type: "AssertStatement", expression: r })).concat(f.body.body)
    },
    freeVars: f.freeVars
  };
}