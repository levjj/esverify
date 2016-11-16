/// <reference path="../typings/mozilla-spidermonkey-parser-api.d.ts"/>
import { Syntax } from "spiderMonkeyParserAPI";

export namespace JSyntax {
  export interface Identifier { type: "Identifier"; name: string; }
  export interface OldIdentifier { type: "OldIdentifier"; name: string; }
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
  export interface FunctionExpression { type: "FunctionExpression";
                                        params: Array<Identifier>;
                                        body: Statement[]; }
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
                         | FunctionExpression;
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
                                 consequent: Statement[];
                                 alternate: Statement[]; }
  export interface ReturnStatement { type: "ReturnStatement";
                                     argument?: Expression; }
  export interface WhileStatement { type: "WhileStatement";
                                    invariants: Array<Expression>;
                                    test: Expression;
                                    body: Statement[]; }
  export interface DebuggerStatement { type: "DebuggerStatement"; }
       
  export type Statement = VariableDeclaration
                        | BlockStatement
                        | ExpressionStatement
                        | AssertStatement
                        | IfStatement
                        | ReturnStatement
                        | WhileStatement
                        | DebuggerStatement;

  export interface FunctionDeclaration { type: "FunctionDeclaration";
                                         id: Identifier;
                                         params: Array<Identifier>;
                                         requires: Array<Expression>;
                                         ensures: Array<Expression>;
                                         body: Statement[]; }
  export type TopLevel = VariableDeclaration
                       | BlockStatement
                       | ExpressionStatement
                       | AssertStatement
                       | IfStatement
                       | ReturnStatement
                       | WhileStatement
                       | DebuggerStatement
                       | FunctionDeclaration;

  export type Program = { body: Array<TopLevel>, invariants: Array<Expression> };
}

function flatMap<A,B>(a: Array<A>, f: (a: A) => Array<B>): Array<B> {
  return a.map(f).reduce((a,b) => a.concat(b));
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
  return node;
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
  return {
    body: flatMap(withoutPseudoCalls("invariant", program.body), topLevelAsJavaScript),
    invariants: findPseudoCalls("invariant", program.body)
  };
}

export function topLevelAsJavaScript(stmt: Syntax.Statement): Array<JSyntax.TopLevel> {
  switch (stmt.type) {
    case "FunctionDeclaration": {
      if (stmt.defaults.length > 0) throw new Error("defaults not supported");
      if (stmt.rest) throw new Error("Rest arguments not supported");
      if (stmt.body.type != "BlockStatement") throw new Error("unsupported");
      if (stmt.generator) throw new Error("generators not supported");
      return [{
        type: "FunctionDeclaration",
        id: stmt.id,
        params: stmt.params.map(patternAsIdentifier),
        requires: findPseudoCalls("requires", stmt.body.body),
        ensures: findPseudoCalls("ensures", stmt.body.body),
        body: flatMap(withoutPseudoCalls("requires",
                      withoutPseudoCalls("ensures", stmt.body.body)), statementAsJavaScript)
      }];
    }
    case "ExpressionStatement":
    case "EmptyStatement":
    case "VariableDeclaration":
    case "BlockStatement":
    case "IfStatement":
    case "WhileStatement":
    case "DebuggerStatement":
      return statementAsJavaScript(stmt);
    default:
      throw new Error("Not supported:\n" + JSON.stringify(stmt));
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
        consequent: stmt.consequent.type == "BlockStatement"
                ? flatMap(stmt.consequent.body, statementAsJavaScript)
                : statementAsJavaScript(stmt.consequent),
        alternate: stmt.alternate ? (stmt.alternate.type == "BlockStatement"
                ? flatMap(stmt.alternate.body, statementAsJavaScript)
                : statementAsJavaScript(stmt.alternate)) : []
      }];
    case "WhileStatement":
      const stmts: Array<Syntax.Statement> = stmt.body.type == "BlockStatement" ? stmt.body.body : [stmt];
      return [{
        type: "WhileStatement",
        invariants: findPseudoCalls("invariant", stmts),
        test: expressionAsJavaScript(stmt.test),
        body: flatMap(withoutPseudoCalls("invariant", stmts), statementAsJavaScript)
      }];
    case "DebuggerStatement":
      return [stmt];
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
      operator: "+",
      right: expressionAsJavaScript(right)
    }
  };
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
    case "FunctionExpression":
      if (expr.id) throw new Error("named function expressions not supported");
      if (expr.defaults.length > 0) throw new Error("defaults not supported");
      if (expr.rest) throw new Error("Rest arguments not supported");
      if (expr.body.type != "BlockStatement") throw new Error("unsupported");
      if (expr.generator) throw new Error("generators not supported");
      return {
        type: "FunctionExpression",
        params: expr.params.map(patternAsIdentifier),
        body: flatMap(expr.body.body, statementAsJavaScript)
      };
    case "ArrowExpression":
      if (expr.defaults.length > 0) throw new Error("defaults not supported");
      if (expr.rest) throw new Error("Rest arguments not supported");
      if (expr.body.type != "BlockStatement") throw new Error("unsupported");
      if (expr.generator) throw new Error("generators not supported");
      return {
        type: "FunctionExpression",
        params: expr.params.map(patternAsIdentifier),
        body: flatMap(expr.body.body, statementAsJavaScript)
      };
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
      switch (expr.operator) {
        case "=":
          return {
            type: "AssignmentExpression",
            left: expr.left,
            right: expressionAsJavaScript(expr.right)
          };
        case "+=": return assignUpdate(expr.left, "+", expr.right);
        case "-=": return assignUpdate(expr.left, "-", expr.right);
        case "*=": return assignUpdate(expr.left, "*", expr.right);
        case "/=": return assignUpdate(expr.left, "/", expr.right);
        case "%=": return assignUpdate(expr.left, "%", expr.right);
        case "<<=": return assignUpdate(expr.left, "<<", expr.right);
        case ">>=": return assignUpdate(expr.left, ">>", expr.right);
        case ">>>=": return assignUpdate(expr.left, ">>>", expr.right);
        case "|=": return assignUpdate(expr.left, "|", expr.right);
        case "^=": return assignUpdate(expr.left, "^", expr.right);
        case "&=": return assignUpdate(expr.left, "&", expr.right);
        default: throw new Error("unknown operator");
      }
    case "UpdateExpression":
      if (expr.argument.type != "Identifier") throw new Error("only identifiers can be assigned");
      const one: Syntax.Literal = { type: "Literal", value: 1 },
            oneE: JSyntax.Literal = { type: "Literal", value: 1 };
      if (expr.prefix) {
        if (expr.operator == "++") {
          return assignUpdate(expr.argument, "+", one);
        }
        return assignUpdate(expr.argument, "-", one);
      } else {
        if (expr.operator == "++") {
          return {
            type: "SequenceExpression",
            expressions: [
              assignUpdate(expr.argument, "+", one),
              { type: "BinaryExpression", operator: "-", left: expr.argument, right: oneE }
            ]
          };
        };
        return {
          type: "SequenceExpression",
          expressions: [
            assignUpdate(expr.argument, "-", one),
            { type: "BinaryExpression", operator: "+", left: expr.argument, right: oneE }
          ]
        };
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
        return { type: "OldIdentifier", name: (<Syntax.Identifier>expr.arguments[0]).name };
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
      return expr;
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
