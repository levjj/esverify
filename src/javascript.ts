import * as JSyntax from 'estree';
import { MessageException, unexpected } from './message';
import { options } from './options';
import { flatMap } from './util';

export namespace Syntax {
  /* tslint:disable:ter-indent */

  export type Declaration = { type: 'Unresolved' }
                          | { type: 'Var', decl: VariableDeclaration }
                          | { type: 'Func', decl: Function }
                          | { type: 'SpecArg', decl: SpecExpression, argIdx: number }
                          | { type: 'EveryArg', decl: EveryExpression }
                          | { type: 'EveryIdxArg', decl: EveryExpression }
                          | { type: 'PostArg', decl: PostCondition }
                          | { type: 'Param', func: Function; decl: Identifier }
                          | { type: 'This', decl: ClassDeclaration }
                          | { type: 'Class', decl: ClassDeclaration };

  export interface Position { line: number; column: number; }
  export interface SourceLocation { file: string; start: Position; end: Position; }

  export type ClassName = string;

  export interface Identifier { type: 'Identifier'; name: string;
                                decl: Declaration; refs: Array<Identifier>; isWrittenTo: boolean;
                                loc: SourceLocation; }
  export interface OldIdentifier { type: 'OldIdentifier'; id: Identifier; loc: SourceLocation; }
  export interface Literal { type: 'Literal';
                             value: undefined | null | boolean | number | string;
                             loc: SourceLocation; }
  export type UnaryOperator = '-' | '+' | '!' | '~' | 'typeof' | 'void';
  export interface UnaryExpression { type: 'UnaryExpression';
                                     operator: UnaryOperator;
                                     argument: Expression;
                                     loc: SourceLocation; }
  export type BinaryOperator = '===' | '!==' | '<' | '<=' | '>' | '>='
                             | '<<' | '>>' | '>>>' | '+' | '-' | '*' | '/' | '%'
                             | '|' | '^' | '&';
  export interface BinaryExpression { type: 'BinaryExpression';
                                      operator: BinaryOperator;
                                      left: Expression;
                                      right: Expression;
                                      loc: SourceLocation; }
  export type LogicalOperator = '||' | '&&';
  export interface LogicalExpression { type: 'LogicalExpression';
                                       operator: LogicalOperator;
                                       left: Expression;
                                       right: Expression;
                                       loc: SourceLocation; }
  export interface ConditionalExpression { type: 'ConditionalExpression';
                                           test: Expression;
                                           consequent: Expression;
                                           alternate: Expression;
                                           loc: SourceLocation; }
  export interface AssignmentExpression { type: 'AssignmentExpression';
                                          left: Expression;
                                          right: Expression;
                                          loc: SourceLocation; }
  export interface SequenceExpression { type: 'SequenceExpression';
                                        expressions: Expression[];
                                        loc: SourceLocation; }
  export interface CallExpression { type: 'CallExpression';
                                    callee: Expression;
                                    args: Array<Expression>;
                                    loc: SourceLocation; }
  export interface PureExpression { type: 'PureExpression';
                                    loc: SourceLocation; }
  export interface SpecExpression { type: 'SpecExpression';
                                    callee: Expression;
                                    args: Array<string>;
                                    pre: PreCondition;
                                    post: PostCondition;
                                    loc: SourceLocation; }
  export interface EveryExpression { type: 'EveryExpression';
                                     array: Expression;
                                     argument: Identifier;
                                     indexArgument: Identifier | null;
                                     expression: Expression;
                                     loc: SourceLocation; }
  export interface NewExpression { type: 'NewExpression';
                                   callee: Identifier;
                                   args: Array<Expression>;
                                   loc: SourceLocation; }
  export interface ArrayExpression { type: 'ArrayExpression';
                                     elements: Array<Expression>;
                                     loc: SourceLocation; }
  export interface ObjectExpression { type: 'ObjectExpression';
                                      properties: Array<{key: string, value: Expression}>;
                                      loc: SourceLocation; }
  export interface InstanceOfExpression { type: 'InstanceOfExpression';
                                          left: Expression;
                                          right: Identifier;
                                          loc: SourceLocation; }
  export interface InExpression { type: 'InExpression';
                                  property: Expression;
                                  object: Expression;
                                  loc: SourceLocation; }
  export interface MemberExpression { type: 'MemberExpression';
                                      object: Expression;
                                      property: Expression;
                                      loc: SourceLocation; }
  export type PreCondition = Expression;
  export interface PostCondition { argument: Identifier | null;
                                   expression: Expression;
                                   loc: SourceLocation; }
  export interface FunctionExpression { type: 'FunctionExpression';
                                        id: Identifier | null;
                                        params: Array<Identifier>;
                                        requires: Array<PreCondition>;
                                        ensures: Array<PostCondition>;
                                        body: BlockStatement;
                                        freeVars: Array<string>;
                                        loc: SourceLocation; }
  export type Expression = Identifier
                         | OldIdentifier
                         | Literal
                         | UnaryExpression
                         | BinaryExpression
                         | LogicalExpression
                         | ConditionalExpression
                         | AssignmentExpression
                         | SequenceExpression
                         | CallExpression
                         | SpecExpression
                         | EveryExpression
                         | PureExpression
                         | NewExpression
                         | ArrayExpression
                         | ObjectExpression
                         | InstanceOfExpression
                         | InExpression
                         | MemberExpression
                         | FunctionExpression;
  export interface VariableDeclaration { type: 'VariableDeclaration';
                                         id: Identifier;
                                         init: Expression;
                                         kind: 'let' | 'const';
                                         loc: SourceLocation; }
  export interface BlockStatement { type: 'BlockStatement';
                                    body: Statement[];
                                    loc: SourceLocation; }
  export interface ExpressionStatement { type: 'ExpressionStatement';
                                         expression: Expression;
                                         loc: SourceLocation; }
  export interface AssertStatement { type: 'AssertStatement';
                                     expression: Expression;
                                     loc: SourceLocation; }
  export interface IfStatement { type: 'IfStatement';
                                 test: Expression;
                                 consequent: BlockStatement;
                                 alternate: BlockStatement;
                                 loc: SourceLocation; }
  export interface ReturnStatement { type: 'ReturnStatement';
                                     argument: Expression;
                                     loc: SourceLocation; }
  export interface WhileStatement { type: 'WhileStatement';
                                    invariants: Array<Expression>;
                                    test: Expression;
                                    body: BlockStatement;
                                    loc: SourceLocation; }
  export interface DebuggerStatement { type: 'DebuggerStatement';
                                       loc: SourceLocation; }
  export interface FunctionDeclaration { type: 'FunctionDeclaration';
                                         id: Identifier;
                                         params: Array<Identifier>;
                                         requires: Array<PreCondition>;
                                         ensures: Array<PostCondition>;
                                         body: BlockStatement;
                                         freeVars: Array<string>;
                                         loc: SourceLocation; }
  export interface ClassDeclaration { type: 'ClassDeclaration';
                                      id: Identifier;
                                      fields: Array<string>;
                                      invariant: Expression;
                                      loc: SourceLocation; }

  export type Statement = VariableDeclaration
                        | BlockStatement
                        | ExpressionStatement
                        | AssertStatement
                        | IfStatement
                        | ReturnStatement
                        | WhileStatement
                        | DebuggerStatement
                        | FunctionDeclaration
                        | ClassDeclaration;

  export type Function = FunctionExpression | FunctionDeclaration;

  export type Program = { body: Array<Statement>,
                          invariants: Array<Expression> };
}

function unsupported (node: JSyntax.Node, description: string = 'unsupported syntax'): MessageException {
  return new MessageException({
    status: 'error',
    type: 'unsupported',
    loc: loc(node),
    description
  });
}

function findPseudoCalls (type: string, stmts: Array<JSyntax.Statement>): Array<JSyntax.Expression> {
  return flatMap(stmts, stmt => {
    if (stmt.type === 'ExpressionStatement' &&
        stmt.expression.type === 'CallExpression' &&
        stmt.expression.callee.type === 'Identifier' &&
        stmt.expression.callee.name === type) {
      if (stmt.expression.arguments.length !== 1) {
        throw unsupported(stmt.expression, `${type} expects proposition as one single argument`);
      }
      const arg = stmt.expression.arguments[0];
      if (arg.type === 'SpreadElement') throw unsupported(arg);
      return [arg];
    }
    return [];
  });
}

function findPreConditions (stmts: Array<JSyntax.Statement>): Array<Syntax.PreCondition> {
  return findPseudoCalls('requires', stmts).map(expressionAsJavaScript);
}

function findInvariants (stmts: Array<JSyntax.Statement>): Array<Syntax.Expression> {
  return findPseudoCalls('invariant', stmts).map(expressionAsJavaScript);
}

function findPostConditions (stmts: Array<JSyntax.Statement>): Array<Syntax.PostCondition> {
  return findPseudoCalls('ensures', stmts).map(expr => {
    if (expr.type === 'ArrowFunctionExpression' && expr.params.length === 1) {
      if (expr.async || expr.generator) throw unsupported(expr);
      if (expr.body.type === 'BlockStatement') throw unsupported(expr);
      const argument = patternAsIdentifier(expr.params[0]);
      return { argument, expression: expressionAsJavaScript(expr.body), loc: loc(expr) };
    }
    return { argument: null, expression: expressionAsJavaScript(expr), loc: loc(expr) };
  });
}

function withoutPseudoCalls (type: string, stmts: Array<JSyntax.Statement>): Array<JSyntax.Statement> {
  return flatMap(stmts, stmt => {
    if (stmt.type === 'ExpressionStatement' &&
        stmt.expression.type === 'CallExpression' &&
        stmt.expression.callee.type === 'Identifier' &&
        stmt.expression.callee.name === type &&
        stmt.expression.arguments.length === 1) {
      return [];
    }
    return [stmt];
  });
}

export function nullLoc (): Syntax.SourceLocation {
  return { file: options.filename, start: { line: 0, column: 0 }, end: { line: 0, column: 0 } };
}

function loc (n: JSyntax.Node): Syntax.SourceLocation {
  if (!n.loc) {
    throw new MessageException(unexpected(new Error('No location information available on nodes')));
  }
  return { file: options.filename, start: n.loc.start, end: n.loc.end };
}

export function id (name: string, loc: Syntax.SourceLocation = nullLoc(), isWrittenTo: boolean = false):
                Syntax.Identifier {
  return {
    type: 'Identifier',
    name,
    refs: [],
    decl: { type: 'Unresolved' },
    isWrittenTo,
    loc
  };
}

function patternAsIdentifier (node: JSyntax.Pattern): Syntax.Identifier {
  if (node.type !== 'Identifier') throw unsupported(node);
  return id(node.name, loc(node));
}

function unaryOp (unop: JSyntax.UnaryExpression): Syntax.UnaryOperator {
  switch (unop.operator) {
    case '-':
    case '+':
    case '!':
    case '~':
    case 'typeof':
    case 'void':
      return unop.operator;
    default:
      throw unsupported(unop);
  }
}

function binaryOp (binop: JSyntax.BinaryExpression): Syntax.BinaryOperator {
  switch (binop.operator) {
    case '===':
    case '!==':
    case '<':
    case '<=':
    case '>':
    case '>=':
    case '<<':
    case '>>':
    case '>>>':
    case '+':
    case '-':
    case '*':
    case '/':
    case '%':
    case '|':
    case '^':
    case '&':
      return binop.operator;
    default:
      throw unsupported(binop);
  }
}

function checkDistinct (params: Array<JSyntax.Pattern>): void {
  for (let i = 0; i < params.length - 1; i++) {
    const pi = params[i];
    if (pi.type !== 'Identifier') throw unsupported(pi);
    for (let j = i + 1; j < params.length; j++) {
      const pj = params[j];
      if (pj.type !== 'Identifier') throw unsupported(pj);
      if (pi.name === pj.name) throw unsupported(pi, 'params must be distinct');
    }
  }
}

function assignUpdate (left: Syntax.Identifier, op: Syntax.BinaryOperator, right: JSyntax.Expression,
                       stmt: JSyntax.Expression): Syntax.AssignmentExpression {
  return {
    type: 'AssignmentExpression',
    left,
    right: {
      type: 'BinaryExpression',
      left,
      operator: op,
      right: expressionAsJavaScript(right),
      loc: loc(stmt)
    },
    loc: loc(stmt)
  };
}

function returnExpr (expr: JSyntax.Expression): Array<JSyntax.Statement> {
  return [{
    type: 'ReturnStatement',
    argument: expr,
    loc: expr.loc
  }];
}

function literalAsIdentifier (literal: JSyntax.Literal): Syntax.Identifier {
  if (literal.value !== null && literal.value !== undefined &&
      typeof literal.value !== 'string' && typeof literal.value !== 'number' &&
      typeof literal.value !== 'boolean') {
    throw unsupported(literal);
  }
  return id(String(literal.value), loc(literal));
}

function expressionAsJavaScript (expr: JSyntax.Expression): Syntax.Expression {
  switch (expr.type) {
    case 'Identifier':
      if (expr.name === 'undefined') {
        return { type: 'Literal', value: undefined, loc: loc(expr) };
      }
      return id(expr.name, loc(expr));
    case 'Literal':
      if (expr.value instanceof RegExp) throw unsupported(expr);
      return {
        type: 'Literal',
        value: expr.value,
        loc: loc(expr)
      };
    case 'ThisExpression':
      return id('this', loc(expr));
    case 'SequenceExpression':
      return {
        type: 'SequenceExpression',
        expressions: expr.expressions.map(expressionAsJavaScript),
        loc: loc(expr)
      };
    case 'UnaryExpression':
      return {
        type: 'UnaryExpression',
        operator: unaryOp(expr),
        argument: expressionAsJavaScript(expr.argument),
        loc: loc(expr)
      };
    case 'BinaryExpression': {
      if (expr.operator === 'instanceof') {
        if (expr.right.type !== 'Identifier') {
          throw unsupported(expr, 'instance check only works for class names');
        }
        return {
          type: 'InstanceOfExpression',
          left: expressionAsJavaScript(expr.left),
          right: patternAsIdentifier(expr.right),
          loc: loc(expr)
        };
      }
      if (expr.operator === 'in') {
        return {
          type: 'InExpression',
          property: expressionAsJavaScript(expr.left),
          object: expressionAsJavaScript(expr.right),
          loc: loc(expr)
        };
      }
      return {
        type: 'BinaryExpression',
        operator: binaryOp(expr),
        left: expressionAsJavaScript(expr.left),
        right: expressionAsJavaScript(expr.right),
        loc: loc(expr)
      };
    }
    case 'AssignmentExpression':
      if (expr.left.type !== 'Identifier') throw unsupported(expr.left);
      const to = id(expr.left.name, loc(expr), true);
      switch (expr.operator) {
        case '=':
          return {
            type: 'AssignmentExpression',
            left: to,
            right: expressionAsJavaScript(expr.right),
            loc: loc(expr)
          };
        case '+=': return assignUpdate(to, '+', expr.right, expr);
        case '-=': return assignUpdate(to, '-', expr.right, expr);
        case '*=': return assignUpdate(to, '*', expr.right, expr);
        case '/=': return assignUpdate(to, '/', expr.right, expr);
        case '%=': return assignUpdate(to, '%', expr.right, expr);
        case '<<=': return assignUpdate(to, '<<', expr.right, expr);
        case '>>=': return assignUpdate(to, '>>', expr.right, expr);
        case '>>>=': return assignUpdate(to, '>>>', expr.right, expr);
        case '|=': return assignUpdate(to, '|', expr.right, expr);
        case '^=': return assignUpdate(to, '^', expr.right, expr);
        case '&=': return assignUpdate(to, '&', expr.right, expr);
        default: throw unsupported(expr);
      }
    case 'UpdateExpression': {
      if (expr.argument.type !== 'Identifier') throw unsupported(expr.argument);
      const to = id(expr.argument.name, loc(expr.argument), true);
      const one: JSyntax.SimpleLiteral = { type: 'Literal', value: 1, raw: '1', loc: loc(expr) };
      const oneE: Syntax.Literal = { type: 'Literal', value: 1, loc: loc(expr) };
      if (expr.prefix) {
        if (expr.operator === '++') {
          return assignUpdate(to, '+', one, expr);
        }
        return assignUpdate(to, '-', one, expr);
      } else {
        if (expr.operator === '++') {
          return {
            type: 'SequenceExpression',
            expressions: [
              assignUpdate(to, '+', one, expr),
              { type: 'BinaryExpression', operator: '-', left: to, right: oneE, loc: loc(expr) }
            ],
            loc: loc(expr)
          };
        }
        return {
          type: 'SequenceExpression',
          expressions: [
            assignUpdate(to, '-', one, expr),
            { type: 'BinaryExpression', operator: '+', left: to, right: oneE, loc: loc(expr) }
          ],
          loc: loc(expr)
        };
      }
    }
    case 'LogicalExpression':
      return {
        type: 'LogicalExpression',
        operator: expr.operator === '||' ? '||' : '&&',
        left: expressionAsJavaScript(expr.left),
        right: expressionAsJavaScript(expr.right),
        loc: loc(expr)
      };
    case 'ConditionalExpression':
      return {
        type: 'ConditionalExpression',
        test: expressionAsJavaScript(expr.test),
        consequent: expressionAsJavaScript(expr.consequent),
        alternate: expressionAsJavaScript(expr.alternate),
        loc: loc(expr)
      };
    case 'CallExpression':
      if (expr.callee.type === 'Identifier' &&
          expr.callee.name === 'pure') {
        if (expr.arguments.length !== 0) throw unsupported(expr, 'pure modifier has no arguments');
        return { type: 'PureExpression', loc: loc(expr) };
      }
      if (expr.callee.type === 'Identifier' &&
          expr.callee.name === 'old') {
        if (expr.arguments.length !== 1) {
          throw unsupported(expr, 'old modifier has exactly one argument');
        }
        const arg = expr.arguments[0];
        if (arg.type !== 'Identifier') {
          throw unsupported(expr, 'old modifier only supported for identifiers');
        }
        return {
          type: 'OldIdentifier',
          id: id(arg.name, loc(expr.arguments[0])),
          loc: loc(expr)
        };
      }
      if (expr.callee.type === 'Identifier' &&
          expr.callee.name === 'spec') {
        if (expr.arguments.length !== 3) {
          throw unsupported(expr, 'spec(f,req,ens) has three arguments');
        }
        const [callee, arg1, arg2] = expr.arguments;
        if (callee.type === 'SpreadElement') {
          throw unsupported(callee);
        }
        if (arg1.type !== 'ArrowFunctionExpression') {
          throw unsupported(arg1, 'spec(f, req, ens) requires req to be an arrow function');
        }
        if (arg2.type !== 'ArrowFunctionExpression') {
          throw unsupported(arg2, 'spec(f, req, ens) requires ens to be an arrow function');
        }
        const r: JSyntax.ArrowFunctionExpression = arg1;
        const s: JSyntax.ArrowFunctionExpression = arg2;
        if (r.body.type === 'BlockStatement') {
          throw unsupported(r, 'spec(f, req, ens) requires req to be an arrow function with an expression as body');
        }
        if (s.body.type === 'BlockStatement') {
          throw unsupported(s, 'spec(f, req, ens) requires ens to be an arrow function with an expression as body');
        }
        if (r.params.length < s.params.length - 1 ||
            r.params.length > s.params.length ||
            !r.params.every((p, idx) => {
              const otherP = s.params[idx];
              return p.type === 'Identifier' && otherP.type === 'Identifier' && p.name === otherP.name;
            })) {
          throw unsupported(expr, 'spec(f, req, ens) requires req and ens to have same parameters');
        }
        let argument: Syntax.Identifier | null = null;
        if (s.params.length > r.params.length) {
          argument = patternAsIdentifier(s.params[s.params.length - 1]);
        }
        return {
          type: 'SpecExpression',
          callee: expressionAsJavaScript(callee),
          args: r.params.map(p => (p as JSyntax.Identifier).name),
          pre: expressionAsJavaScript(r.body),
          post: { argument, expression: expressionAsJavaScript(s.body), loc: loc(s) },
          loc: loc(expr)
        };
      }
      if (expr.callee.type === 'Identifier' &&
          expr.callee.name === 'every') {
        if (expr.arguments.length !== 2) {
          throw unsupported(expr, 'every(arr, inv) has two arguments');
        }
        const [callee, arg] = expr.arguments;
        if (callee.type === 'SpreadElement') {
          throw unsupported(callee);
        }
        if (arg.type !== 'ArrowFunctionExpression') {
          throw unsupported(arg, 'every(arr, inv) requires inv to be an arrow function');
        }
        const inv: JSyntax.ArrowFunctionExpression = arg;
        if (inv.body.type === 'BlockStatement') {
          throw unsupported(inv, 'every(arr, inv) requires inv to be an arrow function with an expression as body');
        }
        if (inv.params.length < 1 || inv.params.length > 2 || inv.params.some((p, idx) => p.type !== 'Identifier')) {
          throw unsupported(arg, 'every(arr, inv) requires inv to have one or two parameters');
        }
        return {
          type: 'EveryExpression',
          array: expressionAsJavaScript(callee),
          argument: patternAsIdentifier(inv.params[0]),
          indexArgument: inv.params.length > 1 ? patternAsIdentifier(inv.params[1]) : null,
          expression: expressionAsJavaScript(inv.body),
          loc: loc(expr)
        };
      }
      if (expr.callee.type === 'Super') throw unsupported(expr.callee);
      if (expr.arguments.length > 9) throw unsupported(expr, 'more than 9 arguments not supported yet');
      return {
        type: 'CallExpression',
        callee: expressionAsJavaScript(expr.callee),
        args: expr.arguments.map(expr => {
          if (expr.type === 'SpreadElement') {
            throw unsupported(expr);
          } else {
            return expressionAsJavaScript(expr);
          }
        }),
        loc: loc(expr)
      };
    case 'NewExpression':
      if (expr.callee.type !== 'Identifier') throw unsupported(expr.callee);
      if (expr.arguments.length > 9) throw unsupported(expr, 'more than 9 arguments not supported yet');
      return {
        type: 'NewExpression',
        callee: patternAsIdentifier(expr.callee),
        args: expr.arguments.map(expr => {
          if (expr.type === 'SpreadElement') {
            throw unsupported(expr);
          } else {
            return expressionAsJavaScript(expr);
          }
        }),
        loc: loc(expr)
      };
    case 'ArrayExpression':
      return {
        type: 'ArrayExpression',
        elements: expr.elements.map(expr => {
          if (expr.type === 'SpreadElement') {
            throw unsupported(expr);
          } else {
            return expressionAsJavaScript(expr);
          }
        }),
        loc: loc(expr)
      };
    case 'ObjectExpression': {
      const properties = expr.properties.map(property => {
        if (property.kind !== 'init') throw unsupported(property, 'getters and setters not supported');
        if (property.value.type === 'ObjectPattern' ||
            property.value.type === 'ArrayPattern' ||
            property.value.type === 'AssignmentPattern' ||
            property.value.type === 'RestElement') {
          throw unsupported(property.value);
        }
        if (property.key.type === 'Identifier') {
          return {
            key: patternAsIdentifier(property.key).name,
            value: expressionAsJavaScript(property.value)
          };
        } else if (property.key.type === 'Literal') {
          return {
            key: literalAsIdentifier(property.key).name,
            value: expressionAsJavaScript(property.value)
          };
        } else {
          throw unsupported(property.key);
        }
      });
      properties.forEach((property, index) => {
        const duplicateIndex = properties.findIndex(otherProperty => property.key === otherProperty.key);
        if (duplicateIndex < index) throw unsupported(expr, 'duplicate key in object literal');
      });
      return { type: 'ObjectExpression', properties, loc: loc(expr) };
    }
    case 'MemberExpression':
      if (expr.object.type === 'Super') throw unsupported(expr.object);
      let property: Syntax.Expression;
      if (expr.computed) {
        property = expressionAsJavaScript(expr.property);
      } else {
        if (expr.property.type !== 'Identifier') throw unsupported(expr.property);
        property = { type: 'Literal', value: expr.property.name, loc: loc(expr.property) };
      }
      return {
        type: 'MemberExpression',
        object: expressionAsJavaScript(expr.object),
        property,
        loc: loc(expr)
      };
    case 'FunctionExpression':
    case 'ArrowFunctionExpression':
      const body = expr.body.type === 'BlockStatement' ? expr.body.body : returnExpr(expr.body);
      if (expr.generator) throw unsupported(expr, 'generators not supported');
      if (expr.async) throw unsupported(expr, 'async not supported');
      checkDistinct(expr.params);
      const params: Array<Syntax.Identifier> = expr.params.map(patternAsIdentifier);
      const fe: Syntax.FunctionExpression = {
        type: 'FunctionExpression',
        id: (expr.type === 'FunctionExpression' && expr.id) ? id(expr.id.name, loc(expr.id)) : null,
        params,
        requires: findPreConditions(body),
        ensures: findPostConditions(body),
        body: {
          type: 'BlockStatement',
          body: flatMap(withoutPseudoCalls('requires',
                        withoutPseudoCalls('ensures', body)), statementAsJavaScript),
          loc: loc(expr.body)
        },
        freeVars: [],
        loc: loc(expr)
      };
      if (fe.id) fe.id.decl = { type: 'Func', decl: fe };
      return fe;

    default:
      throw unsupported(expr);
  }
}

function statementAsJavaScript (stmt: JSyntax.Statement): Array<Syntax.Statement> {
  function assert (cond: boolean) { if (!cond) throw unsupported(stmt); }
  switch (stmt.type) {
    case 'EmptyStatement':
      return [];
    case 'VariableDeclaration':
      assert(stmt.kind === 'let' || stmt.kind === 'const');
      return stmt.declarations.map(decl => {
        assert(decl.id.type === 'Identifier');
        const d: Syntax.VariableDeclaration = {
          type: 'VariableDeclaration',
          kind: stmt.kind === 'let' ? 'let' : 'const',
          id: patternAsIdentifier(decl.id),
          init: decl.init ? expressionAsJavaScript(decl.init) : { type: 'Literal', value: undefined, loc: loc(stmt) },
          loc: loc(stmt)
        };
        return d;
      });
    case 'BlockStatement':
      return [{
        type: 'BlockStatement',
        body: flatMap(stmt.body, statementAsJavaScript),
        loc: loc(stmt)
      }];
    case 'ExpressionStatement':
      if (stmt.expression.type === 'CallExpression' &&
          stmt.expression.callee.type === 'Identifier' &&
          stmt.expression.callee.name === 'assert' &&
          stmt.expression.arguments.length === 1) {
        const arg = stmt.expression.arguments[0];
        if (arg.type !== 'SpreadElement') {
          return [{ type: 'AssertStatement', expression: expressionAsJavaScript(arg), loc: loc(stmt) }];
        }
      }
      return [{ type: 'ExpressionStatement', expression: expressionAsJavaScript(stmt.expression), loc: loc(stmt) }];
    case 'IfStatement':
      return [{
        type: 'IfStatement',
        test: expressionAsJavaScript(stmt.test),
        consequent: {
          type: 'BlockStatement',
          body: stmt.consequent.type === 'BlockStatement'
                ? flatMap(stmt.consequent.body, statementAsJavaScript)
                : statementAsJavaScript(stmt.consequent),
          loc: loc(stmt.consequent)
        },
        alternate: {
          type: 'BlockStatement',
          body: stmt.alternate ? (stmt.alternate.type === 'BlockStatement'
                ? flatMap(stmt.alternate.body, statementAsJavaScript)
                : statementAsJavaScript(stmt.alternate)) : [],
          loc: loc(stmt.alternate || stmt)
        },
        loc: loc(stmt)
      }];
    case 'WhileStatement':
      const stmts: Array<JSyntax.Statement> = stmt.body.type === 'BlockStatement' ? stmt.body.body : [stmt];
      return [{
        type: 'WhileStatement',
        invariants: findInvariants(stmts),
        test: expressionAsJavaScript(stmt.test),
        body: {
          type: 'BlockStatement',
          body: flatMap(withoutPseudoCalls('invariant', stmts), statementAsJavaScript),
          loc: loc(stmt.body)
        },
        loc: loc(stmt)
      }];
    case 'DebuggerStatement':
      return [{ type: 'DebuggerStatement', loc: loc(stmt) }];
    case 'ReturnStatement':
      return [{
        type: 'ReturnStatement',
        argument: stmt.argument ? expressionAsJavaScript(stmt.argument)
                                : { type: 'Literal', value: undefined, loc: loc(stmt) },
        loc: loc(stmt)
      }];
    case 'FunctionDeclaration': {
      const stmtBody: JSyntax.BlockStatement | JSyntax.Expression = stmt.body;
      const body = stmtBody.type === 'BlockStatement' ? stmtBody.body : returnExpr(stmtBody);
      if (stmt.generator) throw unsupported(stmt, 'generators not supported');
      if (stmt.async) throw unsupported(stmt, 'async not supported');
      checkDistinct(stmt.params);
      const params: Array<Syntax.Identifier> = stmt.params.map(patternAsIdentifier);
      const fd: Syntax.FunctionDeclaration = {
        type: 'FunctionDeclaration',
        id: id(stmt.id.name, loc(stmt.id)),
        params,
        requires: findPreConditions(body),
        ensures: findPostConditions(body),
        body: {
          type: 'BlockStatement',
          body: flatMap(withoutPseudoCalls('requires',
                        withoutPseudoCalls('ensures', body)), statementAsJavaScript),
          loc: loc(stmt.body)
        },
        freeVars: [],
        loc: loc(stmt)
      };
      fd.id.decl = { type: 'Func', decl: fd };
      return [fd];
    }
    case 'ClassDeclaration': {
      if (stmt.superClass) throw unsupported(stmt, 'inheritance not supported');
      if (stmt.body.body.length > 2) {
        throw unsupported(stmt, 'at most one constructor and invariant supported');
      }
      let [m1, m2] = stmt.body.body;
      if (!m2) {
        m2 = {
          type: 'MethodDefinition',
          key: { 'type': 'Identifier', 'name': 'invariant' },
          computed: false,
          value: {
            type: 'FunctionExpression',
            id: null,
            params: [],
            body: {
              type: 'BlockStatement',
              body: [{
                type: 'ReturnStatement',
                argument: { type: 'Literal', value: true, raw: 'true', loc: stmt.loc }
              }],
              loc: stmt.loc
            },
            generator: false,
            loc: stmt.loc
          },
          kind: 'method',
          static: false,
          loc: stmt.loc
        };
      }
      if (!m1 || m1.kind !== 'constructor' && m2.kind !== 'constructor') {
        throw unsupported(stmt, 'class needs one constructor');
      }
      if (m1.kind === 'constructor' && m2.kind === 'constructor') {
        throw unsupported(stmt, 'class can have at most one constructor');
      }
      if (m1.kind === 'get' || m1.kind === 'set') {
        throw unsupported(m1, 'getters and setters not supported');
      }
      if (m1.static) throw unsupported(m1, 'static not supported');
      if (m2.static) throw unsupported(m2, 'static not supported');
      if (m2.kind === 'get' || m2.kind === 'set') {
        throw unsupported(m2, 'getters and setters not supported');
      }
      if (m1.key.type !== 'Identifier') {
        throw unsupported(m1.key, 'key needs to be identifier');
      }
      if (m2.key.type !== 'Identifier') {
        throw unsupported(m2.key, 'key needs to be identifier');
      }

      const constr: JSyntax.Function = m1.kind === 'constructor' ? m1.value : m2.value;
      if (constr === m1.value && m1.key.name !== 'constructor') {
        throw unsupported(m1, "constructor needs to be named 'constructor'");
      }
      if (constr === m2.value && m2.key.name !== 'constructor') {
        throw unsupported(m2, "constructor needs to be named 'constructor'");
      }

      if (constr.generator || constr.async) throw unsupported(constr);

      if (constr.params.length > 9) throw unsupported(constr, 'more than 9 arguments not supported yet');
      if (constr.params.length !== constr.body.body.length) {
        throw unsupported(constr, 'constructor should assign each param to a field');
      }
      checkDistinct(constr.params);
      const params: Array<Syntax.Identifier> = constr.params.map(patternAsIdentifier);
      for (let i = 0; i < params.length; i++) {
        const asg = constr.body.body[i];
        if (asg.type !== 'ExpressionStatement' ||
            asg.expression.type !== 'AssignmentExpression' ||
            asg.expression.left.type !== 'MemberExpression' ||
            asg.expression.left.computed ||
            asg.expression.left.object.type !== 'ThisExpression' ||
            asg.expression.left.property.type !== 'Identifier' ||
            asg.expression.left.property.name !== params[i].name ||
            asg.expression.operator !== '=' ||
            asg.expression.right.type !== 'Identifier' ||
            asg.expression.right.name !== params[i].name) {
          throw unsupported(asg, 'constructor should assign each param to a field');
        }
      }
      if (constr === m1.value && m2.key.name !== 'invariant') {
        throw unsupported(m2, 'no methods other than invariant supported');
      }
      if (constr === m2.value && m1.key.name !== 'invariant') {
        throw unsupported(m1, 'no methods other than invariant supported');
      }

      const inv: JSyntax.Function = m1.kind === 'constructor' ? m2.value : m1.value;
      if (inv.params.length > 0) {
        throw unsupported(inv, 'invariant cannot have parameters');
      }
      if (inv.generator || inv.async) throw unsupported(constr);
      if (inv.body.body.length !== 1) {
        throw unsupported(inv.body, 'invariant needs to be single expression statement');
      }
      const invStmt = inv.body.body[0];
      if (invStmt.type !== 'ReturnStatement' || !invStmt.argument) {
        throw unsupported(inv.body, 'invariant needs to be a single return statement with an expression');
      }
      return [{
        type: 'ClassDeclaration',
        id: patternAsIdentifier(stmt.id),
        fields: params.map(p => p.name),
        invariant: expressionAsJavaScript(invStmt.argument),
        loc: loc(stmt)
      }];
    }
    default:
      throw unsupported(stmt);
  }
}

export abstract class Visitor<E,S> {

  abstract visitIdentifier (expr: Syntax.Identifier): E;
  abstract visitOldIdentifier (expr: Syntax.OldIdentifier): E;
  abstract visitLiteral (expr: Syntax.Literal): E;
  abstract visitUnaryExpression (expr: Syntax.UnaryExpression): E;
  abstract visitBinaryExpression (expr: Syntax.BinaryExpression): E;
  abstract visitLogicalExpression (expr: Syntax.LogicalExpression): E;
  abstract visitConditionalExpression (expr: Syntax.ConditionalExpression): E;
  abstract visitAssignmentExpression (expr: Syntax.AssignmentExpression): E;
  abstract visitSequenceExpression (expr: Syntax.SequenceExpression): E;
  abstract visitCallExpression (expr: Syntax.CallExpression): E;
  abstract visitPureExpression (expr: Syntax.PureExpression): E;
  abstract visitSpecExpression (expr: Syntax.SpecExpression): E;
  abstract visitEveryExpression (expr: Syntax.EveryExpression): E;
  abstract visitNewExpression (expr: Syntax.NewExpression): E;
  abstract visitArrayExpression (expr: Syntax.ArrayExpression): E;
  abstract visitObjectExpression (expr: Syntax.ObjectExpression): E;
  abstract visitInstanceOfExpression (expr: Syntax.InstanceOfExpression): E;
  abstract visitInExpression (expr: Syntax.InExpression): E;
  abstract visitMemberExpression (expr: Syntax.MemberExpression): E;
  abstract visitFunctionExpression (expr: Syntax.FunctionExpression): E;

  visitExpression (expr: Syntax.Expression): E {
    switch (expr.type) {
      case 'Identifier': return this.visitIdentifier(expr);
      case 'OldIdentifier': return this.visitOldIdentifier(expr);
      case 'Literal': return this.visitLiteral(expr);
      case 'UnaryExpression': return this.visitUnaryExpression(expr);
      case 'BinaryExpression': return this.visitBinaryExpression(expr);
      case 'LogicalExpression': return this.visitLogicalExpression(expr);
      case 'ConditionalExpression': return this.visitConditionalExpression(expr);
      case 'AssignmentExpression': return this.visitAssignmentExpression(expr);
      case 'SequenceExpression': return this.visitSequenceExpression(expr);
      case 'CallExpression': return this.visitCallExpression(expr);
      case 'SpecExpression': return this.visitSpecExpression(expr);
      case 'EveryExpression': return this.visitEveryExpression(expr);
      case 'PureExpression': return this.visitPureExpression(expr);
      case 'NewExpression': return this.visitNewExpression(expr);
      case 'ArrayExpression': return this.visitArrayExpression(expr);
      case 'ObjectExpression': return this.visitObjectExpression(expr);
      case 'InstanceOfExpression': return this.visitInstanceOfExpression(expr);
      case 'InExpression': return this.visitInExpression(expr);
      case 'MemberExpression': return this.visitMemberExpression(expr);
      case 'FunctionExpression': return this.visitFunctionExpression(expr);
    }
  }

  abstract visitVariableDeclaration (stmt: Syntax.VariableDeclaration): S;
  abstract visitBlockStatement (stmt: Syntax.BlockStatement): S;
  abstract visitExpressionStatement (stmt: Syntax.ExpressionStatement): S;
  abstract visitAssertStatement (stmt: Syntax.AssertStatement): S;
  abstract visitIfStatement (stmt: Syntax.IfStatement): S;
  abstract visitReturnStatement (stmt: Syntax.ReturnStatement): S;
  abstract visitWhileStatement (stmt: Syntax.WhileStatement): S;
  abstract visitDebuggerStatement (stmt: Syntax.DebuggerStatement): S;
  abstract visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration): S;
  abstract visitClassDeclaration (stmt: Syntax.ClassDeclaration): S;

  visitStatement (stmt: Syntax.Statement): S {
    switch (stmt.type) {
      case 'VariableDeclaration': return this.visitVariableDeclaration(stmt);
      case 'BlockStatement': return this.visitBlockStatement(stmt);
      case 'ExpressionStatement': return this.visitExpressionStatement(stmt);
      case 'AssertStatement': return this.visitAssertStatement(stmt);
      case 'IfStatement': return this.visitIfStatement(stmt);
      case 'ReturnStatement': return this.visitReturnStatement(stmt);
      case 'WhileStatement': return this.visitWhileStatement(stmt);
      case 'DebuggerStatement': return this.visitDebuggerStatement(stmt);
      case 'FunctionDeclaration': return this.visitFunctionDeclaration(stmt);
      case 'ClassDeclaration': return this.visitClassDeclaration(stmt);
    }
  }

  abstract visitProgram (prog: Syntax.Program): S;

}

function unsupportedLoc (loc: Syntax.SourceLocation, description: string = '') {
  return new MessageException({ status: 'error', type: 'unsupported', loc, description });
}

function undefinedId (loc: Syntax.SourceLocation) {
  return new MessageException({ status: 'error', type: 'undefined-identifier', loc, description: '' });
}

function alreadyDefined (loc: Syntax.SourceLocation, decl: Syntax.Declaration) {
  if (decl.type === 'Unresolved') {
    throw unexpected(new Error('decl should be resolved'));
  }
  const { file, start } = decl.decl.loc;
  return new MessageException({ status: 'error', type: 'already-defined', loc,
                                description: `at ${file}:${start.line}:${start.column}` });
}

function assignToConst (loc: Syntax.SourceLocation) {
  return new MessageException({ status: 'error', type: 'assignment-to-const', loc, description: '' });
}

function refInInvariant (loc: Syntax.SourceLocation) {
  return new MessageException({ status: 'error', type: 'reference-in-invariant', loc, description: '' });
}

function isWrittenTo (decl: Syntax.Declaration): boolean {
  return decl.type === 'Var' && decl.decl.kind === 'let';
}

class Scope {
  func: Syntax.Function | null;
  ids: { [varname: string]: Syntax.Declaration } = {};
  parent: Scope | null;
  constructor (parent: Scope | null = null, fn: Syntax.Function | null = null) {
    this.parent = parent;
    this.func = fn;
  }

  lookupDef (sym: Syntax.Identifier) {
    if (sym.name in this.ids) throw alreadyDefined(sym.loc, this.ids[sym.name]);
    if (this.parent) this.parent.lookupDef(sym);
  }

  defSymbol (sym: Syntax.Identifier, decl: Syntax.Declaration) {
    // TODO enable shadowing
    this.lookupDef(sym);
    this.ids[sym.name] = decl;
  }

  lookupUse (sym: Syntax.Identifier, clz: boolean): Syntax.Declaration {
    let decl: Syntax.Declaration | null = null;
    if (sym.name in this.ids) {
      decl = this.ids[sym.name];
    } else if (this.parent) {
      decl = this.parent.lookupUse(sym, clz);
      if (this.func && !this.func.freeVars.includes(sym.name) && isWrittenTo(decl)) {
        this.func.freeVars.push(sym.name); // a free variable
      }
    }
    if (!decl || decl.type === 'Unresolved') {
      throw undefinedId(sym.loc);
    }
    if (clz && (decl.type !== 'Class')) throw unsupportedLoc(sym.loc, 'expected class');
    if (!clz && (decl.type === 'Class')) throw unsupportedLoc(sym.loc, 'did not expect class');
    return decl;
  }

  useSymbol (sym: Syntax.Identifier, write: boolean = false, clz: boolean = false, allowRef: boolean = true) {
    const decl = this.lookupUse(sym, clz);
    sym.decl = decl;
    switch (decl.type) {
      case 'Var':
        decl.decl.id.refs.push(sym);
        if (!allowRef) {
          throw refInInvariant(sym.loc);
        }
        if (write) {
          if (decl.decl.kind === 'const') {
            throw assignToConst(sym.loc);
          }
          decl.decl.id.isWrittenTo = true;
        }
        break;
      case 'Func':
        if (!decl.decl.id) throw unsupportedLoc(sym.loc, 'function should have name');
        decl.decl.id.refs.push(sym);
        if (write) {
          throw assignToConst(sym.loc);
        }
        break;
      case 'Param':
        decl.decl.refs.push(sym);
        if (write) {
          throw assignToConst(sym.loc);
        }
        break;
      case 'Class':
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
  allowRef: boolean = true;

  scoped (action: () => void, allowsOld: boolean = this.allowOld, allowsRef: boolean = this.allowRef,
          fn: null | Syntax.Function = this.scope.func) {
    const { scope, allowOld, allowRef } = this;
    try {
      this.scope = new Scope(scope, fn);
      this.allowOld = allowsOld;
      this.allowRef = allowsRef;
      action();
    } finally {
      this.scope = scope;
      this.allowOld = allowOld;
      this.allowRef = allowRef;
    }
  }

  visitIdentifier (expr: Syntax.Identifier) {
    this.scope.useSymbol(expr, false, false, this.allowRef);
  }

  visitOldIdentifier (expr: Syntax.OldIdentifier) {
    if (!this.allowOld) throw unsupportedLoc(expr.loc, 'old() not allowed in this context');
    this.scope.useSymbol(expr.id);
  }

  visitLiteral (expr: Syntax.Literal) { /* empty */ }

  visitUnaryExpression (expr: Syntax.UnaryExpression) {
    this.visitExpression(expr.argument);
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression) {
    this.visitExpression(expr.left);
    this.visitExpression(expr.right);
  }

  visitLogicalExpression (expr: Syntax.LogicalExpression) {
    this.visitExpression(expr.left);
    this.visitExpression(expr.right);
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression) {
    this.visitExpression(expr.test);
    this.visitExpression(expr.consequent);
    this.visitExpression(expr.alternate);
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression) {
    this.visitExpression(expr.right);
    if (expr.left.type !== 'Identifier') throw unsupportedLoc(expr.loc);
    this.scope.useSymbol(expr.left, true);
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression) {
    expr.expressions.forEach(e => this.visitExpression(e));
  }

  visitCallExpression (expr: Syntax.CallExpression) {
    expr.args.forEach(e => this.visitExpression(e));
    this.visitExpression(expr.callee);
  }

  visitPostCondition (expr: Syntax.PostCondition) {
    if (expr.argument) {
      this.scope.defSymbol(expr.argument, { type: 'PostArg', decl: expr });
    }
    this.visitExpression(expr.expression);
  }

  visitSpecExpression (expr: Syntax.SpecExpression) {
    this.visitExpression(expr.callee);
    this.scoped(() => {
      expr.args.forEach((a, argIdx) => {
        this.scope.defSymbol(id(a), { type: 'SpecArg', decl: expr, argIdx });
      });
      this.visitExpression(expr.pre);
    }, false);
    this.scoped(() => {
      expr.args.forEach((a, argIdx) => {
        this.scope.defSymbol(id(a), { type: 'SpecArg', decl: expr, argIdx });
      });
      this.visitPostCondition(expr.post);
    }, true);
  }

  visitEveryExpression (expr: Syntax.EveryExpression) {
    this.visitExpression(expr.array);
    this.scoped(() => {
      this.scope.defSymbol(expr.argument, { type: 'EveryArg', decl: expr });
      if (expr.indexArgument !== null) {
        this.scope.defSymbol(expr.indexArgument, { type: 'EveryIdxArg', decl: expr });
      }
      this.visitExpression(expr.expression);
    }, false);
  }

  visitPureExpression (expr: Syntax.PureExpression) { /* empty */ }

  visitNewExpression (expr: Syntax.NewExpression) {
    this.scope.useSymbol(expr.callee, false, true);
    expr.args.forEach(e => this.visitExpression(e));
  }

  visitArrayExpression (expr: Syntax.ArrayExpression) {
    expr.elements.forEach(e => this.visitExpression(e));
  }

  visitObjectExpression (expr: Syntax.ObjectExpression) {
    expr.properties.forEach(p => this.visitExpression(p.value));
  }

  visitInstanceOfExpression (expr: Syntax.InstanceOfExpression) {
    this.visitExpression(expr.left);
    this.scope.useSymbol(expr.right, false, true);
  }

  visitInExpression (expr: Syntax.InExpression) {
    this.visitExpression(expr.property);
    this.visitExpression(expr.object);
  }

  visitMemberExpression (expr: Syntax.MemberExpression) {
    this.visitExpression(expr.object);
    this.visitExpression(expr.property);
  }

  visitFunctionExpression (expr: Syntax.FunctionExpression) {
    this.scoped(() => {
      if (expr.id) this.scope.defSymbol(expr.id, { type: 'Func', decl: expr });
      expr.params.forEach(p => this.scope.defSymbol(p, { type: 'Param', func: expr, decl: p }));
      expr.requires.forEach(r => this.visitExpression(r));
      expr.ensures.forEach(s => {
        this.scoped(() => this.visitPostCondition(s), true);
      });
      expr.body.body.forEach(s => this.visitStatement(s));
    }, false, this.allowRef, expr);
  }

  visitVariableDeclaration (stmt: Syntax.VariableDeclaration) {
    this.scope.defSymbol(stmt.id, { type: 'Var', decl: stmt });
    this.visitExpression(stmt.init);
  }

  visitBlockStatement (stmt: Syntax.BlockStatement) {
    this.scoped(() => {
      stmt.body.forEach(s => this.visitStatement(s));
    });
  }

  visitExpressionStatement (stmt: Syntax.ExpressionStatement) {
    this.visitExpression(stmt.expression);
  }

  visitAssertStatement (stmt: Syntax.AssertStatement) {
    this.visitExpression(stmt.expression);
  }

  visitIfStatement (stmt: Syntax.IfStatement) {
    this.visitExpression(stmt.test);
    this.scoped(() => {
      stmt.consequent.body.forEach(s => this.visitStatement(s));
    });
    this.scoped(() => {
      stmt.alternate.body.forEach(s => this.visitStatement(s));
    });
  }

  visitReturnStatement (stmt: Syntax.ReturnStatement) {
    this.visitExpression(stmt.argument);
  }

  visitWhileStatement (stmt: Syntax.WhileStatement) {
    this.visitExpression(stmt.test);
    this.scoped(() => {
      stmt.invariants.forEach(i => this.visitExpression(i));
      stmt.body.body.forEach(s => this.visitStatement(s));
    });
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement) { /* empty */ }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration) {
    this.scope.defSymbol(stmt.id, { type: 'Func', decl: stmt });
    this.scoped(() => {
      stmt.params.forEach(p => this.scope.defSymbol(p, { type: 'Param', func: stmt, decl: p }));
      stmt.requires.forEach(r => this.visitExpression(r));
      stmt.ensures.forEach(s => {
        this.scoped(() => this.visitPostCondition(s), true);
      });
      stmt.body.body.forEach(s => this.visitStatement(s));
    }, false, true, stmt);
  }

  visitClassDeclaration (stmt: Syntax.ClassDeclaration) {
    this.scope.defSymbol(stmt.id, { type: 'Class', decl: stmt });
    this.scoped(() => {
      this.scope.defSymbol(id('this'), { type: 'This', decl: stmt });
      this.visitExpression(stmt.invariant);
    }, false, false);
  }

  builtinClass (name: string) {
    const decl: Syntax.ClassDeclaration = {
      type: 'ClassDeclaration',
      id: id(name),
      fields: [],
      invariant: { type: 'Literal', value: true, loc: nullLoc() },
      loc: nullLoc()
    };
    this.scope.defSymbol(decl.id, { type: 'Class', decl });
  }

  visitProgram (prog: Syntax.Program) {
    this.builtinClass('Object');
    this.builtinClass('Function');
    this.builtinClass('Array');
    prog.body.forEach(stmt => this.visitStatement(stmt));
    prog.invariants.forEach(inv => this.visitExpression(inv));
  }
}

export function programAsJavaScript (program: JSyntax.Program): Syntax.Program {
  let stmts: Array<JSyntax.Statement> = [];
  for (const s of program.body) {
    if (s.type === 'ImportDeclaration' ||
        s.type === 'ExportAllDeclaration' ||
        s.type === 'ExportNamedDeclaration' ||
        s.type === 'ExportDefaultDeclaration' ||
        s.type === 'ReturnStatement') {
      throw unsupported(s);
    }
    stmts.push(s);
  }
  const body = flatMap(withoutPseudoCalls('invariant', stmts), statementAsJavaScript);
  const prog: Syntax.Program = {
    body,
    invariants: findInvariants(stmts)
  };
  const resolver = new NameResolver();
  resolver.visitProgram(prog);
  return prog;
}

export function isMutable (id: Syntax.Identifier): boolean {
  if (id.decl.type === 'Unresolved') throw undefinedId(id.loc);
  return isWrittenTo(id.decl);
}

class Stringifier extends Visitor<string,string> {

  depth: number = 0;

  visitIdentifier (expr: Syntax.Identifier): string {
    return expr.name;
  }

  visitOldIdentifier (expr: Syntax.OldIdentifier): string {
    return `old(${expr.id.name})`;
  }

  visitLiteral (expr: Syntax.Literal): string {
    return expr.value === undefined ? 'undefined' : JSON.stringify(expr.value);
  }

  visitUnaryExpression (expr: Syntax.UnaryExpression): string {
    switch (expr.operator) {
      case 'typeof':
      case 'void':
        return `${expr.operator}(${this.visitExpression(expr.argument)})`;
      default:
        return `${expr.operator}${this.visitExpression(expr.argument)}`;
    }
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): string {
    return `(${this.visitExpression(expr.left)} ${expr.operator} ${this.visitExpression(expr.right)})`;
  }

  visitLogicalExpression (expr: Syntax.LogicalExpression): string {
    return `${this.visitExpression(expr.left)} ${expr.operator} ${this.visitExpression(expr.right)}`;
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): string {
    return `${this.visitExpression(expr.test)} ? ${this.visitExpression(expr.consequent)} ` +
                                              `: ${this.visitExpression(expr.alternate)}`;
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression): string {
    return `${this.visitExpression(expr.left)} = ${this.visitExpression(expr.right)}`;
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression): string {
    return `${expr.expressions.map(e => this.visitExpression(e)).join(', ')}`;
  }

  visitCallExpression (expr: Syntax.CallExpression): string {
    return `${this.visitExpression(expr.callee)}(${expr.args.map(a => this.visitExpression(a)).join(', ')})`;
  }

  visitPostCondition (expr: Syntax.PostCondition): string {
    if (expr.argument) {
      return `${this.visitExpression(expr.argument)} => ${this.visitExpression(expr.expression)}`;
    }
    return this.visitExpression(expr.expression);
  }

  visitSpecExpression (expr: Syntax.SpecExpression): string {
    if (expr.post.argument) {
      return `spec(${this.visitExpression(expr.callee)}, ` +
                  `(${expr.args.join(', ')}) => (${this.visitExpression(expr.pre)}), ` +
                  `(${[...expr.args, expr.post.argument.name].join(', ')}) => ` +
                     `(${this.visitExpression(expr.post.expression)}))`;
    }
    return `spec(${this.visitExpression(expr.callee)}, ` +
                `(${expr.args.join(', ')}) => (${this.visitExpression(expr.pre)}), ` +
                `(${expr.args.join(', ')}) => (${this.visitExpression(expr.post.expression)}))`;
  }

  visitEveryExpression (expr: Syntax.EveryExpression): string {
    if (expr.indexArgument !== null) {
      return `every(${this.visitExpression(expr.array)}, ` +
                   `(${expr.argument.name}, ${expr.indexArgument.name}) => (${this.visitExpression(expr.expression)}))`;
    } else {
      return `every(${this.visitExpression(expr.array)}, ` +
                   `${expr.argument.name} => (${this.visitExpression(expr.expression)}))`;
    }
  }

  visitPureExpression (expr: Syntax.PureExpression): string {
    return `pure()`;
  }

  visitNewExpression (expr: Syntax.NewExpression): string {
    return `new ${expr.callee.name}(${expr.args.map(a => this.visitExpression(a)).join(', ')})`;
  }

  visitArrayExpression (expr: Syntax.ArrayExpression): string {
    return `[${expr.elements.map(a => this.visitExpression(a)).join(', ')}]`;
  }

  visitObjectExpression (expr: Syntax.ObjectExpression): string {
    function nameToKey (name: string): string {
      return /^\w+$/.test(name) ? name : `"${name}"`;
    }
    return `{ ${
      expr.properties.map(({ key, value }) => `${nameToKey(key)}: ${this.visitExpression(value)}`).join(', ')} }`;
  }

  visitInstanceOfExpression (expr: Syntax.InstanceOfExpression): string {
    return `(${this.visitExpression(expr.left)} instanceof ${expr.right.name})`;
  }

  visitInExpression (expr: Syntax.InExpression): string {
    return `(${this.visitExpression(expr.property)} in ${this.visitExpression(expr.object)})`;
  }

  visitMemberExpression (expr: Syntax.MemberExpression): string {
    if (expr.property.type === 'Literal' &&
        typeof expr.property.value === 'string' &&
        /^[a-zA-Z_]+$/.test(expr.property.value)) {
      return `${this.visitExpression(expr.object)}.${expr.property.value}`;
    } else {
      return `${this.visitExpression(expr.object)}[${this.visitExpression(expr.property)}]`;
    }
  }

  visitFunctionExpression (expr: Syntax.FunctionExpression): string {
    if (expr.id === null && expr.body.body.length === 1 && expr.body.body[0].type === 'ReturnStatement') {
      const retStmt = expr.body.body[0] as Syntax.ReturnStatement;
      if (expr.params.length === 1) {
        return `${expr.params[0].name} => ${this.visitExpression(retStmt.argument)}`;
      } else {
        return `(${expr.params.map(p => p.name).join(', ')}) => ${this.visitExpression(retStmt.argument)}`;
      }
    }
    return `(function ${expr.id ? expr.id.name + ' ' : ''}(${expr.params.map(p => p.name).join(', ')}) ` +
            `${this.visitStatements(expr.body.body)})`;
  }

  indent (f: () => void) {
    this.depth++;
    try {
      f();
    } finally {
      this.depth--;
    }
  }

  i (s: string): string {
    let d = '';
    for (let i = 0; i < this.depth; i++) d += '  ';
    return d + s;
  }

  visitVariableDeclaration (stmt: Syntax.VariableDeclaration): string {
    return this.i(`${stmt.kind} ${stmt.id.name} = ${this.visitExpression(stmt.init)};\n`);
  }

  visitStatements (stmts: Array<Syntax.Statement>): string {
    let res = '{\n';
    this.indent(() => {
      for (const s of stmts) {
        res += this.visitStatement(s);
      }
    });
    return res + this.i('}');
  }

  visitBlockStatement (stmt: Syntax.BlockStatement): string {
    return this.i(this.visitStatements(stmt.body)) + '\n';
  }

  visitExpressionStatement (stmt: Syntax.ExpressionStatement): string {
    return this.i(`${this.visitExpression(stmt.expression)};\n`);
  }

  visitAssertStatement (stmt: Syntax.AssertStatement): string {
    return this.i(`assert(${this.visitExpression(stmt.expression)});\n`);
  }

  visitIfStatement (stmt: Syntax.IfStatement): string {
    if (stmt.alternate.body.length === 0) {
      return this.i(`if (${this.visitExpression(stmt.test)}) ` +
                    `${this.visitStatements(stmt.consequent.body)}\n`);
    } else {
      return this.i(`if (${this.visitExpression(stmt.test)}) ` +
                    `${this.visitStatements(stmt.consequent.body)} else ` +
                    `${this.visitStatements(stmt.alternate.body)}\n`);
    }
  }

  visitReturnStatement (stmt: Syntax.ReturnStatement): string {
    return this.i(`return ${this.visitExpression(stmt.argument)};\n`);
  }

  visitWhileStatement (stmt: Syntax.WhileStatement): string {
    return this.i(`while (${this.visitExpression(stmt.test)}) ${this.visitStatements(stmt.body.body)}\n`);
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement): string {
    return this.i(`debugger;\n`);
  }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration): string {
    return this.i(`function ${stmt.id.name} (${stmt.params.map(p => p.name).join(', ')}) ` +
                  `${this.visitStatements(stmt.body.body)}\n`);
  }

  visitClassDeclaration (stmt: Syntax.ClassDeclaration): string {
    let res = this.i(`class ${stmt.id.name} {\n`);
    this.depth++;
    res += this.i(`constructor(${stmt.fields.join(', ')}) {\n`);
    this.depth++;
    for (const f of stmt.fields) {
      res += this.i(`this.${f} = ${f};\n`);
    }
    res += this.i(`assert(this.invariant());\n`);
    this.depth--;
    res += this.i(`}\n`);
    res += this.i(`invariant(${stmt.fields.join(', ')}) {\n`);
    this.depth++;
    res += this.i(`return ${this.visitExpression(stmt.invariant)};\n`);
    this.depth--;
    res += this.i(`}\n`);
    this.depth--;
    res += this.i(`}\n`);
    return res;
  }

  visitProgram (prog: Syntax.Program) {
    return prog.body.map(s => this.visitStatement(s)).join('');
  }
}

export function stringifyExpr (expr: Syntax.Expression): string {
  return (new Stringifier()).visitExpression(expr);
}

export function stringifyStmt (stmt: Syntax.Statement): string {
  return (new Stringifier()).visitStatement(stmt);
}

export class Substituter extends Visitor<Syntax.Expression, Syntax.Statement> {

  theta: { [vname: string]: string | Syntax.Expression } = {};

  replaceVar (orig: string, expr: string | Syntax.Expression): Substituter {
    this.theta[orig] = expr;
    return this;
  }

  withoutBindings<A> (cont: () => A, ...bindings: Array<string>): A {
    const origTheta = Object.assign({}, this.theta);
    try {
      bindings.forEach(b => { delete this.theta[b]; });
      return cont();
    } finally {
      this.theta = origTheta;
    }
  }

  visitIdentifier (expr: Syntax.Identifier): Syntax.Expression {
    if (!(expr.name in this.theta)) return expr;
    const e: string | Syntax.Expression = this.theta[expr.name];
    if (typeof(e) !== 'string') return e;
    return {
      type: 'Identifier',
      name: e,
      decl: expr.decl,
      isWrittenTo: false,
      refs: [],
      loc: expr.loc
    };
  }

  visitOldIdentifier (expr: Syntax.OldIdentifier): Syntax.Expression {
    return expr;
  }

  visitLiteral (expr: Syntax.Literal): Syntax.Expression {
    return expr;
  }

  visitPureExpression (expr: Syntax.PureExpression): Syntax.Expression {
    return expr;
  }

  visitUnaryExpression (expr: Syntax.UnaryExpression): Syntax.Expression {
    return {
      type: 'UnaryExpression',
      operator: expr.operator,
      argument: this.visitExpression(expr.argument),
      loc: expr.loc
    };
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): Syntax.Expression {
    return {
      type: 'BinaryExpression',
      operator: expr.operator,
      left: this.visitExpression(expr.left),
      right: this.visitExpression(expr.right),
      loc: expr.loc
    };
  }

  visitLogicalExpression (expr: Syntax.LogicalExpression): Syntax.Expression {
    return {
      type: 'LogicalExpression',
      operator: expr.operator,
      left: this.visitExpression(expr.left),
      right: this.visitExpression(expr.right),
      loc: expr.loc
    };
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): Syntax.Expression {
    return {
      type: 'ConditionalExpression',
      test: this.visitExpression(expr.test),
      consequent: this.visitExpression(expr.consequent),
      alternate: this.visitExpression(expr.alternate),
      loc: expr.loc
    };
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression): Syntax.Expression {
    return {
      type: 'AssignmentExpression',
      left: expr.left,
      right: this.visitExpression(expr.right),
      loc: expr.loc
    };
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression): Syntax.Expression {
    return {
      type: 'SequenceExpression',
      expressions: expr.expressions.map(e => this.visitExpression(e)),
      loc: expr.loc
    };
  }

  visitCallExpression (expr: Syntax.CallExpression): Syntax.Expression {
    return {
      type: 'CallExpression',
      callee: this.visitExpression(expr.callee),
      args: expr.args.map(e => this.visitExpression(e)),
      loc: expr.loc
    };
  }

  visitPostCondition (expr: Syntax.PostCondition): Syntax.PostCondition {
    const expression = expr.argument !== null
      ? this.withoutBindings(() => this.visitExpression(expr.expression), expr.argument.name)
      : this.visitExpression(expr.expression);
    return {
      argument: expr.argument,
      expression,
      loc: expr.loc
    };
  }

  visitSpecExpression (expr: Syntax.SpecExpression): Syntax.Expression {
    return {
      type: 'SpecExpression',
      callee: this.visitExpression(expr.callee),
      args: expr.args,
      pre: this.withoutBindings(() => this.visitExpression(expr.pre), ...expr.args),
      post: this.withoutBindings(() => this.visitPostCondition(expr.post), ...expr.args),
      loc: expr.loc
    };
  }

  visitEveryExpression (expr: Syntax.EveryExpression): Syntax.Expression {
    const array = this.visitExpression(expr.array);
    const expression = expr.indexArgument !== null
      ? this.withoutBindings(() => this.visitExpression(expr.expression), expr.argument.name, expr.indexArgument.name)
      : this.withoutBindings(() => this.visitExpression(expr.expression), expr.argument.name);
    return {
      type: 'EveryExpression',
      array,
      argument: expr.argument,
      indexArgument: expr.indexArgument,
      expression,
      loc: expr.loc
    };
  }

  visitNewExpression (expr: Syntax.NewExpression): Syntax.Expression {
    return {
      type: 'NewExpression',
      callee: expr.callee,
      args: expr.args.map(e => this.visitExpression(e)),
      loc: expr.loc
    };
  }

  visitArrayExpression (expr: Syntax.ArrayExpression): Syntax.Expression {
    return {
      type: 'ArrayExpression',
      elements: expr.elements.map(e => this.visitExpression(e)),
      loc: expr.loc
    };
  }

  visitObjectExpression (expr: Syntax.ObjectExpression): Syntax.Expression {
    return {
      type: 'ObjectExpression',
      properties: expr.properties.map(({ key, value }) => ({ key, value: this.visitExpression(value) })),
      loc: expr.loc
    };
  }

  visitInstanceOfExpression (expr: Syntax.InstanceOfExpression): Syntax.Expression {
    return {
      type: 'InstanceOfExpression',
      left: this.visitExpression(expr.left),
      right: expr.right,
      loc: expr.loc
    };
  }

  visitInExpression (expr: Syntax.InExpression): Syntax.Expression {
    return {
      type: 'InExpression',
      property: this.visitExpression(expr.property),
      object: this.visitExpression(expr.object),
      loc: expr.loc
    };
  }

  visitMemberExpression (expr: Syntax.MemberExpression): Syntax.Expression {
    return {
      type: 'MemberExpression',
      object: this.visitExpression(expr.object),
      property: this.visitExpression(expr.property),
      loc: expr.loc
    };
  }

  visitFunctionExpression (expr: Syntax.FunctionExpression): Syntax.Expression {
    const bindings = expr.id !== null
      ? [expr.id.name, ...expr.params.map(p => p.name)]
      : expr.params.map(p => p.name);
    return {
      type: 'FunctionExpression',
      id: expr.id,
      params: expr.params,
      requires: this.withoutBindings(() => expr.requires.map(r => this.visitExpression(r)), ...bindings),
      ensures: this.withoutBindings(() => expr.ensures.map(e => this.visitPostCondition(e)), ...bindings),
      body: this.withoutBindings(() => this.visitBlockStatement(expr.body), ...bindings),
      freeVars: expr.freeVars,
      loc: expr.loc
    };
  }

  visitVariableDeclaration (stmt: Syntax.VariableDeclaration): Syntax.Statement {
    delete this.theta[stmt.id.name]; // gets restored at end of next block or function
    return {
      type: 'VariableDeclaration',
      id: stmt.id,
      init: this.visitExpression(stmt.init),
      kind: stmt.kind,
      loc: stmt.loc
    };
  }

  visitBlockStatement (stmt: Syntax.BlockStatement): Syntax.BlockStatement {
    const origTheta = Object.assign({}, this.theta);
    try {
      return {
        type: 'BlockStatement',
        body: stmt.body.map(s => this.visitStatement(s)),
        loc: stmt.loc
      };
    } finally {
      this.theta = origTheta;
    }
  }

  visitExpressionStatement (stmt: Syntax.ExpressionStatement): Syntax.Statement {
    return {
      type: 'ExpressionStatement',
      expression: this.visitExpression(stmt.expression),
      loc: stmt.loc
    };
  }

  visitAssertStatement (stmt: Syntax.AssertStatement): Syntax.Statement {
    return {
      type: 'AssertStatement',
      expression: this.visitExpression(stmt.expression),
      loc: stmt.loc
    };
  }

  visitIfStatement (stmt: Syntax.IfStatement): Syntax.Statement {
    return {
      type: 'IfStatement',
      test: this.visitExpression(stmt.test),
      consequent: this.visitBlockStatement(stmt.consequent),
      alternate: this.visitBlockStatement(stmt.alternate),
      loc: stmt.loc
    };
  }

  visitReturnStatement (stmt: Syntax.ReturnStatement): Syntax.Statement {
    return {
      type: 'ReturnStatement',
      argument: this.visitExpression(stmt.argument),
      loc: stmt.loc
    };
  }

  visitWhileStatement (stmt: Syntax.WhileStatement): Syntax.Statement {
    return {
      type: 'WhileStatement',
      invariants: stmt.invariants.map(inv => this.visitExpression(inv)),
      test: this.visitExpression(stmt.test),
      body: this.visitBlockStatement(stmt.body),
      loc: stmt.loc
    };
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement): Syntax.Statement {
    return {
      type: 'DebuggerStatement',
      loc: stmt.loc
    };
  }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration): Syntax.Statement {
    delete this.theta[stmt.id.name]; // gets restored at end of next block or function
    const bindings = stmt.params.map(p => p.name);
    return {
      type: 'FunctionDeclaration',
      id: stmt.id,
      params: stmt.params,
      requires: this.withoutBindings(() => stmt.requires.map(r => this.visitExpression(r)), ...bindings),
      ensures: this.withoutBindings(() => stmt.ensures.map(e => this.visitPostCondition(e)), ...bindings),
      body: this.withoutBindings(() => this.visitBlockStatement(stmt.body), ...bindings),
      freeVars: stmt.freeVars,
      loc: stmt.loc
    };
  }

  visitClassDeclaration (stmt: Syntax.ClassDeclaration): Syntax.Statement {
    delete this.theta[stmt.id.name]; // gets restored at end of next block or function
    return {
      type: 'ClassDeclaration',
      id: stmt.id,
      fields: stmt.fields,
      invariant: this.visitExpression(stmt.invariant),
      loc: stmt.loc
    };
  }

  visitProgram (prog: Syntax.Program): Syntax.Statement {
    return {
      type: 'BlockStatement',
      body: prog.body.map(s => this.visitStatement(s)),
      loc: nullLoc()
    };
  }
}

export function replaceVar (v: string, subst: string | Syntax.Expression, expr: Syntax.Expression): Syntax.Expression {
  const sub = new Substituter();
  sub.replaceVar(v, subst);
  return sub.visitExpression(expr);
}

export function loopTestingCode (whl: Syntax.WhileStatement): Array<Syntax.Statement> {
  return [{
    type: 'FunctionDeclaration',
    id: id('test', whl.loc),
    params: [],
    requires: [],
    ensures: [],
    body: {
      type: 'BlockStatement',
      body: whl.invariants
      .map((inv): Syntax.Statement =>
        ({ type: 'AssertStatement', expression: inv, loc: inv.loc }))
      .concat(whl.body.body),
      loc: whl.loc
    },
    freeVars: [],
    loc: whl.loc
  },
  {
    type: 'ExpressionStatement',
    expression: {
      type: 'CallExpression',
      args: [],
      callee: id('test', whl.loc),
      loc: whl.loc
    },
    loc: whl.loc
  }];
}

export function checkPreconditions (f: Syntax.FunctionDeclaration): Syntax.FunctionDeclaration {
  return {
    type: 'FunctionDeclaration',
    id: f.id,
    params: f.params,
    requires: f.requires,
    ensures: f.ensures,
    body: {
      type: 'BlockStatement',
      body: f.requires
        .map((r): Syntax.Statement =>
          ({ type: 'AssertStatement', expression: r, loc: r.loc }))
        .concat(f.body.body),
      loc: f.loc
    },
    freeVars: f.freeVars,
    loc: f.loc
  };
}
