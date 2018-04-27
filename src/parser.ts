import * as JSyntax from 'estree';
import { Syntax, id } from './javascript';
import { MessageException, unexpected } from './message';
import { options } from './options';
import { flatMap } from './util';

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

function findPreConditions (stmts: Array<JSyntax.Statement>): Array<Syntax.Assertion> {
  return findPseudoCalls('requires', stmts).map(expressionAsAssertion);
}

function findInvariants (stmts: Array<JSyntax.Statement>): Array<Syntax.Assertion> {
  return findPseudoCalls('invariant', stmts).map(expressionAsAssertion);
}

function findPostConditions (stmts: Array<JSyntax.Statement>): Array<Syntax.PostCondition> {
  return findPseudoCalls('ensures', stmts).map(expr => {
    if (expr.type === 'ArrowFunctionExpression' && expr.params.length === 1) {
      if (expr.async || expr.generator) throw unsupported(expr);
      if (expr.body.type === 'BlockStatement') throw unsupported(expr);
      const argument = patternAsIdentifier(expr.params[0]);
      return { argument, expression: expressionAsAssertion(expr.body), loc: loc(expr) };
    }
    return { argument: null, expression: expressionAsAssertion(expr), loc: loc(expr) };
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

function loc (n: JSyntax.Node): Syntax.SourceLocation {
  if (!n.loc) {
    throw new MessageException(unexpected(new Error('No location information available on nodes')));
  }
  return { file: options.filename, start: n.loc.start, end: n.loc.end };
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

function expressionAsTerm (expr: JSyntax.Expression): Syntax.Term {
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
    case 'UnaryExpression':
      return {
        type: 'UnaryTerm',
        operator: unaryOp(expr),
        argument: expressionAsTerm(expr.argument),
        loc: loc(expr)
      };
    case 'BinaryExpression': {
      return {
        type: 'BinaryTerm',
        operator: binaryOp(expr),
        left: expressionAsTerm(expr.left),
        right: expressionAsTerm(expr.right),
        loc: loc(expr)
      };
    }
    case 'LogicalExpression':
      return {
        type: 'LogicalTerm',
        operator: expr.operator,
        left: expressionAsTerm(expr.left),
        right: expressionAsTerm(expr.right),
        loc: loc(expr)
      };
    case 'ConditionalExpression':
      return {
        type: 'ConditionalTerm',
        test: expressionAsTerm(expr.test),
        consequent: expressionAsTerm(expr.consequent),
        alternate: expressionAsTerm(expr.alternate),
        loc: loc(expr)
      };
    case 'CallExpression':
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
      if (expr.callee.type === 'Super') throw unsupported(expr.callee);
      if (expr.arguments.length > 9) throw unsupported(expr, 'more than 9 arguments not supported yet');
      return {
        type: 'CallTerm',
        callee: expressionAsTerm(expr.callee),
        args: expr.arguments.map(expr => {
          if (expr.type === 'SpreadElement') {
            throw unsupported(expr);
          } else {
            return expressionAsTerm(expr);
          }
        }),
        loc: loc(expr)
      };
    case 'MemberExpression':
      if (expr.object.type === 'Super') throw unsupported(expr.object);
      let property: Syntax.Term;
      if (expr.computed) {
        property = expressionAsTerm(expr.property);
      } else {
        if (expr.property.type !== 'Identifier') throw unsupported(expr.property);
        property = { type: 'Literal', value: expr.property.name, loc: loc(expr.property) };
      }
      return {
        type: 'MemberTerm',
        object: expressionAsTerm(expr.object),
        property,
        loc: loc(expr)
      };
    default:
      throw unsupported(expr);
  }
}

function expressionAsAssertion (expr: JSyntax.Expression): Syntax.Assertion {
  switch (expr.type) {
    case 'UnaryExpression':
      if (expr.operator === '!') {
        return {
          type: 'UnaryAssertion',
          operator: '!',
          argument: expressionAsAssertion(expr.argument),
          loc: loc(expr)
        };
      }
      return expressionAsTerm(expr);
    case 'BinaryExpression': {
      if (expr.operator === 'instanceof') {
        if (expr.right.type !== 'Identifier') {
          throw unsupported(expr, 'instance check only works for class names');
        }
        return {
          type: 'InstanceOfAssertion',
          left: expressionAsTerm(expr.left),
          right: patternAsIdentifier(expr.right),
          loc: loc(expr)
        };
      }
      if (expr.operator === 'in') {
        return {
          type: 'InAssertion',
          property: expressionAsTerm(expr.left),
          object: expressionAsTerm(expr.right),
          loc: loc(expr)
        };
      }
      return expressionAsTerm(expr);
    }
    case 'LogicalExpression':
      return {
        type: 'BinaryAssertion',
        operator: expr.operator,
        left: expressionAsAssertion(expr.left),
        right: expressionAsAssertion(expr.right),
        loc: loc(expr)
      };
    case 'CallExpression':
      if (expr.callee.type === 'Identifier' &&
          expr.callee.name === 'pure') {
        if (expr.arguments.length !== 0) throw unsupported(expr, 'pure modifier has no arguments');
        return { type: 'PureAssertion', loc: loc(expr) };
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
          type: 'SpecAssertion',
          callee: expressionAsTerm(callee),
          hasThis: false,
          args: r.params.map(p => (p as JSyntax.Identifier).name),
          pre: expressionAsAssertion(r.body),
          post: { argument, expression: expressionAsAssertion(s.body), loc: loc(s) },
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
          type: 'EveryAssertion',
          array: expressionAsTerm(callee),
          argument: patternAsIdentifier(inv.params[0]),
          indexArgument: inv.params.length > 1 ? patternAsIdentifier(inv.params[1]) : null,
          expression: expressionAsAssertion(inv.body),
          loc: loc(expr)
        };
      }
      return expressionAsTerm(expr);

    default:
      return expressionAsTerm(expr);
  }
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

function findConstructor (clsDef: JSyntax.ClassDeclaration): Array<string> {
  let constrMethod: JSyntax.MethodDefinition | null = null;
  for (const method of clsDef.body.body) {
    if (method.kind === 'constructor') {
      if (constrMethod !== null) {
        throw unsupported(method, 'class can have at most one constructor');
      }
      constrMethod = method;
    }
  }
  if (constrMethod === null) {
    throw unsupported(clsDef, 'class needs one constructor');
  }
  if (constrMethod.kind === 'get' || constrMethod.kind === 'set') {
    throw unsupported(constrMethod, 'getters and setters not supported');
  }
  if (constrMethod.static) throw unsupported(constrMethod, 'static not supported');
  if (constrMethod.key.type !== 'Identifier') {
    throw unsupported(constrMethod.key, 'key needs to be identifier');
  }
  if (constrMethod.key.name !== 'constructor') {
    throw unsupported(constrMethod.key, "constructor needs to be named 'constructor'");
  }
  const constr = constrMethod.value;
  if (constr.generator || constr.async) throw unsupported(constr);
  if (constr.params.length > 9) throw unsupported(constr, 'more than 9 arguments not supported yet');
  if (constr.params.length !== constr.body.body.length) {
    throw unsupported(constr, 'constructor should assign each param to a field');
  }
  checkDistinct(constr.params);
  const params: Array<string> = constr.params.map(patternAsIdentifier).map(i => i.name);
  for (let i = 0; i < params.length; i++) {
    const asg = constr.body.body[i];
    if (asg.type !== 'ExpressionStatement' ||
        asg.expression.type !== 'AssignmentExpression' ||
        asg.expression.left.type !== 'MemberExpression' ||
        asg.expression.left.computed ||
        asg.expression.left.object.type !== 'ThisExpression' ||
        asg.expression.left.property.type !== 'Identifier' ||
        asg.expression.left.property.name !== params[i] ||
        asg.expression.operator !== '=' ||
        asg.expression.right.type !== 'Identifier' ||
        asg.expression.right.name !== params[i]) {
      throw unsupported(asg, 'constructor should assign each param to a field');
    }
  }
  return params;
}

function findClassInvariant (clsDef: JSyntax.ClassDeclaration): JSyntax.Expression {
  let invMethod: JSyntax.MethodDefinition | null = null;
  for (const method of clsDef.body.body) {
    if (method.key.type === 'Identifier' && method.key.name === 'invariant') {
      if (invMethod !== null) {
        throw unsupported(method, 'class can have at most one invariant');
      }
      invMethod = method;
    }
  }
  if (invMethod === null) {
    return { type: 'Literal', value: true, raw: 'true', loc: clsDef.loc };
  }
  if (invMethod.kind === 'get' || invMethod.kind === 'set') {
    throw unsupported(invMethod, 'getters and setters not supported');
  }
  if (invMethod.static) throw unsupported(invMethod, 'static not supported');
  if (invMethod.key.type !== 'Identifier') {
    throw unsupported(invMethod.key, 'key needs to be identifier');
  }
  const inv = invMethod.value;
  if (inv.generator || inv.async) throw unsupported(inv);
  if (inv.params.length > 0) {
    throw unsupported(inv, 'invariant cannot have parameters');
  }
  if (inv.generator || inv.async) throw unsupported(inv);
  if (inv.body.body.length !== 1) {
    throw unsupported(inv.body, 'invariant needs to be single expression statement');
  }
  const invStmt = inv.body.body[0];
  if (invStmt.type !== 'ReturnStatement' || !invStmt.argument) {
    throw unsupported(inv.body, 'invariant needs to be a single return statement with an expression');
  }
  return invStmt.argument;
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
          return [{ type: 'AssertStatement', expression: expressionAsAssertion(arg), loc: loc(stmt) }];
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
        freeVars: [],
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
      const methods: Array<Syntax.MethodDeclaration> = [];
      for (const method of stmt.body.body) {
        if (method.kind === 'constructor') continue;
        if (method.key.type !== 'Identifier') {
          throw unsupported(method.key, 'key needs to be identifier');
        }
        if (method.key.name === 'invariant') continue;
        if (method.kind !== 'method') {
          throw unsupported(method, 'getters and setters not supported');
        }
        if (method.static) throw unsupported(method, 'static not supported');
        const func = method.value;
        if (func.generator) throw unsupported(func, 'generators not supported');
        if (func.async) throw unsupported(func, 'async method not supported');
        checkDistinct(func.params);
        const params: Array<Syntax.Identifier> = func.params.map(patternAsIdentifier);
        methods.push({
          type: 'MethodDeclaration',
          id: id(method.key.name, loc(method.key)),
          params,
          requires: findPreConditions(func.body.body),
          ensures: findPostConditions(func.body.body),
          body: {
            type: 'BlockStatement',
            body: flatMap(withoutPseudoCalls('requires',
                          withoutPseudoCalls('ensures', func.body.body)), statementAsJavaScript),
            loc: loc(stmt.body)
          },
          freeVars: [],
          className: stmt.id.name,
          loc: loc(stmt)
        });
      }
      return [{
        type: 'ClassDeclaration',
        id: patternAsIdentifier(stmt.id),
        fields: findConstructor(stmt),
        invariant: expressionAsAssertion(findClassInvariant(stmt)),
        methods,
        loc: loc(stmt)
      }];
    }
    default:
      throw unsupported(stmt);
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
  return prog;
}
