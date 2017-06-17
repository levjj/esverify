import { Syntax, Visitor, isMutable } from './javascript';
import { A, P, Heap, replaceResultWithCall, transformSpec, truthy, heapEq } from './logic';

class PureContextError extends Error {
  constructor () { super('not supported in pure functional context'); }
}

class QuantifierFreeContextError extends Error {
  constructor () { super('quantifiers not supported in this context'); }
}

class HeapReferenceContextError extends Error {
  constructor () { super('heap references not supported in this context'); }
}

class AssertionTranslator extends Visitor<A, void> {
  oldHeap: Heap;
  heap: Heap;
  allowsQuantifiers: boolean;
  allowsHeapReferences: boolean;

  constructor (oldHeap: Heap, heap: Heap) {
    super();
    this.oldHeap = oldHeap;
    this.heap = heap;
    this.allowsQuantifiers = true;
    this.allowsHeapReferences = true;
  }

  visitIdentifier (expr: Syntax.Identifier): A {
    if (isMutable(expr)) {
      if (!this.allowsHeapReferences) throw new HeapReferenceContextError();
      return { type: 'HeapReference', heap: this.heap, loc: expr.name };
    } else {
      return expr.name;
    }
  }

  visitOldIdentifier (expr: Syntax.OldIdentifier): A {
    if (!this.allowsHeapReferences) throw new HeapReferenceContextError();
    if (!isMutable(expr.id)) { throw new Error('not mutable'); }
    return { type: 'HeapReference', heap: this.oldHeap, loc: expr.id.name };
  }

  visitLiteral (expr: Syntax.Literal): A {
    return expr;
  }

  visitArrayExpression (expr: Syntax.ArrayExpression): A {
    return {
      type: 'ArrayExpression',
      elements: expr.elements.map(e => this.visitExpression(e))
    };
  }

  visitUnaryExpression (expr: Syntax.UnaryExpression): A {
    const argument = this.visitExpression(expr.argument);
    return { type: 'UnaryExpression', operator: expr.operator, argument };
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): A {
    const left = this.visitExpression(expr.left);
    const right = this.visitExpression(expr.right);
    return { type: 'BinaryExpression', operator: expr.operator, left, right };
  }

  visitLogicalExpression (expr: Syntax.LogicalExpression): A {
    const origQF = this.allowsQuantifiers;
    this.allowsQuantifiers = false;
    const left = this.visitExpression(expr.left);
    this.allowsQuantifiers = origQF;
    const right = this.visitExpression(expr.right);
    if (expr.operator === '&&') {
      return { type: 'ConditionalExpression', test: truthy(left), consequent: right, alternate: left };
    } else {
      return { type: 'ConditionalExpression', test: truthy(left), consequent: left, alternate: right };
    }
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): A {
    const origQF = this.allowsQuantifiers;
    this.allowsQuantifiers = false;
    const test = truthy(this.visitExpression(expr.test));
    this.allowsQuantifiers = origQF;
    const consequent = this.visitExpression(expr.consequent);
    const alternate = this.visitExpression(expr.alternate);
    return { type: 'ConditionalExpression', test, consequent, alternate };
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression): A {
    throw new PureContextError();
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression): A {
    // ignore all expressions but the last
    return this.visitExpression(expr.expressions[expr.expressions.length - 1]);
  }

  visitCallExpression (expr: Syntax.CallExpression): A {
    return {
      type: 'CallExpression',
      callee: this.visitExpression(expr.callee),
      heap: this.heap,
      args: expr.args.map(a => this.visitExpression(a))
    };
  }

  visitSpecExpression (expr: Syntax.SpecExpression): A {
    if (!this.allowsQuantifiers) throw new QuantifierFreeContextError();
    const callee = this.visitExpression(expr.callee);
    const r = truthy(translateExpression(this.heap + 1, this.heap + 1, expr.pre));
    let s = truthy(translateExpression(this.heap + 1, this.heap + 2, expr.post.expression));
    s = replaceResultWithCall(callee, this.heap + 1, expr.args, expr.post.argument, s);
    const test: P = transformSpec(callee, expr.args, r, s, this.heap + 1);
    const consequent: A = { type: 'Literal', value: true };
    const alternate: A = { type: 'Literal', value: false };
    return { type: 'ConditionalExpression', test, consequent, alternate };
  }

  visitPureExpression (expr: Syntax.PureExpression): A {
    const test: P = heapEq(this.heap, this.oldHeap);
    const consequent: A = { type: 'Literal', value: true };
    const alternate: A = { type: 'Literal', value: false };
    return { type: 'ConditionalExpression', test, consequent, alternate };
  }

  visitNewExpression (expr: Syntax.NewExpression): A {
    throw new PureContextError();
  }

  visitInstanceOfExpression (expr: Syntax.InstanceOfExpression): A {
    const test: P = { type: 'InstanceOf', left: this.visitExpression(expr.left), right: expr.right.name };
    const consequent: A = { type: 'Literal', value: true };
    const alternate: A = { type: 'Literal', value: false };
    return { type: 'ConditionalExpression', test, consequent, alternate };
  }

  visitInExpression (expr: Syntax.InExpression): A {
    const test: P = { type: 'HasProperty', object: this.visitExpression(expr.object), property: expr.property };
    const consequent: A = { type: 'Literal', value: true };
    const alternate: A = { type: 'Literal', value: false };
    return { type: 'ConditionalExpression', test, consequent, alternate };
  }

  visitMemberExpression (expr: Syntax.MemberExpression): A {
    const object = this.visitExpression(expr.object);
    return { type: 'MemberExpression', object, property: expr.property };
  }

  visitFunctionExpression (expr: Syntax.FunctionExpression): A {
    throw new PureContextError();
  }

  visitVariableDeclaration (stmt: Syntax.VariableDeclaration) {/*empty*/}
  visitBlockStatement (stmt: Syntax.BlockStatement) {/*empty*/}
  visitExpressionStatement (stmt: Syntax.ExpressionStatement) {/*empty*/}
  visitAssertStatement (stmt: Syntax.AssertStatement) {/*empty*/}
  visitIfStatement (stmt: Syntax.IfStatement) {/*empty*/}
  visitReturnStatement (stmt: Syntax.ReturnStatement) {/*empty*/}
  visitWhileStatement (stmt: Syntax.WhileStatement) {/*empty*/}
  visitDebuggerStatement (stmt: Syntax.DebuggerStatement) {/*empty*/}
  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration) {/*empty*/}
  visitClassDeclaration (stmt: Syntax.ClassDeclaration) {/*empty*/}
  visitProgram (prog: Syntax.Program) {/*empty*/}
}

export function translateExpression (oldHeap: Heap, heap: Heap, expr: Syntax.Expression): A {
  const translator = new AssertionTranslator(oldHeap, heap);
  return translator.visitExpression(expr);
}

export function translateNoHeapExpression (expr: Syntax.Expression): A {
  const translator = new AssertionTranslator(0, 0);
  translator.allowsHeapReferences = false;
  return translator.visitExpression(expr);
}
