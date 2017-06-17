import { Syntax, Visitor, isMutable } from './javascript';
import { A, P, Heap, replaceResultWithCall, transformSpec, truthy, not, and, or, heapEq } from './logic';

class PureContextError extends Error {
  constructor () { super('not supported in pure functional context'); }
}

class HeapReferenceContextError extends Error {
  constructor () { super('heap references not supported in this context'); }
}

class PropositionContextError extends Error {
  constructor () { super('spec syntax not supported in this context'); }
}

class AssertionTranslator extends Visitor<A, void> {
  readonly oldHeap: Heap;
  readonly heap: Heap;
  readonly allowsHeapReferences: boolean;

  constructor (oldHeap: Heap, heap: Heap, allowsHeapReferences: boolean = true) {
    super();
    this.oldHeap = oldHeap;
    this.heap = heap;
    this.allowsHeapReferences = allowsHeapReferences;
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
    const left = this.visitExpression(expr.left);
    const right = this.visitExpression(expr.right);
    if (expr.operator === '&&') {
      return { type: 'ConditionalExpression', test: truthy(left), consequent: right, alternate: left };
    } else {
      return { type: 'ConditionalExpression', test: truthy(left), consequent: left, alternate: right };
    }
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): A {
    const test = truthy(this.visitExpression(expr.test));
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
    throw new PropositionContextError();
  }

  visitPureExpression (expr: Syntax.PureExpression): A {
    throw new PropositionContextError();
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

class PropositionTranslator extends Visitor<P, void> {
  readonly oldHeap: Heap;
  readonly heap: Heap;
  readonly allowsHeapReferences: boolean;

  constructor (oldHeap: Heap, heap: Heap, allowsHeapReferences: boolean = true) {
    super();
    this.oldHeap = oldHeap;
    this.heap = heap;
    this.allowsHeapReferences = allowsHeapReferences;
  }

  translateExpression (expr: Syntax.Expression): A {
    const translator = new AssertionTranslator(this.oldHeap, this.heap, this.allowsHeapReferences);
    return translator.visitExpression(expr);
  }

  translateProposition (expr: Syntax.Expression): P {
    return truthy(this.translateExpression(expr));
  }

  visitIdentifier (expr: Syntax.Identifier): P {
    return this.translateProposition(expr);
  }

  visitOldIdentifier (expr: Syntax.OldIdentifier): P {
    return this.translateProposition(expr);
  }

  visitLiteral (expr: Syntax.Literal): P {
    return this.translateProposition(expr);
  }

  visitArrayExpression (expr: Syntax.ArrayExpression): P {
    return this.translateProposition(expr);
  }

  visitUnaryExpression (expr: Syntax.UnaryExpression): P {
    if (expr.operator === '!') return not(this.visitExpression(expr.argument));
    return this.translateProposition(expr);
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): P {
    return this.translateProposition(expr);
  }

  visitLogicalExpression (expr: Syntax.LogicalExpression): P {
    if (expr.operator === '&&') return and(this.visitExpression(expr.left), this.visitExpression(expr.right));
    if (expr.operator === '||') return or(this.visitExpression(expr.left), this.visitExpression(expr.right));
    return this.translateProposition(expr);
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): P {
    const test = this.visitExpression(expr.test);
    const consequent = this.visitExpression(expr.consequent);
    const alternate = this.visitExpression(expr.alternate);
    return or(and(test, consequent), and(not(test), alternate));
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression): P {
    throw new PureContextError();
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression): P {
    // ignore all expressions but the last
    return this.visitExpression(expr.expressions[expr.expressions.length - 1]);
  }

  visitCallExpression (expr: Syntax.CallExpression): P {
    return this.translateProposition(expr);
  }

  visitSpecExpression (expr: Syntax.SpecExpression): P {
    const callee: A = this.translateExpression(expr.callee);
    const r = translateExpression(this.heap + 1, this.heap + 1, expr.pre);
    let s = translateExpression(this.heap + 1, this.heap + 2, expr.post.expression);
    s = replaceResultWithCall(callee, this.heap + 1, expr.args, expr.post.argument, s);
    return transformSpec(callee, expr.args, r, s, this.heap + 1);
  }

  visitPureExpression (expr: Syntax.PureExpression): P {
    return heapEq(this.heap, this.oldHeap);
  }

  visitNewExpression (expr: Syntax.NewExpression): P {
    throw new PureContextError();
  }

  visitInstanceOfExpression (expr: Syntax.InstanceOfExpression): P {
    return { type: 'InstanceOf', left: this.translateExpression(expr.left), right: expr.right.name };
  }

  visitInExpression (expr: Syntax.InExpression): P {
    return { type: 'HasProperty', object: this.translateExpression(expr.object), property: expr.property };
  }

  visitMemberExpression (expr: Syntax.MemberExpression): P {
    return this.translateProposition(expr);
  }

  visitFunctionExpression (expr: Syntax.FunctionExpression): P {
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

export function translateExpression (oldHeap: Heap, heap: Heap, expr: Syntax.Expression): P {
  const translator = new PropositionTranslator(oldHeap, heap);
  return translator.visitExpression(expr);
}

export function translateNoHeapExpression (expr: Syntax.Expression): P {
  const translator = new PropositionTranslator(0, 0, false);
  return translator.visitExpression(expr);
}
