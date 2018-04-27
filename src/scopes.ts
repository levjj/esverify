import { Syntax, Visitor, id, nullLoc } from './javascript';
import { MessageException, unexpected } from './message';

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
  return new MessageException({
    status: 'error',
    type: 'already-defined',
    loc,
    description: `at ${file}:${start.line}:${start.column}`
  });
}

function assignToConst (loc: Syntax.SourceLocation) {
  return new MessageException({ status: 'error', type: 'assignment-to-const', loc, description: '' });
}

function refInInvariant (loc: Syntax.SourceLocation) {
  return new MessageException({ status: 'error', type: 'reference-in-invariant', loc, description: '' });
}

export function isMutable (idOrDecl: Syntax.Identifier | Syntax.Declaration): boolean {
  const decl = idOrDecl.type === 'Identifier' ? idOrDecl.decl : idOrDecl;
  return decl.type === 'Var' && decl.decl.kind === 'let';
}

class Scope {
  funcOrLoop: Syntax.Function | Syntax.WhileStatement | null;
  ids: { [varname: string]: Syntax.Declaration } = {};
  parent: Scope | null;
  constructor (parent: Scope | null = null, fw: Syntax.Function | Syntax.WhileStatement | null = null) {
    this.parent = parent;
    this.funcOrLoop = fw;
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
      if (this.funcOrLoop && !this.funcOrLoop.freeVars.includes(sym.name) && isMutable(decl)) {
        this.funcOrLoop.freeVars.push(sym.name); // a free variable
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

class NameResolver extends Visitor<void, void, void, void> {

  scope: Scope = new Scope();
  allowOld: boolean = false;
  allowRef: boolean = true;

  scoped (action: () => void, allowsOld: boolean = this.allowOld, allowsRef: boolean = this.allowRef,
          fn: Syntax.Function | Syntax.WhileStatement | null = this.scope.funcOrLoop) {
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

  visitIdentifierTerm (term: Syntax.Identifier) {
    this.scope.useSymbol(term, false, false, this.allowRef);
  }

  visitOldIdentifierTerm (term: Syntax.OldIdentifier) {
    if (!this.allowOld) throw unsupportedLoc(term.loc, 'old() not allowed in this context');
    this.scope.useSymbol(term.id);
  }

  visitLiteralTerm (term: Syntax.Literal) { /* empty */ }

  visitUnaryTerm (term: Syntax.UnaryTerm) {
    this.visitTerm(term.argument);
  }

  visitBinaryTerm (term: Syntax.BinaryTerm) {
    this.visitTerm(term.left);
    this.visitTerm(term.right);
  }

  visitLogicalTerm (term: Syntax.LogicalTerm) {
    this.visitTerm(term.left);
    this.visitTerm(term.right);
  }

  visitConditionalTerm (term: Syntax.ConditionalTerm) {
    this.visitTerm(term.test);
    this.visitTerm(term.consequent);
    this.visitTerm(term.alternate);
  }

  visitCallTerm (term: Syntax.CallTerm) {
    term.args.forEach(e => this.visitTerm(e));
    this.visitTerm(term.callee);
  }

  visitMemberTerm (term: Syntax.MemberTerm) {
    this.visitTerm(term.object);
    this.visitTerm(term.property);
  }

  visitTermAssertion (term: Syntax.Term) {
    this.visitTerm(term);
  }

  visitPureAssertion (assertion: Syntax.PureAssertion) { /* empty */ }

  visitPostCondition (post: Syntax.PostCondition) {
    if (post.argument) {
      // scoped at the surrounding context (spec or function body)
      this.scope.defSymbol(post.argument, { type: 'PostArg', decl: post });
    }
    this.visitAssertion(post.expression);
  }

  visitSpecAssertion (assertion: Syntax.SpecAssertion) {
    this.visitTerm(assertion.callee);
    this.scoped(() => {
      assertion.args.forEach((a, argIdx) => {
        this.scope.defSymbol(id(a), { type: 'SpecArg', decl: assertion, argIdx });
      });
      this.visitAssertion(assertion.pre);
    }, false);
    this.scoped(() => {
      assertion.args.forEach((a, argIdx) => {
        this.scope.defSymbol(id(a), { type: 'SpecArg', decl: assertion, argIdx });
      });
      this.visitPostCondition(assertion.post);
    }, true);
  }

  visitEveryAssertion (assertion: Syntax.EveryAssertion) {
    this.visitTerm(assertion.array);
    this.scoped(() => {
      this.scope.defSymbol(assertion.argument, { type: 'EveryArg', decl: assertion });
      if (assertion.indexArgument !== null) {
        this.scope.defSymbol(assertion.indexArgument, { type: 'EveryIdxArg', decl: assertion });
      }
      this.visitAssertion(assertion.expression);
    }, false);
  }

  visitInstanceOfAssertion (assertion: Syntax.InstanceOfAssertion) {
    this.visitTerm(assertion.left);
    this.scope.useSymbol(assertion.right, false, true);
  }

  visitInAssertion (assertion: Syntax.InAssertion) {
    this.visitTerm(assertion.property);
    this.visitTerm(assertion.object);
  }

  visitUnaryAssertion (assertion: Syntax.UnaryAssertion) {
    this.visitAssertion(assertion.argument);
  }

  visitBinaryAssertion (assertion: Syntax.BinaryAssertion) {
    this.visitAssertion(assertion.left);
    this.visitAssertion(assertion.right);
  }

  visitIdentifier (expr: Syntax.Identifier) {
    this.scope.useSymbol(expr, false, false, this.allowRef);
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
      expr.requires.forEach(r => this.visitAssertion(r));
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
    this.visitAssertion(stmt.expression);
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
    this.scoped(() => {
      this.visitExpression(stmt.test);
      stmt.invariants.forEach(i => this.visitAssertion(i));
      stmt.body.body.forEach(s => this.visitStatement(s));
    }, false, true, stmt);
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement) { /* empty */ }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration) {
    this.scope.defSymbol(stmt.id, { type: 'Func', decl: stmt });
    this.scoped(() => {
      stmt.params.forEach(p => this.scope.defSymbol(p, { type: 'Param', func: stmt, decl: p }));
      stmt.requires.forEach(r => this.visitAssertion(r));
      stmt.ensures.forEach(s => {
        this.scoped(() => this.visitPostCondition(s), true);
      });
      stmt.body.body.forEach(s => this.visitStatement(s));
    }, false, true, stmt);
  }

  visitMethodDeclaration (stmt: Syntax.MethodDeclaration, cls: Syntax.ClassDeclaration) {
    this.scoped(() => {
      this.scope.defSymbol(id('this'), { type: 'This', decl: cls });
      stmt.params.forEach(p => this.scope.defSymbol(p, { type: 'Param', func: stmt, decl: p }));
      stmt.requires.forEach(r => this.visitAssertion(r));
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
      this.visitAssertion(stmt.invariant);
    }, false, false);
    stmt.methods.forEach(method => this.visitMethodDeclaration(method, stmt));
  }

  builtinClass (name: string) {
    const decl: Syntax.ClassDeclaration = {
      type: 'ClassDeclaration',
      id: id(name),
      fields: [],
      invariant: { type: 'Literal', value: true, loc: nullLoc() },
      methods: [],
      loc: nullLoc()
    };
    this.scope.defSymbol(decl.id, { type: 'Class', decl });
  }

  visitProgram (prog: Syntax.Program) {
    this.builtinClass('Object');
    this.builtinClass('Function');
    this.builtinClass('Array');
    prog.body.forEach(stmt => this.visitStatement(stmt));
    prog.invariants.forEach(inv => this.visitAssertion(inv));
  }
}

export function resolveNames (program: Syntax.Program): void {
  const resolver = new NameResolver();
  resolver.visitProgram(program);
}
