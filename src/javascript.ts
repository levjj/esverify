export namespace Syntax {
  /* tslint:disable:ter-indent */

  export type Declaration = { type: 'Unresolved' }
                          | { type: 'Var', decl: VariableDeclaration }
                          | { type: 'Func', decl: Function }
                          | { type: 'SpecArg', decl: SpecAssertion, argIdx: number }
                          | { type: 'EveryArg', decl: EveryAssertion }
                          | { type: 'EveryIdxArg', decl: EveryAssertion }
                          | { type: 'PostArg', decl: PostCondition }
                          | { type: 'Param', func: Function; decl: Identifier }
                          | { type: 'This', decl: ClassDeclaration }
                          | { type: 'Class', decl: ClassDeclaration };

  export interface Position { line: number; column: number; }
  export interface SourceLocation { file: string; start: Position; end: Position; }

  export type ClassName = string;

  export interface Identifier { type: 'Identifier';
                                name: string;
                                decl: Declaration;
                                refs: Array<Identifier>;
                                isWrittenTo: boolean;
                                loc: SourceLocation; }
  export interface OldIdentifier { type: 'OldIdentifier'; id: Identifier; loc: SourceLocation; }
  export interface Literal { type: 'Literal';
                             value: undefined | null | boolean | number | string;
                             loc: SourceLocation; }

  export type UnaryOperator = '-' | '+' | '!' | '~' | 'typeof' | 'void';
  export interface UnaryTerm { type: 'UnaryTerm';
                               operator: UnaryOperator;
                               argument: Term;
                               loc: SourceLocation; }
  export type BinaryOperator = '===' | '!==' | '<' | '<=' | '>' | '>='
                             | '<<' | '>>' | '>>>' | '+' | '-' | '*' | '/' | '%'
                             | '|' | '^' | '&';
  export interface BinaryTerm { type: 'BinaryTerm';
                                operator: BinaryOperator;
                                left: Term;
                                right: Term;
                                loc: SourceLocation; }
  export type LogicalOperator = '||' | '&&';
  export interface LogicalTerm { type: 'LogicalTerm';
                                 operator: LogicalOperator;
                                 left: Term;
                                 right: Term;
                                 loc: SourceLocation; }
  export interface ConditionalTerm { type: 'ConditionalTerm';
                                     test: Term;
                                     consequent: Term;
                                     alternate: Term;
                                     loc: SourceLocation; }
  export interface CallTerm { type: 'CallTerm';
                              callee: Term;
                              args: Array<Term>;
                              loc: SourceLocation; }
  export interface MemberTerm { type: 'MemberTerm';
                                object: Term;
                                property: Term;
                                loc: SourceLocation; }
  export interface IsIntegerTerm { type: 'IsIntegerTerm';
                                   term: Term;
                                   loc: SourceLocation; }
  export interface ToIntegerTerm { type: 'ToIntegerTerm';
                                   term: Term;
                                   loc: SourceLocation; }

  export type Term = Identifier
                   | OldIdentifier
                   | Literal
                   | UnaryTerm
                   | BinaryTerm
                   | LogicalTerm
                   | ConditionalTerm
                   | CallTerm
                   | MemberTerm
                   | IsIntegerTerm
                   | ToIntegerTerm;

  export interface PureAssertion { type: 'PureAssertion';
                                   loc: SourceLocation; }
  export interface PostCondition { argument: Identifier | null;
                                   expression: Assertion;
                                   loc: SourceLocation; }
  export interface SpecAssertion { type: 'SpecAssertion';
                                   callee: Term;
                                   hasThis: boolean;
                                   args: Array<string>;
                                   pre: Assertion;
                                   post: PostCondition;
                                   loc: SourceLocation; }
  export interface EveryAssertion { type: 'EveryAssertion';
                                    array: Term;
                                    argument: Identifier;
                                    indexArgument: Identifier | null;
                                    expression: Assertion;
                                    loc: SourceLocation; }
  export interface InstanceOfAssertion { type: 'InstanceOfAssertion';
                                         left: Term;
                                         right: Identifier;
                                         loc: SourceLocation; }
  export interface InAssertion { type: 'InAssertion';
                                 property: Term;
                                 object: Term;
                                 loc: SourceLocation; }
  export interface UnaryAssertion { type: 'UnaryAssertion';
                                    operator: '!';
                                    argument: Assertion;
                                    loc: SourceLocation; }
  export interface BinaryAssertion { type: 'BinaryAssertion';
                                     operator: LogicalOperator;
                                     left: Assertion;
                                     right: Assertion;
                                     loc: SourceLocation; }
  export type Assertion = Term
                        | PureAssertion
                        | SpecAssertion
                        | EveryAssertion
                        | InstanceOfAssertion
                        | InAssertion
                        | UnaryAssertion
                        | BinaryAssertion;

  export interface UnaryExpression { type: 'UnaryExpression';
                                     operator: UnaryOperator;
                                     argument: Expression;
                                     loc: SourceLocation; }
  export interface BinaryExpression { type: 'BinaryExpression';
                                      operator: BinaryOperator;
                                      left: Expression;
                                      right: Expression;
                                      loc: SourceLocation; }
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
                                          left: Identifier | MemberExpression;
                                          right: Expression;
                                          loc: SourceLocation; }
  export interface SequenceExpression { type: 'SequenceExpression';
                                        expressions: Expression[];
                                        loc: SourceLocation; }
  export interface CallExpression { type: 'CallExpression';
                                    callee: Expression;
                                    args: Array<Expression>;
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
  export interface FunctionExpression { type: 'FunctionExpression';
                                        id: Identifier | null;
                                        params: Array<Identifier>;
                                        requires: Array<Assertion>;
                                        ensures: Array<PostCondition>;
                                        body: BlockStatement;
                                        freeVars: Array<Identifier>;
                                        loc: SourceLocation; }

  export type Expression = Identifier
                         | Literal
                         | UnaryExpression
                         | BinaryExpression
                         | LogicalExpression
                         | ConditionalExpression
                         | AssignmentExpression
                         | SequenceExpression
                         | CallExpression
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
                                     expression: Assertion;
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
                                    invariants: Array<Assertion>;
                                    test: Expression;
                                    body: BlockStatement;
                                    freeVars: Array<Identifier>;
                                    loc: SourceLocation; }
  export interface DebuggerStatement { type: 'DebuggerStatement';
                                       loc: SourceLocation; }
  export interface FunctionDeclaration { type: 'FunctionDeclaration';
                                         id: Identifier;
                                         params: Array<Identifier>;
                                         requires: Array<Assertion>;
                                         ensures: Array<PostCondition>;
                                         body: BlockStatement;
                                         freeVars: Array<Identifier>;
                                         loc: SourceLocation; }
  export interface MethodDeclaration { type: 'MethodDeclaration';
                                       id: Identifier;
                                       params: Array<Identifier>;
                                       requires: Array<Assertion>;
                                       ensures: Array<PostCondition>;
                                       body: BlockStatement;
                                       freeVars: Array<Identifier>;
                                       className: string;
                                       loc: SourceLocation; }
  export interface ClassDeclaration { type: 'ClassDeclaration';
                                      id: Identifier;
                                      fields: Array<string>;
                                      invariant: Assertion;
                                      methods: Array<MethodDeclaration>;
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

  export type Function = FunctionExpression | FunctionDeclaration | MethodDeclaration;

  export type Program = { body: Array<Statement>,
                          invariants: Array<Assertion> };

}

export function eqSourceLocation (loc1: Syntax.SourceLocation, loc2: Syntax.SourceLocation): boolean {
  return loc1.file === loc2.file &&
         loc1.start.line === loc2.start.line &&
         loc1.start.column === loc2.start.column &&
         loc1.end.line === loc2.end.line &&
         loc1.end.column === loc2.end.column;
}

export function eqEndPosition (loc1: Syntax.SourceLocation, loc2: Syntax.SourceLocation): boolean {
  return loc1.file === loc2.file &&
         loc1.end.line === loc2.end.line &&
         loc1.end.column === loc2.end.column;
}

export function compEndPosition (loc1: Syntax.SourceLocation, loc2: Syntax.SourceLocation): boolean {
  return loc1.file < loc2.file ||
         loc1.end.line < loc2.end.line ||
         loc1.end.column < loc2.end.column;
}

export type TestCode = ReadonlyArray<Syntax.Statement>;

export type Position = Syntax.Position;
export type SourceLocation = Syntax.SourceLocation;

export abstract class Visitor<T,A,E,S> {

  abstract visitIdentifierTerm (term: Syntax.Identifier): T;
  abstract visitOldIdentifierTerm (term: Syntax.OldIdentifier): T;
  abstract visitLiteralTerm (term: Syntax.Literal): T;
  abstract visitUnaryTerm (term: Syntax.UnaryTerm): T;
  abstract visitBinaryTerm (term: Syntax.BinaryTerm): T;
  abstract visitLogicalTerm (term: Syntax.LogicalTerm): T;
  abstract visitConditionalTerm (term: Syntax.ConditionalTerm): T;
  abstract visitCallTerm (term: Syntax.CallTerm): T;
  abstract visitMemberTerm (term: Syntax.MemberTerm): T;
  abstract visitIsIntegerTerm (term: Syntax.IsIntegerTerm): T;
  abstract visitToIntegerTerm (term: Syntax.ToIntegerTerm): T;

  visitTerm (term: Syntax.Term): T {
    switch (term.type) {
      case 'Identifier': return this.visitIdentifierTerm(term);
      case 'OldIdentifier': return this.visitOldIdentifierTerm(term);
      case 'Literal': return this.visitLiteralTerm(term);
      case 'UnaryTerm': return this.visitUnaryTerm(term);
      case 'BinaryTerm': return this.visitBinaryTerm(term);
      case 'LogicalTerm': return this.visitLogicalTerm(term);
      case 'ConditionalTerm': return this.visitConditionalTerm(term);
      case 'CallTerm': return this.visitCallTerm(term);
      case 'MemberTerm': return this.visitMemberTerm(term);
      case 'IsIntegerTerm': return this.visitIsIntegerTerm(term);
      case 'ToIntegerTerm': return this.visitToIntegerTerm(term);
    }
  }

  abstract visitTermAssertion (assertion: Syntax.Term): A;
  abstract visitPureAssertion (assertion: Syntax.PureAssertion): A;
  abstract visitSpecAssertion (assertion: Syntax.SpecAssertion): A;
  abstract visitEveryAssertion (assertion: Syntax.EveryAssertion): A;
  abstract visitInstanceOfAssertion (assertion: Syntax.InstanceOfAssertion): A;
  abstract visitInAssertion (assertion: Syntax.InAssertion): A;
  abstract visitUnaryAssertion (assertion: Syntax.UnaryAssertion): A;
  abstract visitBinaryAssertion (assertion: Syntax.BinaryAssertion): A;

  visitAssertion (assertion: Syntax.Assertion): A {
    switch (assertion.type) {
      case 'PureAssertion': return this.visitPureAssertion(assertion);
      case 'SpecAssertion': return this.visitSpecAssertion(assertion);
      case 'EveryAssertion': return this.visitEveryAssertion(assertion);
      case 'InstanceOfAssertion': return this.visitInstanceOfAssertion(assertion);
      case 'InAssertion': return this.visitInAssertion(assertion);
      case 'UnaryAssertion': return this.visitUnaryAssertion(assertion);
      case 'BinaryAssertion': return this.visitBinaryAssertion(assertion);
      default: return this.visitTermAssertion(assertion);
    }
  }

  abstract visitIdentifier (expr: Syntax.Identifier): E;
  abstract visitLiteral (expr: Syntax.Literal): E;
  abstract visitUnaryExpression (expr: Syntax.UnaryExpression): E;
  abstract visitBinaryExpression (expr: Syntax.BinaryExpression): E;
  abstract visitLogicalExpression (expr: Syntax.LogicalExpression): E;
  abstract visitConditionalExpression (expr: Syntax.ConditionalExpression): E;
  abstract visitAssignmentExpression (expr: Syntax.AssignmentExpression): E;
  abstract visitSequenceExpression (expr: Syntax.SequenceExpression): E;
  abstract visitCallExpression (expr: Syntax.CallExpression): E;
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
      case 'Literal': return this.visitLiteral(expr);
      case 'UnaryExpression': return this.visitUnaryExpression(expr);
      case 'BinaryExpression': return this.visitBinaryExpression(expr);
      case 'LogicalExpression': return this.visitLogicalExpression(expr);
      case 'ConditionalExpression': return this.visitConditionalExpression(expr);
      case 'AssignmentExpression': return this.visitAssignmentExpression(expr);
      case 'SequenceExpression': return this.visitSequenceExpression(expr);
      case 'CallExpression': return this.visitCallExpression(expr);
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

export function nullLoc (): Syntax.SourceLocation {
  return { file: '<null>', start: { line: 0, column: 0 }, end: { line: 0, column: 0 } };
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

class Traverser extends Visitor<void, void, void, void> {

  visitIdentifierTerm (term: Syntax.Identifier): void { /* empty */ }

  visitOldIdentifierTerm (term: Syntax.OldIdentifier): void {
    this.visitIdentifier(term.id);
  }

  visitLiteralTerm (term: Syntax.Literal): void { /* empty */ }

  visitUnaryTerm (term: Syntax.UnaryTerm): void {
    this.visitTerm(term.argument);
  }

  visitBinaryTerm (term: Syntax.BinaryTerm): void {
    this.visitTerm(term.left);
    this.visitTerm(term.right);
  }

  visitLogicalTerm (term: Syntax.LogicalTerm): void {
    this.visitTerm(term.left);
    this.visitTerm(term.right);
  }

  visitConditionalTerm (term: Syntax.ConditionalTerm): void {
    this.visitTerm(term.test);
    this.visitTerm(term.consequent);
    this.visitTerm(term.alternate);
  }

  visitCallTerm (term: Syntax.CallTerm): void {
    this.visitTerm(term.callee);
    term.args.forEach(e => this.visitTerm(e));
  }

  visitMemberTerm (term: Syntax.MemberTerm): void {
    this.visitTerm(term.object);
    this.visitTerm(term.property);
  }

  visitIsIntegerTerm (term: Syntax.IsIntegerTerm): void {
    this.visitTerm(term.term);
  }

  visitToIntegerTerm (term: Syntax.ToIntegerTerm): void {
    this.visitTerm(term.term);
  }

  visitTermAssertion (assertion: Syntax.Term): void {
    this.visitTerm(assertion);
  }

  visitPureAssertion (assertion: Syntax.PureAssertion): void { /* empty */ }

  visitPostCondition (post: Syntax.PostCondition): void {
    this.visitAssertion(post.expression);
  }

  visitSpecAssertion (assertion: Syntax.SpecAssertion): void {
    this.visitTerm(assertion.callee);
    this.visitAssertion(assertion.pre);
    this.visitPostCondition(assertion.post);
  }

  visitEveryAssertion (assertion: Syntax.EveryAssertion): void {
    this.visitTerm(assertion.array);
    this.visitAssertion(assertion.expression);
  }

  visitInstanceOfAssertion (assertion: Syntax.InstanceOfAssertion): void {
    this.visitTerm(assertion.left);
  }

  visitInAssertion (assertion: Syntax.InAssertion): void {
    this.visitTerm(assertion.property);
    this.visitTerm(assertion.object);
  }

  visitUnaryAssertion (assertion: Syntax.UnaryAssertion): void {
    this.visitAssertion(assertion.argument);
  }

  visitBinaryAssertion (assertion: Syntax.BinaryAssertion): void {
    this.visitAssertion(assertion.left);
    this.visitAssertion(assertion.right);
  }

  visitIdentifier (expr: Syntax.Identifier): void { /* empty */ }

  visitLiteral (expr: Syntax.Literal): void { /* empty */ }

  visitUnaryExpression (expr: Syntax.UnaryExpression): void {
    this.visitExpression(expr.argument);
  }

  visitBinaryExpression (expr: Syntax.BinaryExpression): void {
    this.visitExpression(expr.left);
    this.visitExpression(expr.right);
  }

  visitLogicalExpression (expr: Syntax.LogicalExpression): void {
    this.visitExpression(expr.left);
    this.visitExpression(expr.right);
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): void {
    this.visitExpression(expr.test);
    this.visitExpression(expr.consequent);
    this.visitExpression(expr.alternate);
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression): void {
    this.visitExpression(expr.left);
    this.visitExpression(expr.right);
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression): void {
    expr.expressions.forEach(e => this.visitExpression(e));
  }

  visitCallExpression (expr: Syntax.CallExpression): void {
    this.visitExpression(expr.callee);
    expr.args.forEach(e => this.visitExpression(e));
  }

  visitNewExpression (expr: Syntax.NewExpression): void {
    expr.args.forEach(e => this.visitExpression(e));
  }

  visitArrayExpression (expr: Syntax.ArrayExpression): void {
    expr.elements.forEach(e => this.visitExpression(e));
  }

  visitObjectExpression (expr: Syntax.ObjectExpression): void {
    expr.properties.forEach(({ value }) => this.visitExpression(value));
  }

  visitInstanceOfExpression (expr: Syntax.InstanceOfExpression): void {
    this.visitExpression(expr.left);
  }

  visitInExpression (expr: Syntax.InExpression): void {
    this.visitExpression(expr.property);
    this.visitExpression(expr.object);
  }

  visitMemberExpression (expr: Syntax.MemberExpression): void {
    this.visitExpression(expr.object);
    this.visitExpression(expr.property);
  }

  visitFunctionExpression (expr: Syntax.FunctionExpression): void {
    expr.requires.forEach(req => this.visitAssertion(req));
    expr.ensures.forEach(ens => this.visitPostCondition(ens));
    this.visitBlockStatement(expr.body);
  }

  visitVariableDeclaration (stmt: Syntax.VariableDeclaration): void {
    this.visitExpression(stmt.init);
  }

  visitBlockStatement (stmt: Syntax.BlockStatement): void {
    stmt.body.forEach(s => this.visitStatement(s));
  }

  visitExpressionStatement (stmt: Syntax.ExpressionStatement): void {
     this.visitExpression(stmt.expression);
  }

  visitAssertStatement (stmt: Syntax.AssertStatement): void {
    this.visitAssertion(stmt.expression);
  }

  visitIfStatement (stmt: Syntax.IfStatement): void {
    this.visitExpression(stmt.test);
    this.visitBlockStatement(stmt.consequent);
    this.visitBlockStatement(stmt.alternate);
  }

  visitReturnStatement (stmt: Syntax.ReturnStatement): void {
    this.visitExpression(stmt.argument);
  }

  visitWhileStatement (stmt: Syntax.WhileStatement): void {
    stmt.invariants.forEach(inv => this.visitAssertion(inv));
    this.visitExpression(stmt.test);
    this.visitBlockStatement(stmt.body);
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement): void { /* empty */ }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration): void {
    stmt.requires.forEach(req => this.visitAssertion(req));
    stmt.ensures.forEach(ens => this.visitPostCondition(ens));
    this.visitBlockStatement(stmt.body);
  }

  visitMethodDeclaration (stmt: Syntax.MethodDeclaration): void {
    stmt.requires.forEach(req => this.visitAssertion(req));
    stmt.ensures.forEach(ens => this.visitPostCondition(ens));
    this.visitBlockStatement(stmt.body);
  }

  visitClassDeclaration (stmt: Syntax.ClassDeclaration): void {
    this.visitAssertion(stmt.invariant);
    stmt.methods.forEach(method => this.visitMethodDeclaration(method));
  }

  visitProgram (prog: Syntax.Program): void {
    prog.invariants.forEach(a => this.visitAssertion(a));
    prog.body.forEach(s => this.visitStatement(s));
  }
}

/**
 * Substitutes variables in assertions/expressions with terms/expressions.
 */
export class Substituter extends Visitor<Syntax.Term, Syntax.Assertion, Syntax.Expression, Syntax.Statement> {

  thetaA: { [vname: string]: Syntax.Term } = {};
  thetaE: { [vname: string]: Syntax.Expression } = {};

  replaceVar (orig: string, term: Syntax.Term, expr: Syntax.Expression): Substituter {
    this.thetaA[orig] = term;
    this.thetaE[orig] = expr;
    return this;
  }

  withoutBindings<A> (cont: () => A, ...bindings: Array<string>): A {
    const origThetaA = Object.assign({}, this.thetaA);
    const origThetaE = Object.assign({}, this.thetaE);
    try {
      bindings.forEach(b => { delete this.thetaA[b]; delete this.thetaE[b]; });
      return cont();
    } finally {
      this.thetaA = origThetaA;
      this.thetaE = origThetaE;
    }
  }

  visitIdentifierTerm (term: Syntax.Identifier): Syntax.Term {
    return term.name in this.thetaA ? this.thetaA[term.name] : term;
  }

  visitOldIdentifierTerm (term: Syntax.OldIdentifier): Syntax.Term {
    const newId = this.visitIdentifier(term.id);
    if (newId.type !== 'Identifier') throw new Error('cannot substitute term below old()');
    return {
      type: 'OldIdentifier',
      id: newId,
      loc: term.loc
    };
  }

  visitLiteralTerm (term: Syntax.Literal): Syntax.Term {
    return term;
  }

  visitUnaryTerm (term: Syntax.UnaryTerm): Syntax.Term {
    return {
      type: 'UnaryTerm',
      operator: term.operator,
      argument: this.visitTerm(term.argument),
      loc: term.loc
    };
  }

  visitBinaryTerm (term: Syntax.BinaryTerm): Syntax.Term {
    return {
      type: 'BinaryTerm',
      operator: term.operator,
      left: this.visitTerm(term.left),
      right: this.visitTerm(term.right),
      loc: term.loc
    };
  }

  visitLogicalTerm (term: Syntax.LogicalTerm): Syntax.Term {
    return {
      type: 'LogicalTerm',
      operator: term.operator,
      left: this.visitTerm(term.left),
      right: this.visitTerm(term.right),
      loc: term.loc
    };
  }

  visitConditionalTerm (term: Syntax.ConditionalTerm): Syntax.Term {
    return {
      type: 'ConditionalTerm',
      test: this.visitTerm(term.test),
      consequent: this.visitTerm(term.consequent),
      alternate: this.visitTerm(term.alternate),
      loc: term.loc
    };
  }

  visitCallTerm (term: Syntax.CallTerm): Syntax.Term {
    return {
      type: 'CallTerm',
      callee: this.visitTerm(term.callee),
      args: term.args.map(e => this.visitTerm(e)),
      loc: term.loc
    };
  }

  visitMemberTerm (term: Syntax.MemberTerm): Syntax.Term {
    return {
      type: 'MemberTerm',
      object: this.visitTerm(term.object),
      property: this.visitTerm(term.property),
      loc: term.loc
    };
  }

  visitIsIntegerTerm (term: Syntax.IsIntegerTerm): Syntax.Term {
    return {
      type: 'IsIntegerTerm',
      term: this.visitTerm(term.term),
      loc: term.loc
    };
  }

  visitToIntegerTerm (term: Syntax.ToIntegerTerm): Syntax.Term {
    return {
      type: 'ToIntegerTerm',
      term: this.visitTerm(term.term),
      loc: term.loc
    };
  }

  visitTermAssertion (assertion: Syntax.Term): Syntax.Assertion {
    return this.visitTerm(assertion);
  }

  visitPureAssertion (assertion: Syntax.PureAssertion): Syntax.Assertion {
    return assertion;
  }

  visitPostCondition (post: Syntax.PostCondition): Syntax.PostCondition {
    return {
      argument: post.argument,
      expression: post.argument !== null
        ? this.withoutBindings(() => this.visitAssertion(post.expression), post.argument.name)
        : this.visitAssertion(post.expression),
      loc: post.loc
    };
  }

  visitSpecAssertion (assertion: Syntax.SpecAssertion): Syntax.Assertion {
    return {
      type: 'SpecAssertion',
      callee: this.visitTerm(assertion.callee),
      hasThis: assertion.hasThis,
      args: assertion.args,
      pre: this.withoutBindings(() => this.visitAssertion(assertion.pre), ...assertion.args),
      post: this.withoutBindings(() => this.visitPostCondition(assertion.post), ...assertion.args),
      loc: assertion.loc
    };
  }

  visitEveryAssertion (assertion: Syntax.EveryAssertion): Syntax.Assertion {
    return {
      type: 'EveryAssertion',
      array: this.visitTerm(assertion.array),
      argument: assertion.argument,
      indexArgument: assertion.indexArgument,
      expression: assertion.indexArgument !== null
        ? this.withoutBindings(() => this.visitAssertion(assertion.expression),
                               assertion.argument.name, assertion.indexArgument.name)
        : this.withoutBindings(() => this.visitAssertion(assertion.expression), assertion.argument.name),
      loc: assertion.loc
    };
  }

  visitInstanceOfAssertion (assertion: Syntax.InstanceOfAssertion): Syntax.Assertion {
    return {
      type: 'InstanceOfAssertion',
      left: this.visitTerm(assertion.left),
      right: assertion.right,
      loc: assertion.loc
    };
  }

  visitInAssertion (assertion: Syntax.InAssertion): Syntax.Assertion {
    return {
      type: 'InAssertion',
      property: this.visitTerm(assertion.property),
      object: this.visitTerm(assertion.object),
      loc: assertion.loc
    };
  }

  visitUnaryAssertion (assertion: Syntax.UnaryAssertion): Syntax.Assertion {
    return {
      type: 'UnaryAssertion',
      operator: assertion.operator,
      argument: this.visitAssertion(assertion.argument),
      loc: assertion.loc
    };
  }

  visitBinaryAssertion (assertion: Syntax.BinaryAssertion): Syntax.Assertion {
    return {
      type: 'BinaryAssertion',
      operator: assertion.operator,
      left: this.visitAssertion(assertion.left),
      right: this.visitAssertion(assertion.right),
      loc: assertion.loc
    };
  }

  visitIdentifier (expr: Syntax.Identifier): Syntax.Expression {
    return expr.name in this.thetaE ? this.thetaE[expr.name] : expr;
  }

  visitLiteral (expr: Syntax.Literal): Syntax.Expression {
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
      left: expr.left.type === 'Identifier' ? expr.left : {
        type: 'MemberExpression',
        object: this.visitExpression(expr.left.object),
        property: this.visitExpression(expr.left.property),
        loc: expr.left.loc
      },
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

  visitFunctionExpression (expr: Syntax.FunctionExpression): Syntax.FunctionExpression {
    const bindings = expr.id !== null
      ? [expr.id.name, ...expr.params.map(p => p.name)]
      : expr.params.map(p => p.name);
    return {
      type: 'FunctionExpression',
      id: expr.id,
      params: expr.params,
      requires: expr.requires.map(req =>
        this.withoutBindings(() => this.visitAssertion(req), ...bindings)),
      ensures: expr.ensures.map(ens =>
        this.withoutBindings(() => this.visitPostCondition(ens), ...bindings)),
      body: this.withoutBindings(() => this.visitBlockStatement(expr.body), ...bindings),
      freeVars: expr.freeVars,
      loc: expr.loc
    };
  }

  visitVariableDeclaration (stmt: Syntax.VariableDeclaration): Syntax.Statement {
    delete this.thetaA[stmt.id.name]; // gets restored at end of next block or function
    delete this.thetaE[stmt.id.name]; // gets restored at end of next block or function
    return {
      type: 'VariableDeclaration',
      id: stmt.id,
      init: this.visitExpression(stmt.init),
      kind: stmt.kind,
      loc: stmt.loc
    };
  }

  visitBlockStatement (stmt: Syntax.BlockStatement): Syntax.BlockStatement {
    return {
      type: 'BlockStatement',
      body: this.withoutBindings(() => stmt.body.map(s => this.visitStatement(s))),
      loc: stmt.loc
    };
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
      expression: this.visitAssertion(stmt.expression),
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
      invariants: stmt.invariants.map(inv => this.visitAssertion(inv)),
      test: this.visitExpression(stmt.test),
      body: this.visitBlockStatement(stmt.body),
      freeVars: stmt.freeVars,
      loc: stmt.loc
    };
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement): Syntax.Statement {
    return {
      type: 'DebuggerStatement',
      loc: stmt.loc
    };
  }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration): Syntax.FunctionDeclaration {
    delete this.thetaA[stmt.id.name]; // gets restored at end of next block or function
    delete this.thetaE[stmt.id.name]; // gets restored at end of next block or function
    const bindings = stmt.params.map(p => p.name);
    return {
      type: 'FunctionDeclaration',
      id: stmt.id,
      params: stmt.params,
      requires: stmt.requires.map(req =>
        this.withoutBindings(() => this.visitAssertion(req), ...bindings)),
      ensures: stmt.ensures.map(ens =>
        this.withoutBindings(() => this.visitPostCondition(ens), ...bindings)),
      body: this.withoutBindings(() => this.visitBlockStatement(stmt.body), ...bindings),
      freeVars: stmt.freeVars,
      loc: stmt.loc
    };
  }

  visitMethodDeclaration (stmt: Syntax.MethodDeclaration): Syntax.MethodDeclaration {
    const bindings = [...stmt.params.map(p => p.name)];
    return {
      type: 'MethodDeclaration',
      id: stmt.id,
      params: stmt.params,
      requires: stmt.requires.map(req =>
        this.withoutBindings(() => this.visitAssertion(req), ...bindings)),
      ensures: stmt.ensures.map(ens =>
        this.withoutBindings(() => this.visitPostCondition(ens), ...bindings)),
      body: this.withoutBindings(() => this.visitBlockStatement(stmt.body), ...bindings),
      freeVars: stmt.freeVars,
      className: stmt.className,
      loc: stmt.loc
    };
  }

  visitClassDeclaration (stmt: Syntax.ClassDeclaration): Syntax.Statement {
    delete this.thetaA[stmt.id.name]; // gets restored at end of next block or function
    delete this.thetaE[stmt.id.name];
    return this.withoutBindings((): Syntax.Statement => ({
      type: 'ClassDeclaration',
      id: stmt.id,
      fields: stmt.fields,
      invariant: this.visitAssertion(stmt.invariant),
      methods: stmt.methods.map(method => this.visitMethodDeclaration(method)),
      loc: stmt.loc
    }), 'this');
  }

  visitProgram (prog: Syntax.Program): Syntax.Statement {
    return {
      type: 'BlockStatement',
      body: prog.body.map(s => this.visitStatement(s)),
      loc: nullLoc()
    };
  }
}

export function replaceVarAssertion (varName: string, substA: Syntax.Term, substE: Syntax.Expression,
                                     assertion: Syntax.Assertion): Syntax.Assertion {
  const sub = new Substituter();
  sub.replaceVar(varName, substA, substE);
  return sub.visitAssertion(assertion);
}

export function replaceVarExpr (varName: string, substA: Syntax.Term, substE: Syntax.Expression,
                                expr: Syntax.Expression): Syntax.Expression {
  const sub = new Substituter();
  sub.replaceVar(varName, substA, substE);
  return sub.visitExpression(expr);
}

export function replaceVarFunction (varName: string, substA: Syntax.Term, substE: Syntax.Expression,
                                    f: Syntax.Function): Syntax.Function {
  const sub = new Substituter();
  sub.replaceVar(varName, substA, substE);
  switch (f.type) {
    case 'FunctionDeclaration': return sub.visitFunctionDeclaration(f);
    case 'FunctionExpression': return sub.visitFunctionExpression(f);
    case 'MethodDeclaration': return sub.visitMethodDeclaration(f);
  }
}

export function replaceVarStmt (varName: string, substA: Syntax.Term, substE: Syntax.Expression,
                                stmt: Syntax.Statement): Syntax.Statement {
  const sub = new Substituter();
  sub.replaceVar(varName, substA, substE);
  return sub.visitStatement(stmt);
}

export function replaceVarBlock (varName: string, substA: Syntax.Term, substE: Syntax.Expression,
                                 block: Syntax.BlockStatement): Syntax.BlockStatement {
  const sub = new Substituter();
  sub.replaceVar(varName, substA, substE);
  return sub.visitBlockStatement(block);
}

export function isValidAssignmentTarget (e: Syntax.Expression): e is (Syntax.Identifier | Syntax.MemberExpression) {
  return e.type === 'Identifier' || e.type === 'MemberExpression';
}

export function uniqueIdentifier (loc: Syntax.SourceLocation): number {
  return loc.start.column + loc.start.line * 37 +
         loc.end.column * 331 + loc.end.line * 5023 + loc.file.length * 48353;
}

export function removeTestCodePrefix (prefix: TestCode, code: TestCode): TestCode {
  let prefixLength = 0;
  while (prefix.length > prefixLength && code.length > prefixLength && prefix[prefixLength] === code[prefixLength]) {
    prefixLength++;
  }
  return code.slice(prefixLength);
}

export function copyId (id: Syntax.Identifier): Syntax.Identifier {
  return {
    type: 'Identifier',
    name: id.name,
    decl: id.decl,
    isWrittenTo: id.isWrittenTo,
    refs: id.refs,
    loc: id.loc
  };
}

class SourceLocationFinder extends Traverser {

  position: Syntax.Position;
  bestSourceLocation: Syntax.SourceLocation | null;

  constructor (position: Syntax.Position) {
    super();
    this.position = position;
    this.bestSourceLocation = null;
  }

  matchLocation (loc: Syntax.SourceLocation): void {
    if (loc.start.line > this.position.line) return;
    if (loc.start.line === this.position.line && loc.start.column > this.position.column) return;
    if (loc.end.line < this.position.line) return;
    if (loc.end.line === this.position.line && loc.end.column < this.position.column) return;
    if (this.bestSourceLocation === null) {
      this.bestSourceLocation = loc;
    } else {
      const prevScore = (this.bestSourceLocation.end.line - this.bestSourceLocation.start.line) * 120
       + this.bestSourceLocation.end.column - this.bestSourceLocation.start.column;
      const newScore = (loc.end.line - loc.start.line) * 120 + loc.end.column - loc.start.column;
      if (newScore <= prevScore) {
        this.bestSourceLocation = loc;
      }
    }
  }

  visitTerm (term: Syntax.Term): void {
    this.matchLocation(term.loc);
    super.visitTerm(term);
  }

  visitAssertion (assertion: Syntax.Assertion): void {
    this.matchLocation(assertion.loc);
    super.visitAssertion(assertion);
  }

  visitExpression (expression: Syntax.Expression): void {
    this.matchLocation(expression.loc);
    super.visitExpression(expression);
  }

  visitStatement (stmt: Syntax.Statement): void {
    this.matchLocation(stmt.loc);
    super.visitStatement(stmt);
  }
}

export function findSourceLocation (prog: Syntax.Program, position: Syntax.Position): Syntax.SourceLocation {
  const visitor = new SourceLocationFinder(position);
  visitor.visitProgram(prog);
  if (visitor.bestSourceLocation === null) {
    throw new Error('could not find any source location');
  }
  return visitor.bestSourceLocation;
}
