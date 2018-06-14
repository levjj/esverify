import { Syntax, Visitor } from './javascript';

class Stringifier extends Visitor<string, string, string, string> {

  depth: number = 0;

  formatBlock (stmts: Array<Syntax.Statement | string>): string {
    let res = '{\n';
    this.indent(() => {
      for (const s of stmts) {
        res += typeof s === 'string' ? this.i(s) : this.visitStatement(s);
      }
    });
    return res + this.i('}');
  }

  visitIdentifierTerm (term: Syntax.Identifier): string {
    return term.name;
  }

  visitOldIdentifierTerm (term: Syntax.OldIdentifier): string {
    return `old(${term.id.name})`;
  }

  visitLiteralTerm (term: Syntax.Literal): string {
    return term.value === undefined ? 'undefined' : JSON.stringify(term.value);
  }

  visitUnaryTerm (term: Syntax.UnaryTerm): string {
    switch (term.operator) {
      case 'typeof':
      case 'void':
        return `${term.operator}(${this.visitTerm(term.argument)})`;
      default:
        return `${term.operator}${this.visitTerm(term.argument)}`;
    }
  }

  visitBinaryTerm (term: Syntax.BinaryTerm): string {
    return `(${this.visitTerm(term.left)} ${term.operator} ${this.visitTerm(term.right)})`;
  }

  visitLogicalTerm (term: Syntax.LogicalTerm): string {
    return `(${this.visitTerm(term.left)} ${term.operator} ${this.visitTerm(term.right)})`;
  }

  visitConditionalTerm (term: Syntax.ConditionalTerm): string {
    return `(${this.visitTerm(term.test)} ? ${this.visitTerm(term.consequent)} ` +
                                         `: ${this.visitTerm(term.alternate)})`;
  }

  visitCallTerm (term: Syntax.CallTerm): string {
    return `${this.visitTerm(term.callee)}(${term.args.map(a => this.visitTerm(a)).join(', ')})`;
  }

  visitMemberTerm (term: Syntax.MemberTerm): string {
    if (term.property.type === 'Literal' &&
        typeof term.property.value === 'string' &&
        /^[a-zA-Z_]+$/.test(term.property.value)) {
      return `${this.visitTerm(term.object)}.${term.property.value}`;
    } else {
      return `${this.visitTerm(term.object)}[${this.visitTerm(term.property)}]`;
    }
  }

  visitIsIntegerTerm (term: Syntax.IsIntegerTerm): string {
    return `Number.isInteger(${this.visitTerm(term.term)})`;
  }

  visitToIntegerTerm (term: Syntax.ToIntegerTerm): string {
    return `Math.trunc(${this.visitTerm(term.term)})`;
  }

  visitTermAssertion (assertion: Syntax.Term): string {
    return this.visitTerm(assertion);
  }

  visitPostCondition (post: Syntax.PostCondition): string {
    if (post.argument) {
      return `${this.visitTerm(post.argument)} => ${this.visitAssertion(post.expression)}`;
    }
    return this.visitAssertion(post.expression);
  }

  visitParams (params: Array<string>): string {
    if (params.length === 1) return params[0];
    return `(${params.join(', ')})`;
  }

  visitSpecAssertion (assertion: Syntax.SpecAssertion): string {
    if (assertion.post.argument) {
      return `spec(${this.visitTerm(assertion.callee)}, ` +
                  `${this.visitParams(assertion.args)} => ${this.visitAssertion(assertion.pre)}, ` +
                  `${this.visitParams([...assertion.args, assertion.post.argument.name])} => ` +
                     `${this.visitAssertion(assertion.post.expression)})`;
    }
    return `spec(${this.visitTerm(assertion.callee)}, ` +
                `${this.visitParams(assertion.args)} => ${this.visitAssertion(assertion.pre)}, ` +
                `${this.visitParams(assertion.args)} => ${this.visitAssertion(assertion.post.expression)})`;
  }

  visitEveryAssertion (assertion: Syntax.EveryAssertion): string {
    if (assertion.indexArgument !== null) {
      return `${this.visitTerm(assertion.array)}.every(` +
                   `(${assertion.argument.name}, ${assertion.indexArgument.name}) => ` +
                   `${this.visitAssertion(assertion.expression)})`;
    } else {
      return `${this.visitTerm(assertion.array)}.every(` +
                   `${assertion.argument.name} => ${this.visitAssertion(assertion.expression)})`;
    }
  }

  visitPureAssertion (assertion: Syntax.PureAssertion): string {
    return `pure()`;
  }

  visitInstanceOfAssertion (assertion: Syntax.InstanceOfAssertion): string {
    return `(${this.visitTerm(assertion.left)} instanceof ${assertion.right.name})`;
  }

  visitInAssertion (assertion: Syntax.InAssertion): string {
    return `(${this.visitTerm(assertion.property)} in ${this.visitTerm(assertion.object)})`;
  }

  visitUnaryAssertion (assertion: Syntax.UnaryAssertion) {
    return `!${this.visitAssertion(assertion.argument)}`;
  }

  visitBinaryAssertion (assertion: Syntax.BinaryAssertion): string {
    return `(${this.visitAssertion(assertion.left)} ${assertion.operator} ${this.visitAssertion(assertion.right)})`;
  }

  visitIdentifier (expr: Syntax.Identifier): string {
    return expr.name;
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
    return `(${this.visitExpression(expr.left)} ${expr.operator} ${this.visitExpression(expr.right)})`;
  }

  visitConditionalExpression (expr: Syntax.ConditionalExpression): string {
    return `(${this.visitExpression(expr.test)} ? ${this.visitExpression(expr.consequent)} ` +
                                               `: ${this.visitExpression(expr.alternate)})`;
  }

  visitAssignmentExpression (expr: Syntax.AssignmentExpression): string {
    return `${this.visitExpression(expr.left)} = ${this.visitExpression(expr.right)}`;
  }

  visitSequenceExpression (expr: Syntax.SequenceExpression): string {
    return `(${expr.expressions.map(e => this.visitExpression(e)).join(', ')})`;
  }

  visitCallExpression (expr: Syntax.CallExpression): string {
    return `${this.visitExpression(expr.callee)}(${expr.args.map(a => this.visitExpression(a)).join(', ')})`;
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
    if (expr.id === null && expr.body.body.length === 1 && expr.body.body[0].type === 'ReturnStatement' &&
        expr.requires.length === 0 && expr.ensures.length === 0) {
      const retStmt = expr.body.body[0] as Syntax.ReturnStatement;
      return `${this.visitParams(expr.params.map(p => p.name))} => ${this.visitExpression(retStmt.argument)}`;
    }
    const body: Array<string | Syntax.Statement> = ([] as Array<string | Syntax.Statement>)
      .concat(expr.requires.map(req => `requires(${this.visitAssertion(req)});`))
      .concat(expr.ensures.map(ens => `ensures(${this.visitPostCondition(ens)});`))
      .concat(expr.body.body);
    return `(function ${expr.id ? expr.id.name + ' ' : ''}(${expr.params.map(p => p.name).join(', ')}) ` +
            `${this.formatBlock(body)})`;
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

  visitBlockStatement (stmt: Syntax.BlockStatement): string {
    return this.i(this.formatBlock(stmt.body)) + '\n';
  }

  visitExpressionStatement (stmt: Syntax.ExpressionStatement): string {
    return this.i(`${this.visitExpression(stmt.expression)};\n`);
  }

  visitAssertStatement (stmt: Syntax.AssertStatement): string {
    return this.i(`assert(${this.visitAssertion(stmt.expression)});\n`);
  }

  visitIfStatement (stmt: Syntax.IfStatement): string {
    if (stmt.alternate.body.length === 0) {
      return this.i(`if (${this.visitExpression(stmt.test)}) ` +
                    `${this.formatBlock(stmt.consequent.body)}\n`);
    } else {
      return this.i(`if (${this.visitExpression(stmt.test)}) ` +
                    `${this.formatBlock(stmt.consequent.body)} else ` +
                    `${this.formatBlock(stmt.alternate.body)}\n`);
    }
  }

  visitReturnStatement (stmt: Syntax.ReturnStatement): string {
    return this.i(`return ${this.visitExpression(stmt.argument)};\n`);
  }

  visitWhileStatement (stmt: Syntax.WhileStatement): string {
    return this.i(`while (${this.visitExpression(stmt.test)}) ${this.formatBlock(stmt.body.body)}\n`);
  }

  visitDebuggerStatement (stmt: Syntax.DebuggerStatement): string {
    return this.i(`debugger;\n`);
  }

  visitFunctionDeclaration (stmt: Syntax.FunctionDeclaration): string {
    const body: Array<string | Syntax.Statement> = ([] as Array<string | Syntax.Statement>)
      .concat(stmt.requires.map(req => `requires(${this.visitAssertion(req)});`))
      .concat(stmt.ensures.map(ens => `ensures(${this.visitPostCondition(ens)});`))
      .concat(stmt.body.body);
    return this.i(`function ${stmt.id.name} (${stmt.params.map(p => p.name).join(', ')}) ` +
                  `${this.formatBlock(body)}\n`);
  }

  visitClassDeclaration (stmt: Syntax.ClassDeclaration): string {
    let res = this.i(`class ${stmt.id.name} {\n`);
    this.depth++;
    res += this.i(`constructor(${stmt.fields.join(', ')}) {\n`);
    this.depth++;
    for (const f of stmt.fields) {
      res += this.i(`this.${f} = ${f};\n`);
    }
    this.depth--;
    res += this.i(`}\n`);
    if (stmt.invariant.type !== 'Literal' || stmt.invariant.value !== true) {
      res += this.i(`invariant(${stmt.fields.join(', ')}) {\n`);
      this.depth++;
      res += this.i(`return ${this.visitAssertion(stmt.invariant)};\n`);
      this.depth--;
      res += this.i(`}\n`);
    }
    stmt.methods.forEach(method => {
      const body: Array<string | Syntax.Statement> = ([] as Array<string | Syntax.Statement>)
        .concat(method.requires.map(req => `requires(${this.visitAssertion(req)});`))
        .concat(method.ensures.map(ens => `ensures(${this.visitPostCondition(ens)});`))
        .concat(method.body.body);
      res += this.i(`${method.id.name} (${method.params.map(p => p.name).join(', ')}) ` +
                    `${this.formatBlock(body)}\n`);
    });
    this.depth--;
    res += this.i(`}\n`);
    return res;
  }

  visitProgram (prog: Syntax.Program) {
    return prog.body.map(s => this.visitStatement(s)).join('');
  }
}

export function stringifyAssertion (assertion: Syntax.Assertion): string {
  return (new Stringifier()).visitAssertion(assertion);
}

export function stringifyExpression (expr: Syntax.Expression): string {
  return (new Stringifier()).visitExpression(expr);
}

export const TEST_PREAMBLE = `function assert (p) { if (!p) throw new Error("assertion failed"); }
function spec (f, id, req, ens) {
  if (f._mapping) {
    f._mapping[id] = [req, ens];
    return f;
  } else {
    const mapping = { [id]: [req, ens] };
    const wrapped = function (...args) {
      return Object.values(mapping).reduceRight(function (cont, [req, ens]) {
        return function (...args2) {
          const args3 = req.apply(this, args2);
          return ens.apply(this, args3.concat([cont.apply(this, args3)]));
        };
      }, f).apply(this, args);
    };
    wrapped._mapping = mapping;
    return wrapped;
  }
}
`;

export function stringifyTestCode (body: ReadonlyArray<Syntax.Statement>): string {
  const stringifier = new Stringifier();
  return `${TEST_PREAMBLE}

${body.map(s => stringifier.visitStatement(s)).join('\n')}`;
}
