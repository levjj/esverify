import { stringify } from "lively.ast";
import { nodes } from "lively.ast";
const { funcExpr } = nodes;
import { arr } from "lively.lang";
import * as normalizer from "../generated/jswala.js";

/// <reference path="../typings/mozilla-spidermonkey-parser-api.d.ts"/>
import { Syntax } from "spiderMonkeyParserAPI";

import Theorem from "./theorems";
import { isAssertion, replaceFunctionResult, replaceResultFunction, findDefs } from "./visitors";

export class VerificationScope {

  scopes: Array<VerificationScope>;
  parent: VerificationScope;
  node: Syntax.Node;
  
  constructor(parent: VerificationScope | null, node: Syntax.Node) {
    if (parent) {
      parent.scopes.push(this);
      this.parent = parent;
    }
    this.scopes = [];
    this.node = node;
  }
  
  requires(): Array<Syntax.Expression> {
    throw new Error("not implemented");
  }
  
  assumes(): Array<Syntax.Expression> {
    throw new Error("not implemented");
  }
  
  body(): Array<Syntax.Statement> {
    throw new Error("not implemented");
  }
  
  toProve(): Array<Syntax.Expression> {
    return this.invariants();
  }
  
  describe(post: Syntax.Expression): string {
    throw new Error("not implemented");
  }
  
  describeReq(): string {
    return "assert";
  }
  
  theorems(): Array<Theorem> {
    const vars = this.surroundingVars(),
          pre = this.assumes(),
          body = this.statements(),
          theorems = this.toProve().map(pc =>
            new Theorem(vars, pre, body, pc, this.describe(pc))),
          partials = this.immediates().concat(this.subRequirements()).map(([type, pc, part]) =>
            new Theorem(vars, pre, part, pc, `${type}:\n${stringify(pc)}`));
    return theorems.concat(partials).concat(arr.flatmap(this.scopes, (s: VerificationScope) => s.theorems()));
  }
  
  vars(): Array<string> {
    return findDefs(this.node).concat(this.surroundingVars());
  }
  
  surroundingVars(): Array<string> {
    return this.parent ? this.parent.vars() : [];
  }
  
  statements(): Array<Syntax.Statement> {
    return this.body().filter(stmt => !isAssertion(stmt));
  }
  
  assertions(): Array<Syntax.CallExpression> {
    return this.body().filter(isAssertion).map(stmt => stmt.expression);
  }
  
  upToExpr(expr: Syntax.Expression): Array<Syntax.ExpressionStatement> {
    return arr.takeWhile(this.body(), (stmt: Syntax.ExpressionStatement) => stmt.expression !== expr)
              .filter((stmt: Syntax.ExpressionStatement) => !isAssertion(stmt));
  }
  
  upToStmt(stmt: Syntax.Statement): Array<Syntax.Statement> {
    return arr.takeWhile(this.body(), (s: Syntax.Statement) => s !== stmt)
              .filter((s: Syntax.Statement) => !isAssertion(s));
  }

  immediates(): Array<[string, Syntax.Expression, Array<Syntax.ExpressionStatement>]> {
    return this.assertions()
      .filter(expr => expr.callee.name == "assert")
      .map(expr => ["assert", expr.arguments[0], this.upToExpr(expr)]);
  }
  
  subRequirements(): Array<[string, Syntax.Expression, Array<Syntax.ExpressionStatement>]> {
    return arr.flatmap(
      this.scopes,
      (scope: VerificationScope) => scope.requires().map(expr => [scope.describeReq(), expr, this.upToStmt(scope.node)]));
  }
  
  invariants(): Array<Syntax.Expression> {
    const pi = this.parent ? this.parent.invariants() : [];
    return pi.concat(this.assertions()
      .filter(expr => expr.callee.name == "invariant")
      .map(expr => expr.arguments[0]));
  }
  
}

export class FunctionScope extends VerificationScope {

  node: Syntax.FunctionExpression;
  
  requires(): Array<Syntax.Expression> {
    return [];
  }
  
  assumes(): Array<Syntax.Expression> {
    return this.preConditions().concat(this.parent.invariants());
  }

  body(): Array<Syntax.Statement> {
    return this.node.body.body;
  }
  
  toProve(): Array<Syntax.Expression> {
    return super.toProve().concat(this.postConditions().map(pc => {
      return replaceFunctionResult(this.node, pc);
    }));
  }
  
  describe(post: Syntax.Expression): string {
    const replaced = replaceResultFunction(this.node, post);
    return `${this.node.id.name}:\n${stringify(replaced)}`;
  }

  surroundingVars(): Array<string> {
    return super.surroundingVars().concat(this.node.params.map(p => p.name));
  }

  preConditions(): Array<Syntax.Expression> {
    return this.assertions()
      .filter(expr => expr.callee.name == "requires")
      .map(expr => expr.arguments[0]);
  }
  
  postConditions(): Array<Syntax.Expression> {
    return this.assertions()
      .filter(expr => expr.callee.name == "ensures")
      .map(expr => expr.arguments[0]);
  }
  
}

export class ClassScope extends VerificationScope {
}

export class LoopScope extends VerificationScope {

  node: Syntax.WhileStatement;
  
  requires(): Array<Syntax.Expression> {
    return this.invariants();
  }

  assumes(): Array<Syntax.Expression> {
    return this.invariants().concat([this.node.test]);
  }
  
  body(): Array<Syntax.Statement> {
    return this.node.body.body;
  }
  
  describe(post: Syntax.Expression): string {
    return `loop invariant:\n${stringify(post)}`;
  }
  
  describeReq(): string {
    return "loop entry";
  }

}

export class TopLevelScope extends VerificationScope {

  node: Syntax.Program;
  
  constructor(node: Syntax.Program) {
    super(null, node);
  }
  
  requires(): Array<Syntax.Expression> {
    return [];
  }

  assumes(): Array<Syntax.Expression> {
    return [];
  }
  
  body(): Array<Syntax.Statement> {
    return this.node.body;
  }

  describe(post: Syntax.Expression): string {
    return `initially:\n${stringify(post)}`;
  }
  
}
