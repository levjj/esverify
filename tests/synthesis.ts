import { expect } from 'chai';
import { code, incorrect, unverified, verified, vcs } from './helpers';

declare function assert (x: boolean): void;
declare function ensures (x: boolean | ((y: any) => boolean)): void;
declare function requires (x: boolean): void;
declare function spec (f: any, r: (rx: any) => boolean, s: (sx: any, sy: any) => boolean): boolean;

describe('function counter examples', () => {

  code(() => {
    function g1 (f) {
      requires(spec(f, () => true, y => y === 0));
      ensures(res => res === 1);

      return f();
    }

    function g2 (f) {
      requires(spec(f, x => true, (x, y) => true));
      requires(f(1) === 0);
      ensures(res => res === 1);

      return f(1);
    }

    function g3 (f) {
      requires(spec(f, x => x > 4, (x, y) => y === 23));
      ensures(res => res < 20);

      return f(5);
    }

  });

  verified('g1: precondition f()');
  incorrect('g1: (res === 1)');
  it('g1: (res === 1) returns counterexample', async () => {
    const m = await vcs()[1].verify();
    expect(m.description).to.eql('g1: (res === 1)');
    expect(m.status).to.equal('error');
    if (m.status !== 'error') throw new Error();
    expect(m.type).to.equal('incorrect');
    if (m.type !== 'incorrect') throw new Error();
    expect(m.model.variables()).to.include('f');
    const f = m.model.valueOf('f');
    expect(f.type).to.eql('fun');
    if (f.type !== 'fun') throw new Error();
    expect(f.body.id === null);
    expect(f.body.params).to.have.length(0);
    expect(f.body.body.body).to.have.length(1);
    const retStmt = f.body.body.body[0];
    expect(retStmt.type).to.eql('ReturnStatement');
    if (retStmt.type !== 'ReturnStatement') throw new Error();
    const arg = retStmt.argument;
    expect(arg.type).to.eql('Literal');
    if (arg.type !== 'Literal') throw new Error();
    expect(arg.value).to.eql(0);
  });
  verified('g2: precondition f(1)');
  incorrect('g2: (res === 1)');
  it('g2: (res === 1) returns counterexample', async () => {
    const m = await vcs()[3].verify();
    expect(m.description).to.eql('g2: (res === 1)');
    expect(m.status).to.equal('error');
    if (m.status !== 'error') throw new Error();
    expect(m.type).to.equal('incorrect');
    if (m.type !== 'incorrect') throw new Error();
    expect(m.model.variables()).to.include('f');
    const f = m.model.valueOf('f');
    expect(f.type).to.eql('fun');
    if (f.type !== 'fun') throw new Error();
    expect(f.body.id === null);
    expect(f.body.params).to.have.length(1);
    expect(f.body.params[0].name).to.eql('x_0');
    expect(f.body.body.body).to.have.length(2);

    const ifStmt = f.body.body.body[0];
    expect(ifStmt.type).to.eql('IfStatement');
    if (ifStmt.type !== 'IfStatement') throw new Error();
    const cond = ifStmt.test;
    expect(cond.type).to.eql('BinaryExpression');
    if (cond.type !== 'BinaryExpression') throw new Error();
    expect(cond.operator).to.eql('===');
    const condLeft = cond.left;
    expect(condLeft.type).to.eql('Identifier');
    if (condLeft.type !== 'Identifier') throw new Error();
    expect(condLeft.name).to.eql('x_0');
    const condRight = cond.right;
    expect(condRight.type).to.eql('Literal');
    if (condRight.type !== 'Literal') throw new Error();
    expect(condRight.value).to.eql(1);

    expect(ifStmt.consequent.body).to.have.length(1);
    const thenStmt = ifStmt.consequent.body[0];
    expect(thenStmt.type).to.eql('ReturnStatement');
    if (thenStmt.type !== 'ReturnStatement') throw new Error();
    const thenArg = thenStmt.argument;
    expect(thenArg.type).to.eql('Literal');
    if (thenArg.type !== 'Literal') throw new Error();
    expect(thenArg.value).to.eql(0);

    expect(ifStmt.alternate.body).to.have.length(0);

    const retStmt = f.body.body.body[1];
    expect(retStmt.type).to.eql('ReturnStatement');
    if (retStmt.type !== 'ReturnStatement') throw new Error();
    const arg = retStmt.argument;
    expect(arg.type).to.eql('Literal');
    if (arg.type !== 'Literal') throw new Error();
    expect(arg.value).to.eql(undefined);
  });
  verified('g3: precondition f(5)');
  incorrect('g3: (res < 20)');
  it('g3: (res < 20) returns counterexample', async () => {
    const m = await vcs()[5].verify();
    expect(m.description).to.eql('g3: (res < 20)');
    expect(m.status).to.equal('error');
    if (m.status !== 'error') throw new Error();
    expect(m.type).to.equal('incorrect');
    if (m.type !== 'incorrect') throw new Error();
    expect(m.model.variables()).to.include('f');
    const f = m.model.valueOf('f');
    expect(f.type).to.eql('fun');
    if (f.type !== 'fun') throw new Error();
    expect(f.body.id === null);
    expect(f.body.params).to.have.length(1);
    expect(f.body.params[0].name).to.eql('x_0');
    expect(f.body.body.body).to.have.length(2);

    const ifStmt = f.body.body.body[0];
    expect(ifStmt.type).to.eql('IfStatement');
    if (ifStmt.type !== 'IfStatement') throw new Error();
    const cond = ifStmt.test;
    expect(cond.type).to.eql('BinaryExpression');
    if (cond.type !== 'BinaryExpression') throw new Error();
    expect(cond.operator).to.eql('===');
    const condLeft = cond.left;
    expect(condLeft.type).to.eql('Identifier');
    if (condLeft.type !== 'Identifier') throw new Error();
    expect(condLeft.name).to.eql('x_0');
    const condRight = cond.right;
    expect(condRight.type).to.eql('Literal');
    if (condRight.type !== 'Literal') throw new Error();
    expect(condRight.value).to.eql(5);

    expect(ifStmt.consequent.body).to.have.length(1);
    const thenStmt = ifStmt.consequent.body[0];
    expect(thenStmt.type).to.eql('ReturnStatement');
    if (thenStmt.type !== 'ReturnStatement') throw new Error();
    const thenArg = thenStmt.argument;
    expect(thenArg.type).to.eql('Literal');
    if (thenArg.type !== 'Literal') throw new Error();
    expect(thenArg.value).to.eql(23);

    expect(ifStmt.alternate.body).to.have.length(0);

    const retStmt = f.body.body.body[1];
    expect(retStmt.type).to.eql('ReturnStatement');
    if (retStmt.type !== 'ReturnStatement') throw new Error();
    const arg = retStmt.argument;
    expect(arg.type).to.eql('Literal');
    if (arg.type !== 'Literal') throw new Error();
    expect(arg.value).to.eql(undefined);
  });
});

describe('function spec enforced in test', () => {

  code(() => {
    function g1 (f) {
      requires(spec(f, x => x > 4, (x, y) => true));
      f(4);
    }

    function g2 (f) {
      requires(spec(f, x => true, (x, y) => y > 4));
      const z = f(23);
      assert(z > 5);
    }

    g2(() => 3);
  });

  incorrect('g1: precondition f(4)');
  verified('g2: precondition f(23)');
  incorrect('g2: assert: (z > 5)');
  incorrect('precondition g2(() => 3)');
});

describe('higher-order function spec enforced in test', () => {

  code(() => {
    function g (f) {
      requires(spec(f, () => true, y => spec(y, x => x > 0, (x, z) => true)));

      const y = f();
      y(0);
    }
  });

  verified('g: precondition f()');
  incorrect('g: precondition y(0)');
});

describe('asserting function spec generates call', () => {

  code(() => {
    function f (x) {
      requires(x > 2);
    }
    assert(spec(f, x => x > 1, (x, y) => true));
  });

  incorrect('assert: spec(f, x => (x > 1), (x, y) => true)', ['x', 2]);
});
