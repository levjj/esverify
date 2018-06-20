import { expect } from 'chai';
import { code, incorrect, unverified, verified, vcs } from './helpers';
import { valueToString } from '../src';

declare function ensures (x: boolean | ((y: any) => boolean)): void;
declare function requires (x: boolean): void;

const example = () => {
  return () => {
    function f (x) {
      requires(Number.isInteger(x));
      ensures(y => y > 3);
      return x;
    }
  };
};

describe('description', () => {

  code(example());

  it('included in verification conditions', () => {
    const verificationConditions = vcs();
    expect(verificationConditions).to.have.length(1);
    const vc = verificationConditions[0];
    expect(vc.getDescription()).to.be.eql('f: (y > 3)');
  });
});

describe('verification', () => {

  code(example());

  it('returns message', async () => {
    const vc = vcs()[0];
    const message = await vc.verify();
    expect(message.status).to.be.eql('error');
    if (message.status !== 'error') { throw new Error(); }
    expect(message.type).to.be.eql('incorrect');
    expect(message.description).to.be.eql('f: (y > 3)');
    expect(message.loc).to.be.deep.eq({
      file: '',
      start: { line: 3, column: 20 },
      end: { line: 3, column: 30 }
    });
  });
});

describe('assumptions', () => {

  code(example(), true);

  it('are added automatically', async () => {
    const vc = vcs()[0];
    expect(vc.getAssumptions()).to.have.length(1);
    expect(vc.getAssumptions()[0]).to.be.deep.eq(['Number.isInteger(x)', false]);
  });

  it('can be added', async () => {
    const vc = vcs()[0];
    vc.addAssumption('x > 4');
    expect(vc.getAssumptions()).to.have.length(2);
    expect(vc.getAssumptions()[1]).to.be.deep.eq(['x > 4', true]);
    const message = await vc.verify();
    expect(message.status).to.be.eql('verified');
  });

  it('can be removed', async () => {
    const vc = vcs()[0];
    vc.addAssumption('x > 4');
    let message = await vc.verify();
    expect(message.status).to.be.eql('verified');
    vc.removeAssumption(1);
    expect(vc.getAssumptions()).to.have.length(1);
    message = await vc.verify();
    expect(message.status).to.be.eql('error');
    if (message.status !== 'error') { throw new Error(); }
    expect(message.type).to.be.eql('incorrect');
  });

  it('cannot be removed if non-existing', async () => {
    const vc = vcs()[0];
    expect(() => {
      vc.removeAssumption(2);
    }).to.throw('no such assumption');
  });

  it('cannot be removed if builtin', async () => {
    const vc = vcs()[0];
    expect(() => {
      vc.removeAssumption(0);
    }).to.throw('cannot remove built-in assumptions');
  });
});

describe('assertion', () => {

  code(example());

  it('can be changed', async () => {
    const vc = vcs()[0];
    const vc2 = vc.assert('x >= 1 || x < 1');
    expect(vc2.getDescription()).to.be.eql('x >= 1 || x < 1');
    expect(vc2.getAssumptions()).to.have.length(1);
    const message = await vc2.verify();
    expect(message.status).to.be.eql('verified');
  });
});

describe('trace', () => {

  code(example());

  it('can be obtained', async () => {
    const vc = vcs()[0];
    await vc.verify();
    const message = vc.runWithInterpreter();
    expect(message.status).to.be.eql('error');
    if (message.status !== 'error') { throw new Error(); }
    expect(message.type).to.be.eql('incorrect');
    expect(message.description).to.be.eql('f: (y > 3)');
    expect(vc.steps()).to.be.eq(19);
    expect(vc.pc()).to.be.deep.eq({
      file: '',
      start: { line: 3, column: 25 },
      end: { line: 3, column: 30 }
    });
    expect(vc.iteration()).to.be.eq(0);
    expect(vc.callstack()).to.be.deep.eq([['<program> (:3:25)', {
      file: '',
      start: { line: 3, column: 25 },
      end: { line: 3, column: 30 }
    }, 0]]);
  });
});

describe('scopes', () => {

  code(example(), true);

  it('can be queried', async () => {
    const vc = vcs()[0];
    await vc.verify();
    vc.runWithInterpreter();
    const scopes = vc.getScopes();
    expect(scopes).to.have.length(1);
    const globalScope = scopes[0];

    const fBinding = globalScope.find(([varname]) => varname === 'f');
    expect(fBinding).to.be.an('array');
    expect(fBinding).to.have.length(3);
    expect(fBinding[0]).to.be.eq('f');
    expect(fBinding[1].type).to.be.eq('fun');
    expect(fBinding[2].type).to.be.eq('fun');
    expect(valueToString(fBinding[1])).to.be.eq('function f (x) {\n  return x;\n}');
    expect(valueToString(fBinding[2])).to.be.eq(
      'function (x_0) {\n  if ((x_0 === 0)) {\n    return 0;\n  }\n  return 0;\n}');

    const xBinding = globalScope.find(([varname]) => varname === 'x');
    expect(xBinding).to.be.deep.eq(['x', { type: 'num', v: 0 }, { type: 'num', v: 0 }]);
    expect(valueToString(xBinding[1])).to.be.eq('0');
  });
});

describe('watches', () => {

  code(example(), true);

  it('can be queried', async () => {
    const vc = vcs()[0];
    await vc.verify();
    vc.runWithInterpreter();
    const watches = vc.getWatches();
    expect(watches).to.have.length(0);
  });

  it('can be added', async () => {
    const vc = vcs()[0];
    await vc.verify();
    vc.runWithInterpreter();
    vc.addWatch('x + 1');
    const watches = vc.getWatches();
    expect(watches).to.have.length(1);
    expect(watches).to.be.deep.eq([
      ['x + 1', { type: 'num', v: 1 }, { type: 'num', v: 1 }]
    ]);
  });
});

describe('execution', () => {

  code(example(), true);

  it('can be stepped', async () => {
    const vc = vcs()[0];
    await vc.verify();
    vc.runWithInterpreter();
    vc.restart();
    expect(vc.pc()).to.be.deep.eq({
      file: '',
      start: { line: 1, column: 2 },
      end: { line: 5, column: 9 }
    });
    vc.stepInto();
    expect(vc.pc()).to.be.deep.eq({
      file: '',
      start: { line: 1, column: 13 },
      end: { line: 1, column: 14 }
    });
    vc.stepInto();
    expect(vc.pc()).to.be.deep.eq({
      file: '',
      start: { line: 4, column: 19 },
      end: { line: 4, column: 20 }
    });
    vc.stepInto();
    expect(vc.pc()).to.be.deep.eq({
      file: '',
      start: { line: 4, column: 12 },
      end: { line: 4, column: 21 }
    });
  });

  it('allows navigation', async () => {
    const vc = vcs()[0];
    await vc.verify();
    vc.runWithInterpreter();
    vc.goto({ line: 4, column: 19 });
    expect(vc.pc()).to.be.deep.eq({
      file: '',
      start: { line: 4, column: 19 },
      end: { line: 4, column: 20 }
    });
  });
});

describe('annotations', () => {

  code(example());

  it('are added automatically', async () => {
    const vc = vcs()[0];
    await vc.verify();
    vc.runWithInterpreter();
    expect(vc.getAnnotations()).to.be.deep.eq([
      [
        { file: '', start: { line: 1, column: 13 }, end: { line: 1, column: 14 } },
        [{ type: 'num', v: 0 }],
        { type: 'num', v: 0 }
      ]
    ]);
  });
});
