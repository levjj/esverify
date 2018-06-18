import { expect } from 'chai';
import { code, incorrect, unverified, verified, vcs } from './helpers';

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
    expect(vc.description).to.be.eql('f: (y > 3)');
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

  code(example());

  it('are added automatically', async () => {
    const vc = vcs()[0];
    expect(vc.getAssumptions()).to.have.length(1);
    expect(vc.getAssumptions()[0]).to.be.eql('Number.isInteger(x)');
  });

  it('can be added', async () => {
    const vc = vcs()[0];
    vc.addAssumption('x > 4');
    expect(vc.getAssumptions()).to.have.length(2);
    expect(vc.getAssumptions()[1]).to.be.eql('x > 4');
    const message = await vc.verify();
    expect(message.status).to.be.eql('verified');
  });
});

describe('assertion', () => {

  code(example());

  it('can be changed', async () => {
    const vc = vcs()[0];
    const vc2 = vc.assert('x >= 1 || x < 1');
    expect(vc2.description).to.be.eql('x >= 1 || x < 1');
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

describe('watches', () => {

  code(example());

  it('can be queried', async () => {
    const vc = vcs()[0];
    await vc.verify();
    vc.runWithInterpreter();
    const watches = vc.getWatches();
    expect(watches).to.have.length(2);
    const globalScope = watches[0];

    const fBinding = globalScope.find(([varname]) => varname === 'f');
    expect(fBinding).to.be.an('array');
    expect(fBinding).to.have.length(3);
    expect(fBinding[0]).to.be.eq('f');
    expect(fBinding[1]).to.be.a('function');
    expect(fBinding[2]).to.be.a('function');

    const xBinding = globalScope.find(([varname]) => varname === 'x');
    expect(xBinding).to.be.deep.eq(['x', 0, 0]);

    const customWatches = watches[1];
    expect(customWatches).to.have.length(0);
  });

  it('can be added', async () => {
    const vc = vcs()[0];
    await vc.verify();
    vc.runWithInterpreter();
    vc.addWatch('x + 1');
    const watches = vc.getWatches();
    expect(watches).to.have.length(2);
    const customWatches = watches[1];
    expect(customWatches).to.be.deep.eq([
      ['x + 1', 1, 1]
    ]);
  });
});

describe('execution', () => {

  code(example());

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
      [{ file: '', start: { line: 1, column: 13 }, end: { line: 1, column: 14 } }, [0], 0]
    ]);
  });
});
