import { expect } from 'chai';
import { code, incorrect, unverified, verified, vcs } from './helpers';

declare const assert: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const requires: (x: boolean) => void;
declare const spec: (f: any, r: (rx: any) => boolean, s: (sx: any, sy: any) => boolean) => boolean;

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
