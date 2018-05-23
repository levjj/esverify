import { expect } from 'chai';
import { verificationConditions } from '../src';
import { FreeVar } from '../src/logic';
import { log } from '../src/message';
import { plainToJSVal } from '../src/model';
import { setOptions } from '../src/options';
import VerificationCondition from '../src/verification';

declare const assert: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const invariant: (x: boolean) => void;
declare const old: (x: any) => any;
declare const pure: () => boolean;
declare const requires: (x: boolean) => void;
declare const spec: (f: any, r: (rx: any) => boolean, s: (sx: any, sy: any) => boolean) => boolean;

let savedVCs: Array<VerificationCondition>;

export function vcs (): Array<VerificationCondition> {
  return savedVCs;
}

export function code (fn: () => any) {
  before(() => {
    const code = fn.toString();
    const t = verificationConditions(code.substring(14, code.length - 2));
    if (!(t instanceof Array)) {
      log(t);
      if (t.status === 'error' && t.type === 'unexpected') console.log(t.error);
      throw new Error('failed to find verification conditions');
    }
    savedVCs = t;
  });
}

function helper (expected: 'verified' | 'unverified' | 'incorrect' | 'timeout', description: string,
                 debug: boolean, expectedModel: Map<FreeVar, any>): Mocha.ITest {
  const body = async () => {
    /* tslint:disable:no-unused-expression */
    if (debug) {
      setOptions({ quiet: false, verbose: true, timeout: 60 });
      console.log(savedVCs.map(vc => vc.description).join('\n'));
    }
    const vc = savedVCs.find(v => v.description === description);
    expect(vc).to.be.ok;
    const res = await vc.verify();
    if (res.status === 'error' && debug) console.log(res);
    if (expected === 'verified' || expected === 'unverified') {
      const st = res.status === 'error' && res.type === 'incorrect' ? res.type : res.status;
      expect(st).to.be.eql(expected);
      if (res.status === 'unverified') {
        for (const v of expectedModel.keys()) {
          expect(res.model.variables()).to.include(typeof v === 'string' ? v : v.name);
          expect(res.model.valueOf(v)).to.eql(plainToJSVal(expectedModel.get(v)));
        }
      }
    } else if (expected === 'timeout') {
      expect(res.status).to.eql('timeout');
    } else {
      expect(res.status).to.equal('error');
      if (res.status === 'error') {
        expect(res.type).to.equal(expected);
        if (res.type === 'incorrect') {
          for (const v of expectedModel.keys()) {
            expect(res.model.variables()).to.include(typeof v === 'string' ? v : v.name);
            expect(res.model.valueOf(v)).to.eql(plainToJSVal(expectedModel.get(v)));
          }
        }
      }
    }
  };
  if (debug) {
    return it.only(description + ' ' + expected, body).timeout(60000);
  } else {
    return it(description + ' ' + expected, body);
  }
}

export function skip (description: string) { return it.skip(description); }

interface VerifiedFun {
  (description: string): Mocha.ITest;
  debug: (description: string) => Mocha.ITest;
}
interface UnverifiedFun {
  (description: string, ...expectedVariables: Array<[FreeVar, any]>): Mocha.ITest;
  debug: (description: string, ...expectedVariables: Array<[FreeVar, any]>) => Mocha.ITest;
}

export const verified: VerifiedFun = (() => {
  const f: any = (description: string): Mocha.ITest => helper('verified', description, false, new Map());
  f.debug = (description: string): Mocha.ITest => helper('verified', description, true, new Map());
  return f;
})();

export const unverified: UnverifiedFun = (() => {
  const f: any = (description: string, ...expectedVariables: Array<[FreeVar, any]>): Mocha.ITest =>
    helper('unverified', description, false, new Map(expectedVariables));
  f.debug = (description: string, ...expectedVariables: Array<[FreeVar, any]>): Mocha.ITest =>
    helper('unverified', description, true, new Map(expectedVariables));
  return f;
})();

export const incorrect: UnverifiedFun = (() => {
  const f: any = (description: string, ...expectedVariables: Array<[FreeVar, any]>): Mocha.ITest =>
    helper('incorrect', description, false, new Map(expectedVariables));
  f.debug = (description: string, ...expectedVariables: Array<[FreeVar, any]>): Mocha.ITest =>
    helper('incorrect', description, true, new Map(expectedVariables));
  return f;
})();

export const timeout: VerifiedFun = (() => {
  const f: any = (description: string): Mocha.ITest => helper('timeout', description, false, new Map()).timeout(6000);
  f.debug = (description: string): Mocha.ITest => helper('timeout', description, true, new Map());
  return f;
})();
