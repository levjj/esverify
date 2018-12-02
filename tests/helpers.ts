import 'mocha';
import { expect } from 'chai';
import { verificationConditions } from '../src';
import { FreeVar } from '../src/logic';
import { log } from '../src/message';
import { plainToJSVal } from '../src/model';
import { setOptions } from '../src/options';
import { sourceAsJavaScript } from '../src/parser';
import { interpret } from '../src/interpreter';
import VerificationCondition from '../src/verification';
import { TEST_PREAMBLE } from '../src/codegen';

let savedVCs: Array<VerificationCondition>;

export function vcs (): Array<VerificationCondition> {
  return savedVCs;
}

export function code (fn: () => any, each: boolean = false) {
  const setUp = () => {
    const code = fn.toString();
    const t = verificationConditions(code.substring(14, code.length - 2));
    if (!(t instanceof Array)) {
      log(t);
      if (t.status === 'error' && t.type === 'unexpected') console.log(t.error);
      throw new Error('failed to find verification conditions');
    }
    savedVCs = t;
  };
  if (each) {
    beforeEach(setUp);
  } else {
    before(setUp);
  }
}

function helper (expected: 'verified' | 'unverified' | 'incorrect' | 'timeout', description: string,
                 debug: boolean, expectedModel: Map<FreeVar, any>): Mocha.ITest {
  const body = async () => {
    /* tslint:disable:no-unused-expression */
    if (debug) {
      setOptions({ quiet: false, verbose: true, timeout: 60 });
      console.log(savedVCs.map(vc => vc.getDescription()).join('\n'));
    }
    const vc = savedVCs.find(v => v.getDescription() === description);
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

function bisimulationHelper (description: string, fn: () => any, steps: number, debug: boolean) {
  const testBody = () => {
    const code = fn.toString().substring(14, fn.toString().length - 2);
    const program = sourceAsJavaScript(code, false);
    const interpreterOutputs: Array<any> = [];
    let interpreterError: { error: any } | undefined;
    const evalOutputs: Array<any> = [];
    let evalError: { error: any } | undefined;
    function log (out: any): void {
      evalOutputs.push(out);
      if (debug) console.log(out);
    }
    if (debug) console.log('\eval outputs:        ');
    try {
      /* tslint:disable:no-eval */
      eval(TEST_PREAMBLE + code);
    } catch (error) {
      evalError = { error };
    }
    if (debug) console.log('\eval error:          ', evalError);
    const interpreter = interpret(program);
    interpreter.define('log', (out: any): void => {
      interpreterOutputs.push(out);
      if (debug) console.log(out);
    }, 'const');
    if (debug) console.log('\ninterpreter outputs:');
    try {
      interpreter.run();
    } catch (error) {
      interpreterError = { error };
    }
    if (debug) {
      console.log('\ninterpreter error:  ', interpreterError);
      console.log('\ninterpreter steps:  ', interpreter.steps, `(expected ${steps})`);
    }
    /* tslint:disable:no-unused-expression */
    expect(interpreterOutputs).to.have.length(evalOutputs.length);
    expect(interpreterOutputs).to.deep.eq(evalOutputs);
    if (evalError === undefined) {
      expect(interpreterError).to.be.undefined;
    } else {
      expect(typeof evalError.error).to.be.eq(typeof interpreterError.error);
      expect(evalError.error.message).to.be.eq(interpreterError.error.message);
    }
    expect(interpreter.steps).to.eq(steps, 'expected number of steps');
  };
  if (debug) {
    return it.only(`interprets ${description}`, testBody).timeout(60000);
  } else {
    return it(`interprets ${description}`, testBody);
  }
}

interface BisimulationFun {
  (description: string, code: () => any, steps: number): Mocha.ITest;
  debug: (description: string, code: () => any, steps: number) => Mocha.ITest;
}

export const bisumulate: BisimulationFun = (() => {
  const f: any = (description: string, code: () => any, steps: number): Mocha.ITest =>
    bisimulationHelper(description, code, steps, false);
  f.debug = (description: string, code: () => any, steps: number): Mocha.ITest =>
    bisimulationHelper(description, code, steps, true);
  return f;
})();
