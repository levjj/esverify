import { expect } from 'chai';
import { code, incorrect, unverified, verified } from './helpers';
import { verificationConditions } from '../src';

declare const assert: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const requires: (x: boolean) => void;
declare const spec: (f: any, r: (rx: any) => boolean, s: (sx: any, sy: any) => boolean) => boolean;

describe('undefined identifier', () => {

  const code = () => {
    // @ts-ignore: intentionally using undefined variable
    monsole.log('hello');
  };

  it('gets rejected', () => {
    const src = code.toString();
    const t = verificationConditions(src.substring(14, src.length - 2));
    expect(t).to.have.property('status', 'error');
    expect(t).to.have.property('type', 'undefined-identifier');
  });
});

describe('console', () => {

  code(() => {
    function f (x) {
      ensures(y => y === undefined);

      return console.log(x);
    }

    console.log();
    // @ts-ignore: intentionally using wrong method name
    console.mog('hello');
  });

  verified('f: console has property "log"');
  verified('f: precondition console.log(x)');
  verified('f: (y === undefined)');
  verified('console has property "log"');
  unverified('precondition console.log()');
  incorrect('console has property "mog"');
  incorrect('precondition console.mog("hello")');
});
