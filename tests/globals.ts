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

describe('parseInt', () => {

  code(() => {
    function f (x) {
      requires(typeof x === 'string');
      ensures(y => typeof y === 'number');

      return parseInt(x, 10);
    }

    function g (x) {
      requires(typeof x === 'string');
      ensures(y => y !== 12);

      return parseInt(x, 10);
    }

    const z = parseInt('23', 10);
    assert(z === 23);
    parseInt('23', 16);
  });

  verified('f: precondition parseInt(x, 10)');
  verified('f: (typeof(y) === "number")');
  verified('g: precondition parseInt(x, 10)');
  incorrect('g: (y !== 12)', ['x', '12']);
  verified('precondition parseInt("23", 10)');
  verified('assert: (z === 23)');
  unverified('precondition parseInt("23", 16)');
});

describe('Math', () => {

  code(() => {
    function f (x) {
      requires(typeof x === 'number');
      ensures(y => y >= 4);

      return Math.max(x, 4);
    }

    function g (x) {
      requires(typeof x === 'number');
      ensures(y => y !== 5);

      return Math.max(x, 4);
    }

    const z = Math.max(12, 44);
    assert(z === 44);
    // @ts-ignore: intentionally using wrong type
    Math.max('abc', 16);
  });

  verified('f: Math has property "max"');
  verified('f: precondition Math.max(x, 4)');
  verified('f: (y >= 4)');
  verified('g: Math has property "max"');
  verified('g: precondition Math.max(x, 4)');
  incorrect('g: (y !== 5)', ['x', 5]);
  verified('Math has property "max"');
  verified('precondition Math.max(12, 44)');
  verified('assert: (z === 44)');
  verified('Math has property "max"');
  unverified('precondition Math.max("abc", 16)');
});
