import { expect } from 'chai';
import { code, incorrect, unverified, verified } from './helpers';
import { verificationConditions } from '../src';

declare function assert (x: boolean): void;
declare function ensures (x: boolean | ((y: any) => boolean)): void;
declare function requires (x: boolean): void;

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
      ensures(y => Number.isInteger(y));

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
  verified('f: Number.isInteger(y)');
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

describe('Number', () => {

  code(() => {
    function f (x) {
      requires(typeof x === 'number');
      requires(Number.isInteger(x));
      ensures(y => Number.isInteger(y));

      return x + 1;
    }

    function g (x) {
      requires(typeof x === 'number');
      requires(x > 0);
      requires(x < 1);
      ensures(y => Number.isInteger(y));

      return x;
    }

    const y = Number.isInteger(12);
    assert(y === true);
    // @ts-ignore: intentionally using wrong type
    const z = Number.isInteger('abc');
    assert(z === false);
  });

  verified('f: Number.isInteger(y)');
  incorrect('g: Number.isInteger(y)', ['x', 0.5]);
  verified('Number has property "isInteger"');
  verified('precondition Number.isInteger(12)');
  verified('assert: (y === true)');
  verified('Number has property "isInteger"');
  verified('precondition Number.isInteger("abc")');
  verified('assert: (z === false)');
});

describe('Random dice roll', () => {

  code(() => {
    const d6 = Math.trunc(Math.random() * 6 + 1);
    assert(typeof d6 === 'number');
    assert(d6 >= 1);
    assert(d6 <= 6);
    assert(Number.isInteger(d6));
  });

  verified('Math has property "trunc"');
  verified('Math has property "random"');
  verified('precondition Math.random()');
  verified('precondition Math.trunc(((Math.random() * 6) + 1))');
  verified('assert: (typeof(d6) === "number")');
  verified('assert: (d6 >= 1)');
  verified('assert: (d6 <= 6)');
  verified('assert: Number.isInteger(d6)');
});

describe('alert', () => {

  code(() => {
    function f (x) {
      ensures(y => y === undefined);

      return alert(x);
    }

    alert();
  });

  verified('f: precondition alert(x)');
  verified('f: (y === undefined)');
  unverified('precondition alert()');
});
