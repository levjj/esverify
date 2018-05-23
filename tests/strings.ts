import { code, incorrect, verified, unverified } from './helpers';

declare const assert: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const requires: (x: boolean) => void;

describe('string concatenation', () => {
  code(() => {
    function f (x, y) {
      requires(typeof x === 'string');
      requires(typeof y === 'string');
      requires(x + y === 'ab');
      ensures(z => z === 'abc');

      return x + y;
    }

    const s1 = 'hello';
    const s2 = 'world';
    const s3 = s1 + ' ' + s2;
    assert(s3 === 'hello world');
    assert(s1 + ' ' + s2 === 'hello world');
    assert(s2 + s1 === 'helloworld');
  });

  incorrect('f: (z === "abc")', ['x', ''], ['y', 'ab']);
  verified('assert: (s3 === "hello world")');
  verified('assert: (((s1 + " ") + s2) === "hello world")');
  incorrect('assert: ((s2 + s1) === "helloworld")');
});

describe('string length', () => {
  code(() => {
    function f (x) {
      requires(typeof x === 'string');
      ensures(z => z.length !== 3);
      return x;
    }

    const s1 = 'hello';
    const l1 = s1.length;
    assert(l1 === 5);
    assert(s1.length === 5);
    const l2 = (s1 + ' world').length;
    const l3 = s1.length + ' world'.length;
    assert(l2 === l3);
    assert(l2 === 11);
    assert(l2 > 11);

  });

  incorrect('f: (z.length !== 3)', ['x', '\u0000\u0000\u0000']);
  verified('s1 has property "length"');
  verified('assert: (l1 === 5)');
  verified('assert: (s1.length === 5)');
  verified('(s1 + " world") has property "length"');
  verified('s1 has property "length"');
  verified('" world" has property "length"');
  verified('assert: (l2 === l3)');
  verified('assert: (l2 === 11)');
  incorrect('assert: (l2 > 11)');
});

describe('string access character by index', () => {
  code(() => {
    function f (x) {
      requires(typeof x === 'string');
      requires(x[0] === 'a');
      ensures(z => z.length !== 2);
      return x;
    }

    const s1 = 'hello';
    const c1 = s1[0];
    const c2 = s1[3 - 2];
    assert(s1[0] === 'h');
    assert(c1 === 'h');
    assert(c2 === 'e');
    const c3 = s1[6];
    assert(c3 === undefined);
  });

  incorrect('f: (z.length !== 2)', ['x', 'a\u0000']);
  verified('s1 has property 0');
  verified('s1 has property (3 - 2)');
  verified('assert: (s1[0] === "h")');
  verified('assert: (c1 === "h")');
  verified('assert: (c2 === "e")');
  incorrect('s1 has property 6');
  verified('assert: (c3 === undefined)');
});

describe('string substr', () => {

  code(() => {
    const str = 'abcd';
    const substr = str.substr(1, 2);
    assert(substr === 'bc');

    function f (a) {
      requires(typeof a === 'string');
      requires(a.length === 6);
      ensures(y => y.length === 2);
      ensures(y => y[1] === a[3]);

      return a.substr(2, 2);
    }

    function g (a) {
      requires(typeof a === 'string');
      requires(a.length === 6);
      ensures(y => y[1] !== a[3]);

      return a.substr(2, 2);
    }

    const d = 'abc';
    d.substr(-1, 4);
  });

  verified('precondition str.substr(1, 2)');
  verified('assert: (substr === "bc")');
  verified('f: a has property "substr"');
  verified('f: precondition a.substr(2, 2)');
  verified('f: (y.length === 2)');
  verified('f: (y[1] === a[3])');
  verified('g: a has property "substr"');
  verified('g: precondition a.substr(2, 2)');
  incorrect('g: (y[1] !== a[3])', ['a', '\u0000\u0000\u0000\u0000\u0000\u0000']);
  unverified('precondition d.substr(-1, 4)');
});

describe('string substring', () => {

  code(() => {
    const str = 'abc';
    const substr = str.substring(1, 2);
    assert(substr === 'b');

    function f (a) {
      requires(typeof a === 'string');
      requires(a.length === 6);
      ensures(y => y.length === 2);
      ensures(y => y[1] === a[3]);

      return a.substring(2, 4);
    }

    function g (a) {
      requires(typeof a === 'string');
      requires(a.length === 6);
      ensures(y => y[1] !== a[3]);

      return a.substring(2, 4);
    }

    const d = 'abc';
    d.substring(1, 4);
  });

  verified('precondition str.substring(1, 2)');
  verified('assert: (substr === "b")');
  verified('f: a has property "substring"');
  verified('f: precondition a.substring(2, 4)');
  verified('f: (y.length === 2)');
  verified('f: (y[1] === a[3])');
  verified('g: a has property "substring"');
  verified('g: precondition a.substring(2, 4)');
  incorrect('g: (y[1] !== a[3])', ['a', '\u0000\u0000\u0000\u0000\u0000\u0000']);
  unverified('precondition d.substring(1, 4)');
});

describe('string class', () => {

  code(() => {
    const str = new String('abc');
    assert(str instanceof String);
    const l1 = str.length;
    assert(l1 === 5);
    const c1 = str[0];
    assert(c1 === 'a');

    const substr = str.substring(1, 2);
    assert(substr[0] === 'b');

    function f (a) {
      requires(a instanceof String);
      requires(a.length === 6);
      ensures(y => y.length === 2);
      ensures(y => y[1] === a[3]);

      return a.substring(2, 4);
    }
  });

  verified('precondition str.substring(1, 2)');
});
