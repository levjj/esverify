import { code, incorrect, verified, unverified } from './helpers';

declare function assert (x: boolean): void;
declare function ensures (x: boolean | ((y: any) => boolean)): void;
declare function requires (x: boolean): void;

describe('simple arrays', () => {
  /* tslint:disable:no-unused-expression */

  code(() => {
    function f (a: Array<number>) {
      requires(a instanceof Array);
      requires(a.length >= 1);

      return a[0];
    }

    function g (a: Array<number>) {
      requires(a instanceof Array);
      requires(a.length >= 1);
      requires(a.length < 5);
      ensures(res => res > 3);

      return a[0];
    }

    const a0 = [];
    assert(a0 instanceof Array);
    assert(a0 instanceof Object);
    assert('length' in a0);
    assert(a0.length === 0);

    const a1 = [23];
    assert(a1 instanceof Array);
    assert(a1 instanceof Object);
    assert('length' in a1);
    assert(a1.length === 1);
    assert(0 in a1);
    assert(a1[0] > 22);
    const p = 3 - 2 - 1;
    assert(a1[p] > 22);
    f(a1);

    const a2 = [23, 42];
    assert(a2.length === 2);
    assert(!(2 in a2));
    f(a2);
    a2[2];

    function ff (a: Array<number>) {
      requires(a instanceof Array);
      requires(a.every(e => e > 3));
      requires(a.length >= 2);
      assert(a[0] > 2); // holds
      assert(a[1] > 4); // does not hold
      assert(a[2] > 0); // out of bounds
    }

    ff([5, 4]);
    ff([5]); // precondition violated
  });

  verified('f: a has property 0');
  verified('g: a has property 0');
  incorrect('g: (res > 3)', ['a', [false, false]]);

  verified('assert: (a0 instanceof Array)');
  verified('assert: (a0 instanceof Object)');
  verified('assert: ("length" in a0)');
  verified('assert: (a0.length === 0)');

  verified('assert: (a1 instanceof Array)');
  verified('assert: (a1 instanceof Object)');
  verified('assert: ("length" in a1)');
  verified('assert: (a1.length === 1)');
  verified('assert: (0 in a1)');
  verified('assert: (a1[0] > 22)');
  verified('assert: (a1[p] > 22)');
  verified('precondition f(a1)');

  verified('assert: (a2.length === 2)');
  verified('assert: !(2 in a2)');
  verified('precondition f(a2)');
  incorrect('a2 has property 2');
});

describe('array invariants', () => {

  code(() => {
    function f_1 () {
      ensures(res => res.every(e => e > 23));

      return [42, 69];
    }

    function f_2 (a: Array<number>) {
      requires(a.every(e => e > 23));
      requires(a.length >= 1);
      ensures(res => res > 12);

      return a[0];
    }

    function f_3 (a: Array<number>) {
      requires(a.every(e => e > 23));
      requires(a.length >= 3);
      ensures(a[2] > 12);
    }

    function f_4 () {
      ensures(res => res.every((e, i) => e > i));

      return [1, 2, 3];
    }

    function g_1 () {
      ensures(res => res.every(e => e > 23));

      return [42, 69, 4];
    }

    function g_2 (a: Array<number>) {
      requires(a.every(e => e > 23));
      requires(a.length >= 1);
      requires(a.length < 6);
      ensures(res => res > 42);

      return a[0];
    }

    function g_3 (a: Array<number>) {
      requires(a.every(e => e > 23));
      requires(a.length === 0);
      ensures(a[2] > 12);
    }

    function g_4 () {
      ensures(res => res.every((e, i) => e > i));

      return [1, 2, 2];
    }
  });

  verified('f_1: res.every(e => (e > 23))');
  verified('f_2: a has property 0');
  verified('f_2: (res > 12)');
  verified('f_3: (a[2] > 12)');
  verified('f_4: res.every((e, i) => (e > i))');
  incorrect('g_1: res.every(e => (e > 23))');
  verified('g_2: a has property 0');
  incorrect('g_2: (res > 42)', ['a', [24]]);
  incorrect('g_3: (a[2] > 12)', ['a', []]);
  incorrect('g_4: res.every((e, i) => (e > i))');
});

describe('array constructor', () => {

  code(() => {
    const a = new Array(3, 2);
    assert(a.length === 2);
    assert(a[1] === 2);

    const b = Array(3, 2);
    assert(b.length === 2);
    assert(b[1] === 2);
  });

  verified('assert: (a.length === 2)');
  verified('assert: (a[1] === 2)');
  verified('assert: (b.length === 2)');
  verified('assert: (b[1] === 2)');
});

describe('array slice', () => {

  code(() => {
    const arr = [1, 2, 3];
    const sliced = arr.slice(1, 2);
    assert(sliced[0] === 2);

    function f (a) {
      requires(a instanceof Array);
      requires(a.length === 6);
      ensures(y => y.length === 2);
      ensures(y => y[1] === a[3]);

      return a.slice(2, 4);
    }

    function g (a) {
      requires(a instanceof Array);
      requires(a.length === 6);
      ensures(y => y[1] !== a[3]);

      return a.slice(2, 4);
    }

    const d = [1, 2, 3];
    d.slice(1, 4);
  });

  verified('precondition arr.slice(1, 2)');
  verified('assert: (sliced[0] === 2)');
  verified('f: a has property "slice"');
  verified('f: precondition a.slice(2, 4)');
  verified('f: (y.length === 2)');
  verified('f: (y[1] === a[3])');
  verified('g: a has property "slice"');
  verified('g: precondition a.slice(2, 4)');
  incorrect('g: (y[1] !== a[3])', ['a', [2, 2, 2, 8, 2, 2]]).timeout(4000);
  unverified('precondition d.slice(1, 4)');
});
