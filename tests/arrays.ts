import { code, incorrect, verified } from './helpers';

declare const assert: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const every: (a: Array<any>, b: ((x: any) => boolean) | ((x: any, y: any) => boolean)) => boolean;
declare const requires: (x: boolean) => void;

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
  });

  verified('f: a has property 0');
  verified('g: a has property 0');
  incorrect('g: (res > 3)', ['a', [true]]);

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
      ensures(res => every(res, e => e > 23));

      return [42, 69];
    }

    function f_2 (a: Array<number>) {
      requires(every(a, e => e > 23));
      requires(a.length >= 1);
      ensures(res => res > 12);

      return a[0];
    }

    function f_3 (a: Array<number>) {
      requires(every(a, e => e > 23));
      requires(a.length >= 3);
      ensures(a[2] > 12);

      a[2];
    }

    function f_4 () {
      ensures(res => every(res, (e, i) => e > i));

      return [1, 2, 3];
    }

    function g_1 () {
      ensures(res => every(res, e => e > 23));

      return [42, 69, 4];
    }

    function g_2 (a: Array<number>) {
      requires(every(a, e => e > 23));
      requires(a.length >= 1);
      ensures(res => res > 42);

      return a[0];
    }

    function g_3 (a: Array<number>) {
      requires(every(a, e => e > 23));
      requires(a.length >= 3);
      ensures(a[2] > 12);
    }

    function g_4 () {
      ensures(res => every(res, (e, i) => e > i));

      return [1, 2, 2];
    }
  });

  verified('f_1: every(res, e => (e > 23))');
  verified('f_2: a has property 0');
  verified('f_2: (res > 12)');
  verified('f_3: a has property 2');
  verified('f_3: (a[2] > 12)');
  verified('f_4: every(res, (e, i) => (e > i))');
  incorrect('g_1: every(res, e => (e > 23))');
  verified('g_2: a has property 0');
  incorrect('g_2: (res > 42)', ['a', [24]]);
  incorrect('g_3: (a[2] > 12)', ['a', [true, true, true]]);
  incorrect('g_4: every(res, (e, i) => (e > i))');
});
