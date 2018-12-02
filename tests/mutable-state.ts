import 'mocha';
import { code, incorrect, unverified, verified } from './helpers';

declare function assert (x: boolean): void;
declare function invariant (x: boolean): void;
declare function ensures (x: boolean | ((y: any) => boolean)): void;
declare function requires (x: boolean): void;
declare function pure (): boolean;
declare function old<T> (x: T): T;

describe('counter', () => {

  code(() => {
    let counter = 0;
    invariant(Number.isInteger(counter));
    invariant(counter >= 0);

    function increment () {
      ensures(counter > old(counter));

      counter++;
    }

    function decrement () {
      ensures(old(counter) > 0 ? counter < old(counter) : counter === old(counter));

      if (counter > 0) counter--;
    }
  });

  verified('initially: Number.isInteger(counter)');
  verified('initially: (counter >= 0)');
  verified('increment: (counter > old(counter))');
  verified('increment: Number.isInteger(counter)');
  verified('increment: (counter >= 0)');
  verified('decrement: ((old(counter) > 0) ? (counter < old(counter)) : (counter === old(counter)))');
  verified('decrement: Number.isInteger(counter)');
  verified('decrement: (counter >= 0)');
});

describe('simple steps', () => {

  code(() => {
    let i = 0;
    assert(i < 1);
    i = 3;
    assert(i < 2);
  });

  verified('assert: (i < 1)');
  incorrect('assert: (i < 2)', [{ name: 'i', heap: 2 }, 3]);
});

describe('loop', () => {

  code(() => {
    let i = 0;

    while (i < 5) {
      invariant(i <= 5);
      invariant(Number.isInteger(i));
      i++;
    }

    assert(i === 5);
  });

  verified('invariant on entry: (i <= 5)');
  verified('invariant on entry: Number.isInteger(i)');
  verified('invariant maintained: (i <= 5)');
  verified('invariant maintained: Number.isInteger(i)');
  verified('assert: (i === 5)');
});

describe('loop with missing invariant', () => {

  code(() => {
    let i = 0;

    while (i < 5) {
      i++;
    }

    assert(i === 5);
  });

  unverified('assert: (i === 5)', [{ name: 'i', heap: 2 }, false]);
});

describe('sum', () => {

  code(() => {
    function sumTo (n) {
      requires(Number.isInteger(n));
      requires(n >= 0);
      ensures(res => res === (n + 1) * n / 2);

      let i = 0;
      let s = 0;
      while (i < n) {
        invariant(i <= n);
        invariant(s === (i + 1) * i / 2);
        invariant(Number.isInteger(i));
        invariant(Number.isInteger(s));
        i++;
        s = s + i;
      }
      return s;
    }
  });

  verified('sumTo: invariant on entry: (i <= n)');
  verified('sumTo: invariant on entry: (s === (((i + 1) * i) / 2))');
  verified('sumTo: invariant on entry: Number.isInteger(i)');
  verified('sumTo: invariant on entry: Number.isInteger(s)');
  verified('sumTo: invariant maintained: (i <= n)');
  verified('sumTo: invariant maintained: (s === (((i + 1) * i) / 2))');
  verified('sumTo: invariant maintained: Number.isInteger(i)');
  verified('sumTo: invariant maintained: Number.isInteger(s)');
  verified('sumTo: (res === (((n + 1) * n) / 2))');
});

describe('mutable variables', () => {

  code(() => {
    let x = 2;
    const y = 3;
    function f (z) {
      requires(x < y);
    }
    f(0);
    x = 4;
    f(1);
  });

  verified('precondition f(0)');
  incorrect('precondition f(1)');
});

describe('pure functions', () => {

  code(() => {
    let x = 0;

    function f () { ensures(pure()); x++; }
    function g () { ensures(pure()); return x + 1; }
    function h1 (y) { /*empty*/ }
    function h2a () { h1(3); }
    function h2b () { ensures(pure()); h1(4); }
    function h3a () { ensures(pure()); h2a(); }
    function h3b () { ensures(pure()); h2b(); }
  });

  unverified('f: pure()'); // not pure
  verified('g: pure()'); // pure
  verified('h2b: pure()'); // inlined h1 pure
  unverified('h3a: pure()'); // pure, but only one level inlining
  verified('h3b: pure()'); // calling other pure function
});

describe('global mutable variable with missing invariant', () => {

  code(() => {
    let x = 23;
    let y = 42;
    let z = 69;

    invariant(typeof y === 'number');

    invariant(typeof z === 'number' && z > 22);

    function f () {
      ensures(res => res > 22);

      return x;
    }

    function g () {
      ensures(res => res > 22);

      return y;
    }

    function h () {
      ensures(res => res > 22);

      return z;
    }
  });

  incorrect('f: (res > 22)', [{ name: 'x', heap: 3 }, 23], [{ name: 'x', heap: 4 }, false]);
  incorrect('g: (res > 22)', [{ name: 'y', heap: 3 }, 42], [{ name: 'y', heap: 4 }, 22]);
  verified('h: (res > 22)');
});
