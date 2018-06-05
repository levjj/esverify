import { expect } from 'chai';
import { code, incorrect, unverified, verified, vcs } from './helpers';

declare const assert: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const requires: (x: boolean) => void;
declare const spec: (f: any, r: (rx: any) => boolean, s: (sx: any, sy: any) => boolean) => boolean;

describe('max()', () => {

  code(() => {
    function max (a, b) {
      requires(typeof(a) === 'number');
      requires(typeof(b) === 'number');
      ensures(res => res >= a);

      if (a >= b) {
        return a;
      } else {
        return b;
      }
    }
  });

  it('finds a verification conditions', () => {
    expect(vcs()).to.have.length(1);
  });

  it('has a description', async () => {
    expect(vcs()[0].description).to.be.eql('max: (res >= a)');
  });

  verified('max: (res >= a)');
});

describe('max() with missing pre', () => {

  code(() => {
    function max (a, b) {
      requires(typeof(a) === 'number');
      ensures(res => res >= a);

      if (a >= b) {
        return a;
      } else {
        return b;
      }
    }
  });

  unverified('max: (res >= a)', ['b', false]);
});

describe('global call', () => {

  code(() => {
    function inc (n) {
      requires(typeof(n) === 'number');
      ensures(res => res > n);

      return n + 1;
    }

    let i = 3;
    let j = inc(i);
    assert(j > 3);
  });

  verified('precondition inc(i)');
  verified('assert: (j > 3)');
  verified('inc: (res > n)');
});

describe('assert within function', () => {

  code(() => {
    function f (n) {
      requires(typeof(n) === 'number');
      ensures(res => res > 3);

      assert(n > 3);
      return n;
    }
  });

  incorrect('f: assert: (n > 3)', ['n', 3]);
  verified('f: (res > 3)');
});

describe('inline global call', () => {

  code(() => {
    function inc (n) {
      return n + 1;
    }
    function inc2 (n) {
      return inc(inc(n));
    }

    let i = 3;
    let j = inc(i);
    assert(j === 4);
    let k = inc2(i);
    assert(k === 5);
  });

  verified('assert: (j === 4)');
  unverified('assert: (k === 5)', [{ name: 'k', heap: 4 }, 8]); // only inline one level
});

describe('post conditions global call', () => {

  code(() => {
    function inc (n) {
      requires(typeof(n) === 'number');
      ensures(res => res > n);

      return n + 1;
    }
    function inc2 (n) {
      return inc(inc(n));
    }

    let i = 3;
    let j = inc(i);
    assert(j >= 4);
    let k = inc2(i);
    assert(k >= 5);
  });

  verified('inc: (res > n)');
  incorrect('inc2: precondition inc(n)', ['n', true]);
  incorrect('inc2: precondition inc(inc(n))');
  verified('precondition inc(i)');
  verified('assert: (j >= 4)');
  verified('precondition inc2(i)');
  unverified('assert: (k >= 5)', [{ name: 'k', heap: 4 }, 8]);
  // only inline one level, so post-cond of inc(inc(i)) not available
});

describe('closures', () => {

  code(() => {
    function cons (x) {
      function f () { return x; }
      return f;
    }
    const g = cons(1);
    const g1 = g();
    assert(g1 === 1);
    const h = cons(2);
    const h1 = h();
    assert(h1 === 2);
  });

  verified('assert: (g1 === 1)');
  verified('assert: (h1 === 2)');
});

describe('fibonacci', () => {

  code(() => {
    function fib (n) {
      requires(Number.isInteger(n));
      requires(n >= 0);
      ensures(res => res >= n);
      ensures(res => res >= 1);

      if (n <= 1) return 1;
      return fib(n - 1) + fib(n - 2);
    }
  });

  verified('fib: precondition fib((n - 1))');
  verified('fib: precondition fib((n - 2))');
  verified('fib: (res >= n)');
  verified('fib: (res >= 1)');
});

describe('buggy fibonacci', () => {

  code(() => {
    function fib (n) {
      requires(Number.isInteger(n));
      requires(n >= 0);
      ensures(res => res >= n);

      if (n <= 1) return n;
      return fib(n - 1) + fib(n - 2);
    }
  });

  verified('fib: precondition fib((n - 1))');
  verified('fib: precondition fib((n - 2))');
  incorrect('fib: (res >= n)', ['n', 2]);
});

describe('function expressions', () => {

  code(() => {
    const x = (function (z: number) { return z; })(3);
    assert(x === 3);
    const y = ((z: number) => z)(4);
    assert(y === 4);
  });

  verified('assert: (x === 3)');
  verified('assert: (y === 4)');
});

describe('function bug', () => {

  code(() => {
    function f (x) {
      ensures(!spec(f, y => true, y => y !== x));
      f(x);
    }
  });

  verified('f: !spec(f, y => true, y => (y !== x))');
});

describe('integers', () => {

  code(() => {
    function f (i) {
      requires(Number.isInteger(i));
      ensures(res => Number.isInteger(res) && res > i && res <= i + 1);

      return i + 1;
    }

    function g (i) {
      requires(Number.isInteger(i));
      requires(i === 9 / 2);
      ensures(1 + 1 === 1);
    }

    function h (i) {
      requires(Number.isInteger(i) && i > 1 && i < 4);
      ensures(res => res > 2);
    }
  });

  verified('f: ((Number.isInteger(res) && (res > i)) && (res <= (i + 1)))');
  verified('g: ((1 + 1) === 1)');
  incorrect('h: (res > 2)', ['i', 2]);
});

describe('reals', () => {

  code(() => {
    function f (i) {
      requires(typeof i === 'number');
      ensures(res => typeof res === 'number' && res > i && res < i + 1);

      return i + 0.5;
    }

    function g (i) {
      requires(typeof i === 'number');
      requires(i === 9 / 2);
      ensures(1 + 1 === 1);
    }

    function h (i) {
      requires(typeof i === 'number' && i > 1 && i < 2);
      ensures(res => res >= 1.5);
    }
  });

  verified('f: (((typeof(res) === "number") && (res > i)) && (res < (i + 1)))');
  incorrect('g: ((1 + 1) === 1)', ['i', 4.5]);
  incorrect('h: (res >= 1.5)', ['i', 1.5]);
});
