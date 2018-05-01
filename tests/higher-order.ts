import { code, incorrect, verified } from './helpers';

declare const assert: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const pure: () => boolean;
declare const requires: (x: boolean) => void;
declare const spec: (f: any, r: (rx: any) => boolean, s: (sx: any, sy: any) => boolean) => boolean;

describe('fibonacci increasing (external proof)', () => {

  code(() => {
    function fib (n) {
      ensures(pure());

      if (n <= 1) return 1;
      return fib(n - 1) + fib(n - 2);
    }

    function fibInc (n) {
      requires(typeof(n) === 'number');
      requires(n >= 0);
      ensures(fib(n) >= n);
      ensures(pure());

      fib(n);
      if (n >= 2) {
        fibInc(n - 1); fib(n - 1);
        fibInc(n - 2); fib(n - 2);
      }
    }
  });

  verified('fib: pure()');
  verified('fibInc: precondition fibInc((n - 1))');
  verified('fibInc: precondition fibInc((n - 2))');
  verified('fibInc: (fib(n) >= n)');
});

describe('simple higher-order functions', () => {

  code(() => {
    function inc (n) {
      requires(typeof(n) === 'number');
      ensures(res => res > n);

      return n + 1;
    }

    function twice (f, n) {
      requires(spec(f, (x) => typeof(x) === 'number', (x,y) => y > x));
      requires(typeof(n) === 'number');
      ensures(res => res > n + 1);

      return f(f(n));
    }

    const x = 3;
    const y = twice(inc, x);
    assert(y >= 5);
  });

  verified('inc: (res > n)');
  verified('twice: precondition f(n)');
  verified('twice: precondition f(f(n))');
  verified('twice: (res > (n + 1))');
  verified('precondition twice(inc, x)');
  verified('assert: (y >= 5)');
});

describe('higher-order proofs', () => {

  code(() => {
    function fib (n) {
      requires(n >= 0);
      ensures(pure());
      ensures(res => typeof(res) === 'number');

      if (n <= 1) {
        return 1;
      } else {
        return fib(n - 1) + fib(n - 2);
      }
    }

    function fibInc (n) {
      requires(n >= 0);
      ensures(fib(n) <= fib(n + 1));
      ensures(pure());

      fib(n);
      fib(n + 1);

      if (n > 0) {
        fib(n - 1);
        fibInc(n - 1);
      }

      if (n > 1) {
        fib(n - 2);
        fibInc(n - 2);
      }
    }

    function fMono (f, fInc, n, m) {
      requires(spec(f, x => x >= 0, (x, y) => pure() && typeof y === 'number'));
      requires(spec(fInc, x => x >= 0, x => pure() && f(x) <= f(x + 1)));
      requires(n >= 0);
      requires(m >= 0);
      requires(n < m);
      ensures(pure());
      ensures(f(n) <= f(m));

      if (n + 1 === m) {
        fInc(n);
      } else {
        fInc(n);
        fMono(f, fInc, n + 1, m);
      }
    }

    function fibMono (n, m) {
      requires(n >= 0);
      requires(m >= 0);
      requires(n < m);
      ensures(pure());
      ensures(fib(n) <= fib(m));

      fMono(fib, fibInc, n, m);
    }

  });

  verified('fib: precondition fib((n - 1))');
  verified('fib: precondition fib((n - 2))');
  verified('fib: pure()');
  verified('fib: (typeof(res) === "number")');
  verified('fibInc: precondition fib(n)');
  verified('fibInc: precondition fib((n + 1))');
  verified('fibInc: precondition fib((n - 1))');
  verified('fibInc: precondition fibInc((n - 1))');
  verified('fibInc: precondition fib((n - 2))');
  verified('fibInc: precondition fibInc((n - 2))');
  verified('fibInc: (fib(n) <= fib((n + 1)))');
  verified('fibInc: pure()');
  verified('fMono: precondition fInc(n)');
  verified('fMono: precondition fInc(n)');
  verified('fMono: precondition fMono(f, fInc, (n + 1), m)');
  verified('fMono: pure()');
  verified('fMono: (f(n) <= f(m))');
  verified('fibMono: precondition fMono(fib, fibInc, n, m)');
  verified('fibMono: pure()');
  verified('fibMono: (fib(n) <= fib(m))');
});

describe('nested function bug', () => {

  code(() => {
    function f (x) {
      function g (y) {
        return x;
      }
      return g;
    }
    f(1)(2);
    assert(f(1)(2) === f(1));
  });

  incorrect('assert: (f(1)(2) === f(1))');
});

describe('functions returning functions', () => {

  code(() => {
    function twice (f: any) {
      requires(spec(f, (x) => typeof(x) === 'number',
                       (x,y) => typeof(y) === 'number' && y > x));
      ensures(res => spec(res, (x) => typeof(x) === 'number',
                               (x,y) => typeof(y) === 'number' && y > x + 1));
      return function (x) {
        requires(typeof(x) === 'number');
        ensures(y => typeof(y) === 'number' && y > x + 1);
        return f(f(x));
      };
    }
  });

  verified('twice: spec(res, x => (typeof(x) === "number"), ' +
                           '(x, y) => ((typeof(y) === "number") && (y > (x + 1))))');
});

describe('function subtyping with same type', () => {

  code(() => {
    function f (g) {
      requires(spec(g, x => x > 3, (x, y) => y > x));
      ensures(spec(g , x => x > 3, (x, y) => y > x));
    }
  });

  verified('f: spec(g, x => (x > 3), (x, y) => (y > x))');
});

describe('function subtyping with stronger pre', () => {

  code(() => {
    function f (g) {
      requires(spec(g, x => x > 3, (x, y) => y > x));
      ensures(spec(g , x => x > 4, (x, y) => y > x));
    }
  });

  verified('f: spec(g, x => (x > 4), (x, y) => (y > x))');
});

describe('function subtyping with weaker pre', () => {

  code(() => {
    function f (g) {
      requires(spec(g, x => x > 3, (x, y) => y > x));
      ensures(spec(g , x => x > 2, (x, y) => y > x));
    }
  });

  incorrect('f: spec(g, x => (x > 2), (x, y) => (y > x))', ['x', 3]);
});

describe('function subtyping with stronger post', () => {

  code(() => {
    function f (g) {
      requires(spec(g, x => x > 3, (x, y) => y > x));
      ensures(spec(g , x => x > 3, (x, y) => y > x + 1));
    }
  });

  incorrect('f: spec(g, x => (x > 3), (x, y) => (y > (x + 1)))', ['x', 1657]);
});

describe('function subtyping with weaker post', () => {

  code(() => {
    function f (g) {
      requires(spec(g, x => x > 3, (x, y) => y > x));
      ensures(spec(g , x => x > 3, (x, y) => y >= x));
    }
  });

  verified('f: spec(g, x => (x > 3), (x, y) => (y >= x))');
});
