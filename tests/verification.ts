import { expect } from 'chai';
import { verificationConditions } from '../index';
import { consoleLog } from "../src/message";
import VerificationCondition from '../src/verification';

declare const requires: (x: boolean) => void;
declare const ensures: (x: boolean) => void;
declare const invariant: (x: boolean) => void;
declare const assert: (x: boolean) => void;
declare const old: (x: any) => any;
declare const pure: () => boolean;
declare const spec: (f: any, r: (rx: any) => boolean, s: (sx: any) => boolean) => boolean;

let vcs: Array<VerificationCondition>;

function code(fn: () => any) {
  before(() => {
    const code = fn.toString();
    const t = verificationConditions(code.substring(14, code.length - 2));
    if (!(t instanceof Array)) {
      consoleLog(t);
      if (t.status == "error") console.log(t.error);
      throw new Error('failed to find verification conditions');
    }
    vcs = t;
  });
}

function helper(expected: "verified" | "unverified" | "incorrect", description: string, debug: boolean = false) {
  const body = async () => {
    const vc = vcs.find(v => v.description === description);
    expect(vc).to.be.ok;
    if (debug) vc.enableDebugging();
    const res = await vc.verify();
    if (res.status == "error") console.log(res.error);
    expect(res.status).to.be.eql(expected);
  };
  if (debug) {
    it.only(description + ' ' + expected, body);
  } else {
    it(description + ' ' + expected, body);
  }
}

function skip(description: string) { it.skip(description); }
function verified(description: string) { helper('verified', description); }
function unverified(description: string) { helper('unverified', description); }
function incorrect(description: string) { helper('incorrect', description); }

function verifiedDebug(description: string) { helper('verified', description, true); }
function unverifiedDebug(description: string) { helper('unverified', description, true); }
function incorrectDebug(description: string) { helper('incorrect',description, true); }

describe('max()', () => {

  code(() => {
    function max(a, b) {
      requires(typeof(a) == 'number');
      requires(typeof(b) == 'number');
      ensures(max(a, b) >= a);

      if (a >= b) {
        return a;
      } else {
        return b;
      }
    }
  });

  it('finds a verification conditions', () => {
    expect(vcs).to.have.length(1);
  });

  it('has a description', async () => {
    expect(vcs[0].description).to.be.eql('max: (max(a, b) >= a)');
  });

  verified('max: (max(a, b) >= a)');
});

describe('max() with missing pre', () => {

  code(() => {
    function max(a, b) {
      requires(typeof(a) == 'number');
      ensures(max(a, b) >= a);

      if (a >= b) {
        return a;
      } else {
        return b;
      }
    }
  });

  unverified('max: (max(a, b) >= a)');

  it('returns counter-example', async () => {
    const m = await vcs[0].verify();
    if (m.status != "unverified") throw new Error();
    expect(m.model).to.have.property("b");
    expect(m.model.b).to.eql(false);
  });
});

describe('counter', () => {

  code(() => {
    let counter = 0;
    invariant(typeof counter == 'number');
    invariant(counter >= 0);

    function increment() {
      ensures(counter > old(counter));

      counter++;
    }

    function decrement() {
      ensures(old(counter) > 0 ? counter < old(counter) : counter == old(counter));

      if (counter > 0) counter--;
    }
  });

  verified('initially: (typeof(counter) == "number")');
  verified('initially: (counter >= 0)');
  verified('increment: (counter > old(counter))');
  verified('increment: (typeof(counter) == "number")');
  verified('increment: (counter >= 0)');
  verified('decrement: (old(counter) > 0) ? (counter < old(counter)) : (counter == old(counter))');
  verified('decrement: (typeof(counter) == "number")');
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
  incorrect('assert: (i < 2)');
});

describe('loop', () => {

  code(() => {
    let i = 0;

    while (i < 5) {
      invariant(i <= 5);
      i++;
    }

    assert(i === 5);
  });

  verified('invariant on entry: (i <= 5)');
  verified('invariant maintained: (i <= 5)');
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

  unverified('assert: (i === 5)');
});

describe('sum', () => {

  code(() => {
    function sumTo(n) {
      requires(typeof n == 'number');
      requires(n >= 0);
      ensures(sumTo(n) == (n + 1) * n / 2);

      let i = 0, s = 0;
      while (i < n) {
        invariant(i <= n);
        invariant(s == (i + 1) * i / 2);
        i++;
        s = s + i;
      }
      return s;
    }
  });

  verified('sumTo: invariant on entry: (i <= n)');
  verified('sumTo: invariant on entry: (s == (((i + 1) * i) / 2))');
  verified('sumTo: invariant maintained: (i <= n)');
  verified('sumTo: invariant maintained: (s == (((i + 1) * i) / 2))');
  verified('sumTo: (sumTo(n) == (((n + 1) * n) / 2))');
});


describe('global call', () => {

  code(() => {
    function inc(n) {
      requires(typeof(n) == 'number');
      ensures(inc(n) > n);

      return n + 1;
    }

    let i = 3;
    let j = inc(i);
    assert(j > 3);
  });

  verified('precondition inc(i)');
  verified('assert: (j > 3)');
  verified('inc: (inc(n) > n)');
});

describe('inline global call', () => {

  code(() => {
    function inc(n) {
      return n + 1;
    }
    function inc2(n) {
      return inc(inc(n));
    }

    let i = 3;
    let j = inc(i);
    assert(j == 4);
    let k = inc2(i);
    assert(k == 5);
  });

  verified('assert: (j == 4)');
  unverified('assert: (k == 5)'); // only inline one level
});

describe('post conditions global call', () => {

  code(() => {
    function inc(n) {
      requires(typeof(n) == 'number');
      ensures(inc(n) > n);

      return n + 1;
    }
    function inc2(n) {
      return inc(inc(n));
    }

    let i = 3;
    let j = inc(i);
    assert(j >= 4);
    let k = inc2(i);
    assert(k >= 5);
  });

  verified('inc: (inc(n) > n)')
  incorrect('inc2: precondition inc(n)');
  incorrect('inc2: precondition inc(inc(n))');
  verified('precondition inc(i)');
  verified('assert: (j >= 4)');
  verified('precondition inc2(i)');
  unverified('assert: (k >= 5)'); // only inline one level, so post-cond of inc(inc(i)) not available
});

describe('mutable variables', () => {

  code(() => {
    let x = 2;
    const y = 3;
    function f(z) {
      requires(x < y);
    }
    f(0);
    x = 4;
    f(1);
  });

  verified('precondition f(0)');
  incorrect('precondition f(1)');
});

describe('closures', () => {

  code(() => {
    function cons(x) {
      function f() { return x; }
      return f;
    }
    const g = cons(1);
    const g1 = g();
    assert(g1 == 1);
    const h = cons(2);
    const h1 = h();
    assert(h1 == 2);
  });

  verified('assert: (g1 == 1)');
  verified('assert: (h1 == 2)');
});

describe('fibonacci increasing', () => {

  code(() => {
    function fib(n) {
      requires(typeof(n) == 'number');
      requires(n >= 0);
      ensures(fib(n) >= n);
      ensures(fib(n) >= 1);

      if (n <= 1) return 1;
      return fib(n - 1) + fib(n - 2);
    }
  });

  verified('fib: precondition fib((n - 1))');
  verified('fib: precondition fib((n - 2))');
  verified('fib: (fib(n) >= n)');
});

describe('buggy fibonacci', () => {

  code(() => {
    function fib(n) {
      requires(typeof(n) == 'number');
      requires(n >= 0);
      ensures(fib(n) >= n);

      if (n <= 1) return n;
      return fib(n - 1) + fib(n - 2);
    }
  });

  verified('fib: precondition fib((n - 1))');
  verified('fib: precondition fib((n - 2))');
  incorrect('fib: (fib(n) >= n)');
  it('returns counter-example', async () => {
    const m = await vcs[2].verify();
    if (m.status != "incorrect") throw new Error();
    expect(m.model).to.have.property("n");
    expect(m.model.n).to.eql(2);
  });
});

describe('pure functions', () => {

  code(() => {
    let x = 0;

    function f() { ensures(pure()); x++; }
    function g() { ensures(pure()); return x + 1; }
    function h1() { }
    function h2a() { h1(); }
    function h2b() { ensures(pure()); h1(); }
    function h3a() { ensures(pure()); h2a(); }
    function h3b() { ensures(pure()); h2b(); }
  });

  unverified('f: pure()'); // not pure
  verified('g: pure()'); // pure
  verified('h2b: pure()'); // inlined h1 pure
  unverified('h3a: pure()'); // pure, but only one level inlining
  verified('h3b: pure()'); // calling other pure function
});

describe('fibonacci increasing (external proof)', () => {

  code(() => {
    function fib(n) {
      ensures(pure());

      if (n <= 1) return 1;
      return fib(n - 1) + fib(n - 2);
    }

    function fibInc(n) {
      requires(typeof(n) == 'number');
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
    function inc(n) {
      requires(typeof(n) == 'number');
      ensures(inc(n) > n);

      return n + 1;
    }

    function twice(f, n) {
      requires(spec(f, x => typeof(x) == 'number', x => f(x) > x));
      requires(typeof(n) == 'number');
      ensures(twice(f, n) > n + 1);

      return f(f(n));
    }

    const x = 3;
    const y = twice(inc, x);
    assert(y >= 5);
  });

  verified('inc: (inc(n) > n)');
  verified('twice: precondition f(n)');
  verified('twice: precondition f(f(n))');
  verified('twice: (twice(f, n) > (n + 1))');
  verified('precondition twice(inc, x)');
  verified('assert: (y >= 5)');
});

describe.skip('mapLen example', () => {

  code(() => {
    function map(arr, f) {
      if (arr.length == 0) return [];
      return [f(arr[0])].concat(map(arr.slice(1), f));
    }

    function mapLen(arr, f) {
      requires(arr.constructor == Array);
      ensures(map(f, arr).length == arr.length);

      map(arr, f);
      if (arr.length > 0) {
        mapLen(arr.slice(1), f);
        map(arr.slice(1), f);
      }
    }
  });

  verified('mapLen: mapLen: requires: (arr.constructor == Array)');
  verified('mapLen: (map(f, arr).length == arr.length)');
});
