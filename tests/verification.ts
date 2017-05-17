/* eslint no-unused-expressions:0 */
/* global describe, it, expect, requires, ensures, invariant, assert, old, spec, pure, console */

/// <reference path="../typings/mocha/mocha.d.ts" />
/// <reference path="../typings/chai/chai.d.ts" />
import { expect, use } from 'chai';
import * as chaiSubset from 'chai-subset';
import { verify } from '../index';
import VerificationCondition from '../src/verification';

declare const requires: (x: any) => void;
declare const ensures: (x: any) => void;
declare const invariant: (x: any) => void;
declare const assert: (x: any) => void;
declare const old: (x: any) => any;
declare const pure: () => boolean;
declare const spec: (f: any, r: (rx: any) => void, s: (sx: any) => void) => boolean;

use(chaiSubset);

let vcs: Array<VerificationCondition>;
function helper(description: string, expected: string, debug: boolean = false) {
  const body = async () => {
    const vc = vcs.find(v => v.description === description);
    expect(vc).to.not.be.undefined;
    if (!vc) throw new Error();
    await vc.solve();
    if (debug) vc.debugOut();
    expect(vc.result().status).to.be.eql(expected);
  };
  if (debug) {
    it.only(description.replace(/\n/g, ' ') + ' ' + expected, body);
  } else {
    it(description.replace(/\n/g, ' ') + ' ' + expected, body);
  }
}

function skip(description: string) { it.skip(description.replace(/\n/g, ' ')); }
function verified(description: string) { helper(description, 'verified'); }
function incorrect(description: string) { helper(description, 'incorrect'); }
function tested(description: string) { helper(description, 'tested'); }
function unknown(description: string) { helper(description, 'unknown'); }

function verifiedDebug(description: string) { helper(description, 'verified', true); }
function incorrectDebug(description: string) { helper(description, 'incorrect', true); }
function testedDebug(description: string) { helper(description, 'tested', true); }
function unknownDebug(description: string) { helper(description, 'unknown', true); }

describe('max()', () => {

  const code = (() => {
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
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  it('finds a verification conditions', () => {
    expect(vcs).to.have.length(1);
  });

  it('has a description', async () => {
    expect(vcs[0].description).to.be.eql('max:\n(max(a, b) >= a)');
  });

  verified('max:\n(max(a, b) >= a)');
});

describe('max() with missing pre', () => {

  const code = (() => {
    function max(a, b) {
      requires(typeof(b) == 'number');
      ensures(max(a, b) >= a);

      if (a >= b) {
        return a;
      } else {
        return b;
      }
    }
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  unknown('max:\n(max(a, b) >= a)');

  it.skip('returns counter-example', async () => {
    await vcs[0].solve();
    expect(vcs[0].getModel()).to.containSubset({
      a: false,
      b: 0,
    });
  });
});

describe('counter', () => {

  const code = (() => {
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
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('initially:\n(typeof(counter) == "number")');
  verified('initially:\n(counter >= 0)');
  verified('increment:\n(counter > old(counter))');
  verified('increment:\n(typeof(counter) == "number")');
  verified('increment:\n(counter >= 0)');
  verified('decrement:\n(old(counter) > 0) ? (counter < old(counter)) : (counter == old(counter))');
  verified('decrement:\n(typeof(counter) == "number")');
  verified('decrement:\n(counter >= 0)');
});

describe('simple steps', () => {

  const code = (() => {
    let i = 0;
    assert(i < 1);
    i = 3;
    assert(i < 2);
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('assert:\n(i < 1)');
  incorrect('assert:\n(i < 2)');
});

describe('loop', () => {

  const code = (() => {
    let i = 0;

    while (i < 5) {
      invariant(i <= 5);
      i++;
    }

    assert(i === 5);
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('invariant on entry:\n(i <= 5)');
  verified('invariant maintained:\n(i <= 5)');
  verified('assert:\n(i === 5)');
});

describe('loop with missing invariant', () => {

  const code = (() => {
    let i = 0;

    while (i < 5) {
      i++;
    }

    assert(i === 5);
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  tested('assert:\n(i === 5)');
});

describe('sum', () => {

  const code = (() => {
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
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('sumTo:\ninvariant on entry:\n(i <= n)');
  verified('sumTo:\ninvariant on entry:\n(s == (((i + 1) * i) / 2))');
  verified('sumTo:\ninvariant maintained:\n(i <= n)');
  verified('sumTo:\ninvariant maintained:\n(s == (((i + 1) * i) / 2))');
  verified('sumTo:\n(sumTo(n) == (((n + 1) * n) / 2))');
});


describe('global call', () => {

  const code = (() => {
    function inc(n) {
      requires(typeof(n) == 'number');
      ensures(inc(n) > n);

      return n + 1;
    }

    let i = 3;
    let j = inc(i);
    assert(j > 3);
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('precondition inc(i)');
  verified('assert:\n(j > 3)');
  verified('inc:\n(inc(n) > n)');
});

describe('inline global call', () => {

  const code = (() => {
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
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('assert:\n(j == 4)');
  unknown('assert:\n(k == 5)'); // only inline one level
});

describe('post conditions global call', () => {

  const code = (() => {
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
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('inc:\n(inc(n) > n)')
  unknown('inc2:\nprecondition inc(n)');
  unknown('inc2:\nprecondition inc(inc(n))');
  verified('precondition inc(i)');
  verified('assert:\n(j >= 4)');
  verified('precondition inc2(i)');
  unknown('assert:\n(k >= 5)'); // only inline one level, so post-cond of inc(inc(i)) not available
});

describe('mutable variables', () => {

  const code = (() => {
    let x = 2;
    const y = 3;
    function f(z) {
      requires(x < y);
    }
    f(0);
    x = 4;
    f(1);
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('precondition f(0)');
  unknown('precondition f(1)');
});

describe('closures', () => {

  const code = (() => {
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
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('assert:\n(g1 == 1)');
  verified('assert:\n(h1 == 2)');
});

describe('fibonacci increasing', () => {

  const code = (() => {
    function fib(n) {
      requires(typeof(n) == 'number');
      requires(n >= 0);
      ensures(fib(n) >= n);
      ensures(fib(n) >= 1);

      if (n <= 1) return 1;
      return fib(n - 1) + fib(n - 2);
    }
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('fib:\nprecondition fib((n - 1))');
  verified('fib:\nprecondition fib((n - 2))');
  verified('fib:\n(fib(n) >= n)');
});

describe('buggy fibonacci', () => {

  const code = (() => {
    function fib(n) {
      requires(typeof(n) == 'number');
      requires(n >= 0);
      ensures(fib(n) >= n);

      if (n <= 1) return n;
      return fib(n - 1) + fib(n - 2);
    }
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('fib:\nprecondition fib((n - 1))');
  verified('fib:\nprecondition fib((n - 2))');
  unknown('fib:\n(fib(n) >= n)');
  it.skip('returns counter-example', async () => {
    await vcs[4].solve();
    expect(vcs[4].getModel()).to.containSubset({
      n: 2
    });
  });
});

describe('pure functions', () => {

  const code = (() => {
    let x = 0;

    function f() { ensures(pure()); x++; }
    function g() { ensures(pure()); return x + 1; }
    function h1() { }
    function h2a() { h1(); }
    function h2b() { ensures(pure()); h1(); }
    function h3a() { ensures(pure()); h2a(); }
    function h3b() { ensures(pure()); h2b(); }
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  unknown('f:\npure()'); // not pure
  verified('g:\npure()'); // pure
  verified('h2b:\npure()'); // inlined h1 pure
  unknown('h3a:\npure()'); // pure, but only one level inlining
  verified('h3b:\npure()'); // calling other pure function
});

describe('fibonacci increasing (external proof)', () => {

  const code = (() => {
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
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('fib:\npure()');
  verified('fibInc:\nprecondition fibInc((n - 1))');
  verified('fibInc:\nprecondition fibInc((n - 2))');
  verified('fibInc:\n(fib(n) >= n)');
});

describe('simple higher-order functions', () => {

  const code = (() => {
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
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('inc:\n(inc(n) > n)');
  verified('twice:\nprecondition f(n)');
  verified('twice:\nprecondition f(f(n))');
  verified('twice:\n(twice(f, n) > (n + 1))');
  verified('precondition twice(inc, x)');
  verified('assert:\n(y >= 5)');
});

describe.skip('mapLen example', () => {

  const code = (() => {
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
  }).toString();

  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error('failed to find verification conditions');
    vcs = t;
  });

  verified('mapLen:\nmapLen:\nrequires:\n(arr.constructor == Array)');
  verified('mapLen:\n(map(f, arr).length == arr.length)');
});
