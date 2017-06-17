import { expect } from 'chai';
import { verificationConditions } from '../index';
import { log } from '../src/message';
import { setOptions } from '../src/options';
import VerificationCondition from '../src/verification';

declare const requires: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const invariant: (x: boolean) => void;
declare const assert: (x: boolean) => void;
declare const old: (x: any) => any;
declare const pure: () => boolean;
declare const spec: (f: any, r: (rx: any) => boolean, s: (sx: any, sy: any) => boolean) => boolean;

let vcs: Array<VerificationCondition>;

function code (fn: () => any) {
  before(() => {
    const code = fn.toString();
    const t = verificationConditions(code.substring(14, code.length - 2));
    if (!(t instanceof Array)) {
      log(t);
      if (t.status === 'error' && t.type === 'unexpected') console.log(t.error);
      throw new Error('failed to find verification conditions');
    }
    vcs = t;
  });
}

function helper (expected: 'verified' | 'unverified' | 'incorrect', description: string, debug: boolean = false) {
  const body = async () => {
    /* tslint:disable:no-unused-expression */
    if (debug) {
      setOptions({ quiet: false, verbose: true });
      console.log(vcs.map(vc => vc.description).join('\n'));
    }
    const vc = vcs.find(v => v.description === description);
    expect(vc).to.be.ok;
    const res = await vc.verify();
    if (res.status === 'error' && res.type === 'unexpected') console.log(res.error);
    if (expected === 'verified' || expected === 'unverified') {
      const st = res.status === 'error' && res.type === 'incorrect' ? res.type : res.status;
      expect(st).to.be.eql(expected);
    } else {
      expect(res.status === 'error' && res.type === expected).to.be.true;
    }
  };
  if (debug) {
    it.only(description + ' ' + expected, body);
  } else {
    it(description + ' ' + expected, body);
  }
}

function skip (description: string) { it.skip(description); }
function verified (description: string) { helper('verified', description); }
function unverified (description: string) { helper('unverified', description); }
function incorrect (description: string) { helper('incorrect', description); }

function verifiedDebug (description: string) { helper('verified', description, true); }
function unverifiedDebug (description: string) { helper('unverified', description, true); }
function incorrectDebug (description: string) { helper('incorrect',description, true); }

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
    expect(vcs).to.have.length(1);
  });

  it('has a description', async () => {
    expect(vcs[0].description).to.be.eql('max: (res >= a)');
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

  unverified('max: (res >= a)');

  it('returns counter-example', async () => {
    const m = await vcs[0].verify();
    if (m.status !== 'unverified') throw new Error();
    expect(m.model).to.have.property('b');
    expect(m.model.b).to.eql(false);
  });
});

describe('counter', () => {

  code(() => {
    let counter = 0;
    invariant(typeof counter === 'number');
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

  verified('initially: (typeof(counter) === "number")');
  verified('initially: (counter >= 0)');
  verified('increment: (counter > old_counter)');
  verified('increment: (typeof(counter) === "number")');
  verified('increment: (counter >= 0)');
  verified('decrement: (old_counter > 0) ? (counter < old_counter) : (counter === old_counter)');
  verified('decrement: (typeof(counter) === "number")');
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
    function sumTo (n) {
      requires(typeof n === 'number');
      requires(n >= 0);
      ensures(res => res === (n + 1) * n / 2);

      let i = 0;
      let s = 0;
      while (i < n) {
        invariant(i <= n);
        invariant(s === (i + 1) * i / 2);
        i++;
        s = s + i;
      }
      return s;
    }
  });

  verified('sumTo: invariant on entry: (i <= n)');
  verified('sumTo: invariant on entry: (s === (((i + 1) * i) / 2))');
  verified('sumTo: invariant maintained: (i <= n)');
  verified('sumTo: invariant maintained: (s === (((i + 1) * i) / 2))');
  verified('sumTo: (res === (((n + 1) * n) / 2))');
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
  unverified('assert: (k === 5)'); // only inline one level
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
      requires(typeof(n) === 'number');
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
      requires(typeof(n) === 'number');
      requires(n >= 0);
      ensures(res => res >= n);

      if (n <= 1) return n;
      return fib(n - 1) + fib(n - 2);
    }
  });

  verified('fib: precondition fib((n - 1))');
  verified('fib: precondition fib((n - 2))');
  incorrect('fib: (res >= n)');
  it('returns counter-example', async () => {
    const m = await vcs[2].verify();
    if (m.status !== 'error' || m.type !== 'incorrect') throw new Error();
    expect(m.model).to.have.property('n');
    expect(m.model.n).to.eql(2);
  });
});

describe('pure functions', () => {

  code(() => {
    let x = 0;

    function f () { ensures(pure()); x++; }
    function g () { ensures(pure()); return x + 1; }
    function h1 () { /*empty*/ }
    function h2a () { h1(); }
    function h2b () { ensures(pure()); h1(); }
    function h3a () { ensures(pure()); h2a(); }
    function h3b () { ensures(pure()); h2b(); }
  });

  unverified('f: pure()'); // not pure
  verified('g: pure()'); // pure
  verified('h2b: pure()'); // inlined h1 pure
  unverified('h3a: pure()'); // pure, but only one level inlining
  verified('h3b: pure()'); // calling other pure function
});

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
      requires(spec(f, x => x >= 0, x => pure() && typeof (f(x)) === 'number'));
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

describe('mapLen example', () => {

  code(() => {

    class List {
      head: any;
      tail: List;
      constructor (head, tail) { this.head = head; this.tail = tail; }
      invariant () { return this.tail === null || this.tail instanceof List; }
    }

    function map (lst, f) {
      requires(lst === null || lst instanceof List);
      requires(spec(f, x => true, x => pure()));
      ensures(pure());
      ensures(res => res === null || res instanceof List);

      if (lst === null) return null;
      return new List(f(lst.head), map(lst.tail, f));
    }

    function len (lst) {
      requires(lst === null || lst instanceof List);
      ensures(pure());
      ensures(res => res >= 0);

      return lst === null ? 0 : len(lst.tail) + 1;
    }

    function mapLen (lst, f) {
      requires(lst === null || lst instanceof List);
      requires(spec(f, x => true, x => pure()));
      ensures(pure());
      ensures(len(lst) === len(map(lst, f)));

      const l = len(lst);
      const r = len(map(lst, f));
      if (lst === null) {
        assert(l === 0);
        assert(r === 0);
      } else {
        const l1 = len(lst.tail);
        assert(l === l1 + 1);

        f(lst.head);
        const r1 = len(map(lst.tail, f));
        assert(r === r1 + 1);

        mapLen(lst.tail, f);
        assert(l1 === r1);
        assert(l === r);
      }
    }
  });

  verified('map: property head exists on object');
  verified('map: precondition f(lst.head)');
  verified('map: property tail exists on object');
  verified('map: precondition map(lst.tail, f)');
  verified('map: class invariant List');
  verified('map: pure()');
  verified('map: (res === null) || (res instanceof List)');
  verified('len: property tail exists on object');
  verified('len: precondition len(lst.tail)');
  verified('len: pure()');
  verified('len: (res >= 0)');
  verified('mapLen: precondition len(lst)');
  verified('mapLen: precondition map(lst, f)');
  verified('mapLen: precondition len(map(lst, f))');
  verified('mapLen: assert: (l === 0)');
  verified('mapLen: assert: (r === 0)');
  verified('mapLen: property tail exists on object');
  verified('mapLen: precondition len(lst.tail)');
  verified('mapLen: assert: (l === (l1 + 1))');
  verified('mapLen: property head exists on object');
  verified('mapLen: precondition f(lst.head)');
  verified('mapLen: property tail exists on object');
  verified('mapLen: precondition map(lst.tail, f)');
  verified('mapLen: precondition len(map(lst.tail, f))');
  verified('mapLen: assert: (r === (r1 + 1))');
  verified('mapLen: property tail exists on object');
  verified('mapLen: precondition mapLen(lst.tail, f)');
  verified('mapLen: assert: (l1 === r1)');
  verified('mapLen: assert: (l === r)');
  verified('mapLen: pure()');
  verified('mapLen: (len(lst) === len(map(lst, f)))');

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

  verified('twice: spec(res, (x) => ((typeof(x) === "number")), (x, y) => ((typeof(y) === "number") && (y > (x + 1))))');
});

describe('function bug', () => {

  code(() => {
    function f (x) {
      ensures(!spec(f, y => true, y => y !== x));
      f(x);
    }
  });

  verified('f: !spec(f, (y) => (true), (y) => ((y !== x)))');
});
