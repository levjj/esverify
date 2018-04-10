import { expect } from 'chai';
import { verificationConditions } from '../src/index';
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
    if (res.status === 'error' && debug) console.log(res);
    if (expected === 'verified' || expected === 'unverified') {
      const st = res.status === 'error' && res.type === 'incorrect' ? res.type : res.status;
      expect(st).to.be.eql(expected);
    } else {
      expect(res.status).to.equal('error');
      if (res.status === 'error') {
        expect(res.type).to.equal(expected);
      }
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
    expect(m.model.variables()).to.include('b');
    expect(m.model.valueOf('b')).to.eql({ type: 'bool', v: false });
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

describe('assert within function', () => {

  code(() => {
    function f (n) {
      requires(typeof(n) === 'number');
      ensures(res => res > 3);

      assert(n > 3);
      return n;
    }
  });

  incorrect('f: assert: (n > 3)');
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
    expect(m.model.variables()).to.include('n');
    expect(m.model.valueOf('n')).to.eql({ type: 'num', v: 2 });
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

  incorrect('f: (res > 22)');
  incorrect('g: (res > 22)');
  verified('h: (res > 22)');

  it('returns counter-example for missing invariant', async () => {
    const m = await vcs[0].verify();
    expect(m.description).to.eql('f: (res > 22)');
    if (m.status !== 'error' || m.type !== 'incorrect') throw new Error();
    expect(m.model.variables()).to.include('x');
    expect(m.model.valueOf({ name: 'x', heap: 3 })).to.eql({ type: 'num', v: 23 });
    expect(m.model.valueOf({ name: 'x', heap: 4 })).to.eql({ type: 'bool', v: true });
  });

  it('returns counter-example with insufficient invariant', async () => {
    const m = await vcs[3].verify();
    expect(m.description).to.eql('g: (res > 22)');
    if (m.status !== 'error' || m.type !== 'incorrect') throw new Error();
    expect(m.model.variables()).to.include('y');
    expect(m.model.valueOf({ name: 'y', heap: 3 })).to.eql({ type: 'num', v: 42 });
    expect(m.model.valueOf({ name: 'y', heap: 4 })).to.eql({ type: 'num', v: 0 });
  });
});

describe('simple class invariant', () => {

  code(() => {
    function greaterThree (y: number) {
      return y > 3;
    }

    class A {
      readonly x: number;
      constructor (x: number) {
        this.x = x;
      }
      invariant () {
        return greaterThree(this.x);
      }
    }

    function greaterTwo (a: A) {
      requires(a instanceof A);
      ensures(a.x > 2);
      greaterThree(a.x);
    }
  });

  verified('greaterTwo: a has property "x"');
  verified('greaterTwo: (a.x > 2)');
});

describe('class invariant with reference to mutable variable', () => {

  const code = () => {
    let x = 23;

    class A {
      readonly x: number;
      constructor (x: number) {
        this.x = x;
      }
      invariant () {
        return x > 4;
      }
    }
  };

  it('gets rejected', () => {
    const src = code.toString();
    const t = verificationConditions(src.substring(14, src.length - 2));
    expect(t).to.have.property('status', 'error');
    expect(t).to.have.property('type', 'reference-in-invariant');
  });
});

describe('mapLen internal', () => {

  code(() => {
    class List {
      head: any;
      tail: List;
      constructor (head, tail) {
        this.head = head; this.tail = tail;
      }
      invariant () { return this.tail === null || this.tail instanceof List; }
    }

    function len (lst) {
      requires(lst === null || lst instanceof List);
      ensures(res => typeof(res) === 'number');
      ensures(pure());
      return lst === null ? 0 : 1 + len(lst.tail);
    }

    function map (f, lst) {
      requires(lst === null || lst instanceof List);
      requires(spec(f, x => true, x => pure()));
      ensures(pure());
      ensures(res => res === null || res instanceof List);
      ensures(res => len(lst) === len(res));
      len(lst);
      const res = lst === null ? null : new List(f(lst.head), map(f, lst.tail));
      len(res);
      return res;
    }
  });

  verified('len: lst has property "tail"');
  verified('len: precondition len(lst.tail)');
  verified('len: (typeof(res) === "number")');
  verified('len: pure()');
  verified('map: precondition len(lst)');
  verified('map: lst has property "head"');
  verified('map: precondition f(lst.head)');
  verified('map: lst has property "tail"');
  verified('map: precondition map(f, lst.tail)');
  verified('map: class invariant List');
  verified('map: precondition len(res)');
  verified('map: pure()');
  verified('map: (res === null) || (res instanceof List)');
  verified('map: (len(lst) === len(res))');
});

describe('mapLen external', () => {

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

  verified('map: lst has property "head"');
  verified('map: precondition f(lst.head)');
  verified('map: lst has property "tail"');
  verified('map: precondition map(lst.tail, f)');
  verified('map: class invariant List');
  verified('map: pure()');
  verified('map: (res === null) || (res instanceof List)');
  verified('len: lst has property "tail"');
  verified('len: precondition len(lst.tail)');
  verified('len: pure()');
  verified('len: (res >= 0)');
  verified('mapLen: precondition len(lst)');
  verified('mapLen: precondition map(lst, f)');
  verified('mapLen: precondition len(map(lst, f))');
  verified('mapLen: assert: (l === 0)');
  verified('mapLen: assert: (r === 0)');
  verified('mapLen: lst has property "tail"');
  verified('mapLen: precondition len(lst.tail)');
  verified('mapLen: assert: (l === (l1 + 1))');
  verified('mapLen: lst has property "head"');
  verified('mapLen: precondition f(lst.head)');
  verified('mapLen: precondition map(lst.tail, f)');
  verified('mapLen: precondition len(map(lst.tail, f))');
  verified('mapLen: assert: (r === (r1 + 1))');
  verified('mapLen: precondition mapLen(lst.tail, f)');
  verified('mapLen: assert: (l1 === r1)');
  verified('mapLen: assert: (l === r)');
  verified('mapLen: pure()');
  verified('mapLen: (len(lst) === len(map(lst, f)))');

});

describe('map invariant', () => {

  code(() => {
    class List {
      head: any;
      tail: List;
      each: (element: any) => boolean;
      constructor (head, tail, each) {
        this.head = head; this.tail = tail; this.each = each;
      }
      invariant () {
        return spec(this.each, x => true, (x, y) => pure() && typeof(y) === 'boolean') &&
               this.each(this.head) &&
               (this.tail === null || this.tail instanceof List && this.each === this.tail.each);
      }
    }

    function map (f, lst, newEach) {
      requires(spec(newEach, x => true, (x, y) => pure() && typeof(y) === 'boolean'));
      requires(lst === null || spec(f, x => lst.each(x), (x, y) => pure() && newEach(y)));
      requires(lst === null || lst instanceof List);
      ensures(res => res === null || (res instanceof List && res.each === newEach));
      ensures(pure());
      if (lst === null) {
        return null;
      } else {
        return new List(f(lst.head), map(f, lst.tail, newEach), newEach);
      }
    }
  });

  verified('map: lst has property "head"');
  verified('map: lst has property "tail"');
  verified('map: precondition f(lst.head)');
  verified('map: precondition map(f, lst.tail, newEach)');
  verified('map: class invariant List');
  verified('map: pure()');
  verified('map: (res === null) || (res instanceof List) && (res.each === newEach)');
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

  verified('twice: spec(res, (x) => ((typeof(x) === "number")), ' +
                            '(x, y) => ((typeof(y) === "number") && (y > (x + 1))))');
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

describe('merge sort', () => {

  code(() => {
    class IntList {
      head: number;
      tail: null | IntList;
      constructor (head, tail) {
        this.head = head; this.tail = tail;
      }
      invariant () {
        return typeof(this.head) === 'number' && (this.tail === null || this.tail instanceof IntList);
      }
    }

    class IntListPartition {
      left: IntList;
      right: IntList;
      constructor (left, right) {
        this.left = left; this.right = right;
      }
      invariant () {
        return (this.left === null || this.left instanceof IntList) &&
              (this.right === null || this.right instanceof IntList);
      }
    }

    function partition (lst, fst, snd, alternate) {
      requires(lst === null || lst instanceof IntList);
      requires(fst === null || fst instanceof IntList);
      requires(snd === null || snd instanceof IntList);
      requires(typeof(alternate) === 'boolean');
      ensures(res => res instanceof IntListPartition);
      ensures(pure());

      if (lst === null) {
        return new IntListPartition(fst, snd);
      } else if (alternate) {
        return partition(lst.tail, new IntList(lst.head, fst), snd, false);
      } else {
        return partition(lst.tail, fst, new IntList(lst.head, snd), true);
      }
    }

    function isSorted (list) {
      requires(list === null || list instanceof IntList);
      ensures(res => typeof(res) === 'boolean');
      ensures(pure());

      return list === null || list.tail === null ||
            list.head <= list.tail.head && isSorted(list.tail);
    }

    function merge (left, right) {
      requires(left === null || left instanceof IntList);
      requires(isSorted(left));
      requires(right === null || right instanceof IntList);
      requires(isSorted(right));
      ensures(res => res === null || res instanceof IntList);
      ensures(res => isSorted(res));
      ensures(res => (left === null && right === null) === (res === null));
      ensures(res => !(left !== null && (right === null || right.head >= left.head))
                      ||
                    (res !== null && res.head === left.head));
      ensures(res => !(right !== null && (left === null || right.head < left.head))
                      ||
                    (res !== null && res.head === right.head));
      ensures(pure());

      if (left === null) {
        return right;
      } else if (right === null) {
        return left;
      } else if (left.head <= right.head) {
        isSorted(left);
        isSorted(left.tail);
        const merged = merge(left.tail, right);
        const res = new IntList(left.head, merged);
        isSorted(res);
        return res;
      } else {
        isSorted(right);
        isSorted(right.tail);
        const merged = merge(left, right.tail);
        const res = new IntList(right.head, merged);
        isSorted(res);
        return res;
      }
    }

    function sort (list) {
      requires(list === null || list instanceof IntList);
      ensures(res => res === null || res instanceof IntList);
      ensures(res => isSorted(res));
      ensures(pure());

      if (list === null || list.tail === null) {
        isSorted(list);
        assert(isSorted(list));
        return list;
      }
      const part = partition(list, null, null, false);
      return merge(sort(part.left), sort(part.right));
    }
  });

  verified('partition: class invariant IntListPartition');
  verified('partition: lst has property "head"');
  verified('partition: lst has property "tail"');
  verified('partition: class invariant IntList');
  verified('partition: precondition partition(lst.tail, new IntList(lst.head, fst), snd, false)');
  verified('partition: precondition partition(lst.tail, fst, new IntList(lst.head, snd), true)');
  verified('partition: (res instanceof IntListPartition)');
  verified('partition: pure()');
  verified('isSorted: list has property "head"');
  verified('isSorted: list has property "tail"');
  verified('isSorted: precondition isSorted(list.tail)');
  verified('isSorted: (typeof(res) === "boolean")');
  verified('isSorted: pure()');
  verified('merge: left has property "head"');
  verified('merge: left has property "tail"');
  verified('merge: right has property "head"');
  verified('merge: right has property "tail"');
  verified('merge: precondition isSorted(left)');
  verified('merge: precondition isSorted(left.tail)');
  verified('merge: precondition merge(left.tail, right)');
  verified('merge: class invariant IntList');
  verified('merge: precondition isSorted(res)');
  verified('merge: precondition isSorted(right)');
  verified('merge: precondition isSorted(right.tail)');
  verified('merge: precondition merge(left, right.tail)');
  verified('merge: class invariant IntList');
  verified('merge: precondition isSorted(res)');
  verified('merge: (res === null) || (res instanceof IntList)');
  verified('merge: isSorted(res)');
  verified('merge: ((left === null) && (right === null) === (res === null))');
  verified('merge: !(left !== null) && (right === null) || (right.head >= left.head) || ' +
                  '(res !== null) && (res.head === left.head)');
  verified('merge: !(right !== null) && (left === null) || (right.head < left.head) || ' +
                  '(res !== null) && (res.head === right.head)');
  verified('merge: pure()');
  verified('sort: list has property "tail"');
  verified('sort: precondition isSorted(list)');
  verified('sort: assert: isSorted(list)');
  verified('sort: precondition partition(list, null, null, false)');
  verified('sort: part has property "left"');
  verified('sort: precondition sort(part.left)');
  verified('sort: part has property "right"');
  verified('sort: precondition sort(part.right)');
  verified('sort: precondition merge(sort(part.left), sort(part.right))');
  verified('sort: (res === null) || (res instanceof IntList)');
  verified('sort: isSorted(res)');
  verified('sort: pure()');
});

describe('promise', () => {

  code(() => {
    class Promise {
      value: any;
      constructor (value) {
        this.value = value;
      }
    }

    function resolve (fulfill) {
      // fulfill is value, promise or then-able
      requires(!('then' in fulfill) || spec(fulfill.then, () => true, () => true));

      if (fulfill instanceof Promise) {
        return fulfill;
      } else if ('then' in fulfill) {
        return new Promise(fulfill.then());
      } else {
        return new Promise(fulfill);
      }
    }

    function then (promise, fulfill) {
      // fulfill returns value or promise
      requires(promise instanceof Promise);
      requires(spec(fulfill, x => true, (x, res) => true));

      const res = fulfill(promise.value);
      if (res instanceof Promise) {
        return res;
      } else {
        return new Promise(res);
      }
    }

    const p = resolve(0);
    const p2 = then(p, n => {
      return n + 2;
    });
    const p3 = then(p2, n => {
      return new Promise(n + 5);
    });
  });

  verified('resolve: fulfill has property "then"');
  verified('resolve: precondition fulfill.then()');
  verified('resolve: class invariant Promise');
  verified('resolve: class invariant Promise');
  verified('then: promise has property "value"');
  verified('then: precondition fulfill(promise.value)');
  verified('then: class invariant Promise');
  verified('precondition resolve(0)');
  verified('precondition then(p, (function  (n) {\n  return (n + 2);\n}))');
  verified('func: class invariant Promise');
  verified('precondition then(p2, (function  (n) {\n  return new Promise((n + 5));\n}))');
});

describe('simple object access', () => {

  code(() => {
    class A {
      b: number;
      constructor (b) {
        this.b = b;
      }
      invariant () {
        return this.b >= 0;
      }
    }

    function f (a: A) {
      requires(a instanceof A);
      ensures(res => res >= 0);

      return a.b;
    }

    function g (a: A) {
      requires(a instanceof A);
      ensures(res => res < 0);

      return a.b;
    }

    const a = new A(23);
    assert(a instanceof A);
    assert(a instanceof Object);
    assert('b' in a);
    assert(a.b > 22);
    assert(a['b'] > 22);
    const p = 'b';
    assert(a[p] > 22);
  });

  verified('f: a has property "b"');
  verified('f: (res >= 0)');
  verified('g: a has property "b"');
  incorrect('g: (res < 0)');
  verified('class invariant A');
  verified('assert: (a instanceof A)');
  verified('assert: (a instanceof Object)');
  verified('assert: ("b" in a)');
  verified('assert: (a.b > 22)');
  verified('assert: (a[p] > 22)');
});

describe('simple arrays', () => {

  code(() => {
    function f (a: Array<number>) {
      requires(a instanceof Array);
      requires(a.length >= 1);

      return a[0];
    }

    function g (a: Array<number>) {
      requires(a instanceof Array);
      requires(a.length >= 1);
      ensures(res => res > 0);

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
  incorrect('g: (res > 0)');

  it('g: (res > 0) returns counter-example', async () => {
    const m = await vcs[2].verify();
    expect(m.description).to.eql('g: (res > 0)');
    if (m.status !== 'error' || m.type !== 'incorrect') throw new Error();
    expect(m.model.variables()).to.include('a');
    expect(m.model.valueOf('a')).to.eql({ type: 'arr', elems: [{ type: 'str', v: 'number' }] });
  });

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
