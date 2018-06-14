import { bisumulate } from './helpers';

declare function log (out: any): void;
declare function assert (x: boolean): void;
declare function spec<X,Y> (f: (X) => Y, id: number, r: (rx: X) => [X], s: (sx: X, sy: Y) => Y): (X) => Y;

describe('interpreter', () => {

  bisumulate('trivial program', () => {
    /* tslint:disable:no-unused-expression */
    0;
  }, 1);

  bisumulate('output', () => {
    log(0);
  }, 3);

  bisumulate('global', () => {
    log(Math);
  }, 3);

  bisumulate('literals', () => {
    log(undefined);
    log(null);
    log(true);
    log(23);
    log('foo');
  }, 15);

  bisumulate('unary operators', () => {
    log(-4);
    log(!false);
    log(typeof 23);
    log(void(0));
  }, 16);

  bisumulate('binary operators', () => {
    log((1 as any) === 2);
    log(('foo' as any) !== 'bar');
    log(12 < 23);
    log(32 >> 2);
    log(1 + 2);
    log('foo' + 'bar');
    log(3 * 5);
    log(0xFF & 0x80);
  }, 40);

  bisumulate('logical expressions', () => {
    log(23 && 42);
    log(0 && false);
    true && log(2);
    false && log(3);
    log(23 || false);
    log(0 || 42);
    true || log(2);
    false || log(3);
  }, 24);

  bisumulate('conditional expressions', () => {
    /* tslint:disable:no-constant-condition */
    log(true ? 23 : 42);
    log(false ? 'foo' : 'bar');
    true ? log(2) : log(4);
    false ? log('f') : log('b');
  }, 16);

  bisumulate('assignment', () => {
    let x = 0;
    log(x);
    x = 23;
    log(x);
  }, 10);

  bisumulate('sequence expressions', () => {
    log((log(0), log(1)));
  }, 8);

  bisumulate('calling native functions', () => {
    log(Math.max(4, 5));
    log(Number.isInteger(44));
  }, 13);

  bisumulate('calling native methods', () => {
    log('hello'.substring(1));
  }, 6);

  bisumulate('calling custom functions', () => {
    function inc (x) {
      log(x);
      return x + 1;
    }
    log(inc(12));
  }, 13);

  bisumulate('calling custom methods', () => {
    const o = {
      m: function (x) {
        log(x);
        return this.p + x;
      },
      p: 5
    };
    log(o.m(10));
  }, 19);

  bisumulate('new expressions', () => {
    class A { x: any;
      constructor (x) {
        this.x = x;
      }
    }
    const a = new A(23);
    log(a);
    log(a.x);
  }, 13);

  bisumulate('array expressions', () => {
    const a = [1, 2, 3, log(4), 5];
    log(a);
    log(a[2]);
  }, 17);

  bisumulate('object expressions', () => {
    const o = {
      a: 12,
      b: log(24)
    };
    log(o);
    log(o.a);
    log(o.b);
  }, 19);

  bisumulate('instanceof expressions', () => {
    log([] instanceof Array);
    log((23 as any) instanceof Array);
  }, 10);

  bisumulate('in expressions', () => {
    log(0 in [12]);
    log(4 in [12]);
    log('a' in { a: 23 });
    log('b' in { a: 23 });
  }, 24);

  bisumulate('member expressions', () => {
    log(Math.max);
    log(['abc'][0]);
    log(['abc'][2]);
    log({ a: 23 }.a);
    log({ a: 23 }['a']);
    log({ a: 23 }['b']);
    log((23 as any)['b']);
  }, 40);

  bisumulate('function expressions', () => {
    log((function f (x) { return x; }).name);
  }, 5);

  bisumulate('variable declarations', () => {
    const a = 23;
    log(a);
    let b;
    log(b);
    const c = a + 1;
    log(c);
    b = c;
    log(b);
    let d = b;
    log(d);
    {
      const e = 23;
      log(e + a);
    }
    // @ts-ignore: intentional error
    log(e);
  }, 36);

  bisumulate('closures', () => {
    function adder (x) {
      let s = 0;
      return y => x + y;
    }

    const add2 = adder(2);
    log(add2(3));
    log(add2(4));

    function counter () {
      let s = 0;
      return () => { s += 1; return s; };
    }

    const counter1 = counter();
    log(counter1());
    log(counter1());
    const counter2 = counter();
    log(counter1());
    log(counter2());
    log(counter1());
  }, 92);

  bisumulate('if statements', () => {
    if (true) {
      log(12);
    }
    if (false) {
      // @ts-ignore: intentionally unreachable
      log(20);
    }
    if (true) {
      log('foo');
    } else {
      // @ts-ignore: intentionally unreachable
      log('bar');
    }
    if ('str') {
      log('f');
    } else {
      // @ts-ignore: intentionally unreachable
      log('b');
    }
    if (0) {
      // @ts-ignore: intentionally unreachable
      log([1, 2]);
    } else {
      log([2, 1]);
    }
  }, 19);

  bisumulate('return statements', () => {
    function f (x) {
      log(x);
      if (x === 0) {
        log('hello');
        return 23;
      }
      log('ret');
      return x;
    }
    log(f(0));
    log(f(1));
  }, 33);

  bisumulate('while statements', () => {
    let i = 0;
    let s = 0;
    while (log(0), i < 4) {
      i++;
      s += i;
      log(i);
      log(s);
    }
    log(i);
    log(s);
  }, 108);

  bisumulate('class declarations', () => {
    class A {
      b: number;
      constructor (b) {
        this.b = b;
      }
      invariant () {
        return typeof this.b === 'number';
      }
      m (x) {
        log('A.m');
        log(x);
        return this.n(x + 1) + x;
      }
      n (x) {
        log('A.n');
        log(x);
        return 1;
      }
    }

    const a = new A(5);
    log(a.m(4));
    log(a.n(0));
    log(a.n(5));
    log((new A(-1)).m(-4));

    class B {
      constructor () { /* emtpy */ }
      method () {
        log('B.method');
        return 23;
      }
    }

    const b = new B();
    const bm = b.method;
    log(bm());
  }, 112);

  bisumulate('assert', () => {
    assert(1 < 3);
    assert(Number.isInteger(23));
    assert(0 > 23);
  }, 15);

  bisumulate('spec, unwrapped call', () => {
    function f (x) { log(x); return x; }
    const f2 = spec(f, 23, x => { assert(x > 0); return [x]; }, (x, y) => { assert(y > 0); return y; });
    log(f(-2));
  }, 19);

  bisumulate('spec, valid call', () => {
    function f (x) { log(x); return x; }
    const f2 = spec(f, 23, x => { assert(x > 0); return [x]; }, (x, y) => { assert(y > 0); return y; });
    log(f2(2));
  }, 37);

  bisumulate('spec, violate pre', () => {
    function f (x) { log(x); return 23; }
    const f2 = spec(f, 23, x => { assert(x > 0); return [x]; }, (x, y) => { assert(y > 0); return y; });
    log(f2(-2));
  }, 17);

  bisumulate('spec, violate post', () => {
    function f (x) { log(x); return -4; }
    const f2 = spec(f, 23, x => { assert(x > 0); return [x]; }, (x, y) => { assert(y > 0); return y; });
    log(f2(2));
  }, 32);
});
