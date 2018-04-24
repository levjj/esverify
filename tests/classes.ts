import { expect } from 'chai';
import { verificationConditions } from '../src';
import { code, incorrect, verified } from './helpers';

declare const assert: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const pure: () => boolean;
declare const requires: (x: boolean) => void;
declare const spec: (f: any, r: (rx: any) => boolean, s: (sx: any, sy: any) => boolean) => boolean;

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
  verified('map: ((res === null) || (res instanceof List))');
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
  verified('map: ((res === null) || (res instanceof List))');
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
  verified('map: ((res === null) || ((res instanceof List) && (res.each === newEach)))');
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
  verified('precondition then(p, n => (n + 2))');
  verified('func: class invariant Promise');
  verified('precondition then(p2, n => new Promise((n + 5)))');
});

describe('simple class instance access', () => {

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
  incorrect('g: (res < 0)', ['a', { _cls_: 'A', _args_: [0] }]);
  verified('class invariant A');
  verified('assert: (a instanceof A)');
  verified('assert: (a instanceof Object)');
  verified('assert: ("b" in a)');
  verified('assert: (a.b > 22)');
  verified('assert: (a[p] > 22)');
});
