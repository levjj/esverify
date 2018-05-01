import { code, incorrect, verified } from './helpers';

declare const assert: (x: boolean) => void;
declare const ensures: (x: boolean | ((y: any) => boolean)) => void;
declare const requires: (x: boolean) => void;

describe('simple object access', () => {

  code(() => {
    function f (a) {
      requires('b' in a);
      requires(a.b >= 1);
      ensures(res => res >= 0);

      return a.b;
    }

    function g (a) {
      requires('b' in a);
      requires(a.b >= 1);
      ensures(res => res < 0);

      return a.b;
    }

    const a = { b: 23 };
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
  incorrect('g: (res < 0)', ['a', { b: 1, _str_: 2, length: 0 }]);
  verified('assert: (a instanceof Object)');
  verified('assert: ("b" in a)');
  verified('assert: (a.b > 22)');
  verified('assert: (a[p] > 22)');
});
