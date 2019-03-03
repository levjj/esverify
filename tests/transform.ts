import 'mocha';
import { expect } from 'chai';
import { transformSourceCode } from '../src';
import { sourceAsJavaScript } from '../src/parser';
import { stringifyTestCode } from '../src/codegen';
import { codeToString } from './helpers';

declare function ensures (x: boolean | ((y: any) => boolean)): void;
declare function requires (x: boolean): void;
declare function assert (x: boolean): void;

function expectTransformation (originalCode: () => any, expectedTransformedSource: string) {
  const originalSource = codeToString(originalCode);
  const expectedSource = stringifyTestCode(sourceAsJavaScript(expectedTransformedSource).body);
  const transformedSource = transformSourceCode(originalSource);
  expect(transformedSource).to.be.eql(expectedSource);
}

describe('source transformation', () => {

  it('retains assertions', () => {
    expectTransformation(() => {
      const x = 23;
      const y = 42;
      assert(x < y);
    }, `
    let x = 23;
    let y = 42;
    assert(x < y);`);
  });

  it('retains assertions in functions', () => {
    expectTransformation(() => {
      function f (x) {
        assert(x > 0);
      }
    }, `
    function f (x) {
      assert(x > 0);
    }`);
  });

  it('changes preconditions to assertions', () => {
    expectTransformation(() => {
      function f (x) {
        requires(Number.isInteger(x));
        return x;
      }
    }, `
    function f (x) {
      return x;
    }
    f = spec(f, 10371, (function (x) {
        assert(Number.isInteger(x));
        return [x];
    }), (x, _tmp_24438) => _tmp_24438);`);
  });

  it('changes postconditions to assertions', () => {
    expectTransformation(() => {
      function f (x) {
        ensures(y => y > 3);
        return x;
      }
    }, `
    function f (x) {
      return x;
    }
    f = spec(f, 10371, x => [x], (function (x, _tmp_24438) {
        assert(_tmp_24438 > 3);
        return _tmp_24438;
    }));`);
  });
});
