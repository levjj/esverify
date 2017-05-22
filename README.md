esverify
========

Program Verification for ECMAScript/JavaScript

Example
-------

Given a simple JavaScript `max` function, we can add pre- and post-conditions
using special pseudo-calls to `requires` and `ensures` with boolean expressions.

```js
function max(a, b) {
  requires(typeof(a) == "number");
  requires(typeof(b) == "number");
  ensures(max(a,b) >= a);

  if (a >= b) {
    return a;
  } else {
    return b;
  }
}
```

These expressions will then be statically verified with respect to the function
body with an SMT solver.

More examples can be found in the `tests` directory.

Supported Features:

* expressions with boolean values, integer arithmetic and strings
* function pre- and postconditions as well as inline assertions and invariants
* automatically generates counter-examples for failed assertions
* runs counter-example as JavaScript code to reproduce errors in dynamic context
  and differentiate incorrect programs from false negatives
* mutable variables and limited temporal reasoning, e.g. `old(x) > x`
* control flow including branching, returns and while loops with manually
  specified invariants
* inductive reasoning with loop invariants and recursive functions
* automatic inlining of function body for external proofs of function properties
  (restricted to one level of inlining)
* closures
* checking of function purity
* higher-order functions
* simple and higher-order proofs

It is based on the [z3](https://github.com/Z3Prover/z3) SMT solver but avoids
trigger heuristics and thereby timeouts and other unpredictable results by
requiring manual instantiation with function calls which will be used for a
deterministic trigger instantiation.

Usage
-----

    npm install -g esverify
    esverify max.js

Interactive Tools
-----------------

More tool support will be coming soon.

As a first step, there is a
[verification workspace](https://github.com/levjj/esverify-editor) which allows
inspection of verification results including potential counter-examples.

Additionally, there is a [Vim Plugin](https://github.com/levjj/esverify-vim)
which displays verification results inline.

Acknowledgements
----------------

Inspired by [Dafny](https://github.com/Microsoft/dafny) and
[LiquidHaskell](https://github.com/ucsd-progsys/liquidhaskell).

