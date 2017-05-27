# esverify

[![Build Status](https://travis-ci.org/levjj/esverify.svg?branch=master)](https://travis-ci.org/levjj/esverify)

Program Verification for ECMAScript/JavaScript

## Example

Given a simple JavaScript `max` function, we can add pre- and post-conditions
using special pseudo-calls to `requires` and `ensures` with boolean expressions.

```js
function max(a, b) {
  requires(typeof(a) === "number");
  requires(typeof(b) === "number");
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
* simple immutable classes with invariants (no methods or inheritance)

It is based on the [z3](https://github.com/Z3Prover/z3) SMT solver but avoids
trigger heuristics and thereby timeouts and other unpredictable results by
requiring manual instantiation with function calls which will be used for a
deterministic trigger instantiation.

## Usage as Command Line Tool

```
$ npm install -g esverify

...

$ esverify --help
Usage: esverify [OPTIONS] FILE

Options:
  -f, --logformat FORMAT  Format can be either "simple" or "colored"
                          (default format is "colored")
  --z3path PATH           Path to local z3 executable
                          (default path is "z3")
  -r, --remote            Invokes z3 remotely via HTTP request
  --z3url URL             URL to remote z3 web server
  -q, --quiet             Suppresses output
  -h, --help              Prints this help text and exit
  -v, --version           Prints version information
```

## Usage as Library

Installation via npm:

```
$ npm install esverify --save
```

Can now import `verify` which returns a promise of messages:

```js
import { verify } from "esverify";

const opts = { };
const msgs = await verify("assert(1 > 2);", opts);
msgs.forEach(msg => console.log(msg.status));
```

The options and returned messages have the following structure:

```TypeScript
type opts = {
  filename: string,
  logformat: "simple" | "colored" = "colored",
  quiet: boolean = true,
  z3path: string = "z3",
  z3url: string,
  remote: boolean = false
}

type msg = {
  status: "verified" | "unverified" | "error",
  loc: { file: string, start: { line: number, column: number },
                       end:   { line: number, column: number }},
  description: string
}
```

## Interactive Tools

More tool support will be coming soon.

As a first step, there is a
[verification workspace](https://github.com/levjj/esverify-editor) which allows
inspection of verification results including potential counter-examples.

Additionally, there is a [Vim Plugin](https://github.com/levjj/esverify-vim)
which displays verification results inline.

## Acknowledgements

Inspired by [Dafny](https://github.com/Microsoft/dafny) and
[LiquidHaskell](https://github.com/ucsd-progsys/liquidhaskell).

