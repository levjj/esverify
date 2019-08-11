# esverify

[![Build Status](https://api.travis-ci.com/levjj/esverify.svg?branch=master)](https://travis-ci.com/levjj/esverify)
[![NPM Version](https://img.shields.io/npm/v/esverify.svg)](https://www.npmjs.com/package/esverify)
[![Greenkeeper badge](https://badges.greenkeeper.io/levjj/esverify.svg)](https://greenkeeper.io/)

Program Verification for ECMAScript/JavaScript ([esverify.org](http://esverify.org/)).

**Alpha: This is still a research prototype and not yet ready for production use.**

## Documentation

A detailed documentation of esverify and its theoretical foundations is
currently work-in-progress and will be published soon.

## Example

Given a simple JavaScript `max` function, we can add pre- and post-conditions
using special pseudo-calls to `requires` and `ensures` with boolean expressions.

```js
function max(a, b) {
  requires(typeof a === "number");
  requires(typeof b === "number");
  ensures(res => res >= a);

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

## Supported Features

* Expressions with boolean values, strings, integer and real number arithmetic
* Function pre- and post conditions as well as inline assertions and invariants
* Automatically generates counter-examples for failed assertions
* Runs counter-example as JavaScript code to reproduce errors in dynamic context
  and differentiate incorrect programs from false negatives
* Mutable variables and limited temporal reasoning, e.g. `old(x) > x`
* Control flow including branching, returns and while loops with manually
  specified invariants
* Inductive reasoning with loop invariants and recursive functions
* Automatic inlining of function body for external proofs of function properties
  (restricted to one level of inlining)
* Closures
* Checking of function purity
* Higher-order functions
* Simple proof checking using Curry-Howard correspondence
* Simple immutable classes with fields, methods and class invariant (no inheritance)
* Immutable JavaScript objects using string keys
* Immutable arrays (no sparse arrays)
* Restricted verifier preamble for global objects such as `console` and `Math`

It is based on the [z3](https://github.com/Z3Prover/z3) SMT solver but avoids
trigger heuristics and thereby (most) timeouts and other unpredictable results by
requiring manual instantiation. Function definitions and class invariants correspond
to universal quantifiers and function calls and field access act as triggers that
instantiate these quantifiers in a deterministic way.

## To Do (see [GitHub issues](https://github.com/levjj/esverify/issues))

* Termination checking
* Mutable objects, arrays and classes
* Modules with imports and exports
* Prototype and subclass inheritance
* Verifier-only "ghost" variables, arguments and functions/predicates
* TypeScript as input language

## Usage as Command Line Tool

Simple usage without installation:

```
$ npx esverify file.js
```

Installation:

```
$ npm install -g esverify
```

Command Line Options:

```
$ esverify --help
Usage: esverify [OPTIONS] FILE

Options:
  --z3path PATH           Path to local z3 executable
                          (default path is "z3")
  -r, --remote            Invokes z3 remotely via HTTP request
  --z3url URL             URL to remote z3 web server
  --noqi                  Disables quantifier instantiations
  -t, --timeout SECS      Sets timeout in seconds for z3
                          (default timeout is 10s, 0 disables timeout)
  -f, --logformat FORMAT  Format can be either "simple" or "colored"
                          (default format is "colored")
  -q, --quiet             Suppresses output
  -v, --verbose           Prints SMT input, output and test code
  --logsmt PATH           Path for logging SMT input in verbose mode
                          (default path is "/tmp/vc.smt")
  -h, --help              Prints this help text and exit
  --version               Prints version information
```

## Usage as Library

Installation via npm:

```
$ npm install esverify --save
```

Import `verify` and invoke on source code to receive a promise of messages.

```js
import { verify } from "esverify";

const opts = { };
const messages = await verify("assert(1 > 2);", opts);
messages.forEach(msg => console.log(msg.status));
```

The options and returned messages have the following structure:

```ts
type opts = {
  filename: string,
  logformat: "simple" | "colored" = "colored",
  z3path: string = "z3",
  z3url: string,
  remote: boolean = false,
  quiet: true,
  verbose: false,
  logsmt: '/tmp/vc.smt'
  timeout: 5,
  qi: true
}

type msg = {
  status: "verified" | "unverified" | "timeout" | "error",
  loc: { file: string, start: { line: number, column: number },
                       end:   { line: number, column: number }},
  description: string
}
```

## Interactive Tools

A simple [web-based editor](https://github.com/levjj/esverify-editor)
is available online at [esverify.org/try](http://esverify.org/try).

Additionally, there is a [Vim Plugin](https://github.com/levjj/esverify-vim)
and an [Emacs Plugin](https://github.com/SohumB/flycheck-esverify)
which display verification results inline.

More tool support will be coming soon.

## License

[MIT License](https://github.com/levjj/esverify/blob/master/LICENSE)

## Issues

Please report bugs to the [GitHub Issue Tracker](https://github.com/levjj/esverify/issues). esverify is currently developed and maintained by [Christopher Schuster](https://livoris.net/).

## Acknowledgements

Inspired by [Dafny](https://github.com/Microsoft/dafny) and
[LiquidHaskell](https://github.com/ucsd-progsys/liquidhaskell).

This project is developed by the
[Software and Languages Research Group at University of California, Santa Cruz](http://slang.soe.ucsc.edu/).
Thanks also to Tommy, Sohum and Cormac for support and advice.
