/// <reference path="../typings/mocha/mocha.d.ts" />
/// <reference path="../typings/chai/chai.d.ts" />
import { expect, use } from "chai";
import * as chaiSubset from "chai-subset";
use(chaiSubset);

import { verify } from "../index";
import VerificationCondition from "../src/vc";

let vcs: Array<VerificationCondition>;
function helper(description: string, expected: string, debug: boolean = false) {
  const body = async () => {
    const vc = vcs.find(vc => vc.description == description);
    expect(vc).to.not.be.undefined;
    if (!vc) throw new Error();
    await vc.solve();
    if (debug) vc.debugOut();
    expect(vc.result().status).to.be.eql(expected);
  };
  if (debug) {
    it.only(description.replace(/\n/g, " "), body);
  } else {
    it(description.replace(/\n/g, " "), body);
  }
}

function sat(description: string) { helper(description, "sat"); }
function unsat(description: string) { helper(description, "unsat"); }
function notest(description: string) { helper(description, "notest"); }

function satDebug(description: string) { helper(description, "sat", true); }
function unsatDebug(description: string) { helper(description, "unsat", true); }
function notestDebug(description: string) { helper(description, "notest", true); }

describe("max()", () => {
  
  const code = (() => {
    function max(a, b) {
      requires(typeof(a) == "number");
      requires(typeof(b) == "number");
      if (a >= b) {
        return a;
      } else {
        return b;
      }
      ensures(max(a, b) >= a);
    }
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  it("finds a verification conditions", () => {
    expect(vcs).to.have.length(1);
  });
  
  it("has a description", async () => {
    expect(vcs[0].description).to.be.eql("max:\n(max(a, b) >= a)");
  });

  sat("max:\n(max(a, b) >= a)");
});

describe("max() with missing pre", () => {
  
  const code = (() => {
    function max(a, b) {
      requires(typeof(b) == "number");
      if (a >= b) {
        return a;
      } else {
        return b;
      }
      ensures(max(a, b) >= a);
    }
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  notest("max:\n(max(a, b) >= a)");
  
  it("returns counter-example", async () => {
    await vcs[0].solve();
    expect(vcs[0].getModel()).to.containSubset({
      a: false,
      b: 0,
    });
  });
});

describe("counter", () => {
  
  const code = (() => {
    let counter = 0;
    invariant(typeof counter == "number");
    invariant(counter >= 0);
    
    function increment() {
      counter++;
      ensures(counter > old(counter));
    }
    
    function decrement() {
      if (counter > 0) counter--;
      ensures(old(counter) > 0 ? counter < old(counter) : counter == old(counter));
    }
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  sat('initially:\n(typeof(counter) == "number")');
  sat("initially:\n(counter >= 0)");
  sat("increment:\n(counter > old(counter))");
  sat('increment:\n(typeof(counter) == "number")');
  sat("increment:\n(counter >= 0)");
  sat("decrement:\n(old(counter) > 0) ? (counter < old(counter)) : (counter == old(counter))");
  sat('decrement:\n(typeof(counter) == "number")');
  sat("decrement:\n(counter >= 0)");
});

describe("simple steps", () => {
  
  const code = (() => {
    let i = 0;
    assert(i < 1);
    i = 3;
    assert(i < 2);
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  sat("assert:\n(i < 1)");
  unsat("assert:\n(i < 2)");
});

describe("loop", () => {
  
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
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  sat("invariant on entry:\n(i <= 5)");
  sat("invariant maintained:\n(i <= 5)");
  sat("assert:\n(i === 5)");
});

describe("loop with missing invariant", () => {
  
  const code = (() => {
    let i = 0;

    while (i < 5) {
      i++;
    }
    
    assert(i === 5);
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  notest("assert:\n(i === 5)");
});

describe("sum", () => {
  
  const code = (() => {
    function sumTo(n) {
      requires(typeof n == "number");
      requires(n >= 0);
      
      let i = 0, s = 0;
      while (i < n) {
        invariant(i <= n);
        invariant(s == (i + 1) * i / 2);
        i++;
        s = s + i;
      }
      return s;
      
      ensures(sumTo(n) == (n + 1) * n / 2);
    }
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  sat("sumTo:\ninvariant on entry:\n(i <= n)");
  sat("sumTo:\ninvariant on entry:\n(s == (((i + 1) * i) / 2))");
  sat("sumTo:\ninvariant maintained:\n(i <= n)");
  sat("sumTo:\ninvariant maintained:\n(s == (((i + 1) * i) / 2))");
  sat("sumTo:\n(sumTo(n) == (((n + 1) * n) / 2))");
});


describe("global call", () => {
  
  const code = (() => {
    function inc(n) {
      requires(typeof(n) == "number");
      return n + 1;
      ensures(inc(n) > n);
    }

    let i = 3;
    let j = inc(i);
    assert(j > 3);
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  sat('inc:\nrequires:\n(typeof(n) == "number")');
  sat("assert:\n(j > 3)");
  sat("inc:\n(inc(n) > n)");
  
});

describe("inline global call", () => {
  
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
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  sat("assert:\n(j == 4)");
  notest("assert:\n(k == 5)");
});

describe("post conditions global call", () => {
  
  const code = (() => {
    function inc(n) {
      requires(typeof(n) == "number");
      return n + 1;
      ensures(inc(n) > n);
    }
    function inc2(n) {
      return inc(inc(n));
    }

    let i = 3;
    let j = inc(i);
    assert(j == 4);
    let k = inc2(i);
    assert(k >= 5);
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  sat('inc:\nrequires:\n(typeof(n) == "number")');
  unsat('inc2:\ninc:\nrequires:\n(typeof(n) == "number")');
  sat('assert:\n(j == 4)');
  sat("assert:\n(k >= 5)");
});

describe("fibonacci increasing", () => {
  
  const code = (() => {
    function fib(n) {
      requires(typeof(n) == "number");
      requires(n >= 0);
      if (n <= 1) return 1;
      return fib(n - 1) + fib(n - 2);
      ensures(fib(n) >= n);
    }
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  sat('fib:\nfib:\nrequires:\n(typeof(n) == "number")');
  sat('fib:\nfib:\nrequires:\n(n >= 0)');
  sat('fib:\n(fib(n) >= n)');
});

describe("buggy fibonacci", () => {
  
  const code = (() => {
    function fib(n) {
      requires(typeof(n) == "number");
      requires(n >= 0);
      if (n <= 1) return n;
      return fib(n - 1) + fib(n - 2);
      ensures(fib(n) >= n);
    }
  }).toString();
  
  beforeEach(() => {
    const t = verify(code.substring(14, code.length - 2));
    if (!t) throw new Error("failed to find verification conditions");
    vcs = t;
  });

  sat('fib:\nfib:\nrequires:\n(typeof(n) == "number")');
  sat('fib:\nfib:\nrequires:\n(n >= 0)');
  unsat('fib:\n(fib(n) >= n)');
  it("returns counter-example", async () => {
    await vcs[4].solve();
    expect(vcs[4].getModel()).to.containSubset({
      n: 2
    });
  });
});
