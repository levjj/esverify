/// <reference path="../typings/mocha/mocha.d.ts" />
/// <reference path="../typings/chai/chai.d.ts" />
import { expect, use } from "chai";
import * as chaiSubset from "chai-subset";
use(chaiSubset);

import { verify } from "../index";
import VerificationCondition from "../src/vc";

describe("verify", () => {
  var requires, ensures, invariant, assert, old; // do not rewrite assertions
  
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
    
    let vcs: Array<VerificationCondition>;
    
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
    
    it("can be verified", async () => {
      await vcs[0].solve();
      expect(vcs[0].result().status).to.be.eql("sat");
    });
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
    
    let vcs: Array<VerificationCondition>;
    
    beforeEach(() => {
      const t = verify(code.substring(14, code.length - 2));
      if (!t) throw new Error("failed to find verification conditions");
      vcs = t;
    });

    it("can not be verified", async () => {
      await vcs[0].solve();
      expect(vcs[0].result().status).to.be.eql("notest"); // ideally "unsat""
    });
    
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
    
    let vcs: Array<VerificationCondition>;
    
    beforeEach(() => {
      const t = verify(code.substring(14, code.length - 2));
      if (!t) throw new Error("failed to find verification conditions");
      vcs = t;
    });

    it("finds all verification conditions", () => {
      expect(vcs).to.have.length(8);
    });
    
    it("is initialized correctly", async () => {
      expect(vcs[0].description).to.be.eql('initially:\n(typeof(counter) == "number")');
      await vcs[0].solve();
      expect(vcs[0].result().status).to.be.eql("sat");
      expect(vcs[1].description).to.be.eql("initially:\n(counter >= 0)");
      await vcs[1].solve();
      expect(vcs[1].result().status).to.be.eql("sat");
    });
    
    it("increment increments", async () => {
      expect(vcs[2].description).to.be.eql("increment:\n(counter > old(counter))");
      await vcs[2].solve();
      expect(vcs[2].result().status).to.be.eql("sat");
    });

    it("increment maintains invariants", async () => {
      expect(vcs[3].description).to.be.eql('increment:\n(typeof(counter) == "number")');
      await vcs[3].solve();
      expect(vcs[3].result().status).to.be.eql("sat");
      expect(vcs[4].description).to.be.eql("increment:\n(counter >= 0)");
      await vcs[4].solve();
      expect(vcs[4].result().status).to.be.eql("sat");
    });
    
    it("decrement decrements", async () => {
      expect(vcs[5].description).to.be.eql("decrement:\n(old(counter) > 0) ? (counter < old(counter)) : (counter == old(counter))");
      await vcs[5].solve();
      expect(vcs[5].result().status).to.be.eql("sat");
    });

    it("decrement maintains invariants", async () => {
      expect(vcs[6].description).to.be.eql('decrement:\n(typeof(counter) == "number")');
      await vcs[6].solve();
      expect(vcs[6].result().status).to.be.eql("sat");
      expect(vcs[7].description).to.be.eql("decrement:\n(counter >= 0)");
      await vcs[7].solve();
      expect(vcs[7].result().status).to.be.eql("sat");
    });
    
  });
  
  describe("simple steps", () => {
    
    const code = (() => {
      let i = 0;
      assert(i < 1);
      i = 3;
      assert(i < 2);
    }).toString();
    
    let vcs: Array<VerificationCondition>;
    
    beforeEach(() => {
      const t = verify(code.substring(14, code.length - 2));
      if (!t) throw new Error("failed to find verification conditions");
      vcs = t;
    });

    it("finds all verification conditions", () => {
      expect(vcs).to.have.length(2);
    });
    
    it("verifies first assertion", async () => {
      expect(vcs[0].description).to.be.eql("assert:\n(i < 1)");
      await vcs[0].solve();
      expect(vcs[0].result().status).to.be.eql("sat");
    });

    it("does not verify second assertion", async () => {
      expect(vcs[1].description).to.be.eql("assert:\n(i < 2)");
      await vcs[1].solve();
      expect(vcs[1].result().status).to.be.eql("unsat");
    });
    
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
    
    let vcs: Array<VerificationCondition>;
    
    beforeEach(() => {
      const t = verify(code.substring(14, code.length - 2));
      if (!t) throw new Error("failed to find verification conditions");
      vcs = t;
    });

    it("finds all verification conditions", () => {
      expect(vcs).to.have.length(3);
    });
    
    it("invariant holds on entry", async () => {
      expect(vcs[0].description).to.be.eql("invariant on entry:\n(i <= 5)");
      await vcs[0].solve();
      expect(vcs[0].result().status).to.be.eql("sat");
    });
    
    it("invariant maintained by loop", async () => {
      expect(vcs[1].description).to.be.eql("invariant maintained:\n(i <= 5)");
      await vcs[1].solve();
      expect(vcs[1].result().status).to.be.eql("sat");
    });

    it("results in final state", async () => {
      expect(vcs[2].description).to.be.eql("assert:\n(i === 5)");
      await vcs[2].solve();
      expect(vcs[2].result().status).to.be.eql("sat");
    });
    
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
    
    let vcs: Array<VerificationCondition>;
    
    beforeEach(() => {
      const t = verify(code.substring(14, code.length - 2));
      if (!t) throw new Error("failed to find verification conditions");
      vcs = t;
    });

    it("finds all verification conditions", () => {
      expect(vcs).to.have.length(5);
    });
    
    it("bound invariant holds on loop entry", async () => {
      expect(vcs[0].description).to.be.eql("sumTo:\ninvariant on entry:\n(i <= n)");
      await vcs[0].solve();
      expect(vcs[0].result().status).to.be.eql("sat");
    });
    
    it("equality invariant holds on loop entry", async () => {
      expect(vcs[1].description).to.be.eql("sumTo:\ninvariant on entry:\n(s == (((i + 1) * i) / 2))");
      await vcs[1].solve();
      expect(vcs[1].result().status).to.be.eql("sat");
    });
    
    it("counter invariant maintained by loop", async () => {
      expect(vcs[2].description).to.be.eql("sumTo:\ninvariant maintained:\n(i <= n)");
      await vcs[2].solve();
      expect(vcs[2].result().status).to.be.eql("sat");
    });

    it("equality invariant maintained by loop", async () => {
      expect(vcs[3].description).to.be.eql("sumTo:\ninvariant maintained:\n(s == (((i + 1) * i) / 2))");
      await vcs[3].solve();
      expect(vcs[3].result().status).to.be.eql("sat");
    });

    it("verifies post condition", async () => {
      expect(vcs[4].description).to.be.eql("sumTo:\n(sumTo(n) == (((n + 1) * n) / 2))");
      await vcs[4].solve();
      expect(vcs[4].result().status).to.be.eql("sat");
    });

  });
  
  
  describe("calls in code", () => {
    
    const code = (() => {
      function inc(n) {
        ensures(inc(n) == n + 1);
        return n + 1;
      }
      
      function test() {
        ensures(test() == 2);
        return inc(inc(0));
      }
    }).toString();
    
    let vcs: Array<VerificationCondition>;
    
    beforeEach(() => {
      const t = verify(code.substring(14, code.length - 2));
      if (!t) throw new Error("failed to find verification conditions");
      vcs = t;
    });

    it("find all verification conditions", () => {
      expect(vcs).to.have.length(2);
    });
    
    it("verifies callee", async () => {
      expect(vcs[0].description).to.be.eql("inc:\ninc(n) == (n + 1)");
      await vcs[0].solve();
      expect(vcs[0].result().status).to.be.eql("sat");
    });
    
    it("verifies caller", async () => {
      expect(vcs[1].description).to.be.eql("test:\ntest() == 2");
      await vcs[1].solve();
      expect(vcs[1].result().status).to.be.eql("sat");
    });

  });
});
