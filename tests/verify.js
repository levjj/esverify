/* global describe, beforeEach, it */

import { expect } from "mocha-es6";

import { theoremsInSource } from "../index.js";

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
    
    let theorems;
    
    beforeEach(() => {
      theorems = theoremsInSource(code.substring(14, code.length - 2));
    });

    it("finds a theorem", () => {
      expect(theorems).to.have.length(1);
    });
    
    it("has a description", async () => {
      expect(theorems[0].description).to.be.eql("max:\nmax(a, b) >= a");
    });
    
    it("can be verified", async () => {
      await theorems[0].solve();
      expect(theorems[0].result().status).to.be.eql("sat");
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
    
    let theorems;
    
    beforeEach(() => {
      theorems = theoremsInSource(code.substring(14, code.length - 2));
    });

    it("can not be verified", async () => {
      await theorems[0].solve();
      expect(theorems[0].result().status).to.be.eql("unsat");
    });
    
    it("returns counter-example", async () => {
      await theorems[0].solve();
      expect(theorems[0].getModel()).to.containSubset({
        _res: 0,
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
        ensures(old(counter) > 0 ? counter < old(counter) : counter === old(counter));
      }
    }).toString();
    
    let theorems;
    
    beforeEach(() => {
      theorems = theoremsInSource(code.substring(14, code.length - 2));
    });

    it("finds all theorem", () => {
      expect(theorems).to.have.length(8);
    });
    
    it("is initialized correctly", async () => {
      expect(theorems[0].description).to.be.eql("initially:\ntypeof counter == 'number'");
      await theorems[0].solve();
      expect(theorems[0].result().status).to.be.eql("sat");
      expect(theorems[1].description).to.be.eql("initially:\ncounter >= 0");
      await theorems[1].solve();
      expect(theorems[1].result().status).to.be.eql("sat");
    });
    
    it("increment maintains invariants", async () => {
      expect(theorems[2].description).to.be.eql("increment:\ntypeof counter == 'number'");
      await theorems[2].solve();
      expect(theorems[2].result().status).to.be.eql("sat");
      expect(theorems[3].description).to.be.eql("increment:\ncounter >= 0");
      await theorems[3].solve();
      expect(theorems[3].result().status).to.be.eql("sat");
    });
    
    it("increment increments", async () => {
      expect(theorems[4].description).to.be.eql("increment:\ncounter > old(counter)");
      await theorems[4].solve();
      expect(theorems[4].result().status).to.be.eql("sat");
    });

    it("decrement maintains invariants", async () => {
      expect(theorems[5].description).to.be.eql("decrement:\ntypeof counter == 'number'");
      await theorems[5].solve();
      expect(theorems[5].result().status).to.be.eql("sat");
      expect(theorems[6].description).to.be.eql("decrement:\ncounter >= 0");
      await theorems[6].solve();
      expect(theorems[6].result().status).to.be.eql("sat");
    });
    
    it("decrement decrements", async () => {
      expect(theorems[7].description).to.be.eql("decrement:\nold(counter) > 0 ? counter < old(counter) : counter === old(counter)");
      await theorems[7].solve();
      expect(theorems[7].result().status).to.be.eql("sat");
    });

  });
  
  describe("simple steps", () => {
    
    const code = (() => {
      let i = 0;
      assert(i < 1);
      i = 3;
      assert(i < 2);
    }).toString();
    
    let theorems;
    
    beforeEach(() => {
      theorems = theoremsInSource(code.substring(14, code.length - 2));
    });

    it("finds all theorem", () => {
      expect(theorems).to.have.length(2);
    });
    
    it("verifies first assertion", async () => {
      expect(theorems[0].description).to.be.eql("assert:\ni < 1");
      await theorems[0].solve();
      expect(theorems[0].result().status).to.be.eql("sat");
    });

    it("does not verify second assertion", async () => {
      expect(theorems[1].description).to.be.eql("assert:\ni < 2");
      await theorems[1].solve();
      expect(theorems[1].result().status).to.be.eql("unsat");
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
    
    let theorems;
    
    beforeEach(() => {
      theorems = theoremsInSource(code.substring(14, code.length - 2));
    });

    it("finds all theorem", () => {
      expect(theorems).to.have.length(3);
    });
    
    it("results in final state", async () => {
      expect(theorems[0].description).to.be.eql("assert:\ni === 5");
      await theorems[0].solve();
      expect(theorems[0].result().status).to.be.eql("sat");
    });
    
    it("invariant holds on entry", async () => {
      expect(theorems[1].description).to.be.eql("loop entry:\ni <= 5");
      await theorems[1].solve();
      expect(theorems[1].result().status).to.be.eql("sat");
    });
    
    it("invariant maintained by loop", async () => {
      expect(theorems[2].description).to.be.eql("loop invariant:\ni <= 5");
      await theorems[2].solve();
      expect(theorems[2].result().status).to.be.eql("sat");
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
    
    let theorems;
    
    beforeEach(() => {
      theorems = theoremsInSource(code.substring(14, code.length - 2));
    });

    it("finds all theorem", () => {
      expect(theorems).to.have.length(5);
    });
    
    it("verifies post condition", async () => {
      expect(theorems[0].description).to.be.eql("sumTo:\nsumTo(n) == (n + 1) * n / 2");
      await theorems[0].solve();
      expect(theorems[0].result().status).to.be.eql("sat");
    });
    
    it("bound invariant holds on loop entry", async () => {
      expect(theorems[1].description).to.be.eql("loop entry:\ni <= n");
      await theorems[1].solve();
      expect(theorems[1].result().status).to.be.eql("sat");
    });
    
    it("equality invariant holds on loop entry", async () => {
      expect(theorems[2].description).to.be.eql("loop entry:\ns == (i + 1) * i / 2");
      await theorems[2].solve();
      expect(theorems[2].result().status).to.be.eql("sat");
    });
    
    it("counter invariant maintained by loop", async () => {
      expect(theorems[3].description).to.be.eql("loop invariant:\ni <= n");
      await theorems[3].solve();
      expect(theorems[3].result().status).to.be.eql("sat");
    });

    it("equality invariant maintained by loop", async () => {
      expect(theorems[4].description).to.be.eql("loop invariant:\ns == (i + 1) * i / 2");
      await theorems[4].solve();
      expect(theorems[4].result().status).to.be.eql("sat");
    });

  });
});
