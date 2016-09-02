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
      expect(theorems[0].isSatisfiable()).to.be.true;
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
      expect(theorems[0].isSatisfiable()).to.be.false;
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
      expect(theorems[0].isSatisfiable()).to.be.true;
      expect(theorems[1].description).to.be.eql("initially:\ncounter >= 0");
      await theorems[1].solve();
      expect(theorems[1].isSatisfiable()).to.be.true;
    });
    
    it("increment increments", async () => {
      expect(theorems[2].description).to.be.eql("increment:\ncounter > old(counter)");
      await theorems[2].solve();
      expect(theorems[2].isSatisfiable()).to.be.true;
    });
        
    it("increment maintains invariants", async () => {
      expect(theorems[3].description).to.be.eql("increment:\ntypeof counter == 'number'");
      await theorems[3].solve();
      expect(theorems[3].isSatisfiable()).to.be.true;
      expect(theorems[4].description).to.be.eql("increment:\ncounter >= 0");
      await theorems[4].solve();
      expect(theorems[4].isSatisfiable()).to.be.true;
    });
    
    it("decrement decrements", async () => {
      expect(theorems[5].description).to.be.eql("decrement:\nold(counter) > 0 ? counter < old(counter) : counter === old(counter)");
      await theorems[5].solve();
      expect(theorems[5].isSatisfiable()).to.be.true;
    });

    it("decrement maintains invariants", async () => {
      expect(theorems[6].description).to.be.eql("decrement:\ntypeof counter == 'number'");
      await theorems[6].solve();
      expect(theorems[6].isSatisfiable()).to.be.true;
      expect(theorems[7].description).to.be.eql("decrement:\ncounter >= 0");
      await theorems[7].solve();
      expect(theorems[7].isSatisfiable()).to.be.true;
    });
    
  });
});
