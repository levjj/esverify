/* global describe, beforeEach, it */

import { expect } from "mocha-es6";

import { theoremsInSource } from "../index.js";

describe("verify", () => {
  describe("max()", () => {
    
    var requires, ensures;
    function max(a, b) {
      requires(typeof(a) == "number");
      requires(typeof(b) == "number");
      ensures(max(a, b) >= a);
      if (a >= b) {
        return a;
      } else {
        return b;
      }
    }
    
    let theorems;
    
    beforeEach(() => {
      theorems = theoremsInSource(max.toString());
    });

    it("finds a theorem", () => {
      expect(theorems).to.have.length(1);
    });
    
    it("has a description", async () => {
      await theorems[0].solve();
      expect(theorems[0].description()).to.be.eql("max:\nmax(a, b) >= a");
    });
    
    it("can be verified", async () => {
      await theorems[0].solve();
      const result = theorems[0].isSatisfiable();
      expect(result).to.be.true;
    });
  });
  
  describe("max() with missing pre", () => {
    
    var requires, ensures;
    function max(a, b) {
      requires(typeof(b) == "number");
      ensures(max(a, b) >= a);
      if (a >= b) {
        return a;
      } else {
        return b;
      }
    }
    
    let theorems;
    
    beforeEach(() => {
      theorems = theoremsInSource(max.toString());
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
});
