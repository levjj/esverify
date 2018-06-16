// Simple Classes: Adder
class Adder {
  constructor (base) {
    this.base = base;
  }
  invariant () {
    return typeof this.base === 'number';
  }
  addTo (n) {
    requires(typeof n === 'number');
    return this.base + n;
  }
}

const adder = new Adder(5);
const m = adder.addTo(3);
assert(m === 8);

function f (a) {
  requires(a instanceof Adder);
  ensures(res => res !== 2); // does not hold if a is "new A(1)"

  return a.addTo(1);
}
