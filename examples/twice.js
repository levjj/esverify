// Higher-order Functions: twice
function inc (n) {
  requires(Number.isInteger(n));
  ensures(res => Number.isInteger(res) && res > n);
  return n + 1;
}

function twice (f) {
  requires(spec(f, (x) => Number.isInteger(x),
                   (x, y) => Number.isInteger(y) && y > x));
  ensures(g => spec(g, (x) => Number.isInteger(x),
                       (x, y) => Number.isInteger(y) && y > x + 1));
  return function (n) {
    requires(Number.isInteger(n));
    ensures(res => Number.isInteger(res) && res > n + 1);
    return f(f(n));
  };
}

const incTwice = twice(inc);
const y = incTwice(3);
assert(y > 4);
