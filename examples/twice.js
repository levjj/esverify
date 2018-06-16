// Higher-order Functions: twice
function inc (n) {
  requires(Number.isInteger(n));
  ensures(res => Number.isInteger(res) && res > n);

  return n + 1;
}

function twice (f, n) {
  requires(spec(f, x => Number.isInteger(x), (x, y) => Number.isInteger(y) && y > x));
  requires(Number.isInteger(n));
  ensures(res => res > n + 1);

  return f(f(n));
}

const x = 3;
const y = twice(inc, x);
assert(y > 4);
