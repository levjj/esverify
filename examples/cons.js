// Closures
function cons(x) {
  function f () { return x; }
  return f;
}
const g = cons(1);
const g1 = g();
assert(g1 === 1);
const h = cons(2);
const h1 = h();
assert(h1 === 2);
