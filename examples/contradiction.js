// Proofs: Simple contradiction
function contradiction(p, p1, a3) {
  // p1: { x: nat | p(x) <=> 0 <= x <= 3}
  requires(spec(p1, (x) => Number.isInteger(x),
                    (x) => pure() && p(x) === (0 <= x && x <= 3)));
  // a3: { x: nat | p(x) => p(x+1) }
  requires(spec(a3, (x) => Number.isInteger(x) && p(x),
                    (x) => pure() && p(x+1)));
  ensures(false);

  // have p(3) from p1(3);
  p1(3);

  // have p(4) from a3(3);
  a3(3);

  // have 0 <= 4 <= 3 from p1(4);
  p1(4);
}

