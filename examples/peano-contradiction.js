// Proofs: Peano axioms
function contradiction(nat, zero, s, a1, a2, p, p1, a3) {
  // nat: any -> Prop
  requires(spec(nat, (x) => true, (x,y) => pure() && typeof y === 'boolean'));
  
  // zero: nat
  requires(nat(zero));
  
  // s: nat -> nat
  requires(spec(s, (x) => nat(x), (x, y) => pure() && nat(y)));

  // a1: { x: nat, y: nat | x = y <=> x+1 = y+1 }
  requires(spec(a1, (x, y) => nat(x) && nat(y),
                    (x, y) => pure() && (x === y) === (s(x) === s(y))));
                    
  // a2: { x: nat | 0 !== x+1 }
  requires(spec(a2, (x) => nat(x), (x) => pure() && s(x) !== zero));
  
  // p1: { x: nat | p(x) <=> 0 <= x <= 3}
  requires(spec(p1, (x) => nat(x),
                    (x) => pure() && 
                           p(x) === (x === zero || x === s(zero) ||
                                     x === s(s(zero)) || x === s(s(s(zero))))));
  // a3: { x: nat | p(x) => p(x+1) }
  requires(spec(a3, (x) => nat && p(x),
                    (x) => pure() && p(s(x))));
  ensures(false);

  // have p(3) from p1(3);
  p1(s(s(s(zero))));
  assert(p(s(s(s(zero)))));
  
  // have p(4) from a3(3);
  a3(s(s(s(zero))));
  assert(p(s(s(s(s(zero))))));
  
  // have 0 <= 4 <= 3 from p1(4);
  p1(s(s(s(s(zero)))));
  assert((s(s(s(s(zero)))) === zero ||
          s(s(s(s(zero)))) === s(zero) ||
          s(s(s(s(zero)))) === s(s(zero)) ||
          s(s(s(s(zero)))) === s(s(s(zero)))));

  // have 4 != 0 from a2(3);
  a2(s(s(s(zero))));
  assert(s(s(s(s(zero)))) !== zero);

  // have 3 != 0 from a2(2);
  a2(s(s(zero)));
  assert(s(s(s(zero))) !== zero);

  // have 2 != 0 from a2(1);
  a2(s(zero));
  assert(s(s(zero)) !== zero);

  // have 1 != 0 from a2(0);
  a2(zero);
  assert(s(zero) !== zero);
  
  // have 4 !== 1 from a1(3, 0)
  a1(s(s(s(zero))), zero);
  assert(s(s(s(s(zero)))) !== s(zero));

  // have 4 !== 2 from a1(3, 1), a1(2, 0)
  a1(s(s(s(zero))), s(zero));
  a1(s(s(zero)), zero);
  assert(s(s(s(s(zero)))) !== s(s(zero)));

  // have 4 !== 3 from a1(3, 2), a1(2, 1), a1(1, 0)
  a1(s(s(s(zero))), s(s(zero)));
  a1(s(s(zero)), s(zero));
  a1(s(zero), zero);
  assert(s(s(s(s(zero)))) !== s(s(s(zero))));
}

