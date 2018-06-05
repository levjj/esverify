function inc(n) {
  return n + 1;
}

let i = 3;
let j = inc(i);      // call automatically inlines function body
assert(j === 4);
