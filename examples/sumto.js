// Loops: sumTo
function sumTo (n) {
  requires(Number.isInteger(n));
  requires(n >= 0);
  ensures(res => res === (n + 1) * n / 2);

  let i = 0;
  let s = 0;
  while (i < n) {
    invariant(i <= n);
    invariant(s === (i + 1) * i / 2);
    invariant(Number.isInteger(i));
    invariant(Number.isInteger(s));
    i++;
    s = s + i;
  }
  return s;
}
