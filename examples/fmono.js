function fib (n) {
  requires(Number.isInteger(n));
  requires(n >= 0);
  ensures(pure());
  ensures(res => Number.isInteger(res));

  if (n <= 1) {
    return 1;
  } else {
    return fib(n - 1) + fib(n - 2);
  }
}

function fibInc (n) {
  requires(Number.isInteger(n));
  requires(n >= 0);
  ensures(fib(n) <= fib(n + 1));
  ensures(pure());

  fib(n);
  fib(n + 1);

  if (n > 0) {
    fib(n - 1);
    fibInc(n - 1);
  }

  if (n > 1) {
    fib(n - 2);
    fibInc(n - 2);
  }
}

function fMono (f, fInc, n, m) {
  requires(spec(f, x => Number.isInteger(x) && x >= 0,
                   (x, y) => pure() && Number.isInteger(y)));
  requires(spec(fInc, x => Number.isInteger(x) && x >= 0,
                      x => pure() && f(x) <= f(x + 1)));
  requires(Number.isInteger(n));
  requires(n >= 0);
  requires(Number.isInteger(m));
  requires(m >= 0);
  requires(n < m);
  ensures(pure());
  ensures(f(n) <= f(m));

  if (n + 1 === m) {
    fInc(n);
  } else {
    fInc(n);
    fMono(f, fInc, n + 1, m);
  }
}

function fibMono (n, m) {
  requires(Number.isInteger(n));
  requires(n >= 0);
  requires(Number.isInteger(m));
  requires(m >= 0);
  requires(n < m);
  ensures(pure());
  ensures(fib(n) <= fib(m));

  fMono(fib, fibInc, n, m);
}
