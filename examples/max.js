// Simple Example: max
// This is a live demo, simply edit the code and click "verify" above!

function max(a, b) {
  requires(typeof(a) === 'number');
  requires(typeof(b) === 'number');
  ensures(res => res >= a);
  ensures(res => res >= b); // this post-condition does not hold

  if (a >= b) {
    return a;
  } else {
    return a;               // due to a bug in the implementation
  }
}
