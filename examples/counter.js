// Mutable Variables: Counter
let counter = 0;
invariant(Number.isInteger(counter));
invariant(counter >= 0);

function increment () {
  ensures(counter > old(counter));

  counter++;
}

function decrement () {
  ensures(old(counter) > 0 ? counter < old(counter) : counter === old(counter));

  if (counter > 0) counter--;
}
