// Parameterized List Class
class List {
  constructor (head, tail, each) {
    this.head = head; this.tail = tail; this.each = each;
  }
  invariant () {
    return spec(this.each, (x) => true, (x, y) => pure() && typeof(y) === 'boolean')
       && (true && this.each)(this.head) // same as 'this.each(this.head)'
                                         // but avoids binding 'this'
       && (this.tail === null || (this.tail instanceof List &&
                                  this.each === this.tail.each));
  }
}

function map (f, lst, newEach) {
  requires(spec(newEach, (x) => true, (x, y) => pure() && typeof(y) === 'boolean'));
  requires(lst === null || spec(f, (x) => (true && lst.each)(x),
                                   (x, y) => pure() && newEach(y)));
  requires(lst === null || lst instanceof List);
  ensures(res => res === null || (res instanceof List && res.each === newEach));
  ensures(pure()); // necessary for recursive calls

  return lst === null ? null
                      : new List(f(lst.head), map(f, lst.tail, newEach), newEach);
}
