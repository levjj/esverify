class List {
  constructor (head, tail) { this.head = head; this.tail = tail; }
  invariant () { return this.tail === null || this.tail instanceof List; }
}

function map (lst, f) {
  requires(lst === null || lst instanceof List);
  requires(spec(f, x => true, x => pure()));
  ensures(pure());
  ensures(res => res === null || res instanceof List);

  if (lst === null) return null;
  return new List(f(lst.head), map(lst.tail, f));
}

function len (lst) {
  requires(lst === null || lst instanceof List);
  ensures(pure());
  ensures(res => typeof res === 'number' && res >= 0);

  return lst === null ? 0 : len(lst.tail) + 1;
}

function mapLen (lst, f) {
  requires(lst === null || lst instanceof List);
  requires(spec(f, x => true, x => pure()));
  ensures(pure());
  ensures(len(lst) === len(map(lst, f)));

  const l = len(lst);
  const r = len(map(lst, f));
  if (lst === null) {
    assert(l === 0);
    assert(r === 0);
  } else {
    const l1 = len(lst.tail);
    assert(l === l1 + 1);

    f(lst.head);
    const r1 = len(map(lst.tail, f));
    assert(r === r1 + 1);

    mapLen(lst.tail, f);
    assert(l1 === r1);
    assert(l === r);
  }
}
