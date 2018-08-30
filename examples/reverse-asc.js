// Reversing an ascending list
class IntList {
  constructor (head, tail) {
    this.head = head;
    this.tail = tail;
  }
  invariant () {
    return typeof(this.head) === 'number' &&
           (this.tail === null || this.tail instanceof IntList);
  }
}

function isAscending (list) {
  requires(list === null || list instanceof IntList);
  ensures(res => typeof(res) === 'boolean');
  ensures(pure());

  return list === null || list.tail === null ||
        list.head <= list.tail.head && isAscending(list.tail);
}

function isDescending (list) {
  requires(list === null || list instanceof IntList);
  ensures(res => typeof(res) === 'boolean');
  ensures(pure());

  return list === null || list.tail === null ||
        list.head >= list.tail.head && isDescending(list.tail);
}

function reverseHelper (pivot, acc, list) {
  requires(list === null || list instanceof IntList);
  requires(isAscending(list));
  requires(typeof pivot === 'number');
  requires(list === null || pivot <= list.head);
  requires(acc === null || acc instanceof IntList);
  requires(isDescending(acc));
  requires(acc === null || pivot >= acc.head);
  ensures(res => res === null || res instanceof IntList);
  ensures(res => isDescending(res));
  ensures(pure());

  const newList = new IntList(pivot, acc);
  isDescending(newList);

  if (list === null) {
    return newList;
  } else {
    assert(list.tail === null || list.tail instanceof IntList);
    isAscending(list);      // instantiation
    isAscending(list.tail); // instantiation
    return reverseHelper(list.head, newList, list.tail);
  }
}

function reverse (list) {
  requires(list === null || list instanceof IntList);
  requires(isAscending(list));
  ensures(res => res === null || res instanceof IntList);
  ensures(res => isDescending(res));
  ensures(pure());

  if (list === null) {
    isDescending(list);     // instantiation
    return list;
  } else {
    isAscending(list);      // instantiation
    isAscending(list.tail); // instantiation
    isDescending(null);     // instantiation
    return reverseHelper(list.head, null, list.tail);
  }
}

