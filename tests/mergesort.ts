import 'mocha';
import { code, verified } from './helpers';

declare function assert (x: boolean): void;
declare function ensures (x: boolean | ((y: any) => boolean)): void;
declare function requires (x: boolean): void;
declare function pure (): boolean;

describe('merge sort', () => {

  code(() => {
    class IntList {
      head: number;
      tail: null | IntList;
      constructor (head, tail) {
        this.head = head; this.tail = tail;
      }
      invariant () {
        return typeof(this.head) === 'number' && (this.tail === null || this.tail instanceof IntList);
      }
    }

    class IntListPartition {
      left: IntList;
      right: IntList;
      constructor (left, right) {
        this.left = left; this.right = right;
      }
      invariant () {
        return (this.left === null || this.left instanceof IntList) &&
              (this.right === null || this.right instanceof IntList);
      }
    }

    function partition (lst, fst, snd, alternate) {
      requires(lst === null || lst instanceof IntList);
      requires(fst === null || fst instanceof IntList);
      requires(snd === null || snd instanceof IntList);
      requires(typeof(alternate) === 'boolean');
      ensures(res => res instanceof IntListPartition);
      ensures(pure());

      if (lst === null) {
        return new IntListPartition(fst, snd);
      } else if (alternate) {
        return partition(lst.tail, new IntList(lst.head, fst), snd, false);
      } else {
        return partition(lst.tail, fst, new IntList(lst.head, snd), true);
      }
    }

    function isSorted (list) {
      requires(list === null || list instanceof IntList);
      ensures(res => typeof(res) === 'boolean');
      ensures(pure());

      return list === null || list.tail === null ||
            list.head <= list.tail.head && isSorted(list.tail);
    }

    function merge (left, right) {
      requires(left === null || left instanceof IntList);
      requires(isSorted(left));
      requires(right === null || right instanceof IntList);
      requires(isSorted(right));
      ensures(res => res === null || res instanceof IntList);
      ensures(res => isSorted(res));
      ensures(res => (left === null && right === null) === (res === null));
      ensures(res => !(left !== null && (right === null || right.head >= left.head))
                      ||
                    (res !== null && res.head === left.head));
      ensures(res => !(right !== null && (left === null || right.head < left.head))
                      ||
                    (res !== null && res.head === right.head));
      ensures(pure());

      if (left === null) {
        return right;
      } else if (right === null) {
        return left;
      } else if (left.head <= right.head) {
        isSorted(left);
        isSorted(left.tail);
        const merged = merge(left.tail, right);
        const res = new IntList(left.head, merged);
        isSorted(res);
        return res;
      } else {
        isSorted(right);
        isSorted(right.tail);
        const merged = merge(left, right.tail);
        const res = new IntList(right.head, merged);
        isSorted(res);
        return res;
      }
    }

    function sort (list) {
      requires(list === null || list instanceof IntList);
      ensures(res => res === null || res instanceof IntList);
      ensures(res => isSorted(res));
      ensures(pure());

      if (list === null || list.tail === null) {
        isSorted(list);
        assert(isSorted(list));
        return list;
      }
      const part = partition(list, null, null, false);
      return merge(sort(part.left), sort(part.right));
    }
  });

  verified('partition: class invariant IntListPartition');
  verified('partition: lst has property "head"');
  verified('partition: lst has property "tail"');
  verified('partition: class invariant IntList');
  verified('partition: precondition partition(lst.tail, new IntList(lst.head, fst), snd, false)');
  verified('partition: precondition partition(lst.tail, fst, new IntList(lst.head, snd), true)');
  verified('partition: (res instanceof IntListPartition)');
  verified('partition: pure()');
  verified('isSorted: list has property "head"');
  verified('isSorted: list has property "tail"');
  verified('isSorted: precondition isSorted(list.tail)');
  verified('isSorted: (typeof(res) === "boolean")');
  verified('isSorted: pure()');
  verified('merge: left has property "head"');
  verified('merge: left has property "tail"');
  verified('merge: right has property "head"');
  verified('merge: right has property "tail"');
  verified('merge: precondition isSorted(left)');
  verified('merge: precondition isSorted(left.tail)');
  verified('merge: precondition merge(left.tail, right)');
  verified('merge: class invariant IntList');
  verified('merge: precondition isSorted(res)');
  verified('merge: precondition isSorted(right)');
  verified('merge: precondition isSorted(right.tail)');
  verified('merge: precondition merge(left, right.tail)');
  verified('merge: class invariant IntList');
  verified('merge: precondition isSorted(res)');
  verified('merge: ((res === null) || (res instanceof IntList))');
  verified('merge: isSorted(res)');
  verified('merge: (((left === null) && (right === null)) === (res === null))');
  verified('merge: (!((left !== null) && ((right === null) || (right.head >= left.head))) || ' +
                    '((res !== null) && (res.head === left.head)))');
  verified('merge: (!((right !== null) && ((left === null) || (right.head < left.head))) || ' +
                    '((res !== null) && (res.head === right.head)))');
  verified('merge: pure()');
  verified('sort: list has property "tail"');
  verified('sort: precondition isSorted(list)');
  verified('sort: assert: isSorted(list)');
  verified('sort: precondition partition(list, null, null, false)');
  verified('sort: part has property "left"');
  verified('sort: precondition sort(part.left)');
  verified('sort: part has property "right"');
  verified('sort: precondition sort(part.right)');
  verified('sort: precondition merge(sort(part.left), sort(part.right))');
  verified('sort: ((res === null) || (res instanceof IntList))');
  verified('sort: isSorted(res)');
  verified('sort: pure()');
});
