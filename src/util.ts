export function flatMap<A,B>(a: Array<A>, f: (a: A) => Array<B>): Array<B> {
  return a.map(f).reduce((a,b) => a.concat(b));
}

export function pushAll<A>(a: Array<A>, b: Array<A>) {
  for (const be of b) {
    a.push(be);
  }
}