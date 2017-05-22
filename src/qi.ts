import { Syntax, P, Heap, PropTransformer, Substituter, PropReducer, tru, and, eq, implies, eqProp, copy } from "./logic";
import { HeapsWithLocal, LocsWithLocal, VarsWithLocal } from "./smt";

class TriggerEraser extends PropTransformer {
  visitCallTrigger(prop: Syntax.CallTrigger): P {
    return tru;
  }
  
  visitForAll(prop: Syntax.ForAll): P {
    // do not erase under quantifier -> leave unchanged
    return copy(prop);
  }
}

export function eraseTriggersProp(prop: P): P {
  const v = new TriggerEraser();
  return v.visitProp(prop);
}

class QuantifierTransformer extends PropTransformer {
  readonly heaps: HeapsWithLocal;
  readonly locs: LocsWithLocal;
  readonly vars: VarsWithLocal;
  position: boolean;

  constructor(heaps: HeapsWithLocal, locs: LocsWithLocal, vars: VarsWithLocal) {
    super();
    this.heaps = heaps;
    this.locs = locs;
    this.vars = vars;
    this.position = true;
  }

  freshHeap(prefered: Heap, card: number | null = null): Heap {
    let n = prefered;
    while (this.heaps.has(n)) n++;
    this.heaps.set(n, card);
    return n;
  }
  
  freshLoc(prefered: Syntax.Location, card: number | null = null): Syntax.Location {
    let n = prefered;
    while (this.locs.has(n)) n = n + "_";
    this.locs.set(n, card);
    return n;
  }
  
  freshVar(prefered: Syntax.Variable, card: number | null = null): Syntax.Variable {
    let n = prefered;
    while (this.vars.has(n)) n = n + "_";
    this.vars.set(n, card);
    return n;
  }

  localizeHeap(prop: Syntax.ForAll, heap: number, skolemize: boolean, newHeap: Syntax.HeapExpression): Syntax.HeapExpression {
    let h: Syntax.HeapExpression;
    if (skolemize) {
      h = { type: "LocalHeap", local: this.freshHeap(heap, prop.args.length), heap: newHeap, args: prop.args };
    } else {
      h = this.freshHeap(heap);
    }
    return h;
  }

  localizeLoc(prop: Syntax.ForAll, loc: Syntax.Location, skolemize: boolean, newHeap: Syntax.HeapExpression): Syntax.LocationExpression {
    let l: Syntax.LocationExpression;
    if (skolemize) {
      l = { type: "LocalLocation", local: this.freshLoc(loc, prop.args.length), heap: newHeap, args: prop.args };
    } else {
      l = this.freshLoc(loc);
    }
    return l;
  }

  localizeVar(prop: Syntax.ForAll, v: Syntax.Variable, skolemize: boolean, newHeap: Syntax.HeapExpression): Syntax.Expression {
    let e: Syntax.Expression;
    if (skolemize) {
      e = { type: "LocalVariable", local: this.freshVar(v, prop.args.length), heap: newHeap, args: prop.args };
    } else {
      e = this.freshVar(v);
    }
    return e;
  }

  liftExistantials(prop: Syntax.ForAll, skolemize: boolean, newHeap: Syntax.HeapExpression = this.freshHeap(0)): Substituter {
    const sub = new Substituter();
    sub.replaceHeap(0, newHeap);
    prop.existsHeaps.forEach(h => sub.replaceHeap(h, this.localizeHeap(prop, h, skolemize, newHeap)));
    prop.existsLocs.forEach(l => sub.replaceLoc(l, this.localizeLoc(prop, l, skolemize, newHeap)));
    prop.existsVars.forEach(v => sub.replaceVar(v, this.localizeVar(prop, v, skolemize, newHeap)));
    return sub;
  }

  visitNot(prop: Syntax.Not): P {
    this.position = !this.position;
    try {
      return super.visitNot(prop);
    } finally {
      this.position = !this.position;
    }
  }
}

class QuantifierLifter extends QuantifierTransformer {
  visitForAll(prop: Syntax.ForAll): P {
    if (this.position) return copy(prop);
    const sub = this.liftExistantials(prop, true);
    prop.args.forEach(a => sub.replaceVar(a, this.freshVar(a)));
    const callee = sub.visitExpr(prop.callee);
    const trigger = this.visitProp({ type: "CallTrigger", callee, heap: 0, args: prop.args });
    return sub.visitProp(implies(trigger, prop.prop));
  }
}

class TriggerCollector extends PropReducer<Array<Syntax.CallTrigger>> {
  position: boolean;

  constructor(position: boolean) {
    super();
    this.position = position;
  }

  empty(): Array<Syntax.CallTrigger> { return []; }

  reduce(a: Array<Syntax.CallTrigger>, b: Array<Syntax.CallTrigger>) {
    return a.concat(b);
  }

  visitNot(prop: Syntax.Not): Array<Syntax.CallTrigger> {
    this.position = !this.position;
    try {
      return super.visitNot(prop);
    } finally {
      this.position = !this.position;
    }
  }

  visitCallTrigger(prop: Syntax.CallTrigger): Array<Syntax.CallTrigger> {
    const res = super.visitCallTrigger(prop);
    return this.position ? this.r([prop], res) : res;
  }
  
  visitForAll(prop: Syntax.ForAll): Array<Syntax.CallTrigger>  {
    return this.visitExpr(prop.callee); // do not collect under quantifier
  }
}

class QuantifierInstantiator extends QuantifierTransformer {
  triggers: Array<Syntax.CallTrigger>; // relies on 
  instantiations: number;

  constructor(heaps: HeapsWithLocal, locs: LocsWithLocal, vars: VarsWithLocal) {
    super(heaps, locs, vars);
    this.instantiations = 0;
  }

  instantiate(prop: Syntax.ForAll, trigger: Syntax.CallTrigger) {
    const match = eq(prop.callee, trigger.callee);
    const sub = this.liftExistantials(prop, false, trigger.heap);
    // substitute arguments
    prop.args.forEach((a, idx) => {
      sub.replaceVar(a, trigger.args[idx]);
    });
    return implies(match, sub.visitProp(prop.prop));
  }

  visitForAll(prop: Syntax.ForAll): P {
    if (!this.position) return copy(prop);
    const clauses: Array<P> = [prop];
    for (const t of this.triggers) {
      if (prop.args.length != t.args.length || prop.instantiations.some(trigger => eqProp(t, trigger))) {
        continue;
      }
      debugger;
      const instantiated: P = this.instantiate(prop, t);
      clauses.push(instantiated);
      prop.instantiations.push(t);
      this.instantiations++;
    }
    return and(...clauses);
  }

  process(prop: P) {
    this.triggers = (new TriggerCollector(true)).visitProp(prop);
    return this.visitProp(prop);
  }
}

class QuantifierEraser extends PropTransformer {
  visitCallTrigger(prop: Syntax.CallTrigger): P {
    return tru;
  }
  
  visitForAll(prop: Syntax.ForAll): P {
    return tru;
  }
}

export function instantiateQuantifiers(heaps: HeapsWithLocal, locs: LocsWithLocal, vars: VarsWithLocal, p: P): P {
  let prop = (new QuantifierLifter(heaps, locs, vars)).visitProp(p);
  const instantiator = new QuantifierInstantiator(heaps, locs, vars);
  let num = -1;
  while (instantiator.instantiations> num) {
    num = instantiator.instantiations;
    prop = instantiator.process(prop);
    prop = (new QuantifierLifter(heaps, locs, vars)).visitProp(prop);
  }
  prop = (new QuantifierEraser()).visitProp(prop);
  return prop;
}
