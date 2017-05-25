import { Syntax, P, Heap, Heaps, Locs, Vars, Transformer, Substituter, Reducer, tru, and, eq, implies, eqProp, copy } from "./logic";

class TriggerEraser extends Transformer {
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

class QuantifierTransformer extends Transformer {
  readonly heaps: Heaps;
  readonly locs: Locs;
  readonly vars: Vars;
  position: boolean;

  constructor(heaps: Heaps, locs: Locs, vars: Vars) {
    super();
    this.heaps = heaps;
    this.locs = locs;
    this.vars = vars;
    this.position = true;
  }

  freshHeap(prefered: Heap): Heap {
    let n = prefered;
    while (this.heaps.has(n)) n++;
    this.heaps.add(n);
    return n;
  }
  
  freshLoc(prefered: Syntax.Location): Syntax.Location {
    let n = prefered;
    while (this.locs.has(n)) n = n + "_";
    this.locs.add(n);
    return n;
  }
  
  freshVar(prefered: Syntax.Variable): Syntax.Variable {
    let n = prefered;
    while (this.vars.has(n)) n = n + "_";
    this.vars.add(n);
    return n;
  }

  liftExistantials(prop: Syntax.ForAll, newHeap: Syntax.HeapExpression = this.freshHeap(prop.heap)): Substituter {
    const sub = new Substituter();
    sub.replaceHeap(prop.heap, newHeap);
    prop.existsHeaps.forEach(h => sub.replaceHeap(h, this.freshHeap(h)));
    prop.existsLocs.forEach(l => sub.replaceLoc(l, this.freshLoc(l)));
    prop.existsVars.forEach(v => sub.replaceVar(v, this.freshVar(v)));
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
    const sub = this.liftExistantials(prop);
    if (prop.existsHeaps.size + prop.existsLocs.size + prop.existsVars.size > 0) {
      throw new Error("Existentials in negative positions not supported");
    }
    prop.args.forEach(a => sub.replaceVar(a, this.freshVar(a)));
    const callee = sub.visitExpr(prop.callee);
    const trigger = this.visitProp({ type: "CallTrigger", callee, heap: prop.heap, args: prop.args });
    return sub.visitProp(implies(trigger, prop.prop));
  }
}

class TriggerCollector extends Reducer<Array<Syntax.CallTrigger>> {
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

  constructor(heaps: Heaps, locs: Locs, vars: Vars) {
    super(heaps, locs, vars);
    this.instantiations = 0;
  }

  instantiate(prop: Syntax.ForAll, trigger: Syntax.CallTrigger) {
    const match = eq(prop.callee, trigger.callee);
    const sub = this.liftExistantials(prop, trigger.heap);
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

class QuantifierEraser extends Transformer {
  visitCallTrigger(prop: Syntax.CallTrigger): P {
    return tru;
  }
  
  visitForAll(prop: Syntax.ForAll): P {
    return tru;
  }
}

export function instantiateQuantifiers(heaps: Heaps, locs: Locs, vars: Vars, p: P): P {
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
