import { Syntax, P, Heap, Heaps, Locs, Vars, Transformer, Substituter, Reducer, tru, and, eq, implies, eqProp, copy } from './logic';

class TriggerEraser extends Transformer {
  visitCallTrigger (prop: Syntax.CallTrigger): P {
    return tru;
  }

  visitAccessTrigger (prop: Syntax.AccessTrigger): P {
    return tru;
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): P {
    // do not erase under quantifier -> leave unchanged
    return copy(prop);
  }

  visitForAllAccess (prop: Syntax.ForAllAccess): P {
    // do not erase under quantifier -> leave unchanged
    return copy(prop);
  }
}

export function eraseTriggersProp (prop: P): P {
  const v = new TriggerEraser();
  return v.visitProp(prop);
}

class QuantifierTransformer extends Transformer {
  readonly heaps: Heaps;
  readonly locs: Locs;
  readonly vars: Vars;
  position: boolean;

  constructor (heaps: Heaps, locs: Locs, vars: Vars) {
    super();
    this.heaps = heaps;
    this.locs = locs;
    this.vars = vars;
    this.position = true;
  }

  freshHeap (prefered: Heap): Heap {
    let n = prefered;
    while (this.heaps.has(n)) n++;
    this.heaps.add(n);
    return n;
  }

  freshLoc (prefered: Syntax.Location): Syntax.Location {
    let n = prefered;
    while (this.locs.has(n)) n = n + '_';
    this.locs.add(n);
    return n;
  }

  freshVar (prefered: Syntax.Variable): Syntax.Variable {
    let n = prefered;
    while (this.vars.has(n)) n = n + '_';
    this.vars.add(n);
    return n;
  }

  liftExistantials (prop: Syntax.ForAllCalls, newHeap: Syntax.HeapExpression = this.freshHeap(prop.heap)): Substituter {
    const sub = new Substituter();
    sub.replaceHeap(prop.heap, newHeap);
    prop.existsHeaps.forEach(h => sub.replaceHeap(h, this.freshHeap(h)));
    prop.existsLocs.forEach(l => sub.replaceLoc(l, this.freshLoc(l)));
    prop.existsVars.forEach(v => sub.replaceVar(v, this.freshVar(v)));
    return sub;
  }

  visitNot (prop: Syntax.Not): P {
    this.position = !this.position;
    try {
      return super.visitNot(prop);
    } finally {
      this.position = !this.position;
    }
  }
}

class QuantifierLifter extends QuantifierTransformer {
  visitForAllCalls (prop: Syntax.ForAllCalls): P {
    if (this.position) return copy(prop);
    if (prop.existsHeaps.size + prop.existsLocs.size + prop.existsVars.size > 0) {
      throw new Error('Existentials in negative positions not supported');
    }
    const sub = this.liftExistantials(prop);
    prop.args.forEach(a => sub.replaceVar(a, this.freshVar(a)));
    const callee = sub.visitExpr(prop.callee);
    const trigger = this.visitProp({ type: 'CallTrigger', callee, heap: prop.heap, args: prop.args });
    return sub.visitProp(implies(trigger, prop.prop));
  }

  visitForAllAccess (prop: Syntax.ForAllAccess): P {
    if (this.position) return copy(prop);
    const sub = new Substituter();
    sub.replaceVar('this', this.freshVar('this'));
    const trigger = this.visitProp({ type: 'AccessTrigger', object: 'this' });
    return sub.visitProp(implies(trigger, prop.prop));
  }
}

type Triggers = [Array<Syntax.CallTrigger>, Array<Syntax.AccessTrigger>];

class TriggerCollector extends Reducer<Triggers> {
  position: boolean;

  constructor (position: boolean) {
    super();
    this.position = position;
  }

  empty (): Triggers { return [[], []]; }

  reduce (a: Triggers, b: Triggers): Triggers {
    return [a[0].concat(b[0]), a[1].concat(b[1])];
  }

  visitNot (prop: Syntax.Not): Triggers {
    this.position = !this.position;
    try {
      return super.visitNot(prop);
    } finally {
      this.position = !this.position;
    }
  }

  visitCallTrigger (prop: Syntax.CallTrigger): Triggers {
    const res = super.visitCallTrigger(prop);
    return this.position ? this.r([[prop],[]], res) : res;
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): Triggers {
    return this.visitExpr(prop.callee); // do not collect under quantifier
  }

  visitAccessTrigger (prop: Syntax.AccessTrigger): Triggers {
    const res = super.visitAccessTrigger(prop);
    return this.position ? this.r([[],[prop]], res) : res;
  }

  visitForAllAccess (prop: Syntax.ForAllAccess): Triggers {
    return this.empty(); // do not collect under quantifier
  }
}

class QuantifierInstantiator extends QuantifierTransformer {
  triggers: Triggers;
  instantiations: number;

  constructor (heaps: Heaps, locs: Locs, vars: Vars) {
    super(heaps, locs, vars);
    this.instantiations = 0;
  }

  instantiateCall (prop: Syntax.ForAllCalls, trigger: Syntax.CallTrigger) {
    const match = eq(prop.callee, trigger.callee);
    const sub = this.liftExistantials(prop, trigger.heap);
    // substitute arguments
    prop.args.forEach((a, idx) => {
      sub.replaceVar(a, trigger.args[idx]);
    });
    return implies(match, sub.visitProp(prop.prop));
  }

  instantiateAccess (prop: Syntax.ForAllAccess, trigger: Syntax.AccessTrigger) {
    const sub = new Substituter();
    sub.replaceVar('this', trigger.object);
    return sub.visitProp(prop.prop);
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): P {
    if (!this.position) return copy(prop);
    const clauses: Array<P> = [prop];
    for (const t of this.triggers[0]) {
      if (prop.args.length !== t.args.length || prop.instantiations.some(trigger => eqProp(t, trigger))) {
        continue;
      }
      const instantiated: P = this.instantiateCall(prop, t);
      clauses.push(instantiated);
      prop.instantiations.push(t);
      this.instantiations++;
    }
    return and(...clauses);
  }

  visitForAllAccess (prop: Syntax.ForAllAccess): P {
    if (!this.position) return copy(prop);
    const clauses: Array<P> = [prop];
    for (const t of this.triggers[1]) {
      if (prop.instantiations.some(trigger => eqProp(t, trigger))) {
        continue;
      }
      const instantiated: P = this.instantiateAccess(prop, t);
      clauses.push(instantiated);
      prop.instantiations.push(t);
      this.instantiations++;
    }
    return and(...clauses);
  }

  process (prop: P) {
    this.triggers = (new TriggerCollector(true)).visitProp(prop);
    return this.visitProp(prop);
  }
}

class QuantifierEraser extends Transformer {
  visitCallTrigger (prop: Syntax.CallTrigger): P {
    return tru;
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): P {
    return tru;
  }

  visitAccessTrigger (prop: Syntax.AccessTrigger): P {
    return tru;
  }

  visitForAllAccess (prop: Syntax.ForAllAccess): P {
    return tru;
  }
}

export function instantiateQuantifiers (heaps: Heaps, locs: Locs, vars: Vars, p: P): P {
  let prop = (new QuantifierLifter(heaps, locs, vars)).visitProp(p);
  const instantiator = new QuantifierInstantiator(heaps, locs, vars);
  let num = -1;
  while (instantiator.instantiations > num) {
    num = instantiator.instantiations;
    prop = instantiator.process(prop);
    prop = (new QuantifierLifter(heaps, locs, vars)).visitProp(prop);
  }
  prop = (new QuantifierEraser()).visitProp(prop);
  return prop;
}
