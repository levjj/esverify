import { FreeVars, Heap, Heaps, Locs, P, Reducer, Substituter, Syntax, Transformer, Traverser, Vars, and, copy,
         eqExpr, eqHeap, eqProp, implies, tru } from './logic';
import { getOptions } from './options';
import { propositionToSMT } from './smt';

declare const console: { log: (s: string) => void };

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

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): P {
    // do not erase under quantifier -> leave unchanged
    return copy(prop);
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): P {
    // do not erase under quantifier -> leave unchanged
    return copy(prop);
  }
}

export function eraseTriggersProp (prop: P): P {
  const v = new TriggerEraser();
  return v.visitProp(prop);
}

abstract class QuantifierTransformer extends Transformer {
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
    let name = prefered;
    if (this.locs.has(name)) {
      const m = name.match(/(.*)_(\d+)$/);
      let idx = m ? +m[2] : 0;
      name = m ? m[1] : name;
      while (this.locs.has(`${name}_${idx}`)) idx++;
      name = `${name}_${idx}`;
    }
    this.locs.add(name);
    return name;
  }

  freshVar (prefered: Syntax.Variable): Syntax.Variable {
    let name = prefered;
    if (this.vars.has(name)) {
      const m = name.match(/(.*)_(\d+)$/);
      let idx = m ? +m[2] : 0;
      name = m ? m[1] : name;
      while (this.vars.has(`${name}_${idx}`)) idx++;
      name = `${name}_${idx}`;
    }
    this.vars.add(name);
    return name;
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

  abstract visitForAllCalls (prop: Syntax.ForAllCalls): P;
  abstract visitForAllAccessObject (prop: Syntax.ForAllAccessObject): P;
  abstract visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): P;
}

class QuantifierLifter extends QuantifierTransformer {

  freeVars: FreeVars;

  constructor (heaps: Heaps, locs: Locs, vars: Vars, freeVars: FreeVars) {
    super(heaps, locs, vars);
    this.freeVars = freeVars;
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): P {
    if (this.position) return copy(prop);
    if (prop.existsHeaps.size + prop.existsLocs.size + prop.existsVars.size > 0) {
      throw new Error('Existentials in negative positions not supported');
    }
    const thisArg: string = this.freshVar(prop.thisArg);
    const trigger: P = {
      type: 'CallTrigger',
      callee: prop.callee,
      heap: prop.heap,
      thisArg: prop.thisArg,
      args: prop.args,
      fuel: prop.fuel
    };
    const sub = this.liftExistantials(prop);
    sub.replaceVar(prop.thisArg, thisArg);
    const renamedVars: Array<Syntax.Variable> = [];
    prop.args.forEach(a => {
      const renamedVar = this.freshVar(a);
      renamedVars.push(renamedVar);
      this.freeVars.push(renamedVar);
      sub.replaceVar(a, renamedVar);
    });
    prop.liftCallback(thisArg, renamedVars);
    return this.visitProp(sub.visitProp(implies(trigger, prop.prop)));
  }

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): P {
    if (this.position) return copy(prop);
    const trigger: P = {
      type: 'AccessTrigger',
      object: prop.thisArg,
      property: this.freshVar('prop'),
      heap: prop.heap,
      fuel: prop.fuel
    };
    const sub = new Substituter();
    sub.replaceVar(prop.thisArg, this.freshVar(prop.thisArg));
    return this.visitProp(sub.visitProp(implies(trigger, prop.prop)));
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): P {
    if (this.position) return copy(prop);
    const trigger: P = {
      type: 'AccessTrigger',
      object: prop.object,
      property: prop.property,
      heap: prop.heap,
      fuel: prop.fuel
    };
    const sub = new Substituter();
    sub.replaceVar(prop.property, this.freshVar(prop.property));
    return this.visitProp(sub.visitProp(implies(trigger, prop.prop)));
  }
}

class MaximumDepthFinder extends Reducer<number> {
  empty (): number { return 0; }

  reduce (a: number, b: number): number {
    return Math.max(a, b);
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): number {
    return 1 + super.visitForAllCalls(prop);
  }

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): number {
    return 1 + super.visitForAllAccessObject(prop);
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): number {
    return 1 + super.visitForAllAccessProperty(prop);
  }
}

class TriggerFueler extends Traverser {

  fuel: number = 0;

  visitCallTrigger (prop: Syntax.CallTrigger): void {
    super.visitCallTrigger(prop);
    prop.fuel = this.fuel;
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): void {
    super.visitForAllCalls(prop);
    prop.fuel = this.fuel;
  }

  visitAccessTrigger (prop: Syntax.AccessTrigger): void {
    super.visitAccessTrigger(prop);
    prop.fuel = this.fuel;
  }

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): void {
    super.visitForAllAccessObject(prop);
    prop.fuel = this.fuel;
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): void {
    super.visitForAllAccessProperty(prop);
    prop.fuel = this.fuel;
  }

  process (prop: P): P {
    this.fuel = (new MaximumDepthFinder()).visitProp(prop);
    this.visitProp(prop);
    return prop;
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
    return this.position && prop.fuel > 0 ? this.r([[prop],[]], res) : res;
  }

  visitAccessTrigger (prop: Syntax.AccessTrigger): Triggers {
    const res = super.visitAccessTrigger(prop);
    return this.position && prop.fuel > 0 ? this.r([[],[prop]], res) : res;
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): Triggers {
    return this.visitExpr(prop.callee); // do not collect under quantifier
  }

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): Triggers {
    return this.empty(); // do not collect under quantifier
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): Triggers {
    return this.empty(); // do not collect under quantifier
  }
}

class QuantifierInstantiator extends QuantifierTransformer {
  triggers: Triggers = [[], []];
  instantiations: number;

  constructor (heaps: Heaps, locs: Locs, vars: Vars) {
    super(heaps, locs, vars);
    this.instantiations = 0;
  }

  consumeFuel (prop: P, prevFuel: number): P {
    const fueler = new TriggerFueler();
    fueler.fuel = prevFuel - 1;
    fueler.visitProp(prop);
    return prop;
  }

  instantiateCall (prop: Syntax.ForAllCalls, trigger: Syntax.CallTrigger) {
    const sub = this.liftExistantials(prop, trigger.heap);
    // substitute arguments
    sub.replaceVar(prop.thisArg, trigger.thisArg);
    prop.args.forEach((a, idx) => {
      sub.replaceVar(a, trigger.args[idx]);
    });
    const replaced = sub.visitProp(prop.prop);
    return this.consumeFuel(replaced, trigger.fuel);
  }

  instantiateAccessObject (prop: Syntax.ForAllAccessObject, trigger: Syntax.AccessTrigger) {
    const sub = new Substituter();
    sub.replaceVar(prop.thisArg, trigger.object);
    sub.replaceHeap(prop.heap, trigger.heap);
    const replaced = sub.visitProp(prop.prop);
    return this.consumeFuel(replaced, trigger.fuel);
  }

  instantiateAccessProperty (prop: Syntax.ForAllAccessProperty, trigger: Syntax.AccessTrigger) {
    const sub = new Substituter();
    sub.replaceVar(prop.property, trigger.property);
    sub.replaceHeap(prop.heap, trigger.heap);
    const replaced = sub.visitProp(prop.prop);
    return this.consumeFuel(replaced, trigger.fuel);
  }

  visitForAllCalls (prop: Syntax.ForAllCalls): P {
    if (!this.position) return copy(prop);
    const clauses: Array<P> = [prop];
    for (const t of this.triggers[0]) {
      // continue if already instantiated with same trigger
      if (prop.args.length !== t.args.length || prop.instantiations.some(trigger => eqProp(t, trigger))) {
        continue;
      }
      const instantiated: P = this.instantiateCall(prop, t);
      clauses.push(instantiated);
      prop.instantiations.push(t);
      this.instantiations++;
      if (getOptions().verbose && !getOptions().quiet) {
        console.log('trigger: ' + propositionToSMT(t));
      }
    }
    return and(...clauses);
  }

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): P {
    if (!this.position) return copy(prop);
    const clauses: Array<P> = [prop];
    for (const t of this.triggers[1]) {
      // continue if already instantiated with same trigger, ignoring trigger.property
      if (prop.instantiations.some(trigger => eqHeap(t.heap, trigger.heap) && eqExpr(t.object, trigger.object))) {
        continue;
      }
      const instantiated: P = this.instantiateAccessObject(prop, t);
      clauses.push(instantiated);
      prop.instantiations.push(t);
      this.instantiations++;
      if (getOptions().verbose && !getOptions().quiet) {
        console.log('trigger: ' + propositionToSMT(t));
      }
    }
    return and(...clauses);
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): P {
    if (!this.position) return copy(prop);
    const clauses: Array<P> = [prop];
    for (const t of this.triggers[1]) {
      // continue if already instantiated with same trigger
      if (prop.instantiations.some(trigger => eqProp(t, trigger))) {
        continue;
      }
      const instantiated: P = this.instantiateAccessProperty(prop, t);
      clauses.push(instantiated);
      prop.instantiations.push(t);
      this.instantiations++;
      if (getOptions().verbose && !getOptions().quiet) {
        console.log('trigger: ' + propositionToSMT(t));
      }
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

  visitForAllAccessObject (prop: Syntax.ForAllAccessObject): P {
    return tru;
  }

  visitForAllAccessProperty (prop: Syntax.ForAllAccessProperty): P {
    return tru;
  }
}

export function instantiateQuantifiers (heaps: Heaps, locs: Locs, vars: Vars, freeVars: FreeVars, p: P): P {
  const initialFuel = new TriggerFueler();
  const lifter = new QuantifierLifter(heaps, locs, vars, freeVars);
  const instantiator = new QuantifierInstantiator(heaps, locs, vars);
  let prop = initialFuel.process(lifter.visitProp(p));
  let num = -1;
  while (instantiator.instantiations > num) {
    num = instantiator.instantiations;
    prop = instantiator.process(prop);
    prop = lifter.visitProp(prop);
  }
  prop = (new QuantifierEraser()).visitProp(prop);
  return prop;
}
