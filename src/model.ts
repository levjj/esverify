import { Syntax, id, nullLoc } from './javascript';
import { FreeVar, Vars } from './logic';
import { MessageException } from './message';
import { options } from './options';
import { SMTOutput } from './smt';
import { SExpr, matchSExpr, parseSExpr } from './util';

export namespace JSVal {
  export interface Num { type: 'num'; v: number; }
  export interface Bool { type: 'bool'; v: boolean; }
  export interface Str { type: 'str'; v: string; }
  export interface Null { type: 'null'; }
  export interface Undefined { type: 'undefined'; }
  export interface Fun { type: 'fun'; v: string; }
  export interface Obj { type: 'obj'; v: string; }
  export interface ObjCls { type: 'obj-cls'; cls: string; args: Array<Value>; }
  export interface Arr { type: 'arr'; elems: Array<Value>; }
  export type Value = Num | Bool | Str | Null | Undefined | Fun | Obj | ObjCls | Arr;
}

export type JSVal = JSVal.Value;

interface LazyObjCls { type: 'obj-cls'; cls: string; args: Array<LazyValue>; }
interface ArrRef { type: 'arr-ref'; name: string; }
interface Loc { type: 'loc'; name: string; }
type LazyValue = JSVal.Num | JSVal.Bool | JSVal.Str | JSVal.Null | JSVal.Undefined | JSVal.Fun |
                 JSVal.Obj | LazyObjCls | ArrRef;
type ArrLengths = (arr: ArrRef) => number;
type ArrElems = (arr: ArrRef, idx: number) => LazyValue;
type HeapMapping = (loc: Loc) => LazyValue;

export function valueToJavaScript (val: JSVal): Syntax.Expression {
  switch (val.type) {
    case 'num':
    case 'bool':
    case 'str':
      return { type: 'Literal', value: val.v, loc: nullLoc() };
    case 'null':
      return { type: 'Literal', value: null, loc: nullLoc() };
    case 'undefined':
      return { type: 'Literal', value: undefined, loc: nullLoc() };
    case 'fun':
      return {
        type: 'FunctionExpression',
        id: null,
        params: [],
        requires: [],
        ensures: [],
        body: {
          type: 'BlockStatement',
          body: [],
          loc: nullLoc()
        },
        freeVars: [],
        loc: nullLoc()
      };
    case 'obj':
      return { type: 'Literal', value: null, loc: nullLoc() };
    case 'obj-cls':
      return {
        type: 'NewExpression',
        callee: id(val.cls),
        args: val.args.map(arg => valueToJavaScript(arg)),
        loc: nullLoc()
      };
    case 'arr':
      return {
        type: 'ArrayExpression',
        elements: val.elems.map(arg => valueToJavaScript(arg)),
        loc: nullLoc()
      };
  }
}

export class Model {

  private arrLengths: ArrLengths | null = null;
  private arrElems: ArrElems | null = null;
  private heapMappings: { [varname: string]: HeapMapping } = {};
  private vars: { [varname: string]: LazyValue } = {};
  private locs: { [varname: string]: Loc } = {};
  private heaps: Array<string> = [];

  constructor (smt: SMTOutput) {
    // assumes smt starts with "sat", so remove "sat"
    const smt2 = smt.slice(3, smt.length);
    if (smt2.trim().startsWith('(error')) this.modelError(smt2.trim());
    let data: SExpr;
    try {
      data = parseSExpr(smt2.trim());
    } catch (e) {
      throw this.modelError(e.message);
    }
    if (typeof data === 'string') throw this.modelError(data);
    if (data.length < 2) throw this.modelError(smt);
    if (data[0] !== 'model') throw this.modelError(smt);
    data.slice(1).forEach(s => this.parseDefinition(s));
  }

  public valueOf (name: FreeVar): JSVal {
    if (typeof name === 'string') {
      const val = this.vars[name];
      if (!val) throw this.modelError(`no such var ${name}`);
      return this.hydrate(val);
    } else {
      const loc = this.locs[name.name];
      if (!loc) throw this.modelError(`no such loc ${name.name}`);
      const heap = this.heapMappings[this.heaps[name.heap]];
      if (!heap) throw this.modelError(`no such heap ${name.heap}`);
      return this.hydrate(heap(loc));
    }
  }

  public variables (): Vars {
    return new Set([...Object.keys(this.vars), ...Object.keys(this.locs)]);
  }

  private parseDefinition (data: SExpr) {
    if (typeof data === 'string' || data.length < 1) {
      throw this.modelError('expected define-fun');
    }
    const m = matchSExpr(data,
      ['define-fun', { name: 'name' }, { group: 'args' }, { expr: 'return' }, { expr: 'body' }]);
    if (m === null) return; // skip everything except for define-fun
    const name: string = m.name as string;
    if (name.startsWith('v_')) {
      this.vars[name.substr(2)] = this.parseLazyValue(m.body);
    } else if (name.startsWith('l_')) {
      const locVal = m.body;
      if (typeof locVal !== 'string') throw this.modelError('expected loc');
      this.locs[name.substr(2)] = { type: 'loc', name: locVal };
    } else if (name.startsWith('h_')) {
      this.heaps[parseInt(name.substr(2), 10)] = this.parseHeap(m.body);
    } else if (name === 'arrlength') {
      this.arrLengths = this.parseArrayLengths(m.body);
    } else if (name === 'arrelems') {
      this.arrElems = this.parseArrayElems(m.body);
    } else if (name.startsWith('c_')) {
      return; // skip class names
    } else if (name.startsWith('app') || name.startsWith('pre') || name.startsWith('post') ||
               name.startsWith('eff') || name.startsWith('call')) {
      return; // skip functions
    } else {
      const heapMatch = matchSExpr(data,
        ['define-fun', { name: 'name' }, [['x!0', 'Loc']], 'JSVal', { expr: 'body' }]);
      if (heapMatch !== null) {
        this.heapMappings[heapMatch.name as string] = this.parseHeapMapping(heapMatch.body);
      } else {
        throw this.modelError(`unexpected key: ${name}`);
      }
    }
  }

  private modelError (smt: SMTOutput): MessageException {
    return new MessageException({
      status: 'error',
      type: 'unrecognized-model',
      loc: { file: options.filename, start: { line: 0, column: 0 }, end: { line: 0, column: 0 } },
      description: `cannot parse smt ${smt}`
    });
  }

  private parseLazyValue (s: SExpr): LazyValue {
    if (typeof s === 'string') {
      if (s === 'jsundefined') {
        return { type: 'undefined' };
      } else if (s === 'jsnull') {
        return { type: 'null' };
      } else if (s.startsWith('jsobj_')) {
        return { type: 'obj-cls', cls: s.substr(6), args: [] };
      } else if (s.startsWith('Arr!')) {
        return { type: 'arr-ref', name: s };
      } else {
        throw this.modelError(s);
      }
    } else {
      if (s.length < 1) throw this.modelError(s.toString());
      const tag = s[0];
      if (typeof tag !== 'string') throw this.modelError(tag.toString());
      if (tag === 'jsbool') {
        if (s.length !== 2) throw this.modelError(s.toString());
        const v = s[1];
        if (typeof v !== 'string') throw this.modelError(s.toString());
        return { type: 'bool', v: v === 'true' };
      } else if (tag === 'jsnum') {
        if (s.length !== 2) throw this.modelError(s.toString());
        const v = s[1];
        if (typeof v === 'string') {
          return { type: 'num', v: parseInt(v, 10) };
        } else {
          const m = matchSExpr(v, ['-', { name: 'num' }]);
          if (m === null) throw this.modelError(`cannot parse ${v}`);
          return { type: 'num', v: - parseInt(m.num as string, 10) };
        }
      } else if (tag === 'jsstr') {
        if (s.length !== 2) throw this.modelError(s.toString());
        const v = s[1];
        if (typeof v !== 'string') throw this.modelError(s.toString());
        return { type: 'str', v: v.substr(1, v.length - 2) };
      } else if (tag === 'jsfun') {
        if (s.length !== 2) throw this.modelError(s.toString());
        const v = s[1];
        if (typeof v !== 'string') throw this.modelError(s.toString());
        return { type: 'fun', v };
      } else if (tag === 'jsobj') {
        if (s.length !== 2) throw this.modelError(s.toString());
        const v = s[1];
        if (typeof v !== 'string') throw this.modelError(s.toString());
        return { type: 'obj', v };
      } else if (tag === 'jsobj_Array') {
        if (s.length !== 2) throw this.modelError(s.toString());
        const v = s[1];
        if (typeof v !== 'string') throw this.modelError(s.toString());
        return { type: 'arr-ref', name: v };
      } else if (tag.startsWith('jsobj_')) {
        return {
          type: 'obj-cls',
          cls: tag.substr(6),
          args: s.slice(1).map(a => this.parseLazyValue(a))
        };
      } else {
        throw this.modelError(tag);
      }
    }
  }

  private parseHeap (smt: SExpr): string {
    const m = matchSExpr(smt, ['_', 'as-array', { name: 'name' }]);
    if (!m) throw this.modelError('expected (_ as-array $name)');
    return m.name as string;
  }

  private parseHeapMapping (smt: SExpr): HeapMapping {
    const iteMatch = matchSExpr(smt,
      ['ite', ['=', 'x!0', { name: 'loc' }], { expr: 'then' }, { expr: 'els' }]);
    if (iteMatch) {
      const then = this.parseHeapMapping(iteMatch.then);
      const els = this.parseHeapMapping(iteMatch.els);
      return (loc: Loc) => loc.name === iteMatch.loc ? then(loc) : els(loc);
    } else {
      const val: LazyValue = this.parseLazyValue(smt);
      return (loc: Loc) => val;
    }
  }

  private parseArrayLengths (smt: SExpr): ArrLengths {
    const iteMatch = matchSExpr(smt,
      ['ite', ['=', 'x!0', { name: 'arr' }], { expr: 'then' }, { expr: 'els' }]);
    if (iteMatch) {
      const then = this.parseArrayLengths(iteMatch.then);
      const els = this.parseArrayLengths(iteMatch.els);
      return (arrRef: ArrRef) => arrRef.name === iteMatch.arr ? then(arrRef) : els(arrRef);
    } else {
      if (typeof smt !== 'string') throw this.modelError('expected num');
      return (arrRef: ArrRef) => parseInt(smt, 10);
    }
  }

  private parseArrayElems (smt: SExpr): ArrElems {
    const iteMatch = matchSExpr(smt,
      ['ite', ['and', ['=', 'x!0', { name: 'arr' }], ['=', 'x!1', { name: 'i' }]], { expr: 'then' }, { expr: 'els' }]);
    if (iteMatch) {
      const then = this.parseArrayElems(iteMatch.then);
      const els = this.parseArrayElems(iteMatch.els);
      const arr = iteMatch.arr as string;
      const i = parseInt(iteMatch.i as string, 10);
      return (arrRef: ArrRef, idx: number) => arrRef.name === arr && idx === i ? then(arrRef, idx) : els(arrRef, idx);
    } else {
      const val: LazyValue = this.parseLazyValue(smt);
      return (arrRef: ArrRef, idx: number) => val;
    }
  }

  private hydrate (val: LazyValue): JSVal {
    switch (val.type) {
      case 'obj-cls':
        return {
          type: 'obj-cls',
          cls: val.cls,
          args: val.args.map(a => this.hydrate(a))
        };
      case 'arr-ref':
        if (this.arrLengths === null) throw this.modelError('no arrlength');
        return {
          type: 'arr',
          elems: [...Array(this.arrLengths(val))].map((_, i) => {
            if (this.arrElems === null) throw this.modelError('no arrelems');
            return this.hydrate(this.arrElems(val, i));
          })
        };
      default:
        return val;
    }
  }
}
