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
  export interface Fun { type: 'fun'; body: Syntax.FunctionExpression; }
  export interface Obj { type: 'obj'; v: { [key: string]: JSVal }; }
  export interface ObjCls { type: 'obj-cls'; cls: string; args: Array<Value>; }
  export interface Arr { type: 'arr'; elems: Array<Value>; }
  export type Value = Num | Bool | Str | Null | Undefined | Fun | Obj | ObjCls | Arr;
}

export type JSVal = JSVal.Value;

interface LazyObjCls { type: 'obj-cls'; cls: string; args: Array<LazyValue>; }
interface ArrRef { type: 'arr-ref'; name: string; }
interface ObjRef { type: 'obj-ref'; name: string; }
interface FunRef { type: 'fun-ref'; name: string; }
interface Loc { type: 'loc'; name: string; }
type LazyValue = JSVal.Num | JSVal.Bool | JSVal.Str | JSVal.Null | JSVal.Undefined |
                 JSVal.Obj | LazyObjCls | ArrRef | ObjRef | FunRef;
type ArrLengths = (arr: ArrRef) => number;
type ArrElems = (arr: ArrRef, idx: number) => LazyValue;
type ObjProperties = (obj: ObjRef) => string;
type ObjFields = (obj: ObjRef, prop: string) => LazyValue;
type HeapMapping = (loc: Loc) => LazyValue;
interface LazyFun { type: 'fun'; body: Array<{ cond: Array<JSVal>, ret: LazyValue }>; }

export function plainToJSVal (val: any): JSVal {
  if (typeof val === 'number') {
    return { type: 'num', v: val };
  } else if (typeof val === 'boolean') {
    return { type: 'bool', v: val };
  } else if (typeof val === 'string') {
    return { type: 'str', v: val };
  } else if (val === null) {
    return { type: 'null' };
  } else if (val === undefined) {
    return { type: 'undefined' };
  } else if (val instanceof Array) {
    return { type: 'arr', elems: val.map(plainToJSVal) };
  } else if ('_cls_' in val && '_args_' in val) {
    return { type: 'obj-cls', cls: val._cls_, args: val._args_.map(plainToJSVal) };
  } else if (typeof val === 'object') {
    const obj: { [key: string]: JSVal } = {};
    Object.keys(val).forEach(key => obj[key] = plainToJSVal(val[key]));
    return { type: 'obj', v: obj };
  } else {
    throw new Error('unsupported ');
  }
}

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
      return val.body;
    case 'obj':
      return {
        type: 'ObjectExpression',
        properties: Object.keys(val.v).map(key => ({ key, value: valueToJavaScript(val.v[key]) })),
        loc: nullLoc()
      };
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
  private objProperties: ObjProperties | null = null;
  private objPropertyMappings: { [varname: string]: Set<string> } = {};
  private objFields: ObjFields | null = null;
  private heapMappings: { [varname: string]: HeapMapping } = {};
  private vars: { [varname: string]: LazyValue } = {};
  private locs: { [varname: string]: Loc } = {};
  private heaps: Array<string> = [];
  private funs: { [funcref: string]: Array<LazyFun> } = {};
  private funDefaults: Array<LazyValue> = [];

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
    } else if (name === 'objproperties') {
      this.objProperties = this.parseObjectProperties(m.body);
    } else if (name === 'objfield') {
      this.objFields = this.parseObjectFields(m.body);
    } else if (name.startsWith('c_')) {
      return; // skip class names
    } else if (name.startsWith('app')) {
      this.parseFunctions(m.body, parseInt(name.substr(3), 10));
    } else if (name.startsWith('pre') || name.startsWith('post') || name.startsWith('eff') || name.startsWith('call')) {
      return; // skip functions
    } else {
      const heapMatch = matchSExpr(data,
        ['define-fun', { name: 'name' }, [['x!0', 'Loc']], 'JSVal', { expr: 'body' }]);
      if (heapMatch !== null) {
        this.heapMappings[heapMatch.name as string] = this.parseHeapMapping(heapMatch.body);
      } else {
        const propertiesMatch = matchSExpr(data,
          ['define-fun', { name: 'name' }, [['x!0', 'String']], 'Bool', { expr: 'body' }]);
        if (propertiesMatch !== null) {
          const mapping = this.parsePropertyMapping(propertiesMatch.body);
          this.objPropertyMappings[propertiesMatch.name as string] = mapping === null ? new Set() : mapping;
        } else {
          throw this.modelError(`unexpected key: ${name}`);
        }
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

  private tryParseSimpleValue (s: SExpr): JSVal | null {
    if (typeof s === 'string') {
      if (s === 'jsundefined') {
        return { type: 'undefined' };
      } else if (s === 'jsnull') {
        return { type: 'null' };
      } else {
        return null;
      }
    } else {
      if (s.length < 1) return null;
      const tag = s[0];
      if (typeof tag !== 'string') return null;
      if (tag === 'jsbool') {
        if (s.length !== 2) return null;
        const v = s[1];
        if (typeof v !== 'string') return null;
        return { type: 'bool', v: v === 'true' };
      } else if (tag === 'jsnum') {
        if (s.length !== 2) return null;
        const v = s[1];
        if (typeof v === 'string') {
          return { type: 'num', v: parseInt(v, 10) };
        } else {
          const m = matchSExpr(v, ['-', { name: 'num' }]);
          if (m === null) return null;
          return { type: 'num', v: - parseInt(m.num as string, 10) };
        }
      } else if (tag === 'jsstr') {
        if (s.length !== 2) return null;
        const v = s[1];
        if (typeof v !== 'string') return null;
        return { type: 'str', v: v.substr(1, v.length - 2) };
      } else {
        return null;
      }
    }
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
        return { type: 'fun-ref', name: v };
      } else if (tag === 'jsobj') {
        if (s.length !== 2) throw this.modelError(s.toString());
        const v = s[1];
        if (typeof v !== 'string') throw this.modelError(s.toString());
        return { type: 'obj-ref', name: v };
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

  private parseFunctions (smt: SExpr, numArgs: number): void {
    // only find direct matches and treat final value explicitly
    const iteMatch = matchSExpr(smt, ['ite', { group: 'cond' }, { expr: 'then' }, { expr: 'els' }]);
    if (!iteMatch) {
      this.funDefaults[numArgs] = this.parseLazyValue(smt);
      return;
    }
    this.parseFunctions(iteMatch.els, numArgs); // process remaining functions first
    const condList = iteMatch.cond as Array<string>;
    if (condList.length < 3 || condList[0] !== 'and') throw this.modelError('expected (and ...)');
    const funcMatch = matchSExpr(condList[1], ['=', 'x!0', ['jsfun', { name: 'func' }]]);
    if (!funcMatch) return; // skip non-function value mappings
    const funcName = funcMatch.func as string;
    const funcBlocks: Array<LazyFun> =
      funcName in this.funs ? this.funs[funcName] : (this.funs[funcName] = []);
    const fun: LazyFun =
      numArgs in funcBlocks ? funcBlocks[numArgs] : (funcBlocks[numArgs] = { type: 'fun', body: [] });
    const fullCond: Array<JSVal> = [];
    // ignore 'and', func match and heap cond -> remaining part of cond are arguments
    for (let idx = 3; idx < condList.length; idx++) {
      const condMatch = matchSExpr(condList[idx], ['=', `x!${idx - 1}`, { expr: 'val' }]);
      if (!condMatch) throw this.modelError('expected (= x!idx $val)');
      const matchVal: JSVal | null = this.tryParseSimpleValue(condMatch.val);
      if (!matchVal) return;
      fullCond.push(matchVal);
    }
    const then = this.parseLazyValue(iteMatch.then);
    fun.body.unshift({ cond: fullCond, ret: then });
  }

  private parseObjectProperties (smt: SExpr): ObjProperties {
    const iteMatch = matchSExpr(smt,
      ['ite', ['=', 'x!0', { name: 'obj' }], { expr: 'then' }, { expr: 'els' }]);
    if (iteMatch) {
      const then = this.parseObjectProperties(iteMatch.then);
      const els = this.parseObjectProperties(iteMatch.els);
      return (objRef: ObjRef) => objRef.name === iteMatch.obj ? then(objRef) : els(objRef);
    }
    const asArrayMatch = matchSExpr(smt, ['_', 'as-array', { name: 'name' }]);
    if (!asArrayMatch) throw this.modelError('expected (_ as-array $name)');
    return (objRef: ObjRef) => asArrayMatch.name as string;
  }

  private parsePropertyMapping (smt: SExpr): Set<string> | null {
    const iteMatch = matchSExpr(smt,
      ['ite', ['=', 'x!0', { name: 'prop' }], { expr: 'then' }, { expr: 'els' }]);
    if (iteMatch) {
      const then = this.parsePropertyMapping(iteMatch.then);
      const els = this.parsePropertyMapping(iteMatch.els);
      const prop = iteMatch.prop as string;
      if (prop.length < 2 || prop[0] !== '"' || prop[prop.length - 1] !== '"') {
        throw this.modelError('expected string');
      }
      if (then === null) { // if (p = "prop") then false else $x -> $x
        return els;
      } else if (els === null) { // if (p = "prop") then $x else false -> ["prop", $x]
        return new Set([prop.substr(1, prop.length - 2), ...then]);
      } else { // if (p = "prop") then $x else $y -> ["prop", $x, $y]
        return new Set([prop.substr(1, prop.length - 2), ...then, ...els]);
      }
    } else if (smt === 'true') { // include properties on path
      return new Set();
    } else if (smt === 'false') { // do not include properties on path
      return null;
    } else {
      throw this.modelError('expected (true)') ;
    }
  }

  private parseObjectFields (smt: SExpr): ObjFields {
    const iteMatch = matchSExpr(smt,
      ['ite', ['and', ['=', 'x!0', { name: 'obj' }], ['=', 'x!1', { name: 's' }]], { expr: 'then' }, { expr: 'els' }]);
    if (iteMatch) {
      const then = this.parseObjectFields(iteMatch.then);
      const els = this.parseObjectFields(iteMatch.els);
      const arr = iteMatch.obj as string;
      const str = iteMatch.s as string;
      if (str.length < 2 || str[0] !== '"' || str[str.length - 1] !== '"') {
        throw this.modelError('expected string');
      }
      return (objRef: ObjRef, prop: string) =>
        objRef.name === arr && prop === str.substr(1, str.length - 2) ? then(objRef, prop) : els(objRef, prop);
    } else {
      const val: LazyValue = this.parseLazyValue(smt);
      return (objRef: ObjRef, prop: string) => val;
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
      case 'fun-ref':
        const body: Array<Syntax.Statement> = [];
        let numArgs = 0;
        if (this.funs && val.name in this.funs) {
          const funcBlocks: Array<LazyFun> = this.funs[val.name];
          if (Object.keys(funcBlocks).length !== 1) {
            throw this.modelError('no support for variable argument functions');
          }
          numArgs = parseInt(Object.keys(funcBlocks)[0], 10);
          const fun = funcBlocks[numArgs];
          let defaultVal = this.funDefaults[numArgs];
          fun.body.forEach(({ cond, ret }) => {
            if (cond.length === 0) {
              defaultVal = ret;
            } else {
              body.push({
                type: 'IfStatement',
                test: cond
                  .map((condExpr, argIdx): Syntax.Expression => ({
                    type: 'BinaryExpression',
                    operator: '===',
                    left: id(`x_${argIdx}`),
                    right: valueToJavaScript(condExpr),
                    loc: nullLoc()
                  }))
                  .reduceRight((prev, curr) => ({
                    type: 'LogicalExpression',
                    operator: '&&',
                    left: curr,
                    right: prev,
                    loc: nullLoc()
                  })),
                consequent: {
                  type: 'BlockStatement',
                  body: [{
                    type: 'ReturnStatement',
                    argument: valueToJavaScript(this.hydrate(ret)),
                    loc: nullLoc()
                  }],
                  loc: nullLoc()
                },
                alternate: { type: 'BlockStatement', body: [], loc: nullLoc() },
                loc: nullLoc()
              });
            }
          });
          body.push({
            type: 'ReturnStatement',
            argument: valueToJavaScript(this.hydrate(defaultVal)),
            loc: nullLoc()
          });
        }
        return {
          type: 'fun',
          body: {
            type: 'FunctionExpression',
            id: null,
            params: [...Array(numArgs)].map((_, idx) => id(`x_${idx}`)),
            requires: [],
            ensures: [],
            body: {
              type: 'BlockStatement',
              body,
              loc: nullLoc()
            },
            freeVars: [],
            loc: nullLoc()
          }
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
      case 'obj-ref':
        if (this.objProperties === null) throw this.modelError('no objproperties');
        if (this.objFields === null) throw this.modelError('no objfields');
        const obj: { [key: string]: JSVal } = {};
        const objAlias: string = this.objProperties(val);
        if (!(objAlias in this.objPropertyMappings)) throw this.modelError(`no mapping for ${this.objProperties(val)}`);
        for (const key of this.objPropertyMappings[objAlias]) {
          obj[key] = this.hydrate(this.objFields(val, key));
        }
        return { type: 'obj', v: obj };
      default:
        return val;
    }
  }
}
