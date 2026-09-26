/** F* value model. Imperative control flow becomes total recursive functions.
 * The shared lowering owns TypeScript semantics (narrowing, value updates,
 * collection operations); this emitter owns F* types and verification effects.
 */
import type { Ty, TModule } from "./typedir.js";
import type { Decl, Expr, Stmt, Param, MatchPattern, FnDef, FnMethod, FnDefByMethod, ExternDecl } from "./ir.js";
import { exactIntegerLiteral, anyExpr, anyExprInStmts } from "./ir.js";
import { transformModuleFstar } from "./transform.js";
import { parseTsType } from "./types.js";

export function fstarName(s: string): string {
  return "v_" + [...s].map(c => /[A-Za-z0-9]/.test(c) ? c : `_${c.codePointAt(0)!.toString(16)}_`).join("");
}
const n = fstarName;
const ind = (s:string) => s.split("\n").map(l => "  " + l).join("\n");
const app = (f:string, xs:string[]) => `(${f} ${xs.length ? xs.map(x => `(${x})`).join(" ") : "()"})`;
const unknown:Ty = {kind:"unknown"};
type Fn = FnDef | FnMethod | FnDefByMethod | ExternDecl;
type Data = Extract<Decl,{kind:"structure"|"inductive"}>;
interface Binding { text:string; ty:Ty; id:number; nonneg?:boolean }
interface Ctx {
  vars:Map<string,Binding>;
  deps:Set<string>;
  result?:Ty;
  post?:string;
  trace?:string;
  fnName?:string;
  onReturn?:(value:string,ctx:Ctx)=>string;
  onBreak?:(ctx:Ctx)=>string;
  onContinue?:(ctx:Ctx)=>string;
}
type Cont = (ctx:Ctx)=>string;

export function emitFstarFile(mod:TModule, moduleName:string):string {
  const lowered=transformModuleFstar(mod);
  const fail=(s:string):never=>{throw new Error(`F* (${mod.file}): ${s}`);};
  const flatten=(ds:Decl[]):Decl[]=>ds.flatMap(d=>d.kind==="namespace"?flatten(d.decls):[d]);
  const decls=flatten([...(lowered.typesFile?.decls??[]),...lowered.defFile.decls]).flatMap(d=>{
    if(d.kind!=="class")return [d];
    const self:Ty={kind:"user",name:d.name};
    function rewrite(x:any,post=false):any {
      if(!x||typeof x!=="object")return x;
      if(Array.isArray(x))return x.map(v=>rewrite(v,post));
      if(post&&x.kind==="var"&&(x.name==="this"||x.name==="\\result"))return {kind:"tupleProj",obj:{kind:"var",name:"\\result"},index:x.name==="this"?1:0,arity:2,ty:x.ty};
      if(!post&&x.kind==="return")return {...x,value:{kind:"tupleLiteral",elems:[x.value,{kind:"var",name:"this",ty:self}]}};
      if(!post&&x.kind==="assign"&&x.target.startsWith("this."))return {kind:"assign",target:"this",value:{kind:"record",spread:{kind:"var",name:"this",ty:self},fields:[{name:x.target.slice(5),value:x.value}],ty:self}};
      return Object.fromEntries(Object.entries(x).map(([k,v])=>[k,rewrite(v,post)]));
    }
    return [{kind:"structure",name:d.name,fields:d.fields,deriving:[]} as Decl,...d.methods.map(f=>({...f,name:d.name+"."+f.name,params:[{name:"this",type:self},...f.params],returnType:{kind:"tuple",elems:[f.returnType,self]} as Ty,ensures:f.ensures.map(e=>rewrite(e,true)),body:rewrite(f.body)}))];
  });
  const data=new Map<string,Data>();
  const aliases=new Map<string,Ty>();
  const funcs=new Map<string,Fn>();
  const constants=new Map<string,Extract<Decl,{kind:"const"}>>();
  for(const d of decls){
    if(d.kind==="structure"||d.kind==="inductive")data.set(d.name,d);
    if(d.kind==="type-alias")aliases.set(d.name,d.target);
    if(["def","def-by-method","method","extern"].includes(d.kind)&&!funcs.has(d.name))funcs.set(d.name,d as Fn);
    if(d.kind==="const")constants.set(d.name,d);
  }
  const effectful = new Set<string>();
  const loopNumbers = new Map<string,number>();
  const calls = (f:Fn,p:(e:Expr)=>boolean) => f.kind==="extern" ? false : f.kind==="def" ? anyExpr(f.body,p) : anyExprInStmts(f.kind==="method"?f.body:f.methodBody,p);
  for(const f of funcs.values())if(f.kind==="extern"&&f.impure||calls(f,e=>e.kind==="havoc"))effectful.add(f.name);
  let changed=true;
  while(changed){changed=false;for(const f of funcs.values())if(!effectful.has(f.name)&&calls(f,e=>e.kind==="app"&&effectful.has(e.fn))){effectful.add(f.name);changed=true;}}
  const trust:string[]=[];
  let needsUnknown=false;
  let fresh=0;
  const bind=(c:Ctx,id:string,ty:Ty,text=n(id)):Ctx=>({...c,vars:new Map([...c.vars,[id,{text,ty,id:fresh++}]])});
  const root=():Ctx=>({vars:new Map(),deps:new Set()});
  function parts(s:string):[string,Ty[]] {
    const start=s.indexOf("<");if(start<0)return [s,[]];
    const args:string[]=[];let depth=0,last=start+1;
    for(let i=last;i<s.length-1;i++){
      if(s[i]==="<"||s[i]==="("||s[i]==="[")depth++;
      if(s[i]===">"||s[i]===")"||s[i]==="]")depth--;
      if(s[i]===","&&!depth){args.push(s.slice(last,i));last=i+1;}
    }
    args.push(s.slice(last,-1));return [s.slice(0,start),args.map(a=>parseTsType(a.trim()))];
  }
  function expand(t:Ty):Ty {
    if(t.kind==="user"&&aliases.has(t.name))return expand(aliases.get(t.name)!);
    return t;
  }
  function keyType(t:Ty):string {return expand(t).kind==="string"?"(list R.codeunit)":type(t);}
  function key(t:Ty,v:string):string {return expand(t).kind==="string"?app("R.to_list",[v]):v;}
  function type(t:Ty):string {
    switch(t.kind){
      case "int":case "nat":case "bool":return t.kind;
      case "real":return "real";
      case "string":return "R.string";
      case "void":return "unit";
      case "array":return `(S.seq ${type(t.elem)})`;
      case "optional":return `(option ${type(t.inner)})`;
      case "tuple":return `(${t.elems.map(type).join(" & ")})`;
      case "set":return `(FS.set ${keyType(t.elem)})`;
      case "map":return `(FM.map ${keyType(t.key)} ${type(t.value)})`;
      case "fn":return `(${t.params.length?t.params.map(type).join(" -> "):"unit"} -> GTot ${type(t.result)})`;
      case "user":{const [id,args]=parts(t.name);return args.length?`(${n(id)} ${args.map(type).join(" ")})`:n(id);}
      case "unknown":needsUnknown=true;return "ls_unknown";
    }
  }
  function of(e:Expr,c:Ctx):Ty {
    if(e.kind==="var"){
      const f=funcs.get(e.name);
      return expand(c.vars.get(e.name)?.ty??constants.get(e.name)?.type??(f?{kind:"fn",params:f.params.map(p=>p.type),result:f.returnType}:e.ty)??unknown);
    }
    if(e.kind==="app"&&funcs.has(e.fn)){
      const f=funcs.get(e.fn)!;
      const parameters=new Set(f.typeParams.map(p=>p.replace(/\(==\)$/, "")));
      const bindings=new Map<string,Ty>();
      const infer=(pattern:Ty,actual:Ty):void=>{
        if(pattern.kind==="user"&&parameters.has(pattern.name)){if(actual.kind!=="unknown")bindings.set(pattern.name,actual);return;}
        if(pattern.kind==="array"&&actual.kind==="array")infer(pattern.elem,actual.elem);
        if(pattern.kind==="optional"&&actual.kind==="optional")infer(pattern.inner,actual.inner);
        if(pattern.kind==="fn"&&actual.kind==="fn"){
          pattern.params.forEach((p,i)=>{if(actual.params[i])infer(p,actual.params[i]);});infer(pattern.result,actual.result);
        }
      };
      const subst=(t:Ty):Ty=>{
        if(t.kind==="user")return bindings.get(t.name)??t;
        if(t.kind==="array")return {...t,elem:subst(t.elem)};
        if(t.kind==="optional")return {...t,inner:subst(t.inner)};
        if(t.kind==="fn")return {...t,params:t.params.map(subst),result:subst(t.result)};
        if(t.kind==="tuple")return {...t,elems:t.elems.map(subst)};
        return t;
      };
      f.params.forEach((p,i)=>{if(e.args[i])infer(p.type,of(e.args[i],c));});
      return expand(subst(f.returnType));
    }
    if(e.ty&&e.ty.kind!=="unknown")return expand(e.ty);
    switch(e.kind){
      case "num":case "bigint":return {kind:"int"};
      case "bool":return {kind:"bool"};case "str":return {kind:"string"};
      case "toNat":return {kind:"nat"};case "toReal":return {kind:"real"};
      case "app":return funcs.get(e.fn)?.returnType??unknown;
      case "field":{
        const t=of(e.obj,c);if(t.kind==="user"){
          const d=data.get(parts(t.name)[0]);
          if(d?.kind==="structure")return d.fields.find(f=>f.name===e.field)?.type??unknown;
          if(d?.kind==="inductive")return d.constructors.flatMap(x=>x.fields).find(f=>f.name===e.field)?.type??unknown;
        }
        if(["size","length","collectionSize"].includes(e.field))return {kind:"nat"};return unknown;
      }
      case "index":{const t=of(e.arr,c);return t.kind==="array"?t.elem:t.kind==="string"?{kind:"string"}:unknown;}
      case "let":return of(e.body,bind(c,e.name,of(e.value,c)));
      case "if":return of(e.then,c);
      case "tupleLiteral":return {kind:"tuple",elems:e.elems.map(x=>of(x,c))};
      case "tupleProj":{const t=of(e.obj,c);return t.kind==="tuple"?t.elems[e.index]:unknown;}
      case "lambda":{let lc=c;for(const p of e.params)lc=bind(lc,p.name,p.type);const ret=e.body.at(-1);return {kind:"fn",params:e.params.map(p=>p.type),result:ret?.kind==="return"?of(ret.value,lc):unknown};}
      default:return unknown;
    }
  }
  function valueName(id:string,c:Ctx):string {
    if(id==="\\result")return "ls_result";
    if(id==="Unit.unit"||id==="undefined")return "()";
    if(id==="Some"||id==="None")return id;
    const b=c.vars.get(id);if(b)return b.text;
    if(funcs.has(id)||constants.has(id))c.deps.add(id);
    return n(id.replace(/^Pure\./,""));
  }
  function ctor(id:string,t?:string):string {
    if(id==="some")return "Some";if(id==="none")return "None";
    let parent=t?parts(t)[0]:undefined;
    if(!parent){const ds=[...data.values()].filter(d=>d.kind==="inductive"&&d.constructors.some(x=>x.name===id));if(ds.length===1)parent=ds[0].name;}
    if(!parent)fail(`cannot resolve constructor '${id}'`);
    return `C_${n(parent!)}_${n(id)}`;
  }
  const field=(parent:string,id:string)=>`f_${n(parent)}_${n(id)}`;
  function pattern(p:MatchPattern,t:Ty,c:Ctx):[string,Ctx]{
    if(p.kind==="wild")return ["_",c];
    if(p.kind==="literal")return fail("string patterns must be lowered to conditional expressions");
    let fields:Param[]=[];let parent:string|undefined;
    if(t.kind==="optional")fields=[{name:"value",type:t.inner}];
    if(t.kind==="user"){
      parent=parts(t.name)[0];const d=data.get(parent);
      if(d?.kind==="inductive")fields=d.constructors.find(x=>x.name===p.ctor)?.fields??[];
    }
    let cc=c;
    for(let i=0;i<p.binders.length;i++)cc=bind(cc,p.binders[i],fields[i]?.type??unknown);
    return [[ctor(p.ctor,parent),...p.binders.map(n)].join(" "),cc];
  }
  function prop(e:Expr,c:Ctx):string {
    if(e.kind==="forall"||e.kind==="exists")return `(${e.kind} (${n(e.var)}:${type(e.type)}). ${prop(e.body,bind(c,e.var,e.type))})`;
    if(e.kind==="implies")return `(${e.premises.map(x=>prop(x,c)).join(" /\\ ")||"True"} ==> ${prop(e.conclusion,c)})`;
    if(e.kind==="unop"&&["!","¬"].includes(e.op))return `(not (${prop(e.expr,c)}))`;
    if(e.kind==="binop"){
      const logic:Record<string,string>={"∧":"/\\","∨":"\\/","↔":"<==>","&&":"/\\","||":"\\/","==>":"==>"};
      if(logic[e.op])return `(${prop(e.left,c)} ${logic[e.op]} ${prop(e.right,c)})`;
      if(e.op==="in"){
        const t=of(e.right,c),l=expr(e.left,c),r=expr(e.right,c);
        return t.kind==="set"?`(FS.mem ${key(t.elem,l)} ${r})`:t.kind==="map"?`(FM.mem ${key(t.key,l)} ${r})`:`(S.contains ${r} ${l})`;
      }
      if(["=","≠"].includes(e.op)){
        if(of(e.left,c).kind==="fn"||of(e.right,c).kind==="fn")fail("function identity equality is not modeled; use pointwise specifications");
        if(e.right.kind==="constructor"&&!e.right.args.length){
          const t=of(e.left,c);const d=t.kind==="user"?data.get(parts(t.name)[0]):undefined;
          const fields=d?.kind==="inductive"?d.constructors.find(x=>x.name===(e.right as any).name)?.fields:undefined;
          if(fields?.length){const test=`(match ${expr(e.left,c)} with | ${ctor(e.right.name,t.kind==="user"?t.name:undefined)} ${fields.map(()=>"_").join(" ")} -> true | _ -> false)`;return e.op==="="?test:`(not ${test})`;}
        }
        if(["array","string"].includes(of(e.left,c).kind)||["array","string"].includes(of(e.right,c).kind)){const eq=app("S.equal",[expr(e.left,c),expr(e.right,c)]);return e.op==="="?eq:`(not ${eq})`;}
        return `(${expr(e.left,c)} ${e.op==="="?"==":"=!="} ${expr(e.right,c)})`;
      }
      if(["<",">","≤","≥"].includes(e.op)){
        const real=of(e.left,c).kind==="real"||of(e.right,c).kind==="real";
        const op=({"≤":"<=","≥":">="} as Record<string,string>)[e.op]??e.op;
        return `(${expr(e.left,c)} ${op}${real?".":""} ${expr(e.right,c)})`;
      }
    }
    return expr(e,c);
  }
  function expr(e:Expr,c:Ctx,expected?:Ty):string {
    switch(e.kind){
      case "var":return e.name==="undefined"?(expected?.kind==="void"?"()":"None"):valueName(e.name,c);
      case "num":
        if(!Number.isFinite(e.value)||Number.isInteger(e.value)&&!Number.isSafeInteger(e.value))fail("number literals must be safe integers; use bigint for larger literals");
        return Number.isSafeInteger(e.value)?`(${e.value})`:`(${e.value}R)`;
      case "bigint":return `(${e.value})`;
      case "bool":return String(e.value);
      case "str":{let s="S.empty";for(let i=0;i<e.value.length;i++)s=app("S.build",[s,String(e.value.charCodeAt(i))]);return s;}
      case "constructor":return e.args.length?app(ctor(e.name,e.type),e.args.map(x=>expr(x,c))):ctor(e.name,e.type);
      case "binop":{
        if(e.op==="=="||e.op==="!=")return app("R.decide",[prop({...e,op:e.op==="=="?"=":"≠"},c)]);
        if(["=","≠","in","↔","==>"].includes(e.op))return app("R.decide",[prop(e,c)]);
        if(["∧","∨"].includes(e.op))return `(${expr(e.left,c)} ${e.op==="∧"?"&&":"||"} ${expr(e.right,c)})`;
        const l=expr(e.left,c),r=expr(e.right,c);
        const op=({"≤":"<=","≥":">="} as Record<string,string>)[e.op]??e.op;
        const real=of(e.left,c).kind==="real"||of(e.right,c).kind==="real";
        if(real&&["<",">","<=",">="].includes(op))return app("R.decide",[prop(e,c)]);
        if(op==="arrayConcat"||op==="++")return app("S.append",[l,r]);
        if(["<<",">>"].includes(op)){
          const k=exactIntegerLiteral(e.right);
          if(k!==null&&k>=0n&&k<=4096n)return `(${l} ${op==="<<"?"*":"/"} ${1n<<k})`;
          return app(op==="<<"?"R.shift_left":"R.shift_right",[l,r]);
        }
        if(op==="&"){
          const m=exactIntegerLiteral(e.right);
          if(m!==null&&m>=0n&&(m&(m+1n))===0n)return `(${l} % ${m+1n})`;
          return app("R.bit_and",[l,r]);
        }
        if(op==="|")return app("R.bit_or",[l,r]);
        return `(${l} ${op}${real&&["+","-","*","/"].includes(op)?".":""} ${r})`;
      }
      case "unop":return `(${["!","¬"].includes(e.op)?"not":e.op} ${expr(e.expr,c)})`;
      case "toNat":return app("R.nat_of_int",[expr(e.expr,c)]);
      case "toReal":return app("FStar.Real.of_int",[expr(e.expr,c)]);
      case "index":{
        const x=app("S.index",[expr(e.arr,c),expr(e.idx,c)]);
        return of(e.arr,c).kind==="string"?app("S.singleton",[x]):x;
      }
      case "tupleLiteral":return `(${e.elems.map(x=>expr(x,c)).join(", ")})`;
      case "tupleProj":return `(let (${Array.from({length:e.arity},(_,i)=>i===e.index?"ls_item":"_").join(", ")}) = ${expr(e.obj,c)} in ls_item)`;
      case "arrayLiteral":return e.elems.reduce((s,x)=>app("S.build",[s,expr(x,c)]),"S.empty");
      case "emptySet":return "FS.emptyset";
      case "emptyMap":return "FM.emptymap";
      case "mapLiteral":return e.entries.reduce((m,en)=>app("FM.insert",[key(of(e,c).kind==="map"?(of(e,c) as Extract<Ty,{kind:"map"}>).key:of(en.key,c),expr(en.key,c)),expr(en.value,c),m]),"FM.emptymap");
      case "field":{
        const t=of(e.obj,c),obj=expr(e.obj,c);
        if(e.field==="toNat")return app("R.nat_of_int",[obj]);
        if(!e.datatypeField&&["size","length","collectionSize"].includes(e.field)){
          if(t.kind==="set")return app("FS.cardinality",[obj]);
          if(t.kind==="map")return app("FM.cardinality",[obj]);
          return app("S.length",[obj]);
        }
        if(!e.datatypeField&&e.field==="keys"&&t.kind==="map")return app("FM.domain",[obj]);
        const parent=e.fromUnion??(t.kind==="user"?parts(t.name)[0]:undefined);
        const d=parent?data.get(parent):undefined;
        if(d?.kind==="structure")return `(${obj}).${field(d.name,e.field)}`;
        if(d?.kind==="inductive"){
          const arms=d.constructors.filter(x=>!e.ctor||x.name===e.ctor).filter(x=>x.fields.some(f=>f.name===e.field));
          return `(match ${obj} with ${arms.map(x=>`| ${ctor(x.name,d.name)} ${x.fields.map(f=>f.name===e.field?"ls_field":"_").join(" ")} -> ls_field`).join(" ")})`;
        }
        if(t.kind==="optional"&&e.field==="value")return `(match ${obj} with | Some ls_value -> ls_value)`;
        return fail(`unsupported field ${e.field} of ${JSON.stringify(t)}`);
      }
      case "record":{
        const t=e.ty?.kind!=="unknown" && e.ty?of(e,c):e.spread?of(e.spread,c):of(e,c);const parent=e.ctorOf??(expected?.kind==="user"?parts(expected.name)[0]:undefined)??(t.kind==="user"?parts(t.name)[0]:undefined)??[...data.values()].find(d=>d.kind==="structure"&&d.fields.length===e.fields.length&&d.fields.every(f=>e.fields.some(x=>x.name===f.name)))?.name;
        const d=parent?data.get(parent):undefined;
        if(d?.kind==="structure"){
          const fields=e.fields.map(f=>`${field(d.name,f.name)} = ${expr(f.value,c,d.fields.find(x=>x.name===f.name)?.type)}`);
          if(!e.spread)for(const f of d.fields)if(!e.fields.some(x=>x.name===f.name)){
            if(expand(f.type).kind!=="optional")fail(`record ${d.name} is missing required field ${f.name}`);
            fields.push(`${field(d.name,f.name)} = None`);
          }
          return `{ ${e.spread?expr(e.spread,c)+" with ":""}${fields.join("; ")} }`;
        }
        const updateCtor=e.ctor??(d?.kind==="inductive"?d.constructors.find(x=>e.fields.every(f=>x.fields.some(cf=>cf.name===f.name)))?.name:undefined);
        if(d?.kind==="inductive"&&updateCtor){
          const cn=d.constructors.find(x=>x.name===updateCtor)!;
          return app(ctor(updateCtor,parent),cn.fields.map(f=>{const v=e.fields.find(x=>x.name===f.name);return v?expr(v.value,c):e.spread?expr({kind:"field",obj:e.spread,field:f.name,fromUnion:parent,ctor:updateCtor},c):fail(`missing ${f.name}`);}));
        }
        return fail(`record has no resolved type: ${JSON.stringify(t)}`);
      }
      case "app":{
        if(e.fn==="__fstarApply")return app(expr(e.args[0],c),e.args.slice(1).map(x=>expr(x,c)));
        if(e.ctorOf)return app(ctor(e.fn,e.ctorOf),e.args.map(x=>expr(x,c)));
        if(!funcs.has(e.fn)&&!c.vars.has(e.fn)&&[...data.values()].some(d=>d.kind==="inductive"&&d.constructors.some(x=>x.name===e.fn)))return app(ctor(e.fn,expected?.kind==="user"?expected.name:undefined),e.args.map(x=>expr(x,c)));
        const helpers:Record<string,string>={JSFloorDiv:"R.floor_div",JSTruncDiv:"R.trunc_div",JSRem:"R.rem",MathAbs:"R.abs",MathMin:"R.min",MathMax:"R.max",FloorReal:"R.floor",CeilReal:"R.ceil",JSStringLt:"R.string_lt",StringFromCharCode:"R.from_char_code",IntToString:"R.int_to_string",NatToString:"R.nat_to_string",Perm:"R.perm",SetFromSeq:"R.set_from_seq",SetToSeq:"R.set_to_seq",MaxOfSeq:"R.maximum",MinOfSeq:"R.minimum"};
        if(["Number","BigInt"].includes(e.fn))return expr(e.args[0],c);
        if(e.fn==="SetLiteral")return e.args.reduce((s,x)=>app("FS.insert",[key(of(x,c),expr(x,c)),s]),"FS.emptyset");
        if(e.fn==="SetToSeq"){
          const st=of(e.args[0],c);const seq=app("R.set_to_seq",[expr(e.args[0],c)]);
          return st.kind==="set"&&expand(st.elem).kind==="string"?app("R.map",["R.of_list",seq]):seq;
        }
        if(e.fn==="SetFromSeq"){
          const st=of(e.args[0],c);const seq=expr(e.args[0],c);
          return app("R.set_from_seq",[st.kind==="array"&&expand(st.elem).kind==="string"?app("R.map",["R.to_list",seq]):seq]);
        }
        return app(helpers[e.fn]??valueName(e.fn,c),[...(effectful.has(e.fn)?[`(${fresh++} :: ${c.trace??fail("impure call requires an invocation trace")})`]:[]),...e.args.map(x=>expr(x,c))]);
      }
      case "methodCall":return method(e,c);
      case "lambda":{
        if(anyExprInStmts(e.body,x=>x.kind==="havoc"||x.kind==="app"&&effectful.has(x.fn)))fail("effectful callbacks are not supported; havoc and impure calls require invocation state");
        let lc:Ctx={...c,result:of(e,c).kind==="fn"?(of(e,c) as Extract<Ty,{kind:"fn"}>).result:undefined,post:"True",onReturn:undefined,onBreak:undefined,onContinue:undefined};
        for(const p of e.params)lc=bind(lc,p.name,p.type);
        return `(fun ${e.params.map(p=>`(${n(p.name)}:${type(p.type)})`).join(" ")||"()"} ->\n${ind(block(e.body,lc,()=>"()"))})`;
      }
      case "if":return `(if ${expr(e.cond,c)} then ${expr(e.then,c,expected)} else ${expr(e.else,c,expected)})`;
      case "match":{
        const t=of(e.scrutinee,c);
        if(e.arms.some(a=>a.pattern.kind==="literal")){
          let s="(assert False; FStar.Pervasives.false_elim ())";
          for(const a of [...e.arms].reverse())s=a.pattern.kind==="wild"?expr(a.body,c):a.pattern.kind==="literal"?`(if R.eq ${expr(e.scrutinee,c)} ${expr({kind:"str",value:a.pattern.value},c)} then ${expr(a.body,c)} else ${s})`:fail("mixed match");
          return s;
        }
        return `(match ${expr(e.scrutinee,c)} with\n${e.arms.map(a=>{const [p,cc]=pattern(a.pattern,t,c);return `| ${p} -> ${expr(a.body,cc)}`;}).join("\n")})`;
      }
      case "forall":case "exists":case "implies":return app("R.decide",[prop(e,c)]);
      case "let":{const cc=bind(c,e.name,of(e.value,c),`${n(e.name)}_${fresh}`);return `(let ${cc.vars.get(e.name)!.text} = ${expr(e.value,c)} in\n${expr(e.body,cc)})`;}
      case "havoc":{
        const id=`ls_havoc_${fresh++}`;const t=e.type.kind==="unknown"?(expected??e.type):e.type;
        trust.push(`// Trusted source annotation: havoc. Each invocation has its own trace.\nassume val ${id} : list int -> GTot ${type(t)}\n`);
        return app(id,[c.trace??fail("havoc requires an invocation trace")]);
      }
      case "default":return fail("unexpected synthetic default in F* lowering");
    }
  }
  function method(e:Extract<Expr,{kind:"methodCall"}>,c:Ctx):string {
    const t=expand(e.objTy),obj=expr(e.obj,c),m=e.method;
    if(t.kind==="array"&&["map","filter","every","some","reduce","find","findIndex","flatMap","filterMap"].includes(m)){
      const argc=m==="reduce"?2:1,arity=m==="reduce"?2:1;
      if(e.args.length!==argc)fail(`.${m} expects ${argc} arguments; thisArg and omitted reduce initial values are not supported`);
      const callback=of(e.args[0],c);
      if(callback.kind!=="fn"||callback.params.length!==arity)fail(`.${m} requires a ${arity}-parameter callback; index/array callback arguments are not supported`);
    }
    const a=e.args.map((x,i)=>expr(x,c,t.kind==="map"&&m==="set"?(i===0?t.key:t.value):t.kind==="array"&&m==="push"?t.elem:undefined));
    if(t.kind==="string"){
      if(m==="indexOf")return app("R.string_index_of",[obj,a[0]]);
      if(m==="includes")return `(${app("R.string_index_of",[obj,a[0]])} >= 0)`;
      if(["trim","trimStart","trimEnd"].includes(m))return app(`R.${m}`,[obj]);
      if(m==="toLowerCase"||m==="toUpperCase"){
        const id=`ls_string_${m}`;
        const definition=`// Deterministic library abstraction: Unicode ${m}; no result properties assumed.\nassume val ${id} : R.string -> GTot R.string\n`;
        if(!trust.includes(definition))trust.push(definition);
        return app(id,[obj]);
      }
    }
    if(t.kind==="array"||t.kind==="string"){
      switch(m){
        case "map":case "filter":case "every":case "some":return app(`R.${m}`,[...a,obj]);
        case "reduce":return app("R.fold",[...a,obj]);
        case "slice":return app("R.slice",[obj,a[0]??"0",a[1]??app("S.length",[obj])]);
        case "push":return app("S.build",[obj,...a]);
        case "unshift":return app("S.append",[app("S.singleton",a),obj]);
        case "set":case "with":return app("S.update",[obj,...a]);
        case "includes":return a.length===1?app("R.contains",[obj,a[0]]):app("R.contains",[app("R.slice",[obj,a[1],app("S.length",[obj])]),a[0]]);
        case "indexOf":return app("R.index_of",[obj,a[0],a[1]??"0"]);
        case "find":case "findIndex":case "findLast":case "findLastIndex":return app(`R.${m}`,[...a,obj]);
        case "flat":case "flatten":return app("R.flatten",[obj]);
        case "flatMap":return app("R.flatten",[app("R.map",[...a,obj])]);
        case "filterSome":return app("R.filter_some",[obj]);
        case "filterMap":return app("R.filter_some",[app("R.map",[...a,obj])]);
        case "charCodeAt":return app("S.index",[obj,a[0]??"0"]);
        case "at":return app("R.at",[obj,...a]);
        case "concat":return app("S.append",[obj,...a]);
        case "sort":case "toSorted":return app("R.sort",[a[0]??"(fun x y -> x - y)",obj]);
        case "reverse":case "toReversed":return app("R.reverse",[obj]);
        case "join":return app("R.join",[obj,...a]);
        case "startsWith":case "endsWith":return app(`R.${m}`,[obj,...a]);
      }
    }
    if(t.kind==="map"){
      if(a.length)a[0]=key(t.key,a[0]);
      if(m==="get")return app("FM.elements",[obj,...a]);
      if(m==="getDirect")return app("FM.lookup",[...a,obj]);
      if(m==="has")return app("FM.mem",[...a,obj]);
      if(m==="set")return app("FM.insert",[...a,obj]);
      if(m==="delete"||m==="erase")return app("FM.remove",[...a,obj]);
      if(m==="merge")return app("FM.merge",[a[0],obj]);
      if(m==="keys")return app("R.set_to_seq",[app("FM.domain",[obj])]);
      if(m==="entries"||m==="toArray")return app("R.map_to_seq",[obj]);
      if(m==="values")return app("R.map_values",[obj]);
    }
    if(t.kind==="set"){
      if(a.length)a[0]=key(t.elem,a[0]);
      if(m==="has")return app("FS.mem",[...a,obj]);
      if(m==="add"||m==="insert")return app("FS.insert",[...a,obj]);
      if(m==="delete"||m==="erase")return app("FS.remove",[...a,obj]);
      if(m==="toArray")return app("R.set_to_seq",[obj]);
    }
    if(t.kind==="user")return app(expr({kind:"field",obj:e.obj,field:m,datatypeField:true},c),a);
    return fail(`unsupported ${t.kind} method '${m}'`);
  }
  function block(ss:Stmt[],c:Ctx,k:Cont):string {
    if(!ss.length)return k(c);
    const [s,...rest]=ss;const next=(cc:Ctx)=>block(rest,cc,k);
    switch(s.kind){
      case "let":case "ghostLet":case "let-bind":{
        let ty=s.kind==="let-bind"?of(s.value,c):s.type;
        if(ty.kind==="nat")ty={kind:"int",big:ty.big};
        const inferred=of(s.value,c);
        if(inferred.kind!=="unknown"&&(s.value.kind==="app"||ty.kind==="unknown"))ty=inferred;
        const cc=bind(c,s.name,ty,`${n(s.name)}_${fresh}`);
        cc.vars.get(s.name)!.nonneg = s.value.kind==="num"&&s.value.value>=0;
        return `let ${cc.vars.get(s.name)!.text}${ty.kind==="unknown"?"":` : ${type(ty)}`} = ${expr(s.value,c,ty)} in\n${next(cc)}`;
      }
      case "assign":case "bind":case "ghostAssign":{
        if(s.target==="_")return `let _ = ${expr(s.value,c)} in\n${next(c)}`;
        const old=c.vars.get(s.target);if(!old)return fail(`assignment to unbound ${s.target}`);
        const text=`${n(s.target)}_${fresh++}`;
        const cc={...c,vars:new Map([...c.vars,[s.target,{...old,text}]])};
        return `let ${text} : ${type(old.ty)} = ${expr(s.value,c,old.ty)} in\n${next(cc)}`;
      }
      case "return":{const v=expr(s.value,c,c.result);return c.onReturn?c.onReturn(v,c):v;}
      case "assert":return `${s.assumed?"assume":"assert"} (${prop(s.expr,c)});\n${next(c)}`;
      case "break":return c.onBreak?c.onBreak(c):fail("break outside loop");
      case "continue":return c.onContinue?c.onContinue(c):fail("continue outside loop");
      case "if":{
        const scoped=(cc:Ctx)=>next({...c,vars:new Map([...c.vars].map(([key,b])=>[key,cc.vars.get(key)?.id===b.id?cc.vars.get(key)!:b]))});
        return `if ${expr(s.cond,c)} then (\n${ind(block(s.then,c,scoped))}\n) else (\n${ind(block(s.else,c,scoped))}\n)`;
      }
      case "match":{
        const scoped=(cc:Ctx)=>next({...c,vars:new Map([...c.vars].map(([key,b])=>[key,cc.vars.get(key)?.id===b.id?cc.vars.get(key)!:b]))});
        if(s.arms.some(a=>a.pattern.kind==="literal")){
          let tail="assert False; FStar.Pervasives.false_elim ()";
          for(const a of [...s.arms].reverse())tail=a.pattern.kind==="wild"?block(a.body,c,scoped):a.pattern.kind==="literal"?`if R.eq ${expr(s.scrutinee,c)} ${expr({kind:"str",value:a.pattern.value},c)} then (${block(a.body,c,scoped)}) else (${tail})`:fail("mixed match");
          return tail;
        }
        return `match ${expr(s.scrutinee,c)} with\n${s.arms.map(a=>{const [p,cc]=pattern(a.pattern,of(s.scrutinee,c),c);return `| ${p} -> (\n${ind(block(a.body,cc,scoped))}\n)`;}).join("\n")}`;
      }
      case "forin":{
        const idx:Expr={kind:"var",name:s.idx,ty:{kind:"nat"}};
        const bump:Stmt={kind:"assign",target:s.idx,value:{kind:"binop",op:"+",left:idx,right:{kind:"num",value:1}}};
        return block([{kind:"let",name:s.idx,type:{kind:"nat"},mutable:true,value:{kind:"num",value:0}},
          {kind:"while",cond:{kind:"binop",op:"<",left:idx,right:s.bound},invariants:[{kind:"binop",op:"≤",left:idx,right:s.bound},...s.invariants],decreasing:{kind:"binop",op:"-",left:s.bound,right:idx},doneWith:null,body:[...s.body,bump]},...rest],c,k);
      }
      case "while":{
        const assigned=new Set<string>();
        const walk=(xs:Stmt[])=>{for(const x of xs){if(["assign","bind","ghostAssign"].includes(x.kind))assigned.add((x as any).target);if(x.kind==="if"){walk(x.then);walk(x.else);}if(x.kind==="match")x.arms.forEach(a=>walk(a.body));if(x.kind==="while"||x.kind==="forin")walk(x.body);}};
        walk(s.body);
        const params=[...c.vars].filter(([id])=>assigned.has(id));
        const loopId=fresh++;const loop=`ls_loop_${loopId}`;
        const step=`ls_step_${fresh++}`;
        let lc={...c,trace:c.trace?`(${loopId} :: ${step} :: ${c.trace})`:undefined};
        for(const [id,b] of params)lc={...lc,vars:new Map([...lc.vars,[id,{...b,text:`${n(id)}_${fresh++}`} ]])};
        const again=(cc:Ctx,initial=false)=>app(loop,[...(c.trace?[initial?"0":`(${step}+1)`]:[]),...params.map(([id])=>cc.vars.get(id)!.text)]);
        const exit=(cc:Ctx)=>next({...c,vars:new Map([...c.vars].map(([id,b])=>[id,cc.vars.get(id)?.id===b.id?cc.vars.get(id)!:b]))});
        const monotone=new Set<string>(params.map(([id])=>id));
        const scan=(ss:Stmt[])=>{for(const x of ss){
          if(x.kind==="assign"||x.kind==="bind"||x.kind==="ghostAssign"){
            const v=x.value;
            if(!(v.kind==="binop"&&v.op==="+"&&v.left.kind==="var"&&v.left.name===x.target&&v.right.kind==="num"&&v.right.value>=0))monotone.delete(x.target);
          }
          if(x.kind==="if"){scan(x.then);scan(x.else);}if(x.kind==="match")x.arms.forEach(a=>scan(a.body));if(x.kind==="while"||x.kind==="forin")scan(x.body);
        }};scan(s.body);
        const auto=params.filter(([id,b])=>b.nonneg&&monotone.has(id)).map(([id])=>`0 <= ${lc.vars.get(id)!.text}`);
        const inv=[...auto,...s.invariants.map(x=>prop(x,lc))].join(" /\\ ")||"True";
        let measure=s.decreasing;
        if(!measure&&s.cond.kind==="binop"&&params.some(([id])=>monotone.has(id))){
          const g=s.cond;
          if(["<","≤"].includes(g.op))measure={kind:"binop",op:"-",left:g.right,right:g.left};
          if([">","≥"].includes(g.op))measure={kind:"binop",op:"-",left:g.left,right:g.right};
        }
        const ordinal=loopNumbers.get(c.fnName??"")??0;loopNumbers.set(c.fnName??"",ordinal+1);
        if(!measure)measure={kind:"app",fn:`${c.fnName}_loop${ordinal}_measure`,args:params.map(([id,b])=>({kind:"var",name:id,ty:b.ty}))};
        const body=block(s.body,{...lc,onBreak:exit,onContinue:again},again);
        return `let rec ${loop} ${c.trace?`(${step}:nat) `:""}${params.map(([id,b])=>`(${lc.vars.get(id)!.text}:${type(b.ty)})`).join(" ")||"()"}\n  : Ghost ${type(c.result??{kind:"void"})}\n      (requires (\n        ${inv}\n      ))\n      (ensures (fun ls_result ->\n        ${c.post??"True"}\n      ))\n      (decreases (R.nat_of_int ${expr(measure,lc)})) =\n${ind(`if ${expr(s.cond,lc)} then (\n${ind(body)}\n) else (\n${ind(exit(lc))}\n)`)}\nin\n${again(c,true)}`;
      }
    }
  }
  function hasEq(t:Ty,seen=new Set<string>()):boolean {
    t=expand(t);if(["int","nat","bool","void"].includes(t.kind))return true;
    if(t.kind==="optional")return hasEq(t.inner,seen);
    if(t.kind==="tuple")return t.elems.every(x=>hasEq(x,seen));
    if(t.kind==="user"){
      if(seen.has(t.name))return true;
      const d=data.get(t.name);if(!d)return false;seen=new Set([...seen,t.name]);
      return (d.kind==="structure"?d.fields:d.constructors.flatMap(x=>x.fields)).every(f=>hasEq(f.type,seen));
    }
    return false;
  }
  const typeTexts:string[]=[];
  for(const d of decls){
    if(d.kind==="structure")typeTexts.push(`${hasEq({kind:"user",name:d.name})?"":"noeq "}type ${n(d.name)} ${(d.typeParams??[]).map(p=>`(${n(p)}:Type)`).join(" ")} = {\n${d.fields.map(f=>`  ${field(d.name,f.name)}: ${type(f.type)};`).join("\n")}\n}\n`);
    if(d.kind==="inductive")typeTexts.push(`${hasEq({kind:"user",name:d.name})?"":"noeq "}type ${n(d.name)} ${(d.typeParams??[]).map(p=>`(${n(p)}:Type)`).join(" ")} =\n${d.constructors.map(x=>`| ${ctor(x.name,d.name)} : ${x.fields.map(f=>type(f.type)+" -> ").join("")}${n(d.name)} ${(d.typeParams??[]).map(n).join(" ")}`).join("\n")}\n`);
    if(d.kind==="type-alias"){
      const ps=mod.typeDecls.find(x=>x.name===d.name)?.typeParams??[];
      typeTexts.push(`type ${n(d.name)} ${ps.map(p=>`(${n(p)}:Type)`).join(" ")} = ${type(d.target)}\n`);
    }
    if(d.kind==="opaque-type")typeTexts.push(`// Abstract source type; no constructors or operations are exposed.\nassume val ${n(d.name)} : eqtype\n`);
    if(d.kind==="class")fail(`class '${d.name}' requires state-passing lowering`);
  }
  const rendered=new Map<string,{text:string;deps:Set<string>}>();
  for(const d of constants.values()){
    const c=root();rendered.set(d.name,{text:`let ${n(d.name)} : ${type(d.type)} = ${expr(d.value,c)}\n`,deps:c.deps});
  }
  for(const f of funcs.values()){
    if(f.typeParams.some(p=>aliases.has(p)))fail(`${f.name}: generic parameters shadowing type aliases are not supported`);
    let c=root();for(const p of f.params)c=bind(c,p.name,p.type);
    c.result=f.returnType;c.fnName=f.name; if(effectful.has(f.name))c.trace="ls_trace";
    const pre=f.requires.map(e=>prop(e,c)).join(" /\\ ")||"True";
    c.post=f.ensures.map(e=>prop(e,bind(c,"\\result",f.returnType,"ls_result"))).join(" /\\ ")||"True";
    const body=f.kind==="extern"?"":f.kind==="def"?expr(f.body,c,f.returnType):block(f.kind==="def-by-method"?f.methodBody:f.body,c,()=>"()");
    const recursive=c.deps.has(f.name);
    const sized=f.params.find(p=>["array","string"].includes(expand(p.type).kind));
    if(f.kind!=="extern" && recursive && !f.decreases && sized)f.decreases={kind:"field",field:"size",obj:{kind:"var",name:sized.name,ty:sized.type}};
    const ps=[...(effectful.has(f.name)?["(ls_trace:list int)"]:[]),...f.params.map(p=>`(${n(p.name)}:${type(p.type)})`)].join(" ")||"()";
    const ts=f.typeParams.map(p=>`(#${n(p.replace(/\(==\)$/, ""))}:${p.endsWith("(==)")?"eqtype":"Type"})`).join(" ");
    if(f.kind==="extern"){
      const binders=[...f.typeParams.map(p=>`#${n(p)}:Type`),...(f.impure?["ls_trace:list int"]:[]),...f.params.map(p=>`${n(p.name)}:${type(p.type)}`)];
      const sig=[...binders.map(b=>`(${b})`),...(f.params.length||f.impure?[]:["unit"]),`Ghost ${type(f.returnType)} (requires (${pre})) (ensures (fun ls_result -> ${c.post}))`].join(" -> ");
      rendered.set(f.name,{text:`// Trusted source declaration: ${f.impure?"impure ":""}extern.\nassume val ${n(f.name)} : ${sig}\n`,deps:c.deps});continue;
    }
    rendered.set(f.name,{text:`let ${recursive?"rec ":""}${n(f.name)} ${ts} ${ps}\n  : Ghost ${type(f.returnType)}\n      (requires (\n        ${pre}\n      ))\n      (ensures (fun ls_result ->\n        ${c.post}\n      ))${f.decreases?`\n      (decreases ${expr(f.decreases,c)})`:""} =\n${ind(body)}\n`,deps:c.deps});
  }
  const ordered:string[]=[],done=new Set<string>(),active=new Set<string>();
  const visit=(id:string)=>{if(done.has(id))return;if(active.has(id))fail(`mutual recursion involving '${id}' is not supported`);active.add(id);const d=rendered.get(id)!;for(const dep of d.deps)if(dep!==id&&rendered.has(dep))visit(dep);active.delete(id);done.add(id);ordered.push(d.text);};
  rendered.forEach((_,id)=>visit(id));
  return `// Generated by lsc. Program source: ${mod.file.split(/[\\/]/).pop()!.replace(/[\r\n]/g," ")}\n// Add proofs in the .fst; regenerate with lsc regen --backend=fstar.\nmodule ${moduleName}\n\nmodule R = LS.Runtime\nmodule S = FStar.Sequence\nmodule FS = FStar.FiniteSet.Base\nmodule FM = FStar.FiniteMap.Base\nopen FStar.FiniteSet.Ambient\nopen FStar.FiniteMap.Ambient\nopen FStar.Real\n\n${[...(needsUnknown?["// Uninspected unknown/any values.\nassume val ls_unknown : eqtype\n"]:[]),...typeTexts,...trust,...ordered].join("\n")}`.replace(/[ \t]+\n/g, "\n");
}
