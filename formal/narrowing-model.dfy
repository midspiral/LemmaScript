// Narrowing, Place/Lens Mutation, and Live-Alias Core Calculus
//
// Standalone native Dafny P2 formalization for midspiral/LemmaScript#387
// (tracked in robertpenner/LemmaScript#45). Never compiled to JS; verifies
// directly with `dafny verify formal/narrowing-model.dfy`.
//
// Proves four theorems over a minimal imperative TypeScript semantics with a
// mutable heap (CoreTS) lowered to LemmaScript's functional value-store
// semantics (CoreVal) parameterized by an arbitrary uninterpreted flow-hint
// oracle `Hint`:
//   1. Checked-read soundness under arbitrary `Hint` given `NoLiveAliasMutation`.
//   2. Precondition and evaluation preservation (`GuardCall(false)`).
//   3. Place lens laws (read-after-write, disjoint frame, wrapper preservation).
//   4. Representation injectivity across T, T | undefined, T | null, and
//      T | null | undefined.

module NarrowingModel {

  type Var = string
  type Field = string
  type Tag = string
  type Addr = nat

  datatype Option<T> = None | Some(value: T)
  datatype Nullish<T> = NUndefined | NNull | NValue(value: T)

  // =========================================================================
  // 1. Semantic Values and Storage Representation Injectivity (Theorem 4)
  // =========================================================================

  // Deep observable JavaScript value (image of an acyclic heap object or primitive).
  datatype Val =
    | VInt(n: int)
    | VBool(b: bool)
    | VUndefined
    | VNull
    | VArr(elems: seq<Val>)
    | VRec(fields: map<Field, Val>)
    | VMap(entries: map<int, Val>)
    | VUnion(tag: Tag, payload: Val)

  datatype StorageRep =
    | RepPlain      // T (neither null nor undefined)
    | RepOptUndef   // T | undefined -> Option<T>
    | RepOptNull    // T | null      -> Option<T>
    | RepNullish    // T | null | undefined -> Nullish<T>

  // Pure functional values stored in CoreVal's environment (no heap).
  datatype FVal =
    | FInt(n: int)
    | FBool(b: bool)
    | FUndefined
    | FNull
    | FOptUndef(optU: Option<FVal>)
    | FOptNull(optN: Option<FVal>)
    | FNullish(nul: Nullish<FVal>)
    | FArr(elems: seq<FVal>)
    | FRec(fields: map<Field, FVal>)
    | FMap(entries: map<int, FVal>)
    | FUnion(tag: Tag, payload: FVal)

  predicate IsNonNullishVal(v: Val) {
    !v.VUndefined? && !v.VNull?
  }

  predicate ValidForRep(rep: StorageRep, v: Val) {
    match rep
    case RepPlain => IsNonNullishVal(v)
    case RepOptUndef => IsNonNullishVal(v) || v.VUndefined?
    case RepOptNull => IsNonNullishVal(v) || v.VNull?
    case RepNullish => true
  }

  function EncodePlain(v: Val): FVal
    requires IsNonNullishVal(v)
    decreases v, 0
  {
    match v {
      case VInt(n) => FInt(n)
      case VBool(b) => FBool(b)
      case VArr(elems) => FArr(seq(|elems|, i requires 0 <= i < |elems| => EncodeAny(elems[i])))
      case VRec(fields) => FRec(map k | k in fields :: EncodeAny(fields[k]))
      case VMap(entries) => FMap(map k | k in entries :: EncodeAny(entries[k]))
      case VUnion(tag, payload) => FUnion(tag, EncodeAny(payload))
    }
  }

  function EncodeAny(v: Val): FVal
    decreases v, 1
  {
    if v.VUndefined? then FUndefined
    else if v.VNull? then FNull
    else EncodePlain(v)
  }

  function EncodeVal(rep: StorageRep, v: Val): FVal
    requires ValidForRep(rep, v)
  {
    match rep {
      case RepPlain => EncodePlain(v)
      case RepOptUndef =>
        if v.VUndefined? then FOptUndef(None)
        else FOptUndef(Some(EncodePlain(v)))
      case RepOptNull =>
        if v.VNull? then FOptNull(None)
        else FOptNull(Some(EncodePlain(v)))
      case RepNullish =>
        if v.VUndefined? then FNullish(NUndefined)
        else if v.VNull? then FNullish(NNull)
        else FNullish(NValue(EncodePlain(v)))
    }
  }

  // Erase storage wrappers back to the observable JS value.
  function EraseFVal(fv: FVal): Val
    decreases fv
  {
    match fv {
      case FInt(n) => VInt(n)
      case FBool(b) => VBool(b)
      case FUndefined => VUndefined
      case FNull => VNull
      case FOptUndef(None) => VUndefined
      case FOptUndef(Some(inner)) => EraseFVal(inner)
      case FOptNull(None) => VNull
      case FOptNull(Some(inner)) => EraseFVal(inner)
      case FNullish(NUndefined) => VUndefined
      case FNullish(NNull) => VNull
      case FNullish(NValue(inner)) => EraseFVal(inner)
      case FArr(elems) => VArr(seq(|elems|, i requires 0 <= i < |elems| => EraseFVal(elems[i])))
      case FRec(fields) => VRec(map k | k in fields :: EraseFVal(fields[k]))
      case FMap(entries) => VMap(map k | k in entries :: EraseFVal(entries[k]))
      case FUnion(tag, payload) => VUnion(tag, EraseFVal(payload))
    }
  }

  lemma Lemma_EraseEncodePlain(v: Val)
    requires IsNonNullishVal(v)
    ensures EraseFVal(EncodePlain(v)) == v
    decreases v, 0
  {
    match v {
      case VInt(_) =>
      case VBool(_) =>
      case VArr(elems) =>
        forall i | 0 <= i < |elems|
          ensures EraseFVal(EncodeAny(elems[i])) == elems[i]
        {
          Lemma_EraseEncodeAny(elems[i]);
        }
      case VRec(fields) =>
        forall k | k in fields
          ensures EraseFVal(EncodeAny(fields[k])) == fields[k]
        {
          Lemma_EraseEncodeAny(fields[k]);
        }
      case VMap(entries) =>
        forall k | k in entries
          ensures EraseFVal(EncodeAny(entries[k])) == entries[k]
        {
          Lemma_EraseEncodeAny(entries[k]);
        }
      case VUnion(_, payload) =>
        Lemma_EraseEncodeAny(payload);
    }
  }

  lemma Lemma_EraseEncodeAny(v: Val)
    ensures EraseFVal(EncodeAny(v)) == v
    decreases v, 1
  {
    if !v.VUndefined? && !v.VNull? {
      Lemma_EraseEncodePlain(v);
    }
  }

  // Theorem 4a: Round-trip decode(encode(rep, v)) == v.
  lemma Theorem4_EncodeEraseRoundtrip(rep: StorageRep, v: Val)
    requires ValidForRep(rep, v)
    ensures EraseFVal(EncodeVal(rep, v)) == v
  {
    if IsNonNullishVal(v) {
      Lemma_EraseEncodePlain(v);
    }
  }

  // Theorem 4b: Representation injectivity — distinct JS values never collide.
  lemma Theorem4_RepresentationInjectivity(rep: StorageRep, v1: Val, v2: Val)
    requires ValidForRep(rep, v1)
    requires ValidForRep(rep, v2)
    requires EncodeVal(rep, v1) == EncodeVal(rep, v2)
    ensures v1 == v2
  {
    Theorem4_EncodeEraseRoundtrip(rep, v1);
    Theorem4_EncodeEraseRoundtrip(rep, v2);
  }

  // Theorem 4c: Null vs undefined and falsy primitives stay distinct in RepNullish.
  lemma Theorem4_NullUndefinedAndFalsyDistinct()
    ensures EncodeVal(RepNullish, VNull) != EncodeVal(RepNullish, VUndefined)
    ensures EncodeVal(RepNullish, VInt(0)) != EncodeVal(RepNullish, VUndefined)
    ensures EncodeVal(RepNullish, VInt(0)) != EncodeVal(RepNullish, VNull)
    ensures EncodeVal(RepNullish, VBool(false)) != EncodeVal(RepNullish, VUndefined)
    ensures EncodeVal(RepNullish, VArr([])) != EncodeVal(RepNullish, VUndefined)
  {}

  // Explicit pairwise widening coercions across T, T | undefined, T | null, T | null | undefined.
  function WidenPlainToOptUndef(fv: FVal): FVal { FOptUndef(Some(fv)) }
  function WidenPlainToOptNull(fv: FVal): FVal { FOptNull(Some(fv)) }
  function WidenOptUndefToNullish(o: Option<FVal>): Nullish<FVal> {
    match o
    case None => NUndefined
    case Some(v) => NValue(v)
  }
  function WidenOptNullToNullish(o: Option<FVal>): Nullish<FVal> {
    match o
    case None => NNull
    case Some(v) => NValue(v)
  }

  // Theorem 4d: Every pairwise widening coercion is injective and preserves observable erasure.
  lemma Theorem4_CoercionsInjective(a: FVal, b: FVal, o1: Option<FVal>, o2: Option<FVal>)
    ensures WidenPlainToOptUndef(a) == WidenPlainToOptUndef(b) ==> a == b
    ensures WidenPlainToOptNull(a) == WidenPlainToOptNull(b) ==> a == b
    ensures WidenOptUndefToNullish(o1) == WidenOptUndefToNullish(o2) ==> o1 == o2
    ensures WidenOptNullToNullish(o1) == WidenOptNullToNullish(o2) ==> o1 == o2
    ensures EraseFVal(WidenPlainToOptUndef(a)) == EraseFVal(a)
    ensures EraseFVal(WidenPlainToOptNull(a)) == EraseFVal(a)
    ensures EraseFVal(FNullish(WidenOptUndefToNullish(o1))) == EraseFVal(FOptUndef(o1))
    ensures EraseFVal(FNullish(WidenOptNullToNullish(o1))) == EraseFVal(FOptNull(o1))
  {}

  // =========================================================================
  // 2. Places and Lenses on Functional Value Stores (Theorem 3)
  // =========================================================================

  type FEnv = map<Var, FVal>

  datatype Place =
    | PVar(x: Var)
    | PField(base: Place, f: Field)
    | PIndex(base: Place, idx: int)
    | PMapKey(base: Place, key: int)
    | PUnwrap(base: Place)
    | PVariant(base: Place, tag: Tag)

  function PlaceRoot(p: Place): Var {
    match p
    case PVar(x) => x
    case PField(b, _) => PlaceRoot(b)
    case PIndex(b, _) => PlaceRoot(b)
    case PMapKey(b, _) => PlaceRoot(b)
    case PUnwrap(b) => PlaceRoot(b)
    case PVariant(b, _) => PlaceRoot(b)
  }

  function ReadPlace(p: Place, env: FEnv): Option<FVal>
    decreases p
  {
    match p {
      case PVar(x) =>
        if x in env then Some(env[x]) else None
      case PField(b, f) =>
        (match ReadPlace(b, env) {
          case Some(FRec(fields)) => if f in fields then Some(fields[f]) else None
          case _ => None
        })
      case PIndex(b, i) =>
        (match ReadPlace(b, env) {
          case Some(FArr(elems)) => if 0 <= i < |elems| then Some(elems[i]) else None
          case _ => None
        })
      case PMapKey(b, k) =>
        (match ReadPlace(b, env) {
          case Some(FMap(entries)) => if k in entries then Some(entries[k]) else None
          case _ => None
        })
      case PUnwrap(b) =>
        (match ReadPlace(b, env) {
          case Some(FOptUndef(Some(v))) => Some(v)
          case Some(FOptNull(Some(v))) => Some(v)
          case Some(FNullish(NValue(v))) => Some(v)
          case _ => None
        })
      case PVariant(b, tag) =>
        (match ReadPlace(b, env) {
          case Some(FUnion(t, payload)) => if t == tag then Some(payload) else None
          case _ => None
        })
    }
  }

  predicate PlaceValid(p: Place, env: FEnv) {
    ReadPlace(p, env).Some?
  }

  function WritePlace(p: Place, env: FEnv, v': FVal): Option<FEnv>
    decreases p
  {
    match p {
      case PVar(x) =>
        if x in env then Some(env[x := v']) else None
      case PField(b, f) =>
        (match ReadPlace(b, env) {
          case Some(FRec(fields)) =>
            if f in fields then WritePlace(b, env, FRec(fields[f := v'])) else None
          case _ => None
        })
      case PIndex(b, i) =>
        (match ReadPlace(b, env) {
          case Some(FArr(elems)) =>
            if 0 <= i < |elems| then WritePlace(b, env, FArr(elems[i := v'])) else None
          case _ => None
        })
      case PMapKey(b, k) =>
        (match ReadPlace(b, env) {
          case Some(FMap(entries)) =>
            if k in entries then WritePlace(b, env, FMap(entries[k := v'])) else None
          case _ => None
        })
      case PUnwrap(b) =>
        (match ReadPlace(b, env) {
          case Some(FOptUndef(Some(_))) => WritePlace(b, env, FOptUndef(Some(v')))
          case Some(FOptNull(Some(_))) => WritePlace(b, env, FOptNull(Some(v')))
          case Some(FNullish(NValue(_))) => WritePlace(b, env, FNullish(NValue(v')))
          case _ => None
        })
      case PVariant(b, tag) =>
        (match ReadPlace(b, env) {
          case Some(FUnion(t, _)) =>
            if t == tag then WritePlace(b, env, FUnion(tag, v')) else None
          case _ => None
        })
    }
  }

  // Path representation of a Place for structural disjointness.
  datatype Step =
    | SField(f: Field)
    | SIndex(idx: int)
    | SMapKey(key: int)
    | SUnwrap
    | SVariant(tag: Tag)

  function PlaceSteps(p: Place): seq<Step> {
    match p
    case PVar(_) => []
    case PField(b, f) => PlaceSteps(b) + [SField(f)]
    case PIndex(b, i) => PlaceSteps(b) + [SIndex(i)]
    case PMapKey(b, k) => PlaceSteps(b) + [SMapKey(k)]
    case PUnwrap(b) => PlaceSteps(b) + [SUnwrap]
    case PVariant(b, tag) => PlaceSteps(b) + [SVariant(tag)]
  }

  predicate StepsDiverge(s1: seq<Step>, s2: seq<Step>) {
    exists i :: 0 <= i < |s1| && 0 <= i < |s2| && s1[i] != s2[i]
  }

  // Two places are disjoint if they have different roots or diverge at some step.
  predicate DisjointPlaces(p: Place, q: Place) {
    PlaceRoot(p) != PlaceRoot(q) || StepsDiverge(PlaceSteps(p), PlaceSteps(q))
  }

  // Theorem 3a: Read-after-write lens law.
  lemma Theorem3_PlaceReadAfterWrite(p: Place, env: FEnv, v': FVal)
    requires PlaceValid(p, env)
    ensures WritePlace(p, env, v').Some?
    ensures ReadPlace(p, WritePlace(p, env, v').value) == Some(v')
    decreases p
  {
    match p {
      case PVar(x) =>
      case PField(b, f) =>
        var Some(FRec(fields)) := ReadPlace(b, env);
        Theorem3_PlaceReadAfterWrite(b, env, FRec(fields[f := v']));
      case PIndex(b, i) =>
        var Some(FArr(elems)) := ReadPlace(b, env);
        Theorem3_PlaceReadAfterWrite(b, env, FArr(elems[i := v']));
      case PMapKey(b, k) =>
        var Some(FMap(entries)) := ReadPlace(b, env);
        Theorem3_PlaceReadAfterWrite(b, env, FMap(entries[k := v']));
      case PUnwrap(b) =>
        match ReadPlace(b, env) {
          case Some(FOptUndef(Some(_))) =>
            Theorem3_PlaceReadAfterWrite(b, env, FOptUndef(Some(v')));
          case Some(FOptNull(Some(_))) =>
            Theorem3_PlaceReadAfterWrite(b, env, FOptNull(Some(v')));
          case Some(FNullish(NValue(_))) =>
            Theorem3_PlaceReadAfterWrite(b, env, FNullish(NValue(v')));
        }
      case PVariant(b, tag) =>
        Theorem3_PlaceReadAfterWrite(b, env, FUnion(tag, v'));
    }
  }

  // Helper: WritePlace only modifies PlaceRoot(p) and preserves env keys.
  lemma Lemma_WritePlaceRootOnly(p: Place, env: FEnv, v': FVal)
    requires PlaceValid(p, env)
    ensures WritePlace(p, env, v').Some?
    ensures var env' := WritePlace(p, env, v').value;
            env'.Keys == env.Keys &&
            (forall y :: y in env && y != PlaceRoot(p) ==> env'[y] == env[y])
    decreases p
  {
    match p {
      case PVar(x) =>
      case PField(b, f) =>
        var Some(FRec(fields)) := ReadPlace(b, env);
        Lemma_WritePlaceRootOnly(b, env, FRec(fields[f := v']));
      case PIndex(b, i) =>
        var Some(FArr(elems)) := ReadPlace(b, env);
        Lemma_WritePlaceRootOnly(b, env, FArr(elems[i := v']));
      case PMapKey(b, k) =>
        var Some(FMap(entries)) := ReadPlace(b, env);
        Lemma_WritePlaceRootOnly(b, env, FMap(entries[k := v']));
      case PUnwrap(b) =>
        match ReadPlace(b, env) {
          case Some(FOptUndef(Some(_))) =>
            Lemma_WritePlaceRootOnly(b, env, FOptUndef(Some(v')));
          case Some(FOptNull(Some(_))) =>
            Lemma_WritePlaceRootOnly(b, env, FOptNull(Some(v')));
          case Some(FNullish(NValue(_))) =>
            Lemma_WritePlaceRootOnly(b, env, FNullish(NValue(v')));
        }
      case PVariant(b, tag) =>
        Lemma_WritePlaceRootOnly(b, env, FUnion(tag, v'));
    }
  }

  lemma Lemma_ReadPlaceDependsOnlyOnRoot(q: Place, env1: FEnv, env2: FEnv)
    requires PlaceRoot(q) in env1 <==> PlaceRoot(q) in env2
    requires PlaceRoot(q) in env1 ==> env1[PlaceRoot(q)] == env2[PlaceRoot(q)]
    ensures ReadPlace(q, env1) == ReadPlace(q, env2)
    decreases q
  {
    match q
    case PVar(_) =>
    case PField(b, _) => Lemma_ReadPlaceDependsOnlyOnRoot(b, env1, env2);
    case PIndex(b, _) => Lemma_ReadPlaceDependsOnlyOnRoot(b, env1, env2);
    case PMapKey(b, _) => Lemma_ReadPlaceDependsOnlyOnRoot(b, env1, env2);
    case PUnwrap(b) => Lemma_ReadPlaceDependsOnlyOnRoot(b, env1, env2);
    case PVariant(b, _) => Lemma_ReadPlaceDependsOnlyOnRoot(b, env1, env2);
  }

  // Helper: writing a place preserves any sibling path diverging at or above p.
  lemma Lemma_SameRootDisjointFrame(p: Place, q: Place, env: FEnv, v': FVal)
    requires PlaceValid(p, env)
    requires PlaceRoot(p) == PlaceRoot(q)
    requires StepsDiverge(PlaceSteps(p), PlaceSteps(q))
    ensures WritePlace(p, env, v').Some?
    ensures ReadPlace(q, WritePlace(p, env, v').value) == ReadPlace(q, env)
    decreases |PlaceSteps(p)| + |PlaceSteps(q)|
  {
    var sp := PlaceSteps(p);
    var sq := PlaceSteps(q);
    var i :| 0 <= i < |sp| && 0 <= i < |sq| && sp[i] != sq[i];
    if |sp| > |sq| {
      // p is deeper than q; step up p until |sp| == |sq| or divergence is at last step.
      match p {
        case PField(b, f) =>
          var Some(FRec(fields)) := ReadPlace(b, env);
          assert PlaceSteps(b)[i] == sp[i];
          Lemma_SameRootDisjointFrame(b, q, env, FRec(fields[f := v']));
        case PIndex(b, idx) =>
          var Some(FArr(elems)) := ReadPlace(b, env);
          assert PlaceSteps(b)[i] == sp[i];
          Lemma_SameRootDisjointFrame(b, q, env, FArr(elems[idx := v']));
        case PMapKey(b, k) =>
          var Some(FMap(entries)) := ReadPlace(b, env);
          assert PlaceSteps(b)[i] == sp[i];
          Lemma_SameRootDisjointFrame(b, q, env, FMap(entries[k := v']));
        case PUnwrap(b) =>
          assert PlaceSteps(b)[i] == sp[i];
          match ReadPlace(b, env) {
            case Some(FOptUndef(Some(_))) =>
              Lemma_SameRootDisjointFrame(b, q, env, FOptUndef(Some(v')));
            case Some(FOptNull(Some(_))) =>
              Lemma_SameRootDisjointFrame(b, q, env, FOptNull(Some(v')));
            case Some(FNullish(NValue(_))) =>
              Lemma_SameRootDisjointFrame(b, q, env, FNullish(NValue(v')));
          }
        case PVariant(b, tag) =>
          assert PlaceSteps(b)[i] == sp[i];
          Lemma_SameRootDisjointFrame(b, q, env, FUnion(tag, v'));
      }
    } else if |sq| > |sp| {
      // q is deeper than p; q's base still diverges from p at index i.
      match q {
        case PField(qb, _) =>
          assert PlaceSteps(qb)[i] == sq[i];
          Lemma_SameRootDisjointFrame(p, qb, env, v');
        case PIndex(qb, _) =>
          assert PlaceSteps(qb)[i] == sq[i];
          Lemma_SameRootDisjointFrame(p, qb, env, v');
        case PMapKey(qb, _) =>
          assert PlaceSteps(qb)[i] == sq[i];
          Lemma_SameRootDisjointFrame(p, qb, env, v');
        case PUnwrap(qb) =>
          assert PlaceSteps(qb)[i] == sq[i];
          Lemma_SameRootDisjointFrame(p, qb, env, v');
        case PVariant(qb, _) =>
          assert PlaceSteps(qb)[i] == sq[i];
          Lemma_SameRootDisjointFrame(p, qb, env, v');
      }
    } else {
      // |sp| == |sq| > 0. Check whether bases already diverge before the last step.
      if exists j :: 0 <= j < |sp| - 1 && sp[j] != sq[j] {
        var j :| 0 <= j < |sp| - 1 && sp[j] != sq[j];
        // Already diverge in their bases; step up q first.
        match q {
          case PField(qb, _) =>
            assert PlaceSteps(qb)[j] == sq[j];
            Lemma_SameRootDisjointFrame(p, qb, env, v');
          case PIndex(qb, _) =>
            assert PlaceSteps(qb)[j] == sq[j];
            Lemma_SameRootDisjointFrame(p, qb, env, v');
          case PMapKey(qb, _) =>
            assert PlaceSteps(qb)[j] == sq[j];
            Lemma_SameRootDisjointFrame(p, qb, env, v');
          case PUnwrap(qb) =>
            assert PlaceSteps(qb)[j] == sq[j];
            Lemma_SameRootDisjointFrame(p, qb, env, v');
          case PVariant(qb, _) =>
            assert PlaceSteps(qb)[j] == sq[j];
            Lemma_SameRootDisjointFrame(p, qb, env, v');
        }
      } else {
        // Bases have identical steps and same root, so bases are equal, and last steps differ.
        assert PlaceSteps(PlaceBase(p)) == sp[..|sp| - 1];
        assert PlaceSteps(PlaceBase(q)) == sq[..|sq| - 1];
        assert sp[..|sp| - 1] == sq[..|sq| - 1];
        Lemma_SameRootAndStepsEqual(PlaceBase(p), PlaceBase(q));
        var b := PlaceBase(p);
        assert PlaceBase(q) == b;
        match p {
          case PField(_, f) =>
            var Some(FRec(fields)) := ReadPlace(b, env);
            Theorem3_PlaceReadAfterWrite(b, env, FRec(fields[f := v']));
          case PIndex(_, idx) =>
            var Some(FArr(elems)) := ReadPlace(b, env);
            Theorem3_PlaceReadAfterWrite(b, env, FArr(elems[idx := v']));
          case PMapKey(_, k) =>
            var Some(FMap(entries)) := ReadPlace(b, env);
            Theorem3_PlaceReadAfterWrite(b, env, FMap(entries[k := v']));
          case PUnwrap(_) =>
            match ReadPlace(b, env) {
              case Some(FOptUndef(Some(_))) =>
                Theorem3_PlaceReadAfterWrite(b, env, FOptUndef(Some(v')));
              case Some(FOptNull(Some(_))) =>
                Theorem3_PlaceReadAfterWrite(b, env, FOptNull(Some(v')));
              case Some(FNullish(NValue(_))) =>
                Theorem3_PlaceReadAfterWrite(b, env, FNullish(NValue(v')));
            }
          case PVariant(_, tag) =>
            Theorem3_PlaceReadAfterWrite(b, env, FUnion(tag, v'));
        }
      }
    }
  }

  function PlaceBase(p: Place): Place
    requires !p.PVar?
  {
    match p
    case PField(b, _) => b
    case PIndex(b, _) => b
    case PMapKey(b, _) => b
    case PUnwrap(b) => b
    case PVariant(b, _) => b
  }

  lemma Lemma_SameRootAndStepsEqual(p: Place, q: Place)
    requires PlaceRoot(p) == PlaceRoot(q)
    requires PlaceSteps(p) == PlaceSteps(q)
    ensures p == q
    decreases p
  {
    match p {
      case PVar(_) =>
        assert |PlaceSteps(q)| == 0;
      case PField(pb, pf) =>
        assert |PlaceSteps(q)| == |PlaceSteps(p)| > 0;
        assert PlaceSteps(q)[|PlaceSteps(q)| - 1] == SField(pf);
        assert PlaceSteps(pb) == PlaceSteps(p)[..|PlaceSteps(p)| - 1];
        assert PlaceSteps(PlaceBase(q)) == PlaceSteps(q)[..|PlaceSteps(q)| - 1];
        Lemma_SameRootAndStepsEqual(pb, PlaceBase(q));
      case PIndex(pb, pi) =>
        assert |PlaceSteps(q)| == |PlaceSteps(p)| > 0;
        assert PlaceSteps(q)[|PlaceSteps(q)| - 1] == SIndex(pi);
        assert PlaceSteps(pb) == PlaceSteps(p)[..|PlaceSteps(p)| - 1];
        assert PlaceSteps(PlaceBase(q)) == PlaceSteps(q)[..|PlaceSteps(q)| - 1];
        Lemma_SameRootAndStepsEqual(pb, PlaceBase(q));
      case PMapKey(pb, pk) =>
        assert |PlaceSteps(q)| == |PlaceSteps(p)| > 0;
        assert PlaceSteps(q)[|PlaceSteps(q)| - 1] == SMapKey(pk);
        assert PlaceSteps(pb) == PlaceSteps(p)[..|PlaceSteps(p)| - 1];
        assert PlaceSteps(PlaceBase(q)) == PlaceSteps(q)[..|PlaceSteps(q)| - 1];
        Lemma_SameRootAndStepsEqual(pb, PlaceBase(q));
      case PUnwrap(pb) =>
        assert |PlaceSteps(q)| == |PlaceSteps(p)| > 0;
        assert PlaceSteps(q)[|PlaceSteps(q)| - 1] == SUnwrap;
        assert PlaceSteps(pb) == PlaceSteps(p)[..|PlaceSteps(p)| - 1];
        assert PlaceSteps(PlaceBase(q)) == PlaceSteps(q)[..|PlaceSteps(q)| - 1];
        Lemma_SameRootAndStepsEqual(pb, PlaceBase(q));
      case PVariant(pb, pt) =>
        assert |PlaceSteps(q)| == |PlaceSteps(p)| > 0;
        assert PlaceSteps(q)[|PlaceSteps(q)| - 1] == SVariant(pt);
        assert PlaceSteps(pb) == PlaceSteps(p)[..|PlaceSteps(p)| - 1];
        assert PlaceSteps(PlaceBase(q)) == PlaceSteps(q)[..|PlaceSteps(q)| - 1];
        Lemma_SameRootAndStepsEqual(pb, PlaceBase(q));
    }
  }

  // Theorem 3b: Disjoint-place frame law.
  lemma Theorem3_PlaceFrameDisjoint(p: Place, q: Place, env: FEnv, v': FVal)
    requires PlaceValid(p, env)
    requires DisjointPlaces(p, q)
    ensures WritePlace(p, env, v').Some?
    ensures ReadPlace(q, WritePlace(p, env, v').value) == ReadPlace(q, env)
  {
    if PlaceRoot(p) != PlaceRoot(q) {
      Lemma_WritePlaceRootOnly(p, env, v');
      Lemma_ReadPlaceDependsOnlyOnRoot(q, WritePlace(p, env, v').value, env);
    } else {
      Lemma_SameRootDisjointFrame(p, q, env, v');
    }
  }

  // Theorem 3c: Wrapper preservation on Unwrap and Variant writes.
  lemma Theorem3_UnwrapWritePreservesWrapper(b: Place, env: FEnv, v': FVal)
    requires PlaceValid(PUnwrap(b), env)
    ensures WritePlace(PUnwrap(b), env, v').Some?
    ensures var env' := WritePlace(PUnwrap(b), env, v').value;
            (ReadPlace(b, env).Some? && ReadPlace(b, env).value.FOptUndef? ==>
              ReadPlace(b, env') == Some(FOptUndef(Some(v')))) &&
            (ReadPlace(b, env).Some? && ReadPlace(b, env).value.FOptNull? ==>
              ReadPlace(b, env') == Some(FOptNull(Some(v')))) &&
            (ReadPlace(b, env).Some? && ReadPlace(b, env).value.FNullish? ==>
              ReadPlace(b, env') == Some(FNullish(NValue(v'))))
  {
    match ReadPlace(b, env)
    case Some(FOptUndef(Some(_))) =>
      Theorem3_PlaceReadAfterWrite(b, env, FOptUndef(Some(v')));
    case Some(FOptNull(Some(_))) =>
      Theorem3_PlaceReadAfterWrite(b, env, FOptNull(Some(v')));
    case Some(FNullish(NValue(_))) =>
      Theorem3_PlaceReadAfterWrite(b, env, FNullish(NValue(v')));
  }

  lemma Theorem3_VariantWritePreservesTag(b: Place, tag: Tag, env: FEnv, v': FVal)
    requires PlaceValid(PVariant(b, tag), env)
    ensures WritePlace(PVariant(b, tag), env, v').Some?
    ensures ReadPlace(b, WritePlace(PVariant(b, tag), env, v').value) == Some(FUnion(tag, v'))
  {
    Theorem3_PlaceReadAfterWrite(b, env, FUnion(tag, v'));
  }

  // =========================================================================
  // 3. CoreTS (JS Heap Semantics) vs. CoreVal (Checked-Read Value Store)
  // =========================================================================

  datatype JVal =
    | JInt(n: int)
    | JBool(b: bool)
    | JUndefined
    | JNull
    | JRef(addr: Addr)

  datatype HeapObj =
    | HArr(elems: seq<JVal>)
    | HRec(fields: map<Field, JVal>)
    | HMap(entries: map<int, JVal>)
    | HUnion(tag: Tag, payload: JVal)

  type JEnv = map<Var, JVal>
  type Heap = map<Addr, HeapObj>

  // Deep read of a JS value from an acyclic heap up to bounded depth.
  function HeapVal(h: Heap, jv: JVal, depth: nat): Option<Val>
    decreases depth, 0
  {
    match jv
    case JInt(n) => Some(VInt(n))
    case JBool(b) => Some(VBool(b))
    case JUndefined => Some(VUndefined)
    case JNull => Some(VNull)
    case JRef(a) =>
      if depth == 0 || a !in h then None
      else match h[a]
        case HArr(elems) =>
          var s := HeapSeq(h, elems, depth - 1);
          if s.Some? then Some(VArr(s.value)) else None
        case HRec(fields) =>
          var m := HeapFieldMap(h, fields, depth - 1);
          if m.Some? then Some(VRec(m.value)) else None
        case HMap(entries) =>
          var m := HeapIntMap(h, entries, depth - 1);
          if m.Some? then Some(VMap(m.value)) else None
        case HUnion(tag, payload) =>
          var p := HeapVal(h, payload, depth - 1);
          if p.Some? then Some(VUnion(tag, p.value)) else None
  }

  function HeapSeq(h: Heap, s: seq<JVal>, depth: nat): Option<seq<Val>>
    decreases depth, 1, |s|
  {
    if |s| == 0 then Some([])
    else
      var head := HeapVal(h, s[0], depth);
      var tail := HeapSeq(h, s[1..], depth);
      if head.Some? && tail.Some? then Some([head.value] + tail.value) else None
  }

  function HeapFieldMap(h: Heap, m: map<Field, JVal>, depth: nat): Option<map<Field, Val>>
    decreases depth, 1
  {
    if forall k :: k in m ==> HeapVal(h, m[k], depth).Some? then
      Some(map k | k in m :: HeapVal(h, m[k], depth).value)
    else None
  }

  function HeapIntMap(h: Heap, m: map<int, JVal>, depth: nat): Option<map<int, Val>>
    decreases depth, 1
  {
    if forall k :: k in m ==> HeapVal(h, m[k], depth).Some? then
      Some(map k | k in m :: HeapVal(h, m[k], depth).value)
    else None
  }

  // Heap addresses reachable from a JS value within `depth` steps.
  function Reachable(h: Heap, jv: JVal, depth: nat): set<Addr>
    decreases depth, 0
  {
    match jv {
      case JRef(a) =>
        if depth == 0 || a !in h then {a}
        else {a} + (match h[a] {
          case HArr(elems) => ReachableSeq(h, elems, depth - 1)
          case HRec(fields) => ReachableFieldMap(h, fields, depth - 1)
          case HMap(entries) => ReachableIntMap(h, entries, depth - 1)
          case HUnion(_, payload) => Reachable(h, payload, depth - 1)
        })
      case _ => {}
    }
  }

  function ReachableSeq(h: Heap, s: seq<JVal>, depth: nat): set<Addr>
    decreases depth, 1, |s|
  {
    if |s| == 0 then {}
    else Reachable(h, s[0], depth) + ReachableSeq(h, s[1..], depth)
  }

  function ReachableFieldMap(h: Heap, m: map<Field, JVal>, depth: nat): set<Addr>
    decreases depth, 1
  {
    set k, a | k in m && a in Reachable(h, m[k], depth) :: a
  }

  function ReachableIntMap(h: Heap, m: map<int, JVal>, depth: nat): set<Addr>
    decreases depth, 1
  {
    set k, a | k in m && a in Reachable(h, m[k], depth) :: a
  }

  // Frame lemma: mutating an address not reachable from `jv` leaves HeapVal(h, jv) unchanged.
  lemma Lemma_HeapUpdateOutsideReachable(h: Heap, addr: Addr, obj: HeapObj, jv: JVal, depth: nat)
    requires addr !in Reachable(h, jv, depth)
    ensures HeapVal(h[addr := obj], jv, depth) == HeapVal(h, jv, depth)
    decreases depth, 0
  {
    match jv
    case JRef(a) =>
      if depth > 0 && a in h {
        assert a != addr;
        match h[a]
        case HArr(elems) =>
          Lemma_HeapSeqUpdateOutsideReachable(h, addr, obj, elems, depth - 1);
        case HRec(fields) =>
          Lemma_HeapFieldMapUpdateOutsideReachable(h, addr, obj, fields, depth - 1);
        case HMap(entries) =>
          Lemma_HeapIntMapUpdateOutsideReachable(h, addr, obj, entries, depth - 1);
        case HUnion(_, payload) =>
          Lemma_HeapUpdateOutsideReachable(h, addr, obj, payload, depth - 1);
      }
    case _ =>
  }

  lemma Lemma_HeapSeqUpdateOutsideReachable(h: Heap, addr: Addr, obj: HeapObj, s: seq<JVal>, depth: nat)
    requires addr !in ReachableSeq(h, s, depth)
    ensures HeapSeq(h[addr := obj], s, depth) == HeapSeq(h, s, depth)
    decreases depth, 1, |s|
  {
    if |s| > 0 {
      Lemma_HeapUpdateOutsideReachable(h, addr, obj, s[0], depth);
      Lemma_HeapSeqUpdateOutsideReachable(h, addr, obj, s[1..], depth);
    }
  }

  lemma Lemma_HeapFieldMapUpdateOutsideReachable(h: Heap, addr: Addr, obj: HeapObj, m: map<Field, JVal>, depth: nat)
    requires addr !in ReachableFieldMap(h, m, depth)
    ensures HeapFieldMap(h[addr := obj], m, depth) == HeapFieldMap(h, m, depth)
    decreases depth, 1
  {
    forall k | k in m
      ensures HeapVal(h[addr := obj], m[k], depth) == HeapVal(h, m[k], depth)
    {
      assert addr !in Reachable(h, m[k], depth);
      Lemma_HeapUpdateOutsideReachable(h, addr, obj, m[k], depth);
    }
    if HeapFieldMap(h, m, depth).Some? {
      assert HeapFieldMap(h[addr := obj], m, depth).Some?;
      assert HeapFieldMap(h[addr := obj], m, depth).value == HeapFieldMap(h, m, depth).value;
    }
  }

  lemma Lemma_HeapIntMapUpdateOutsideReachable(h: Heap, addr: Addr, obj: HeapObj, m: map<int, JVal>, depth: nat)
    requires addr !in ReachableIntMap(h, m, depth)
    ensures HeapIntMap(h[addr := obj], m, depth) == HeapIntMap(h, m, depth)
    decreases depth, 1
  {
    forall k | k in m
      ensures HeapVal(h[addr := obj], m[k], depth) == HeapVal(h, m[k], depth)
    {
      assert addr !in Reachable(h, m[k], depth);
      Lemma_HeapUpdateOutsideReachable(h, addr, obj, m[k], depth);
    }
    if HeapIntMap(h, m, depth).Some? {
      assert HeapIntMap(h[addr := obj], m, depth).Some?;
      assert HeapIntMap(h[addr := obj], m, depth).value == HeapIntMap(h, m, depth).value;
    }
  }

  // Refinement between a CoreVal value and a CoreTS (JVal, Heap).
  predicate ValRefines(fv: FVal, jv: JVal, h: Heap, depth: nat) {
    HeapVal(h, jv, depth) == Some(EraseFVal(fv))
  }

  // State refinement scoped to a live variable set: dead bindings need not agree!
  predicate StateRefines(fenv: FEnv, jenv: JEnv, h: Heap, live: set<Var>, depth: nat) {
    forall x :: x in live ==> x in fenv && x in jenv && ValRefines(fenv[x], jenv[x], h, depth)
  }

  // =========================================================================
  // 4. Expressions, Arbitrary Flow-Hint Oracle, and Theorems 1 & 2
  // =========================================================================

  // Untrusted flow-narrowing hint (arbitrary uninterpreted oracle).
  datatype NarrowHint =
    | HintNone
    | HintUnwrap
    | HintVariant(tag: Tag)

  datatype Expr =
    | ELitInt(n: int)
    | ELitBool(b: bool)
    | EUndefined
    | ENull
    | EVar(x: Var)
    | EField(e: Expr, f: Field)
    | EIndex(e: Expr, idx: int)
    | EMapGet(e: Expr, key: int)
    | EAdd(left: Expr, right: Expr)
    | EEq(left: Expr, right: Expr)          // unconditional left-to-right ===
    | EAnd(left: Expr, right: Expr)         // short-circuiting &&
    | EOr(left: Expr, right: Expr)          // short-circuiting ||
    | EOptField(e: Expr, f: Field)          // single-eval e?.f
    | ENullish(left: Expr, right: Expr)     // single-eval e1 ?? e2
    | EGuard(cond: Expr, body: Expr)        // precondition-bearing call: requires cond
    | EHinted(hintId: int, inner: Expr)     // read position where compiler queries Hint(hintId)

  // Target expression language with explicit backend-checked projections.
  datatype VExpr =
    | VLitInt(n: int)
    | VLitBool(b: bool)
    | VEUndefined
    | VENull
    | VVar(x: Var)
    | VField(e: VExpr, f: Field)
    | VIndex(e: VExpr, idx: int)
    | VMapGet(e: VExpr, key: int)
    | VAdd(left: VExpr, right: VExpr)
    | VEq(left: VExpr, right: VExpr)
    | VAnd(left: VExpr, right: VExpr)
    | VOr(left: VExpr, right: VExpr)
    | VOptField(e: VExpr, f: Field)
    | VNullish(left: VExpr, right: VExpr)
    | VGuard(cond: VExpr, body: VExpr)
    | VCheckUnwrap(inner: VExpr)            // fails check if None / NUndefined / NNull
    | VCheckVariant(inner: VExpr, tag: Tag) // fails check if not FUnion(tag, _)

  function FreeVarsExpr(e: Expr): set<Var> {
    match e
    case ELitInt(_) | ELitBool(_) | EUndefined | ENull => {}
    case EVar(x) => {x}
    case EField(e1, _) => FreeVarsExpr(e1)
    case EIndex(e1, _) => FreeVarsExpr(e1)
    case EMapGet(e1, _) => FreeVarsExpr(e1)
    case EAdd(l, r) => FreeVarsExpr(l) + FreeVarsExpr(r)
    case EEq(l, r) => FreeVarsExpr(l) + FreeVarsExpr(r)
    case EAnd(l, r) => FreeVarsExpr(l) + FreeVarsExpr(r)
    case EOr(l, r) => FreeVarsExpr(l) + FreeVarsExpr(r)
    case EOptField(e1, _) => FreeVarsExpr(e1)
    case ENullish(l, r) => FreeVarsExpr(l) + FreeVarsExpr(r)
    case EGuard(c, b) => FreeVarsExpr(c) + FreeVarsExpr(b)
    case EHinted(_, e1) => FreeVarsExpr(e1)
  }

  // Lowering parameterized by an arbitrary flow-hint oracle `hint`.
  function LowerExpr(hint: int -> NarrowHint, e: Expr): VExpr {
    match e {
      case ELitInt(n) => VLitInt(n)
      case ELitBool(b) => VLitBool(b)
      case EUndefined => VEUndefined
      case ENull => VENull
      case EVar(x) => VVar(x)
      case EField(e1, f) => VField(LowerExpr(hint, e1), f)
      case EIndex(e1, idx) => VIndex(LowerExpr(hint, e1), idx)
      case EMapGet(e1, k) => VMapGet(LowerExpr(hint, e1), k)
      case EAdd(l, r) => VAdd(LowerExpr(hint, l), LowerExpr(hint, r))
      case EEq(l, r) => VEq(LowerExpr(hint, l), LowerExpr(hint, r))
      case EAnd(l, r) => VAnd(LowerExpr(hint, l), LowerExpr(hint, r))
      case EOr(l, r) => VOr(LowerExpr(hint, l), LowerExpr(hint, r))
      case EOptField(e1, f) => VOptField(LowerExpr(hint, e1), f)
      case ENullish(l, r) => VNullish(LowerExpr(hint, l), LowerExpr(hint, r))
      case EGuard(c, b) => VGuard(LowerExpr(hint, c), LowerExpr(hint, b))
      case EHinted(id, inner) =>
        var lowered := LowerExpr(hint, inner);
        (match hint(id) {
          case HintNone => lowered
          case HintUnwrap => VCheckUnwrap(lowered)
          case HintVariant(tag) => VCheckVariant(lowered, tag)
        })
    }
  }

  // Evaluation outcome distinguishing normal value vs. failed precondition/check.
  datatype EvalRes<T> = Ok(val: T) | CheckFail

  // CoreTS expression evaluator (operates on observable Val image of JS heap).
  // Note: JS ignores EHinted entirely!
  function EvalJS(jenv: JEnv, h: Heap, e: Expr, depth: nat): EvalRes<Val>
    decreases e
  {
    match e {
      case ELitInt(n) => Ok(VInt(n))
      case ELitBool(b) => Ok(VBool(b))
      case EUndefined => Ok(VUndefined)
      case ENull => Ok(VNull)
      case EVar(x) =>
        if x in jenv && HeapVal(h, jenv[x], depth).Some? then
          Ok(HeapVal(h, jenv[x], depth).value)
        else CheckFail
      case EField(e1, f) =>
        (match EvalJS(jenv, h, e1, depth) {
          case Ok(VRec(fields)) => if f in fields then Ok(fields[f]) else CheckFail
          case _ => CheckFail
        })
      case EIndex(e1, idx) =>
        (match EvalJS(jenv, h, e1, depth) {
          case Ok(VArr(elems)) => if 0 <= idx < |elems| then Ok(elems[idx]) else CheckFail
          case _ => CheckFail
        })
      case EMapGet(e1, k) =>
        (match EvalJS(jenv, h, e1, depth) {
          case Ok(VMap(entries)) => if k in entries then Ok(entries[k]) else Ok(VUndefined)
          case _ => CheckFail
        })
      case EAdd(l, r) =>
        (match EvalJS(jenv, h, l, depth) {
          case Ok(VInt(n1)) =>
            (match EvalJS(jenv, h, r, depth) {
              case Ok(VInt(n2)) => Ok(VInt(n1 + n2))
              case _ => CheckFail
            })
          case _ => CheckFail
        })
      case EEq(l, r) =>
        // Unconditional left-to-right evaluation: both operands always run!
        (match EvalJS(jenv, h, l, depth) {
          case CheckFail => CheckFail
          case Ok(v1) =>
            (match EvalJS(jenv, h, r, depth) {
              case CheckFail => CheckFail
              case Ok(v2) => Ok(VBool(v1 == v2))
            })
        })
      case EAnd(l, r) =>
        // Short-circuiting: if left is false, right is NOT evaluated.
        (match EvalJS(jenv, h, l, depth) {
          case Ok(VBool(false)) => Ok(VBool(false))
          case Ok(VBool(true)) => EvalJS(jenv, h, r, depth)
          case _ => CheckFail
        })
      case EOr(l, r) =>
        (match EvalJS(jenv, h, l, depth) {
          case Ok(VBool(true)) => Ok(VBool(true))
          case Ok(VBool(false)) => EvalJS(jenv, h, r, depth)
          case _ => CheckFail
        })
      case EOptField(e1, f) =>
        (match EvalJS(jenv, h, e1, depth) {
          case CheckFail => CheckFail
          case Ok(VUndefined) => Ok(VUndefined)
          case Ok(VNull) => Ok(VUndefined)
          case Ok(VRec(fields)) => if f in fields then Ok(fields[f]) else Ok(VUndefined)
          case _ => CheckFail
        })
      case ENullish(l, r) =>
        (match EvalJS(jenv, h, l, depth) {
          case CheckFail => CheckFail
          case Ok(VUndefined) => EvalJS(jenv, h, r, depth)
          case Ok(VNull) => EvalJS(jenv, h, r, depth)
          case Ok(v) => Ok(v)
        })
      case EGuard(c, b) =>
        (match EvalJS(jenv, h, c, depth) {
          case Ok(VBool(true)) => EvalJS(jenv, h, b, depth)
          case _ => CheckFail
        })
      case EHinted(_, inner) =>
        EvalJS(jenv, h, inner, depth)
    }
  }

  // CoreVal expression evaluator (with checked projections VCheckUnwrap / VCheckVariant).
  function EvalVal(fenv: FEnv, ve: VExpr): EvalRes<FVal>
    decreases ve
  {
    match ve {
      case VLitInt(n) => Ok(FInt(n))
      case VLitBool(b) => Ok(FBool(b))
      case VEUndefined => Ok(FUndefined)
      case VENull => Ok(FNull)
      case VVar(x) =>
        if x in fenv then Ok(fenv[x]) else CheckFail
      case VField(e1, f) =>
        (match EvalVal(fenv, e1) {
          case Ok(FRec(fields)) => if f in fields then Ok(fields[f]) else CheckFail
          case _ => CheckFail
        })
      case VIndex(e1, idx) =>
        (match EvalVal(fenv, e1) {
          case Ok(FArr(elems)) => if 0 <= idx < |elems| then Ok(elems[idx]) else CheckFail
          case _ => CheckFail
        })
      case VMapGet(e1, k) =>
        (match EvalVal(fenv, e1) {
          case Ok(FMap(entries)) =>
            if k in entries then Ok(FOptUndef(Some(entries[k]))) else Ok(FOptUndef(None))
          case _ => CheckFail
        })
      case VAdd(l, r) =>
        (match EvalVal(fenv, l) {
          case Ok(FInt(n1)) =>
            (match EvalVal(fenv, r) {
              case Ok(FInt(n2)) => Ok(FInt(n1 + n2))
              case _ => CheckFail
            })
          case _ => CheckFail
        })
      case VEq(l, r) =>
        // Unconditional left-to-right evaluation matching JS ===.
        (match EvalVal(fenv, l) {
          case CheckFail => CheckFail
          case Ok(v1) =>
            (match EvalVal(fenv, r) {
              case CheckFail => CheckFail
              case Ok(v2) => Ok(FBool(EraseFVal(v1) == EraseFVal(v2)))
            })
        })
      case VAnd(l, r) =>
        (match EvalVal(fenv, l) {
          case Ok(FBool(false)) => Ok(FBool(false))
          case Ok(FBool(true)) => EvalVal(fenv, r)
          case _ => CheckFail
        })
      case VOr(l, r) =>
        (match EvalVal(fenv, l) {
          case Ok(FBool(true)) => Ok(FBool(true))
          case Ok(FBool(false)) => EvalVal(fenv, r)
          case _ => CheckFail
        })
      case VOptField(e1, f) =>
        (match EvalVal(fenv, e1) {
          case CheckFail => CheckFail
          case Ok(fv) =>
            var base := UnwrapAllStorage(fv);
            (match base {
              case FUndefined => Ok(FOptUndef(None))
              case FNull => Ok(FOptUndef(None))
              case FOptUndef(None) => Ok(FOptUndef(None))
              case FOptNull(None) => Ok(FOptUndef(None))
              case FNullish(NUndefined) => Ok(FOptUndef(None))
              case FNullish(NNull) => Ok(FOptUndef(None))
              case FRec(fields) =>
                if f in fields then Ok(FOptUndef(Some(fields[f])))
                else Ok(FOptUndef(None))
              case _ => CheckFail
            })
        })
      case VNullish(l, r) =>
        (match EvalVal(fenv, l) {
          case CheckFail => CheckFail
          case Ok(fv) =>
            var base := UnwrapAllStorage(fv);
            (match base {
              case FUndefined => EvalVal(fenv, r)
              case FNull => EvalVal(fenv, r)
              case FOptUndef(None) => EvalVal(fenv, r)
              case FOptNull(None) => EvalVal(fenv, r)
              case FNullish(NUndefined) => EvalVal(fenv, r)
              case FNullish(NNull) => EvalVal(fenv, r)
              case _ => Ok(base)
            })
        })
      case VGuard(c, b) =>
        (match EvalVal(fenv, c) {
          case Ok(FBool(true)) => EvalVal(fenv, b)
          case _ => CheckFail
        })
      case VCheckUnwrap(inner) =>
        (match EvalVal(fenv, inner) {
          case Ok(FOptUndef(Some(v))) => Ok(v)
          case Ok(FOptNull(Some(v))) => Ok(v)
          case Ok(FNullish(NValue(v))) => Ok(v)
          case _ => CheckFail
        })
      case VCheckVariant(inner, tag) =>
        (match EvalVal(fenv, inner) {
          case Ok(FUnion(t, payload)) => if t == tag then Ok(FUnion(t, payload)) else CheckFail
          case _ => CheckFail
        })
    }
  }

  function UnwrapAllStorage(fv: FVal): FVal
    decreases fv
  {
    match fv
    case FOptUndef(Some(inner)) => UnwrapAllStorage(inner)
    case FOptNull(Some(inner)) => UnwrapAllStorage(inner)
    case FNullish(NValue(inner)) => UnwrapAllStorage(inner)
    case _ => fv
  }

  lemma Lemma_UnwrapAllStoragePreservesErase(fv: FVal)
    ensures EraseFVal(UnwrapAllStorage(fv)) == EraseFVal(fv)
    ensures var b := UnwrapAllStorage(fv);
            (EraseFVal(b).VUndefined? || EraseFVal(b).VNull?) <==>
            (b.FUndefined? || b.FNull? || b == FOptUndef(None) || b == FOptNull(None) ||
             b == FNullish(NUndefined) || b == FNullish(NNull))
    decreases fv
  {
    match fv
    case FOptUndef(Some(inner)) => Lemma_UnwrapAllStoragePreservesErase(inner);
    case FOptNull(Some(inner)) => Lemma_UnwrapAllStoragePreservesErase(inner);
    case FNullish(NValue(inner)) => Lemma_UnwrapAllStoragePreservesErase(inner);
    case _ =>
  }

  // Theorem 1 (Expressions) & Theorem 2 (Precondition/Evaluation Preservation):
  // For ANY uninterpreted flow-hint function `hint`:
  //   (a) If the lowered expression passes all backend checks (returns Ok(fv)),
  //       then JS evaluation also succeeds (returns Ok(v_js)) with EraseFVal(fv) == v_js.
  //   (b) Contrapositively (Theorem 2): whenever JS hits CheckFail (including
  //       any evaluated GuardCall(false)), the lowered expression NEVER succeeds
  //       (it MUST return CheckFail).
  lemma Theorem1_And_2_ExprSoundness(
    hint: int -> NarrowHint,
    e: Expr,
    fenv: FEnv,
    jenv: JEnv,
    h: Heap,
    live: set<Var>,
    depth: nat
  )
    requires FreeVarsExpr(e) <= live
    requires StateRefines(fenv, jenv, h, live, depth)
    ensures EvalVal(fenv, LowerExpr(hint, e)).Ok? ==>
            EvalJS(jenv, h, e, depth).Ok? &&
            EraseFVal(EvalVal(fenv, LowerExpr(hint, e)).val) == EvalJS(jenv, h, e, depth).val
    ensures EvalJS(jenv, h, e, depth).CheckFail? ==>
            EvalVal(fenv, LowerExpr(hint, e)).CheckFail?
    decreases e
  {
    var ve := LowerExpr(hint, e);
    match e
    case ELitInt(_) | ELitBool(_) | EUndefined | ENull =>
    case EVar(x) =>
      assert x in live;
    case EField(e1, f) =>
      Theorem1_And_2_ExprSoundness(hint, e1, fenv, jenv, h, live, depth);
    case EIndex(e1, idx) =>
      Theorem1_And_2_ExprSoundness(hint, e1, fenv, jenv, h, live, depth);
    case EMapGet(e1, k) =>
      Theorem1_And_2_ExprSoundness(hint, e1, fenv, jenv, h, live, depth);
    case EAdd(l, r) =>
      Theorem1_And_2_ExprSoundness(hint, l, fenv, jenv, h, live, depth);
      Theorem1_And_2_ExprSoundness(hint, r, fenv, jenv, h, live, depth);
    case EEq(l, r) =>
      Theorem1_And_2_ExprSoundness(hint, l, fenv, jenv, h, live, depth);
      Theorem1_And_2_ExprSoundness(hint, r, fenv, jenv, h, live, depth);
    case EAnd(l, r) =>
      Theorem1_And_2_ExprSoundness(hint, l, fenv, jenv, h, live, depth);
      Theorem1_And_2_ExprSoundness(hint, r, fenv, jenv, h, live, depth);
    case EOr(l, r) =>
      Theorem1_And_2_ExprSoundness(hint, l, fenv, jenv, h, live, depth);
      Theorem1_And_2_ExprSoundness(hint, r, fenv, jenv, h, live, depth);
    case EOptField(e1, f) =>
      Theorem1_And_2_ExprSoundness(hint, e1, fenv, jenv, h, live, depth);
      if EvalVal(fenv, ve).Ok? {
        var Ok(fv) := EvalVal(fenv, LowerExpr(hint, e1));
        Lemma_UnwrapAllStoragePreservesErase(fv);
      }
    case ENullish(l, r) =>
      Theorem1_And_2_ExprSoundness(hint, l, fenv, jenv, h, live, depth);
      Theorem1_And_2_ExprSoundness(hint, r, fenv, jenv, h, live, depth);
      if EvalVal(fenv, ve).Ok? {
        var Ok(fv) := EvalVal(fenv, LowerExpr(hint, l));
        Lemma_UnwrapAllStoragePreservesErase(fv);
      }
    case EGuard(c, b) =>
      Theorem1_And_2_ExprSoundness(hint, c, fenv, jenv, h, live, depth);
      Theorem1_And_2_ExprSoundness(hint, b, fenv, jenv, h, live, depth);
    case EHinted(id, inner) =>
      Theorem1_And_2_ExprSoundness(hint, inner, fenv, jenv, h, live, depth);
  }

  // Theorem 2b (General Short-Circuit Preservation):
  // Whenever the controlling operand of `&&`, `||`, `?.`, or `??` short-circuits
  // in CoreVal, the unevaluated branch (even containing an arbitrary failing
  // `EGuard(ELitBool(false), ...)`) is NOT evaluated and evaluation succeeds.
  lemma Theorem2_ShortCircuitPreservation(
    hint: int -> NarrowHint,
    fenv: FEnv,
    e1: Expr,
    e2: Expr,
    f: Field
  )
    ensures EvalVal(fenv, LowerExpr(hint, e1)) == Ok(FBool(false)) ==>
            EvalVal(fenv, LowerExpr(hint, EAnd(e1, e2))) == Ok(FBool(false))
    ensures EvalVal(fenv, LowerExpr(hint, e1)) == Ok(FBool(true)) ==>
            EvalVal(fenv, LowerExpr(hint, EOr(e1, e2))) == Ok(FBool(true))
    ensures (EvalVal(fenv, LowerExpr(hint, e1)) == Ok(FUndefined) ||
             EvalVal(fenv, LowerExpr(hint, e1)) == Ok(FNull) ||
             EvalVal(fenv, LowerExpr(hint, e1)) == Ok(FOptUndef(None)) ||
             EvalVal(fenv, LowerExpr(hint, e1)) == Ok(FOptNull(None)) ||
             EvalVal(fenv, LowerExpr(hint, e1)) == Ok(FNullish(NUndefined)) ||
             EvalVal(fenv, LowerExpr(hint, e1)) == Ok(FNullish(NNull))) ==>
            EvalVal(fenv, LowerExpr(hint, EOptField(e1, f))) == Ok(FOptUndef(None))
    ensures (EvalVal(fenv, LowerExpr(hint, e1)).Ok? &&
             var base := UnwrapAllStorage(EvalVal(fenv, LowerExpr(hint, e1)).val);
             !base.FUndefined? && !base.FNull? &&
             base != FOptUndef(None) && base != FOptNull(None) &&
             base != FNullish(NUndefined) && base != FNullish(NNull)) ==>
            EvalVal(fenv, LowerExpr(hint, ENullish(e1, e2))) == Ok(UnwrapAllStorage(EvalVal(fenv, LowerExpr(hint, e1)).val))
  {}

  // =========================================================================
  // 5. Imperative Statements, In-Place Heap Mutation, and Live-Alias Ownership
  // =========================================================================

  datatype Stmt =
    | SSkip
    | SSeq(s1: Stmt, s2: Stmt)
    | SLet(x: Var, rep: StorageRep, init: Expr)
    | SAssign(x: Var, rep: StorageRep, rhs: Expr)
    | SMutateArrPush(x: Var, hintId: int, elem: Expr)
    | SMutateIndexSet(x: Var, hintId: int, idx: int, rhs: Expr)
    | SMutateFieldSet(x: Var, hintId: int, f: Field, rhs: Expr)
    | SMutateMapSet(x: Var, hintId: int, key: int, rhs: Expr)
    | SIf(cond: Expr, thenBranch: Stmt, elseBranch: Stmt)

  // Live-alias freedom at a mutation of variable `x` with post-mutation live set `liveAfter`:
  // The mutated heap address of `x` must not be reachable from any OTHER variable
  // that remains live after the mutation.
  predicate NoLiveAliasAtTarget(x: Var, jenv: JEnv, h: Heap, liveAfter: set<Var>, depth: nat) {
    x in jenv && jenv[x].JRef? &&
    var targetAddr := jenv[x].addr;
    targetAddr in h &&
    (forall y :: y in liveAfter && y != x && y in jenv ==>
      targetAddr !in Reachable(h, jenv[y], depth))
  }

  predicate NoLiveAliasAtPush(x: Var, jenv: JEnv, h: Heap, liveAfter: set<Var>, depth: nat) {
    NoLiveAliasAtTarget(x, jenv, h, liveAfter, depth) &&
    h[jenv[x].addr].HArr?
  }

  function PrimitiveToJVal(v: Val): Option<JVal> {
    match v
    case VInt(n) => Some(JInt(n))
    case VBool(b) => Some(JBool(b))
    case VUndefined => Some(JUndefined)
    case VNull => Some(JNull)
    case _ => None
  }

  function StepJS_Push(x: Var, elemVal: Val, jenv: JEnv, h: Heap): Option<Heap> {
    if x in jenv && jenv[x].JRef? && jenv[x].addr in h && h[jenv[x].addr].HArr? && PrimitiveToJVal(elemVal).Some? then
      var a := jenv[x].addr;
      Some(h[a := HArr(h[a].elems + [PrimitiveToJVal(elemVal).value])])
    else None
  }

  function StepJS_IndexSet(x: Var, idx: int, rhsVal: Val, jenv: JEnv, h: Heap): Option<Heap> {
    if x in jenv && jenv[x].JRef? && jenv[x].addr in h && h[jenv[x].addr].HArr? &&
       0 <= idx < |h[jenv[x].addr].elems| && PrimitiveToJVal(rhsVal).Some? then
      var a := jenv[x].addr;
      Some(h[a := HArr(h[a].elems[idx := PrimitiveToJVal(rhsVal).value])])
    else None
  }

  function StepJS_FieldSet(x: Var, f: Field, rhsVal: Val, jenv: JEnv, h: Heap): Option<Heap> {
    if x in jenv && jenv[x].JRef? && jenv[x].addr in h && h[jenv[x].addr].HRec? &&
       f in h[jenv[x].addr].fields && PrimitiveToJVal(rhsVal).Some? then
      var a := jenv[x].addr;
      Some(h[a := HRec(h[a].fields[f := PrimitiveToJVal(rhsVal).value])])
    else None
  }

  function StepJS_MapSet(x: Var, key: int, rhsVal: Val, jenv: JEnv, h: Heap): Option<Heap> {
    if x in jenv && jenv[x].JRef? && jenv[x].addr in h && h[jenv[x].addr].HMap? &&
       key in h[jenv[x].addr].entries && PrimitiveToJVal(rhsVal).Some? then
      var a := jenv[x].addr;
      Some(h[a := HMap(h[a].entries[key := PrimitiveToJVal(rhsVal).value])])
    else None
  }

  // CoreVal mutation lowering driven by `hint(hintId)`:
  // HintUnwrap lowers to Place write-back through `PUnwrap(PVar(x))` (checked unwrap + Some re-wrap!);
  // HintNone lowers to direct `PVar(x)` write-back.
  function TargetPlace(hint: int -> NarrowHint, x: Var, hintId: int): Place {
    if hint(hintId).HintUnwrap? then PUnwrap(PVar(x)) else PVar(x)
  }

  function StepVal_Push(x: Var, unwrapped: bool, elemFVal: FVal, fenv: FEnv): Option<FEnv> {
    var p := if unwrapped then PUnwrap(PVar(x)) else PVar(x);
    match ReadPlace(p, fenv) {
      case Some(FArr(elems)) => WritePlace(p, fenv, FArr(elems + [elemFVal]))
      case _ => None
    }
  }

  function StepVal_IndexSet(p: Place, idx: int, rhsFVal: FVal, fenv: FEnv): Option<FEnv> {
    WritePlace(PIndex(p, idx), fenv, rhsFVal)
  }

  function StepVal_FieldSet(p: Place, f: Field, rhsFVal: FVal, fenv: FEnv): Option<FEnv> {
    WritePlace(PField(p, f), fenv, rhsFVal)
  }

  function StepVal_MapSet(p: Place, key: int, rhsFVal: FVal, fenv: FEnv): Option<FEnv> {
    WritePlace(PMapKey(p, key), fenv, rhsFVal)
  }

  // Multi-step statement evaluators for CoreTS and CoreVal (parameterized by `hint`).
  function ExecJSStmt(s: Stmt, jenv: JEnv, h: Heap, depth: nat): EvalRes<(JEnv, Heap)>
    decreases s
  {
    match s {
      case SSkip => Ok((jenv, h))
      case SSeq(s1, s2) =>
        (match ExecJSStmt(s1, jenv, h, depth) {
          case CheckFail => CheckFail
          case Ok((jenv1, h1)) => ExecJSStmt(s2, jenv1, h1, depth)
        })
      case SLet(x, rep, init) =>
        (match EvalJS(jenv, h, init, depth) {
          case Ok(v) =>
            if ValidForRep(rep, v) && PrimitiveToJVal(v).Some? then
              Ok((jenv[x := PrimitiveToJVal(v).value], h))
            else CheckFail
          case CheckFail => CheckFail
        })
      case SAssign(x, rep, rhs) =>
        (match EvalJS(jenv, h, rhs, depth) {
          case Ok(v) =>
            if x in jenv && ValidForRep(rep, v) && PrimitiveToJVal(v).Some? then
              Ok((jenv[x := PrimitiveToJVal(v).value], h))
            else CheckFail
          case CheckFail => CheckFail
        })
      case SMutateArrPush(x, _, elem) =>
        (match EvalJS(jenv, h, elem, depth) {
          case Ok(ev) =>
            var h' := StepJS_Push(x, ev, jenv, h);
            if h'.Some? then Ok((jenv, h'.value)) else CheckFail
          case CheckFail => CheckFail
        })
      case SMutateIndexSet(x, _, idx, rhs) =>
        (match EvalJS(jenv, h, rhs, depth) {
          case Ok(rv) =>
            var h' := StepJS_IndexSet(x, idx, rv, jenv, h);
            if h'.Some? then Ok((jenv, h'.value)) else CheckFail
          case CheckFail => CheckFail
        })
      case SMutateFieldSet(x, _, f, rhs) =>
        (match EvalJS(jenv, h, rhs, depth) {
          case Ok(rv) =>
            var h' := StepJS_FieldSet(x, f, rv, jenv, h);
            if h'.Some? then Ok((jenv, h'.value)) else CheckFail
          case CheckFail => CheckFail
        })
      case SMutateMapSet(x, _, key, rhs) =>
        (match EvalJS(jenv, h, rhs, depth) {
          case Ok(rv) =>
            var h' := StepJS_MapSet(x, key, rv, jenv, h);
            if h'.Some? then Ok((jenv, h'.value)) else CheckFail
          case CheckFail => CheckFail
        })
      case SIf(cond, t, e) =>
        (match EvalJS(jenv, h, cond, depth) {
          case Ok(VBool(true)) => ExecJSStmt(t, jenv, h, depth)
          case Ok(VBool(false)) => ExecJSStmt(e, jenv, h, depth)
          case _ => CheckFail
        })
    }
  }

  function ExecValStmt(hint: int -> NarrowHint, s: Stmt, fenv: FEnv): EvalRes<FEnv>
    decreases s
  {
    match s {
      case SSkip => Ok(fenv)
      case SSeq(s1, s2) =>
        (match ExecValStmt(hint, s1, fenv) {
          case CheckFail => CheckFail
          case Ok(fenv1) => ExecValStmt(hint, s2, fenv1)
        })
      case SLet(x, rep, init) =>
        (match EvalVal(fenv, LowerExpr(hint, init)) {
          case Ok(fv) =>
            var v := EraseFVal(fv);
            if ValidForRep(rep, v) then Ok(fenv[x := EncodeVal(rep, v)])
            else CheckFail
          case CheckFail => CheckFail
        })
      case SAssign(x, rep, rhs) =>
        (match EvalVal(fenv, LowerExpr(hint, rhs)) {
          case Ok(fv) =>
            var v := EraseFVal(fv);
            if x in fenv && ValidForRep(rep, v) then Ok(fenv[x := EncodeVal(rep, v)])
            else CheckFail
          case CheckFail => CheckFail
        })
      case SMutateArrPush(x, hid, elem) =>
        (match EvalVal(fenv, LowerExpr(hint, elem)) {
          case Ok(fv) =>
            var fenv' := StepVal_Push(x, hint(hid).HintUnwrap?, fv, fenv);
            if fenv'.Some? then Ok(fenv'.value) else CheckFail
          case CheckFail => CheckFail
        })
      case SMutateIndexSet(x, hid, idx, rhs) =>
        (match EvalVal(fenv, LowerExpr(hint, rhs)) {
          case Ok(fv) =>
            var fenv' := StepVal_IndexSet(TargetPlace(hint, x, hid), idx, fv, fenv);
            if fenv'.Some? then Ok(fenv'.value) else CheckFail
          case CheckFail => CheckFail
        })
      case SMutateFieldSet(x, hid, f, rhs) =>
        (match EvalVal(fenv, LowerExpr(hint, rhs)) {
          case Ok(fv) =>
            var fenv' := StepVal_FieldSet(TargetPlace(hint, x, hid), f, fv, fenv);
            if fenv'.Some? then Ok(fenv'.value) else CheckFail
          case CheckFail => CheckFail
        })
      case SMutateMapSet(x, hid, key, rhs) =>
        (match EvalVal(fenv, LowerExpr(hint, rhs)) {
          case Ok(fv) =>
            var fenv' := StepVal_MapSet(TargetPlace(hint, x, hid), key, fv, fenv);
            if fenv'.Some? then Ok(fenv'.value) else CheckFail
          case CheckFail => CheckFail
        })
      case SIf(cond, t, e) =>
        (match EvalVal(fenv, LowerExpr(hint, cond)) {
          case Ok(FBool(true)) => ExecValStmt(hint, t, fenv)
          case Ok(FBool(false)) => ExecValStmt(hint, e, fenv)
          case _ => CheckFail
        })
    }
  }

  lemma Lemma_HeapSeqAppend(h: Heap, s: seq<JVal>, jv: JVal, depth: nat)
    requires HeapSeq(h, s, depth).Some?
    requires HeapVal(h, jv, depth).Some?
    ensures HeapSeq(h, s + [jv], depth) == Some(HeapSeq(h, s, depth).value + [HeapVal(h, jv, depth).value])
    decreases |s|
  {
    if |s| == 0 {
      assert s + [jv] == [jv];
      assert [jv][0] == jv && [jv][1..] == [];
      assert HeapSeq(h, [jv][1..], depth) == Some([]);
      assert [HeapVal(h, jv, depth).value] + [] == [] + [HeapVal(h, jv, depth).value];
    } else {
      assert (s + [jv])[0] == s[0];
      assert (s + [jv])[1..] == s[1..] + [jv];
      Lemma_HeapSeqAppend(h, s[1..], jv, depth);
      var head := HeapVal(h, s[0], depth).value;
      var tail := HeapSeq(h, s[1..], depth).value;
      var last := HeapVal(h, jv, depth).value;
      assert ([head] + tail) + [last] == [head] + (tail + [last]);
    }
  }

  // Theorem 1 (Statement step: In-Place Push under NoLiveAliasMutation + Arbitrary Hint):
  // If CoreVal lowers `x.push(elem)` via Place write-back (with or without PUnwrap),
  // and `NoLiveAliasAtPush(x, jenv, h, liveAfter, depth)` holds (and `x`'s own elements
  // do not cyclically point back to `x`'s array address), then the post-mutation
  // CoreVal environment refines the in-place mutated JS heap on ALL variables in `liveAfter`!
  lemma Theorem1_PushMutationSoundness(
    hint: int -> NarrowHint,
    x: Var,
    unwrapped: bool,
    elem: Expr,
    fenv: FEnv,
    jenv: JEnv,
    h: Heap,
    liveBefore: set<Var>,
    liveAfter: set<Var>,
    depth: nat
  )
    requires depth >= 1
    requires x in liveBefore
    requires FreeVarsExpr(elem) <= liveBefore
    requires liveAfter <= liveBefore
    requires StateRefines(fenv, jenv, h, liveBefore, depth)
    requires NoLiveAliasAtPush(x, jenv, h, liveAfter, depth)
    requires jenv[x].addr !in ReachableSeq(h, h[jenv[x].addr].elems, depth - 1)
    requires EvalVal(fenv, LowerExpr(hint, elem)).Ok?
    requires var fv := EvalVal(fenv, LowerExpr(hint, elem)).val;
             StepVal_Push(x, unwrapped, fv, fenv).Some?
    requires var ev := EvalJS(jenv, h, elem, depth);
             ev.Ok? && (ev.val.VInt? || ev.val.VBool? || ev.val.VUndefined? || ev.val.VNull?)
    ensures var fv := EvalVal(fenv, LowerExpr(hint, elem)).val;
            var fenv' := StepVal_Push(x, unwrapped, fv, fenv).value;
            var h' := StepJS_Push(x, EvalJS(jenv, h, elem, depth).val, jenv, h);
            h'.Some? && StateRefines(fenv', jenv, h'.value, liveAfter, depth)
  {
    Theorem1_And_2_ExprSoundness(hint, elem, fenv, jenv, h, liveBefore, depth);
    var fv := EvalVal(fenv, LowerExpr(hint, elem)).val;
    var ev := EvalJS(jenv, h, elem, depth).val;
    assert EraseFVal(fv) == ev;
    var p := if unwrapped then PUnwrap(PVar(x)) else PVar(x);
    var Some(FArr(elems)) := ReadPlace(p, fenv);
    var fenv' := StepVal_Push(x, unwrapped, fv, fenv).value;
    var a := jenv[x].addr;
    var jElem := match ev
      case VInt(n) => JInt(n)
      case VBool(b) => JBool(b)
      case VUndefined => JUndefined
      case VNull => JNull;
    var h' := h[a := HArr(h[a].elems + [jElem])];
    assert StepJS_Push(x, ev, jenv, h) == Some(h');

    // 1. Every other live variable y != x is unaffected in both fenv' and h'.
    Lemma_WritePlaceRootOnly(p, fenv, FArr(elems + [fv]));
    forall y | y in liveAfter && y != x
      ensures y in fenv' && y in jenv && ValRefines(fenv'[y], jenv[y], h', depth)
    {
      assert fenv'[y] == fenv[y];
      assert a !in Reachable(h, jenv[y], depth);
      Lemma_HeapUpdateOutsideReachable(h, a, HArr(h[a].elems + [jElem]), jenv[y], depth);
    }

    // 2. Variable x itself refines the updated array in h' (preserving wrapper if unwrapped).
    if x in liveAfter {
      Theorem3_PlaceReadAfterWrite(p, fenv, FArr(elems + [fv]));
      if unwrapped {
        Theorem3_UnwrapWritePreservesWrapper(PVar(x), fenv, FArr(elems + [fv]));
      }
      var erasedOld := seq(|elems|, i requires 0 <= i < |elems| => EraseFVal(elems[i]));
      var erasedNew := seq(|elems + [fv]|, i requires 0 <= i < |elems + [fv]| => EraseFVal((elems + [fv])[i]));
      assert erasedNew == erasedOld + [ev];
      assert EraseFVal(fenv'[x]) == VArr(erasedNew);
      assert EraseFVal(fenv[x]) == VArr(erasedOld);
      assert HeapVal(h, JRef(a), depth) == Some(VArr(erasedOld));
      Lemma_HeapSeqUpdateOutsideReachable(h, a, HArr(h[a].elems + [jElem]), h[a].elems, depth - 1);
      Lemma_HeapSeqAppend(h', h[a].elems, jElem, depth - 1);
      assert HeapVal(h', JRef(a), depth) == Some(VArr(erasedOld + [ev]));
    }
  }

  lemma Lemma_HeapSeqUpdate(h: Heap, s: seq<JVal>, idx: int, jv: JVal, depth: nat)
    requires 0 <= idx < |s|
    requires HeapSeq(h, s, depth).Some?
    requires HeapVal(h, jv, depth).Some?
    ensures |HeapSeq(h, s, depth).value| == |s|
    ensures HeapSeq(h, s[idx := jv], depth) == Some(HeapSeq(h, s, depth).value[idx := HeapVal(h, jv, depth).value])
    decreases |s|
  {
    if idx == 0 {
      assert s[0 := jv][0] == jv;
      assert s[0 := jv][1..] == s[1..];
      Lemma_HeapSeqLen(h, s[1..], depth);
      var h0 := HeapVal(h, s[0], depth).value;
      var t := HeapSeq(h, s[1..], depth).value;
      var nv := HeapVal(h, jv, depth).value;
      assert ([h0] + t)[0 := nv] == [nv] + t;
    } else {
      assert s[idx := jv][0] == s[0];
      assert s[idx := jv][1..] == s[1..][idx - 1 := jv];
      Lemma_HeapSeqUpdate(h, s[1..], idx - 1, jv, depth);
      var h0 := HeapVal(h, s[0], depth).value;
      var t := HeapSeq(h, s[1..], depth).value;
      var nv := HeapVal(h, jv, depth).value;
      assert ([h0] + t)[idx := nv] == [h0] + t[idx - 1 := nv];
    }
  }

  lemma Lemma_HeapSeqLen(h: Heap, s: seq<JVal>, depth: nat)
    requires HeapSeq(h, s, depth).Some?
    ensures |HeapSeq(h, s, depth).value| == |s|
    decreases |s|
  {
    if |s| > 0 {
      Lemma_HeapSeqLen(h, s[1..], depth);
    }
  }

  lemma Lemma_TargetPlaceInfo(hint: int -> NarrowHint, x: Var, hid: int, fenv: FEnv)
    requires ReadPlace(TargetPlace(hint, x, hid), fenv).Some?
    ensures PlaceRoot(TargetPlace(hint, x, hid)) == x
    ensures x in fenv && EraseFVal(fenv[x]) == EraseFVal(ReadPlace(TargetPlace(hint, x, hid), fenv).value)
  {
    if hint(hid).HintUnwrap? {
      assert TargetPlace(hint, x, hid) == PUnwrap(PVar(x));
    } else {
      assert TargetPlace(hint, x, hid) == PVar(x);
    }
  }

  lemma Lemma_PrimitiveToJValHeapVal(h: Heap, v: Val, depth: nat)
    requires PrimitiveToJVal(v).Some?
    ensures HeapVal(h, PrimitiveToJVal(v).value, depth) == Some(v)
  {}

  lemma Theorem1_IndexSetSoundness(
    hint: int -> NarrowHint,
    x: Var,
    hid: int,
    idx: int,
    rhs: Expr,
    fenv: FEnv,
    jenv: JEnv,
    h: Heap,
    liveBefore: set<Var>,
    liveAfter: set<Var>,
    depth: nat
  )
    requires depth >= 1
    requires x in liveBefore && FreeVarsExpr(rhs) <= liveBefore && liveAfter <= liveBefore
    requires StateRefines(fenv, jenv, h, liveBefore, depth)
    requires NoLiveAliasAtTarget(x, jenv, h, liveAfter, depth) && h[jenv[x].addr].HArr?
    requires jenv[x].addr !in ReachableSeq(h, h[jenv[x].addr].elems, depth - 1)
    requires EvalVal(fenv, LowerExpr(hint, rhs)).Ok?
    requires var fv := EvalVal(fenv, LowerExpr(hint, rhs)).val;
             StepVal_IndexSet(TargetPlace(hint, x, hid), idx, fv, fenv).Some?
    requires var ev := EvalJS(jenv, h, rhs, depth);
             ev.Ok? && PrimitiveToJVal(ev.val).Some?
    ensures var fv := EvalVal(fenv, LowerExpr(hint, rhs)).val;
            var fenv' := StepVal_IndexSet(TargetPlace(hint, x, hid), idx, fv, fenv).value;
            var h' := StepJS_IndexSet(x, idx, EvalJS(jenv, h, rhs, depth).val, jenv, h);
            h'.Some? && StateRefines(fenv', jenv, h'.value, liveAfter, depth)
  {
    Theorem1_And_2_ExprSoundness(hint, rhs, fenv, jenv, h, liveBefore, depth);
    var fv := EvalVal(fenv, LowerExpr(hint, rhs)).val;
    var ev := EvalJS(jenv, h, rhs, depth).val;
    var base := TargetPlace(hint, x, hid);
    var p := PIndex(base, idx);
    assert PlaceValid(p, fenv);
    Lemma_TargetPlaceInfo(hint, x, hid, fenv);
    var Some(FArr(elems)) := ReadPlace(base, fenv);
    assert EraseFVal(fenv[x]) == EraseFVal(FArr(elems));
    var fenv' := StepVal_IndexSet(base, idx, fv, fenv).value;
    var a := jenv[x].addr;
    var jElem := PrimitiveToJVal(ev).value;
    Lemma_PrimitiveToJValHeapVal(h, ev, depth - 1);
    Lemma_HeapSeqLen(h, h[a].elems, depth - 1);
    assert |h[a].elems| == |elems| && 0 <= idx < |h[a].elems|;
    var h' := h[a := HArr(h[a].elems[idx := jElem])];
    Lemma_WritePlaceRootOnly(p, fenv, fv);
    assert PlaceRoot(p) == PlaceRoot(base) == x;
    forall y | y in liveAfter && y != x
      ensures y in fenv' && y in jenv && ValRefines(fenv'[y], jenv[y], h', depth)
    {
      assert fenv'[y] == fenv[y];
      assert a !in Reachable(h, jenv[y], depth);
      Lemma_HeapUpdateOutsideReachable(h, a, HArr(h[a].elems[idx := jElem]), jenv[y], depth);
    }
    if x in liveAfter {
      Theorem3_PlaceReadAfterWrite(base, fenv, FArr(elems[idx := fv]));
      if hint(hid).HintUnwrap? {
        Theorem3_UnwrapWritePreservesWrapper(PVar(x), fenv, FArr(elems[idx := fv]));
      }
      var erasedOld := seq(|elems|, i requires 0 <= i < |elems| => EraseFVal(elems[i]));
      var erasedNew := seq(|elems|, i requires 0 <= i < |elems| => EraseFVal(elems[idx := fv][i]));
      assert erasedNew == erasedOld[idx := ev];
      assert EraseFVal(fenv'[x]) == VArr(erasedNew);
      Lemma_HeapSeqUpdateOutsideReachable(h, a, HArr(h[a].elems[idx := jElem]), h[a].elems, depth - 1);
      Lemma_HeapSeqUpdate(h', h[a].elems, idx, jElem, depth - 1);
      assert HeapVal(h', JRef(a), depth) == Some(VArr(erasedNew));
    }
  }

  lemma Theorem1_FieldSetSoundness(
    hint: int -> NarrowHint,
    x: Var,
    hid: int,
    f: Field,
    rhs: Expr,
    fenv: FEnv,
    jenv: JEnv,
    h: Heap,
    liveBefore: set<Var>,
    liveAfter: set<Var>,
    depth: nat
  )
    requires depth >= 1
    requires x in liveBefore && FreeVarsExpr(rhs) <= liveBefore && liveAfter <= liveBefore
    requires StateRefines(fenv, jenv, h, liveBefore, depth)
    requires NoLiveAliasAtTarget(x, jenv, h, liveAfter, depth) && h[jenv[x].addr].HRec?
    requires jenv[x].addr !in ReachableFieldMap(h, h[jenv[x].addr].fields, depth - 1)
    requires EvalVal(fenv, LowerExpr(hint, rhs)).Ok?
    requires var fv := EvalVal(fenv, LowerExpr(hint, rhs)).val;
             StepVal_FieldSet(TargetPlace(hint, x, hid), f, fv, fenv).Some?
    requires var ev := EvalJS(jenv, h, rhs, depth);
             ev.Ok? && PrimitiveToJVal(ev.val).Some?
    ensures var fv := EvalVal(fenv, LowerExpr(hint, rhs)).val;
            var fenv' := StepVal_FieldSet(TargetPlace(hint, x, hid), f, fv, fenv).value;
            var h' := StepJS_FieldSet(x, f, EvalJS(jenv, h, rhs, depth).val, jenv, h);
            h'.Some? && StateRefines(fenv', jenv, h'.value, liveAfter, depth)
  {
    Theorem1_And_2_ExprSoundness(hint, rhs, fenv, jenv, h, liveBefore, depth);
    var fv := EvalVal(fenv, LowerExpr(hint, rhs)).val;
    var ev := EvalJS(jenv, h, rhs, depth).val;
    var base := TargetPlace(hint, x, hid);
    var p := PField(base, f);
    assert PlaceValid(p, fenv);
    Lemma_TargetPlaceInfo(hint, x, hid, fenv);
    var Some(FRec(fields)) := ReadPlace(base, fenv);
    assert EraseFVal(fenv[x]) == EraseFVal(FRec(fields));
    var fenv' := StepVal_FieldSet(base, f, fv, fenv).value;
    var a := jenv[x].addr;
    var jVal := PrimitiveToJVal(ev).value;
    var m1 := HeapFieldMap(h, h[a].fields, depth - 1).value;
    var m2 := map k | k in fields :: EraseFVal(fields[k]);
    assert m1 == m2;
    assert m1.Keys == h[a].fields.Keys && m2.Keys == fields.Keys;
    assert h[a].fields.Keys == fields.Keys;
    assert f in h[a].fields;
    var newFields := h[a].fields[f := jVal];
    var h' := h[a := HRec(newFields)];
    Lemma_PrimitiveToJValHeapVal(h', ev, depth - 1);
    Lemma_WritePlaceRootOnly(p, fenv, fv);
    assert PlaceRoot(p) == PlaceRoot(base) == x;
    forall y | y in liveAfter && y != x
      ensures y in fenv' && y in jenv && ValRefines(fenv'[y], jenv[y], h', depth)
    {
      assert fenv'[y] == fenv[y];
      assert a !in Reachable(h, jenv[y], depth);
      Lemma_HeapUpdateOutsideReachable(h, a, HRec(newFields), jenv[y], depth);
    }
    if x in liveAfter {
      var updatedFields := fields[f := fv];
      Theorem3_PlaceReadAfterWrite(base, fenv, FRec(updatedFields));
      if hint(hid).HintUnwrap? {
        Theorem3_UnwrapWritePreservesWrapper(PVar(x), fenv, FRec(updatedFields));
      }
      assert EraseFVal(fenv'[x]) == VRec(map k | k in updatedFields :: EraseFVal(updatedFields[k]));
      Lemma_HeapFieldMapUpdateOutsideReachable(h, a, HRec(newFields), h[a].fields, depth - 1);
      forall k | k in newFields
        ensures k in updatedFields && HeapVal(h', newFields[k], depth - 1) == Some(EraseFVal(updatedFields[k]))
      {
        if k != f {
          assert a !in Reachable(h, h[a].fields[k], depth - 1);
          Lemma_HeapUpdateOutsideReachable(h, a, HRec(newFields), h[a].fields[k], depth - 1);
        }
      }
      assert HeapFieldMap(h', newFields, depth - 1).Some?;
      assert HeapFieldMap(h', newFields, depth - 1).value == (map k | k in updatedFields :: EraseFVal(updatedFields[k]));
      assert HeapVal(h', JRef(a), depth) == Some(EraseFVal(fenv'[x]));
    }
  }

  lemma Theorem1_MapSetSoundness(
    hint: int -> NarrowHint,
    x: Var,
    hid: int,
    key: int,
    rhs: Expr,
    fenv: FEnv,
    jenv: JEnv,
    h: Heap,
    liveBefore: set<Var>,
    liveAfter: set<Var>,
    depth: nat
  )
    requires depth >= 1
    requires x in liveBefore && FreeVarsExpr(rhs) <= liveBefore && liveAfter <= liveBefore
    requires StateRefines(fenv, jenv, h, liveBefore, depth)
    requires NoLiveAliasAtTarget(x, jenv, h, liveAfter, depth) && h[jenv[x].addr].HMap?
    requires jenv[x].addr !in ReachableIntMap(h, h[jenv[x].addr].entries, depth - 1)
    requires EvalVal(fenv, LowerExpr(hint, rhs)).Ok?
    requires var fv := EvalVal(fenv, LowerExpr(hint, rhs)).val;
             StepVal_MapSet(TargetPlace(hint, x, hid), key, fv, fenv).Some?
    requires var ev := EvalJS(jenv, h, rhs, depth);
             ev.Ok? && PrimitiveToJVal(ev.val).Some?
    ensures var fv := EvalVal(fenv, LowerExpr(hint, rhs)).val;
            var fenv' := StepVal_MapSet(TargetPlace(hint, x, hid), key, fv, fenv).value;
            var h' := StepJS_MapSet(x, key, EvalJS(jenv, h, rhs, depth).val, jenv, h);
            h'.Some? && StateRefines(fenv', jenv, h'.value, liveAfter, depth)
  {
    Theorem1_And_2_ExprSoundness(hint, rhs, fenv, jenv, h, liveBefore, depth);
    var fv := EvalVal(fenv, LowerExpr(hint, rhs)).val;
    var ev := EvalJS(jenv, h, rhs, depth).val;
    var base := TargetPlace(hint, x, hid);
    var p := PMapKey(base, key);
    assert PlaceValid(p, fenv);
    Lemma_TargetPlaceInfo(hint, x, hid, fenv);
    var Some(FMap(entries)) := ReadPlace(base, fenv);
    assert EraseFVal(fenv[x]) == EraseFVal(FMap(entries));
    var fenv' := StepVal_MapSet(base, key, fv, fenv).value;
    var a := jenv[x].addr;
    var jVal := PrimitiveToJVal(ev).value;
    var m1 := HeapIntMap(h, h[a].entries, depth - 1).value;
    var m2 := map k | k in entries :: EraseFVal(entries[k]);
    assert m1 == m2;
    assert m1.Keys == h[a].entries.Keys && m2.Keys == entries.Keys;
    assert h[a].entries.Keys == entries.Keys;
    assert key in h[a].entries;
    var newEntries := h[a].entries[key := jVal];
    var h' := h[a := HMap(newEntries)];
    Lemma_PrimitiveToJValHeapVal(h', ev, depth - 1);
    Lemma_WritePlaceRootOnly(p, fenv, fv);
    assert PlaceRoot(p) == PlaceRoot(base) == x;
    forall y | y in liveAfter && y != x
      ensures y in fenv' && y in jenv && ValRefines(fenv'[y], jenv[y], h', depth)
    {
      assert fenv'[y] == fenv[y];
      assert a !in Reachable(h, jenv[y], depth);
      Lemma_HeapUpdateOutsideReachable(h, a, HMap(newEntries), jenv[y], depth);
    }
    if x in liveAfter {
      var updatedEntries := entries[key := fv];
      Theorem3_PlaceReadAfterWrite(base, fenv, FMap(updatedEntries));
      if hint(hid).HintUnwrap? {
        Theorem3_UnwrapWritePreservesWrapper(PVar(x), fenv, FMap(updatedEntries));
      }
      assert EraseFVal(fenv'[x]) == VMap(map k | k in updatedEntries :: EraseFVal(updatedEntries[k]));
      Lemma_HeapIntMapUpdateOutsideReachable(h, a, HMap(newEntries), h[a].entries, depth - 1);
      forall k | k in newEntries
        ensures k in updatedEntries && HeapVal(h', newEntries[k], depth - 1) == Some(EraseFVal(updatedEntries[k]))
      {
        if k != key {
          assert a !in Reachable(h, h[a].entries[k], depth - 1);
          Lemma_HeapUpdateOutsideReachable(h, a, HMap(newEntries), h[a].entries[k], depth - 1);
        }
      }
      assert HeapIntMap(h', newEntries, depth - 1).Some?;
      assert HeapIntMap(h', newEntries, depth - 1).value == (map k | k in updatedEntries :: EraseFVal(updatedEntries[k]));
      assert HeapVal(h', JRef(a), depth) == Some(EraseFVal(fenv'[x]));
    }
  }

  // Predicate characterizing well-scoped, live-alias-safe statements for multi-step soundness.
  predicate StmtLiveAliasSafe(s: Stmt, jenv: JEnv, h: Heap, live: set<Var>, depth: nat)
    decreases s
  {
    match s {
      case SSkip => true
      case SLet(_, _, init) =>
        FreeVarsExpr(init) <= live &&
        (EvalJS(jenv, h, init, depth).Ok? ==> PrimitiveToJVal(EvalJS(jenv, h, init, depth).val).Some?)
      case SAssign(x, _, rhs) =>
        x in live && FreeVarsExpr(rhs) <= live &&
        (EvalJS(jenv, h, rhs, depth).Ok? ==> PrimitiveToJVal(EvalJS(jenv, h, rhs, depth).val).Some?)
      case SMutateArrPush(x, _, elem) =>
        depth >= 1 && x in live && FreeVarsExpr(elem) <= live &&
        NoLiveAliasAtTarget(x, jenv, h, live, depth) && h[jenv[x].addr].HArr? &&
        jenv[x].addr !in ReachableSeq(h, h[jenv[x].addr].elems, depth - 1) &&
        (EvalJS(jenv, h, elem, depth).Ok? ==> PrimitiveToJVal(EvalJS(jenv, h, elem, depth).val).Some?)
      case SMutateIndexSet(x, _, _, rhs) =>
        depth >= 1 && x in live && FreeVarsExpr(rhs) <= live &&
        NoLiveAliasAtTarget(x, jenv, h, live, depth) && h[jenv[x].addr].HArr? &&
        jenv[x].addr !in ReachableSeq(h, h[jenv[x].addr].elems, depth - 1) &&
        (EvalJS(jenv, h, rhs, depth).Ok? ==> PrimitiveToJVal(EvalJS(jenv, h, rhs, depth).val).Some?)
      case SMutateFieldSet(x, _, _, rhs) =>
        depth >= 1 && x in live && FreeVarsExpr(rhs) <= live &&
        NoLiveAliasAtTarget(x, jenv, h, live, depth) && h[jenv[x].addr].HRec? &&
        jenv[x].addr !in ReachableFieldMap(h, h[jenv[x].addr].fields, depth - 1) &&
        (EvalJS(jenv, h, rhs, depth).Ok? ==> PrimitiveToJVal(EvalJS(jenv, h, rhs, depth).val).Some?)
      case SMutateMapSet(x, _, _, rhs) =>
        depth >= 1 && x in live && FreeVarsExpr(rhs) <= live &&
        NoLiveAliasAtTarget(x, jenv, h, live, depth) && h[jenv[x].addr].HMap? &&
        jenv[x].addr !in ReachableIntMap(h, h[jenv[x].addr].entries, depth - 1) &&
        (EvalJS(jenv, h, rhs, depth).Ok? ==> PrimitiveToJVal(EvalJS(jenv, h, rhs, depth).val).Some?)
      case SIf(cond, t, e) =>
        FreeVarsExpr(cond) <= live &&
        (EvalJS(jenv, h, cond, depth) == Ok(VBool(true)) ==> StmtLiveAliasSafe(t, jenv, h, live, depth)) &&
        (EvalJS(jenv, h, cond, depth) == Ok(VBool(false)) ==> StmtLiveAliasSafe(e, jenv, h, live, depth))
      case SSeq(s1, s2) =>
        StmtLiveAliasSafe(s1, jenv, h, live, depth) &&
        (ExecJSStmt(s1, jenv, h, depth).Ok? ==>
          var (j1, h1) := ExecJSStmt(s1, jenv, h, depth).val;
          StmtLiveAliasSafe(s2, j1, h1, OutLiveStmt(s1, live), depth))
    }
  }

  function OutLiveStmt(s: Stmt, live: set<Var>): set<Var>
    decreases s
  {
    match s {
      case SLet(x, _, _) => live + {x}
      case SSeq(s1, s2) => OutLiveStmt(s2, OutLiveStmt(s1, live))
      case SIf(_, t, e) => OutLiveStmt(t, live) * OutLiveStmt(e, live)
      case _ => live
    }
  }

  // Theorem 1 (Full Multi-Step Statement Soundness under Arbitrary Hint):
  // Covers SSkip, SSeq, SLet (lexical shadowing), SAssign (reassignment), SIf,
  // and all 4 Place-lowered mutations (push, indexSet, fieldSet, mapSet).
  lemma Theorem1_StmtSoundness(
    hint: int -> NarrowHint,
    s: Stmt,
    fenv: FEnv,
    jenv: JEnv,
    h: Heap,
    live: set<Var>,
    depth: nat
  )
    requires depth >= 1
    requires StateRefines(fenv, jenv, h, live, depth)
    requires StmtLiveAliasSafe(s, jenv, h, live, depth)
    ensures ExecValStmt(hint, s, fenv).Ok? ==>
            ExecJSStmt(s, jenv, h, depth).Ok? &&
            var (jenv', h') := ExecJSStmt(s, jenv, h, depth).val;
            StateRefines(ExecValStmt(hint, s, fenv).val, jenv', h', OutLiveStmt(s, live), depth)
    decreases s
  {
    if !ExecValStmt(hint, s, fenv).Ok? {
      return;
    }
    match s {
      case SSkip =>
      case SLet(x, rep, init) =>
        Theorem1_And_2_ExprSoundness(hint, init, fenv, jenv, h, live, depth);
        var Ok(fv) := EvalVal(fenv, LowerExpr(hint, init));
        Theorem4_EncodeEraseRoundtrip(rep, EraseFVal(fv));
      case SAssign(x, rep, rhs) =>
        Theorem1_And_2_ExprSoundness(hint, rhs, fenv, jenv, h, live, depth);
        var Ok(fv) := EvalVal(fenv, LowerExpr(hint, rhs));
        Theorem4_EncodeEraseRoundtrip(rep, EraseFVal(fv));
      case SMutateArrPush(x, hid, elem) =>
        Theorem1_And_2_ExprSoundness(hint, elem, fenv, jenv, h, live, depth);
        Theorem1_PushMutationSoundness(
          hint, x, hint(hid).HintUnwrap?, elem,
          fenv, jenv, h, live, live, depth
        );
      case SMutateIndexSet(x, hid, idx, rhs) =>
        Theorem1_And_2_ExprSoundness(hint, rhs, fenv, jenv, h, live, depth);
        Theorem1_IndexSetSoundness(
          hint, x, hid, idx, rhs,
          fenv, jenv, h, live, live, depth
        );
      case SMutateFieldSet(x, hid, f, rhs) =>
        Theorem1_And_2_ExprSoundness(hint, rhs, fenv, jenv, h, live, depth);
        Theorem1_FieldSetSoundness(
          hint, x, hid, f, rhs,
          fenv, jenv, h, live, live, depth
        );
      case SMutateMapSet(x, hid, key, rhs) =>
        Theorem1_And_2_ExprSoundness(hint, rhs, fenv, jenv, h, live, depth);
        Theorem1_MapSetSoundness(
          hint, x, hid, key, rhs,
          fenv, jenv, h, live, live, depth
        );
      case SIf(cond, t, e) =>
        Theorem1_And_2_ExprSoundness(hint, cond, fenv, jenv, h, live, depth);
        var Ok(FBool(b)) := EvalVal(fenv, LowerExpr(hint, cond));
        if b {
          Theorem1_StmtSoundness(hint, t, fenv, jenv, h, live, depth);
        } else {
          Theorem1_StmtSoundness(hint, e, fenv, jenv, h, live, depth);
        }
      case SSeq(s1, s2) =>
        Theorem1_StmtSoundness(hint, s1, fenv, jenv, h, live, depth);
        var Ok(fenv1) := ExecValStmt(hint, s1, fenv);
        var Ok((jenv1, h1)) := ExecJSStmt(s1, jenv, h, depth);
        Theorem1_StmtSoundness(hint, s2, fenv1, jenv1, h1, OutLiveStmt(s1, live), depth);
    }
  }

  // =========================================================================
  // 6. Concrete Sanity Lemmas (Non-Vacuity Checks)
  // =========================================================================

  // Sanity (a): An adversarial/stale flow hint claiming `x` is unwrapped when `x` is None
  // causes CoreVal to fail its check (CheckFail), rather than producing a false value!
  lemma Sanity_StaleHintFailsCheckSafely()
  {
    var staleHint: int -> NarrowHint := (_ => HintUnwrap);
    var fenv: FEnv := map["x" := FOptUndef(None)];
    var jenv: JEnv := map["x" := JUndefined];
    var h: Heap := map[];
    var e := EHinted(0, EVar("x"));
    assert StateRefines(fenv, jenv, h, {"x"}, 1);
    assert EvalVal(fenv, LowerExpr(staleHint, e)) == CheckFail;
  }

  // Sanity (b): Dead-source move (`const b = a; b.push(7); return b`) satisfies
  // NoLiveAliasAtPush because `a` is not in `liveAfter = {"b"}`, and refines JS!
  lemma Sanity_DeadSourceMoveAllowedAndSound()
  {
    var h: Heap := map[0 := HArr([JInt(1)])];
    var jenv: JEnv := map["a" := JRef(0), "b" := JRef(0)];
    var fenv: FEnv := map["a" := FArr([FInt(1)]), "b" := FArr([FInt(1)])];
    var liveBefore := {"a", "b"};
    var liveAfter := {"b"};
    assert [JInt(1)][0] == JInt(1) && [JInt(1)][1..] == [];
    assert HeapVal(h, JInt(1), 1) == Some(VInt(1));
    assert HeapSeq(h, [JInt(1)][1..], 1) == Some([]);
    assert [VInt(1)] + [] == [VInt(1)];
    assert HeapSeq(h, [JInt(1)], 1) == Some([VInt(1)]);
    assert HeapVal(h, JRef(0), 2) == Some(VArr([VInt(1)]));
    assert EraseFVal(FArr([FInt(1)])) == VArr([VInt(1)]);
    assert StateRefines(fenv, jenv, h, liveBefore, 2);
    assert NoLiveAliasAtPush("b", jenv, h, liveAfter, 2);
    var idHint: int -> NarrowHint := (_ => HintNone);
    Theorem1_PushMutationSoundness(
      idHint, "b", false, ELitInt(7),
      fenv, jenv, h, liveBefore, liveAfter, 2
    );
    var fenv' := StepVal_Push("b", false, FInt(7), fenv).value;
    var h' := StepJS_Push("b", VInt(7), jenv, h).value;
    assert StateRefines(fenv', jenv, h', liveAfter, 2);
    assert EraseFVal(fenv'["b"]) == VArr([VInt(1), VInt(7)]);
  }

  // Sanity (c): Live-alias mutation (`const b = a; b.push(7); return a`) fails
  // NoLiveAliasAtPush because `a in liveAfter` and `0 in Reachable(h, jenv["a"], 2)`.
  lemma Sanity_LiveAliasMutationRejected()
  {
    var h: Heap := map[0 := HArr([JInt(1)])];
    var jenv: JEnv := map["a" := JRef(0), "b" := JRef(0)];
    var liveAfter := {"a", "b"};
    assert 0 in Reachable(h, jenv["a"], 2);
    assert !NoLiveAliasAtPush("b", jenv, h, liveAfter, 2);
  }

  // Sanity (d): Precondition preservation on `undefined === guard(false, 1)` (must fail!)
  // vs. short-circuited `false && guard(false, true)` (must succeed!).
  lemma Sanity_GuardOnEqVsShortCircuitAnd()
  {
    var idHint: int -> NarrowHint := (_ => HintNone);
    var fenv: FEnv := map["x" := FOptUndef(None)];
    var jenv: JEnv := map["x" := JUndefined];
    var h: Heap := map[];
    assert StateRefines(fenv, jenv, h, {"x"}, 1);

    // 1. `x === guard(false, 1)` evaluates RHS in JS -> CheckFail in both JS and CoreVal.
    var eqExpr := EEq(EVar("x"), EGuard(ELitBool(false), ELitInt(1)));
    assert EvalJS(jenv, h, eqExpr, 1) == CheckFail;
    assert EvalVal(fenv, LowerExpr(idHint, eqExpr)) == CheckFail;

    // 2. `false && guard(false, true)` short-circuits in JS -> Ok(false) in both JS and CoreVal.
    var andExpr := EAnd(ELitBool(false), EGuard(ELitBool(false), ELitBool(true)));
    assert EvalJS(jenv, h, andExpr, 1) == Ok(VBool(false));
    assert EvalVal(fenv, LowerExpr(idHint, andExpr)) == Ok(FBool(false));
  }

  // Sanity (e): Narrowing-guarded mutation `if (arr !== undefined) { arr.push(7); }`
  // satisfies StmtLiveAliasSafe and Theorem1_StmtSoundness on the `None` path too
  // (untaken `then` branch is not required to satisfy NoLiveAliasAtTarget).
  lemma Sanity_NarrowingGuardedPushOnNonePath()
  {
    var unwrapHint: int -> NarrowHint := (_ => HintUnwrap);
    var fenv: FEnv := map["arr" := FOptUndef(None)];
    var jenv: JEnv := map["arr" := JUndefined];
    var h: Heap := map[];
    var live := {"arr"};
    // `cond` models `arr !== undefined` as `!(arr === undefined)` via `EEq(EVar("arr"), EUndefined)` in `else`.
    var s := SIf(EEq(EVar("arr"), EUndefined), SSkip, SMutateArrPush("arr", 0, ELitInt(7)));
    assert StateRefines(fenv, jenv, h, live, 1);
    assert EvalJS(jenv, h, EEq(EVar("arr"), EUndefined), 1) == Ok(VBool(true));
    assert StmtLiveAliasSafe(s, jenv, h, live, 1);
    Theorem1_StmtSoundness(unwrapHint, s, fenv, jenv, h, live, 1);
    assert ExecValStmt(unwrapHint, s, fenv) == Ok(fenv);
    assert ExecJSStmt(s, jenv, h, 1) == Ok((jenv, h));
  }
}
