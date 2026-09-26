module LS.Runtime
module S = FStar.Sequence
module FS = FStar.FiniteSet.Base
open FStar.FiniteSet.Ambient
module FM = FStar.FiniteMap.Base
open FStar.FiniteMap.Ambient
open FStar.Real

// Arrays and strings are finite value sequences. String elements are UTF-16
// code units, matching JavaScript indexing and length, including surrogate pairs.
type codeunit = n:nat{n < 65536}
type string = S.seq codeunit
let decide (p:prop) : GTot (b:bool{b <==> p}) =
  FStar.IndefiniteDescription.strong_excluded_middle p
let eq (#a:Type) (x y:a) : GTot (b:bool{b <==> x == y}) = decide (x == y)
unfold let contains (#a:Type) (xs:S.seq a) (x:a) = decide (S.contains xs x)
let nat_of_int (x:int) : nat = if x < 0 then 0 else x
let abs (x:int) : nat = if x < 0 then -x else x
let min (a b:int) : int = if a < b then a else b
let max (a b:int) : int = if a > b then a else b
let floor_div (a:int) (b:int{b <> 0}) : int =
  if b > 0 then a / b else (-a) / (-b)
let trunc_div (a:int) (b:int{b <> 0}) : int =
  if (a < 0) <> (b < 0) then -(abs a / abs b) else abs a / abs b
let rem (a:int) (b:int{b <> 0}) : int = a - trunc_div a b * b
let slice_index (n:nat) (i:int) : r:nat{r <= n} =
  if i < 0 then max 0 (n + i) else min i n
let slice (#a:Type) (xs:S.seq a) (lo hi:int)
  : GTot (ys:S.seq a{S.length ys == max 0 (slice_index (S.length xs) hi - slice_index (S.length xs) lo)}) =
  let l = slice_index (S.length xs) lo in
  let h = slice_index (S.length xs) hi in
  if h < l then S.empty else S.drop (S.take xs h) l

let contains_append (#a:Type) (xs ys:S.seq a) (z:a)
  : Lemma (S.contains (S.append xs ys) z <==> S.contains xs z \/ S.contains ys z)
    [SMTPat (S.contains (S.append xs ys) z)] =
  let zs = S.append xs ys in
  if decide (S.contains xs z) then (
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun i -> i < S.length xs /\ S.index xs i == z) in
    assert (S.index zs i == z)
  ) else if decide (S.contains ys z) then (
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun i -> i < S.length ys /\ S.index ys i == z) in
    assert (S.index zs (S.length xs + i) == z)
  ) else if decide (S.contains zs z) then (
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun i -> i < S.length zs /\ S.index zs i == z) in
    if i < S.length xs then assert (S.index xs i == z)
    else assert (S.index ys (i - S.length xs) == z)
  )
let contains_singleton (#a:Type) (x z:a)
  : Lemma (S.contains (S.singleton x) z <==> x == z)
    [SMTPat (S.contains (S.singleton x) z)] =
  assert (S.index (S.singleton x) 0 == x)

let build_singleton (#a:Type) (x:a)
  : Lemma (S.build S.empty x == S.singleton x)
    [SMTPat (S.build S.empty x)] =
  assert (S.equal (S.build S.empty x) (S.singleton x))

let rec map (#a:Type) (#b:Type) (f:a -> GTot b) (xs:S.seq a)
  : GTot (ys:S.seq b{S.length ys == S.length xs /\
      (forall (i:nat). i < S.length xs ==> S.index ys i == f (S.index xs i))})
    (decreases (S.length xs)) =
  if S.length xs = 0 then S.empty
  else S.append (S.singleton (f (S.index xs 0))) (map f (S.drop xs 1))

let rec filter (#a:Type) (f:a -> GTot bool) (xs:S.seq a)
  : GTot (ys:S.seq a{S.length ys <= S.length xs /\
      (forall (x:a). S.contains ys x ==> S.contains xs x /\ f x)})
    (decreases (S.length xs)) =
  if S.length xs = 0 then S.empty else
  let x = S.index xs 0 in
  let tail = filter f (S.drop xs 1) in
  if f x then S.append (S.singleton x) tail else tail

let rec every (#a:Type) (f:a -> GTot bool) (xs:S.seq a)
  : GTot bool (decreases (S.length xs)) =
  if S.length xs = 0 then true else f (S.index xs 0) && every f (S.drop xs 1)
let rec some (#a:Type) (f:a -> GTot bool) (xs:S.seq a)
  : GTot bool (decreases (S.length xs)) =
  if S.length xs = 0 then false else f (S.index xs 0) || some f (S.drop xs 1)
let rec fold (#a:Type) (#b:Type) (f:b -> a -> GTot b) (z:b) (xs:S.seq a)
  : GTot b (decreases (S.length xs)) =
  if S.length xs = 0 then z else fold f (f z (S.index xs 0)) (S.drop xs 1)

let rec to_list (#a:Type) (xs:S.seq a)
  : Tot (ys:list a{FStar.List.Tot.length ys == S.length xs /\
      (forall (i:nat). i < S.length xs ==> FStar.List.Tot.index ys i == S.index xs i)})
    (decreases (S.length xs)) =
  if S.length xs = 0 then [] else S.index xs 0 :: to_list (S.drop xs 1)
let rec of_list (#a:Type) (xs:list a)
  : Tot (ys:S.seq a{S.length ys == FStar.List.Tot.length xs /\
      (forall (i:nat). i < S.length ys ==> S.index ys i == FStar.List.Tot.index xs i) /\
      (forall (x:a). S.contains ys x <==> FStar.List.Tot.memP x xs)})
    (decreases xs) =
  match xs with
  | [] -> S.empty
  | x::tl -> S.append (S.singleton x) (of_list tl)
let sequence_roundtrip (#a:Type) (xs:S.seq a)
  : Lemma (of_list (to_list xs) == xs) [SMTPat (to_list xs)] =
  assert (S.equal (of_list (to_list xs)) xs)

let to_list_injective (#a:Type) (x y:S.seq a)
  : Lemma (ensures (to_list x == to_list y <==> x == y))
    =
  if to_list x == to_list y then (
    assert (S.length x == S.length y);
    assert (forall (i:nat). i < S.length x ==> S.index x i == S.index y i);
    assert (S.equal x y)
  )

let rec bit_or (a b:nat) : Tot nat (decreases a + b) =
  if a = 0 then b else if b = 0 then a
  else 2 * bit_or (a/2) (b/2) + (if a % 2 = 1 || b % 2 = 1 then 1 else 0)
let rec bit_and (a b:nat) : Tot nat (decreases a + b) =
  if a = 0 || b = 0 then 0
  else 2 * bit_and (a/2) (b/2) + (if a % 2 = 1 && b % 2 = 1 then 1 else 0)
let rec find (#a:Type) (p:a -> GTot bool) (xs:S.seq a)
  : GTot (option a) (decreases (S.length xs)) =
  if S.length xs = 0 then None else
  let x = S.index xs 0 in
  if p x then Some x else find p (S.drop xs 1)
let rec findIndex (#a:Type) (p:a -> GTot bool) (xs:S.seq a)
  : GTot (i:int{-1 <= i /\ i < S.length xs}) (decreases (S.length xs)) =
  if S.length xs = 0 then -1 else if p (S.index xs 0) then 0 else
  let i = findIndex p (S.drop xs 1) in if i = -1 then -1 else i + 1
let index_of (#a:Type) (xs:S.seq a) (x:a) (start:int) : GTot int =
  let start = slice_index (S.length xs) start in
  let i = findIndex (fun y -> eq x y) (S.drop xs start) in
  if i = -1 then -1 else start + i
let at (#a:Type) (xs:S.seq a) (i:int) : GTot (option a) =
  let i : int = if i < 0 then S.length xs + i else i in
  if 0 <= i && i < S.length xs then Some (S.index xs i) else None
let rec flatten (#a:Type) (xs:S.seq (S.seq a))
  : GTot (S.seq a) (decreases (S.length xs)) =
  if S.length xs = 0 then S.empty else S.append (S.index xs 0) (flatten (S.drop xs 1))
let rec filter_some (#a:Type) (xs:S.seq (option a))
  : GTot (ys:S.seq a{S.length ys <= S.length xs}) (decreases (S.length xs)) =
  if S.length xs = 0 then S.empty else
  let tail = filter_some (S.drop xs 1) in
  match S.index xs 0 with
  | None -> tail
  | Some x -> S.append (S.singleton x) tail
let rec maximum (xs:S.seq int{S.length xs > 0})
  : GTot (r:int{S.contains xs r /\ (forall (i:nat). i < S.length xs ==> S.index xs i <= r) /\ (forall (x:int). S.contains xs x ==> x <= r)})
    (decreases (S.length xs)) =
  if S.length xs = 1 then S.index xs 0 else max (S.index xs 0) (maximum (S.drop xs 1))
let rec minimum (xs:S.seq int{S.length xs > 0})
  : GTot (r:int{S.contains xs r /\ (forall (i:nat). i < S.length xs ==> r <= S.index xs i) /\ (forall (x:int). S.contains xs x ==> r <= x)})
    (decreases (S.length xs)) =
  if S.length xs = 1 then S.index xs 0 else min (S.index xs 0) (minimum (S.drop xs 1))
let startsWith (s prefix:string) : GTot bool =
  S.length prefix <= S.length s && eq (S.take s (S.length prefix)) prefix
let endsWith (s suffix:string) : GTot bool =
  S.length suffix <= S.length s && eq (S.drop s (S.length s - S.length suffix)) suffix
let from_char_code (n:int) : string = S.singleton (n % 65536)

let rec string_index_of (s needle:string)
  : GTot (i:int{-1 <= i /\ i <= S.length s}) (decreases (S.length s)) =
  if startsWith s needle then 0 else
  if S.length s = 0 then -1 else
  let i = string_index_of (S.drop s 1) needle in
  if i = -1 then -1 else i + 1
let whitespace (c:codeunit) : bool =
  c = 9 || c = 10 || c = 11 || c = 12 || c = 13 || c = 32 || c = 160 ||
  c = 5760 || (8192 <= c && c <= 8202) || c = 8232 || c = 8233 ||
  c = 8239 || c = 8287 || c = 12288 || c = 65279
let rec trimStart (s:string)
  : GTot (r:string{S.length r <= S.length s /\ (S.length r > 0 ==> not (whitespace (S.index r 0)))})
    (decreases (S.length s)) =
  if S.length s = 0 then s else
  if whitespace (S.index s 0) then trimStart (S.drop s 1) else s
let rec trimEnd (s:string)
  : GTot (r:string{S.length r <= S.length s /\ (S.length r > 0 ==> not (whitespace (S.index r (S.length r - 1))))})
    (decreases (S.length s)) =
  if S.length s = 0 then s else
  if whitespace (S.index s (S.length s - 1)) then trimEnd (S.take s (S.length s - 1)) else s
let trim (s:string) : GTot (r:string{S.length r <= S.length s}) = trimEnd (trimStart s)
let rec nat_to_string (n:nat) : Tot (r:string{S.length r >= 1}) (decreases n) =
  if n < 10 then S.singleton (48 + n)
  else S.build (nat_to_string (n / 10)) (48 + n % 10)
let int_to_string (n:int) : Tot (r:string{S.length r >= 1}) =
  if n < 0 then S.append (S.singleton 45) (nat_to_string (-n)) else nat_to_string n

let rec set_from_seq (#a:eqtype) (xs:S.seq a)
  : GTot (s:FS.set a{FS.cardinality s <= S.length xs /\
      (forall x. FS.mem x s <==> S.contains xs x)}) (decreases (S.length xs)) =
  if S.length xs = 0 then FS.emptyset
  else FS.insert (S.index xs 0) (set_from_seq (S.drop xs 1))
let set_to_seq (#a:eqtype) (s:FS.set a)
  : GTot (xs:S.seq a{S.length xs == FS.cardinality s /\
      (forall x. S.contains xs x <==> FS.mem x s)}) =
  of_list (FS.set_as_list s)

let rec occurs (#a:Type) (xs:S.seq a) (x:a)
  : GTot nat (decreases (S.length xs)) =
  if S.length xs = 0 then 0 else (if eq (S.index xs 0) x then 1 else 0) + occurs (S.drop xs 1) x
let perm (#a:Type) (xs ys:S.seq a) : GTot bool =
  decide (forall (x:a). occurs xs x == occurs ys x)
let rec occurs_append (#a:Type) (xs ys:S.seq a) (x:a)
  : Lemma (ensures (occurs (S.append xs ys) x == occurs xs x + occurs ys x))
    [SMTPat (occurs (S.append xs ys) x)] (decreases (S.length xs)) =
  if S.length xs > 0 then (
    assert (S.equal (S.drop (S.append xs ys) 1) (S.append (S.drop xs 1) ys));
    occurs_append (S.drop xs 1) ys x
  ) else assert (S.equal (S.append xs ys) ys)

unfold let total_preorder (#a:Type) (cmp:a -> a -> GTot int) : prop =
  (forall (x y:a). cmp x y <= 0 \/ cmp y x <= 0) /\
  (forall (x y z:a). cmp x y <= 0 /\ cmp y z <= 0 ==> cmp x z <= 0)
unfold let sorted (#a:Type) (cmp:a -> a -> GTot int) (xs:S.seq a) : prop =
  forall (i j:nat). i < j /\ j < S.length xs ==> cmp (S.index xs i) (S.index xs j) <= 0
let sorted_prepend (#a:Type) (cmp:a -> a -> GTot int) (x:a) (xs:S.seq a)
  : Lemma (requires (sorted cmp xs /\ (forall (y:a). S.contains xs y ==> cmp x y <= 0)))
      (ensures (sorted cmp (S.append (S.singleton x) xs))) =
  let ys = S.append (S.singleton x) xs in
  let point (i j:nat) : Lemma (i < j /\ j < S.length ys ==> cmp (S.index ys i) (S.index ys j) <= 0) =
    if i < j && j < S.length ys then (
      assert (S.index ys j == S.index xs (j-1));
      if i = 0 then assert (S.contains xs (S.index xs (j-1)))
      else assert (cmp (S.index xs (i-1)) (S.index xs (j-1)) <= 0)
    )
  in
  FStar.Classical.forall_intro_2 point

let rec insert_sorted (#a:Type) (cmp:a -> a -> GTot int) (x:a) (xs:S.seq a)
  : Ghost (S.seq a)
    (requires (total_preorder cmp /\ sorted cmp xs))
    (ensures (fun ys -> S.length ys == S.length xs + 1 /\ sorted cmp ys /\
      (forall (z:a). S.contains ys z <==> z == x \/ S.contains xs z) /\
      (forall (z:a). occurs ys z == occurs xs z + (if eq x z then 1 else 0))))
    (decreases (S.length xs)) =
  if S.length xs = 0 then S.singleton x else
  let h = S.index xs 0 in
  if cmp x h <= 0 then (
    assert (forall (j:nat). j < S.length xs ==> cmp h (S.index xs j) <= 0);
    assert (forall (j:nat). j < S.length xs ==> cmp x (S.index xs j) <= 0);
    sorted_prepend cmp x xs;
    S.append (S.singleton x) xs
  ) else
  let tl = S.drop xs 1 in
  let ys = insert_sorted cmp x tl in
  assert (forall (z:a). S.contains tl z ==> cmp h z <= 0);
  assert (forall (z:a). S.contains ys z ==> cmp h z <= 0);
  sorted_prepend cmp h ys;
  S.append (S.singleton h) ys
let rec sort (#a:Type) (cmp:a -> a -> GTot int) (xs:S.seq a)
  : Ghost (S.seq a)
    (requires (total_preorder cmp))
    (ensures (fun ys -> S.length ys == S.length xs /\ sorted cmp ys /\ perm xs ys))
    (decreases (S.length xs)) =
  if S.length xs = 0 then S.empty else
  insert_sorted cmp (S.index xs 0) (sort cmp (S.drop xs 1))
