import «stringIndex.types»

namespace StringIndexExample

theorem index_eq_slice (s : String) (i : Int) (hlo : 0 ≤ i) (hhi : i < s.length) :
    JSString.index s i = JSString.slice s i (i + 1) := by
  have hbound : i.toNat < s.toList.length := by
    simp only [String.length_toList]
    omega
  have hlen : (i + 1).toNat - i.toNat = 1 := by omega
  unfold JSString.index JSString.slice
  rw [hlen, List.drop_eq_getElem_cons hbound]
  rw [getElem!_pos s.toList i.toNat hbound, String.singleton_eq_ofList]
  simp only [List.take_succ_cons, List.take_zero]

theorem index_length (s : String) (i : Int) : (JSString.index s i).length = 1 := by
  simp [JSString.index, String.length_singleton]

end StringIndexExample
