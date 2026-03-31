/-
  JSString — Lean definitions matching JavaScript string semantics.
  Used by LemmaScript-generated code.
-/

namespace JSString

/-- JS `String.indexOf(searchString)`: returns the character index of the first
    occurrence, or -1 if not found. -/
def indexOf (s : String) (sub : String) : Int :=
  let rec go (pos : String.Pos) : Int :=
    if h : pos.byteIdx < s.endPos.byteIdx then
      if s.extract pos (pos + sub.endPos) == sub then
        (s.countToPos pos).getD 0
      else
        go (s.next' pos (by omega))
    else
      -1
  termination_by s.endPos.byteIdx - pos.byteIdx
  go ⟨0⟩

/-- Convert a character index (Nat) to a String.Pos. -/
private def posOfIndex (s : String) (n : Nat) : String.Pos :=
  (List.take n s.data).asString.endPos

/-- JS `String.slice(start, end)`: extracts characters from index `start`
    up to (but not including) index `end`. Both indices are Nat. -/
def slice (s : String) (start stop : Nat) : String :=
  let startPos := posOfIndex s start
  let stopPos := posOfIndex s stop
  s.extract startPos stopPos

end JSString
