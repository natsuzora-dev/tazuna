import Tazuna.Linter

/-! What a String means: code points up to U+2FFFF. SMT-LIB's strings (Z3's) stop there, so a value outside cannot be
built, and every string a theorem speaks of is one the solver searched. -/

namespace Tazuna

/-- The largest code point an SMT-LIB string holds. -/
def maxChar : Nat := 0x2FFFF

/-- Whether every character of `s` is at most U+2FFFF. -/
def inDomain (s : String) : Bool := s.toList.all (·.toNat ≤ maxChar)

/-- A string of tazuna's domain. -/
abbrev Str := { s : String // inDomain s = true }

theorem inDomain_append (a b : String) : inDomain (a ++ b) = (inDomain a && inDomain b) := by
  simp [inDomain, String.toList_append, List.all_append]

def Str.append (a b : Str) : Str := ⟨a.1 ++ b.1, by rw [inDomain_append, a.2, b.2]; rfl⟩

def Str.of? (s : String) : Option Str := if h : inDomain s then some ⟨s, h⟩ else none

theorem Str.of?_val (s : Str) : Str.of? s.1 = some s := by simp [Str.of?, s.2]

instance : Inhabited Str := ⟨⟨"", rfl⟩⟩

/-- A string literal as a `Str`, its domain checked by `decide`. -/
macro "str! " s:str : term => `((⟨$s, by decide⟩ : Str))

end Tazuna
