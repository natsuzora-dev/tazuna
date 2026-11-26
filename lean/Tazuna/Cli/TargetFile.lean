import Tazuna.Semantics.GenTarget

/-! The file generate writes a target's trace to: `<service>/<target words>.jsonl`, where the words read as the target's
text (`place accepted`, `event Created`, `request mail.send`) and each name in them has every byte but an ASCII
letter, digit, `_` or `-` percent-encoded, so a name holds no space, dot or slash. Distinct targets of distinct
services get distinct files (`targetFile_inj`), so no target's trace overwrites or removes another's. -/

namespace Tazuna.Cli
open Tazuna.Ir

/-- Whether a file name writes the byte as itself: an ASCII letter or digit, `_` or `-`. -/
def plainByte (n : Nat) : Bool :=
  let c := Char.ofNat n
  n < 128 && (c.isAlphanum || c == '_' || c == '-')

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

def hexValue (c : Char) : Nat := if c.toNat < 58 then c.toNat - 48 else c.toNat - 55

/-- A byte in a file name: itself where it is plain, else `%` and its two upper-case hex digits. -/
def escByte (n : Nat) : List Char :=
  if plainByte n then [Char.ofNat n] else ['%', hexDigit (n / 16), hexDigit (n % 16)]

/-- A name in a file name: each byte of its UTF-8 form escaped, so it holds no space, dot or slash. -/
def escName (s : String) : List Char := s.toUTF8.data.toList.flatMap (escByte ·.toNat)

/-- The byte a file name's text starts with, and the text after it. -/
def unescOne : List Char → Option (Nat × List Char)
  | '%' :: h :: l :: rest => some (hexValue h * 16 + hexValue l, rest)
  | c :: rest => some (c.toNat, rest)
  | [] => none

theorem escByte_facts : ∀ n < 256,
    (plainByte n = true → Char.ofNat n ≠ '%' ∧ (Char.ofNat n).toNat = n ∧ Char.ofNat n ≠ ' ' ∧ Char.ofNat n ≠ '.' ∧
      Char.ofNat n ≠ '/') ∧
    (plainByte n = false → hexValue (hexDigit (n / 16)) * 16 + hexValue (hexDigit (n % 16)) = n ∧
      ∀ c ∈ [' ', '.', '/'], hexDigit (n / 16) ≠ c ∧ hexDigit (n % 16) ≠ c) := by
  decide +kernel


theorem unescOne_escByte {n : Nat} (hn : n < 256) (rest : List Char) :
    unescOne (escByte n ++ rest) = some (n, rest) := by
  obtain ⟨hp, he⟩ := escByte_facts n hn
  unfold escByte
  cases h : plainByte n
  · simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, unescOne, (he h).1]
  · obtain ⟨hpct, hval, -⟩ := hp h
    simp only [↓reduceIte, List.cons_append, List.nil_append]
    unfold unescOne
    split
    · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 hpct
    · rename_i heq; simp only [List.cons.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; simp [hval]
    · rename_i heq; cases heq

theorem escByte_ne_nil (n : Nat) : escByte n ≠ [] := by
  unfold escByte; split <;> simp

/-- An escaped byte holds no space, dot or slash, the characters that part a target's file name. -/
theorem not_mem_escByte {n : Nat} (hn : n < 256) : ∀ c ∈ [' ', '.', '/'], c ∉ escByte n := by
  obtain ⟨hp, he⟩ := escByte_facts n hn
  intro c hc
  unfold escByte
  cases h : plainByte n
  · obtain ⟨-, hd⟩ := he h
    obtain ⟨a, b⟩ := hd c hc
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, Ne.symm a, Ne.symm b⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> decide
  · obtain ⟨-, -, a, b, d⟩ := hp h
    simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact Ne.symm a
    · exact Ne.symm b
    · exact Ne.symm d

theorem flatMap_escByte_inj : (bs bs' : List UInt8) → bs.flatMap (escByte ·.toNat) = bs'.flatMap (escByte ·.toNat) →
    bs = bs'
  | [], [], _ => rfl
  | [], b :: _, h => by simp only [List.flatMap_nil, List.flatMap_cons] at h; exact absurd (List.append_eq_nil_iff.1 h.symm).1 (escByte_ne_nil _)
  | b :: _, [], h => by simp only [List.flatMap_nil, List.flatMap_cons] at h; exact absurd (List.append_eq_nil_iff.1 h).1 (escByte_ne_nil _)
  | b :: bs, b' :: bs', h => by
    simp only [List.flatMap_cons] at h
    have h1 := unescOne_escByte b.toNat_lt (bs.flatMap (escByte ·.toNat))
    rw [h, unescOne_escByte b'.toNat_lt] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    rw [UInt8.toNat_inj.1 h1.1.symm, flatMap_escByte_inj bs bs' h1.2.symm]

theorem escName_inj {a b : String} (h : escName a = escName b) : a = b := by
  have hb := flatMap_escByte_inj _ _ h
  apply String.toByteArray_inj.1
  show a.toUTF8 = b.toUTF8
  cases ha : a.toUTF8; cases hb' : b.toUTF8
  simp only [ha, hb'] at hb
  rw [Array.toList_inj.1 hb]

theorem not_mem_escName (s : String) : ∀ c ∈ [' ', '.', '/'], c ∉ escName s := by
  intro c hc
  simp only [escName, List.mem_flatMap, not_exists, not_and]
  exact fun b _ => not_mem_escByte b.toNat_lt c hc

/-- A command's or query's name as the first word of its target's file: its escaped name, with the `e` escaped where
that spells `event`, so it never reads as an event target's first word. -/
def leadName (s : String) : List Char := if escName s = "event".toList then "%65vent".toList else escName s

theorem escName_ne_e65 (s : String) : escName s ≠ "%65vent".toList := by
  intro h
  unfold escName at h
  cases hb : s.toUTF8.data.toList with
  | nil => rw [hb] at h; cases h
  | cons b bs =>
    rw [hb, List.flatMap_cons] at h
    have h1 := unescOne_escByte b.toNat_lt (bs.flatMap (escByte ·.toNat))
    rw [h] at h1
    have hv : b.toNat = 101 := by
      have : unescOne "%65vent".toList = some (101, "vent".toList) := by decide
      rw [this] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; exact h1.1.symm
    rw [hv] at h
    have : escByte 101 = ['e'] := by decide
    rw [this] at h; cases h

theorem leadName_inj {a b : String} (h : leadName a = leadName b) : a = b := by
  unfold leadName at h
  split at h <;> split at h
  · exact escName_inj (by rename_i h1 h2; rw [h1, h2])
  · exact absurd h.symm (escName_ne_e65 b)
  · exact absurd h (escName_ne_e65 a)
  · exact escName_inj h

theorem leadName_ne_event (s : String) : leadName s ≠ "event".toList := by
  unfold leadName; split
  · decide
  · assumption

theorem not_mem_leadName (s : String) : ' ' ∉ leadName s := by
  unfold leadName; split
  · decide
  · exact not_mem_escName s ' ' (by simp)

/-- The words of a target's file name, joined by spaces: what its text reads, with each name escaped. -/
def _root_.Tazuna.Ir.GenTarget.words : GenTarget → List (List Char)
  | .accepted c => [leadName c, "accepted".toList]
  | .rejected c (some k) => [leadName c, "rejected".toList, escName k]
  | .rejected c none => [leadName c, "rejected".toList]
  | .invalid q (some r) => [leadName q, "invalid".toList, escName r]
  | .invalid q none => [leadName q, "invalid".toList, "%28a".toList, "computed".toList, "name%29".toList]
  | .answered q => [leadName q, "answered".toList]
  | .event (some k) => ["event".toList, escName k]
  | .event none => ["event".toList]
  | .request x n => ["request".toList, escName x ++ '.' :: escName n]

theorem sep_inj {c : Char} : {p q : List Char} → c ∉ p → c ∉ q → ∀ {r r' : List Char}, p ++ c :: r = q ++ c :: r' →
    p = q ∧ r = r'
  | [], [], _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], d :: _, _, hq, _, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h; exact absurd (h.1 ▸ List.mem_cons_self) hq
  | d :: _, [], hp, _, _, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h; exact absurd (h.1 ▸ List.mem_cons_self) hp
  | d :: p, e :: q, hp, hq, _, _, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := sep_inj (fun m => hp (.tail _ m)) (fun m => hq (.tail _ m)) h
    exact ⟨rfl, rfl⟩

theorem ne_dotted {w : List Char} (hw : '.' ∉ w) (x n : String) : w ≠ escName x ++ '.' :: escName n :=
  fun h => hw (h ▸ List.mem_append_right _ List.mem_cons_self)

theorem _root_.Tazuna.Ir.GenTarget.words_inj {g g' : GenTarget} (h : g.words = g'.words) : g = g' := by
  have lead : ∀ {a b}, leadName a = leadName b ↔ a = b := ⟨leadName_inj, fun h => h ▸ rfl⟩
  have esc : ∀ {a b}, escName a = escName b ↔ a = b := ⟨escName_inj, fun h => h ▸ rfl⟩
  have ev : ∀ {a}, leadName a = "event".toList ↔ False := ⟨leadName_ne_event _, False.elim⟩
  have ev' : ∀ {a}, "event".toList = leadName a ↔ False := ⟨fun h => leadName_ne_event _ h.symm, False.elim⟩
  have dot : ∀ {w : List Char}, '.' ∉ w → ∀ {x n}, (w = escName x ++ '.' :: escName n ↔ False) :=
    fun hw => ⟨ne_dotted hw _ _, False.elim⟩
  have dot' : ∀ {w : List Char}, '.' ∉ w → ∀ {x n}, (escName x ++ '.' :: escName n = w ↔ False) :=
    fun hw => ⟨fun h => ne_dotted hw _ _ h.symm, False.elim⟩
  have dotted : ∀ {x n x' n'}, escName x ++ '.' :: escName n = escName x' ++ '.' :: escName n' ↔ x = x' ∧ n = n' := by
    intro x n x' n'
    refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
    obtain ⟨h1, h2⟩ := sep_inj (not_mem_escName x '.' (by simp)) (not_mem_escName x' '.' (by simp)) h
    exact ⟨escName_inj h1, escName_inj h2⟩
  rcases g with c | ⟨c, _ | k⟩ | ⟨q, _ | r⟩ | q | (_ | k) | ⟨x, n⟩ <;>
  rcases g' with c' | ⟨c', _ | k'⟩ | ⟨q', _ | r'⟩ | q' | (_ | k') | ⟨x', n'⟩ <;>
  simp (config := {decide := true}) only [GenTarget.words, List.cons.injEq, List.cons_ne_nil, lead, esc, ev, ev',
    dotted, dot (w := "accepted".toList) (by decide), dot (w := "rejected".toList) (by decide),
    dot (w := "invalid".toList) (by decide), dot (w := "answered".toList) (by decide),
    dot' (w := "accepted".toList) (by decide), dot' (w := "rejected".toList) (by decide),
    dot' (w := "answered".toList) (by decide), and_true, and_false,
    false_and, reduceCtorEq] at h ⊢
  all_goals (try simp only [true_and] at h); all_goals (first | (subst h; rfl) | (obtain ⟨rfl, rfl⟩ := h; rfl))


/-- Words joined by spaces. -/
def joinWords : List (List Char) → List Char
  | [] => []
  | [w] => w
  | w :: w' :: ws => w ++ ' ' :: joinWords (w' :: ws)

theorem joinWords_inj : {ws ws' : List (List Char)} → (∀ w ∈ ws, ' ' ∉ w) → (∀ w ∈ ws', ' ' ∉ w) → ws ≠ [] →
    ws' ≠ [] → joinWords ws = joinWords ws' → ws = ws'
  | [], _, _, _, h, _, _ | _, [], _, _, _, h, _ => absurd rfl h
  | [w], [w'], _, _, _, _, h => by simp only [joinWords] at h; rw [h]
  | [w], w' :: v :: vs, hw, _, _, _, h => by
    simp only [joinWords] at h
    exact absurd (h ▸ List.mem_append_right _ List.mem_cons_self) (hw w List.mem_cons_self)
  | w :: v :: vs, [w'], _, hw', _, _, h => by
    simp only [joinWords] at h
    exact absurd (h.symm ▸ List.mem_append_right _ List.mem_cons_self) (hw' w' List.mem_cons_self)
  | w :: v :: vs, w' :: v' :: vs', hw, hw', _, _, h => by
    simp only [joinWords] at h
    obtain ⟨rfl, h'⟩ := sep_inj (hw w List.mem_cons_self) (hw' w' List.mem_cons_self) h
    rw [joinWords_inj (fun u hu => hw u (.tail _ hu)) (fun u hu => hw' u (.tail _ hu)) (by simp) (by simp) h']

theorem _root_.Tazuna.Ir.GenTarget.words_spaceless (g : GenTarget) : ∀ w ∈ g.words, ' ' ∉ w := by
  have e := fun s => not_mem_escName s ' ' (by simp)
  have l := not_mem_leadName
  cases g with
  | rejected c k => cases k <;> simp (config := {decide := true}) [GenTarget.words, e, l]
  | invalid q r => cases r <;> simp (config := {decide := true}) [GenTarget.words, e, l]
  | event k => cases k <;> simp (config := {decide := true}) [GenTarget.words, e]
  | _ => simp (config := {decide := true}) [GenTarget.words, e, l]

/-- Where generate writes a target's trace, relative to its directory: the service's escaped name, a slash, and the
target's words, `.jsonl`. Distinct services' distinct targets get distinct files (`targetFile_inj`). -/
def targetFile (service : String) (g : GenTarget) : String :=
  String.ofList (escName service ++ '/' :: joinWords g.words ++ ".jsonl".toList)

theorem targetFile_inj {s s' : String} {g g' : GenTarget} (h : targetFile s g = targetFile s' g') : s = s' ∧ g = g' := by
  have h := String.ofList_inj.1 h
  simp only [List.cons_append, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := sep_inj (not_mem_escName s '/' (by simp)) (not_mem_escName s' '/' (by simp)) h
  refine ⟨escName_inj h1, GenTarget.words_inj ?_⟩
  have ne : ∀ g : GenTarget, g.words ≠ [] := fun g => by cases g <;> simp [GenTarget.words] <;> split <;> simp
  exact joinWords_inj g.words_spaceless g'.words_spaceless (ne g) (ne g') (List.append_cancel_right h2)

-- Names that read like the words around them stay apart.
#guard targetFile "counter" (.accepted "add") == "counter/add accepted.jsonl"
#guard targetFile "s" (.invalid "q" none) == "s/q invalid %28a computed name%29.jsonl"
#guard targetFile "s" (.invalid "q" (some "(a computed name)")) == "s/q invalid %28a%20computed%20name%29.jsonl"
#guard targetFile "s" (.accepted "event") == "s/%65vent accepted.jsonl"
#guard targetFile "s" (.request "a.b" "c") == "s/request a%2Eb.c.jsonl"
#guard targetFile "s" (.event (some "é")) == "s/event %C3%A9.jsonl"

end Tazuna.Cli
