import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Lex

open List

variable {α : Type*} [DecidableEq α]

namespace TraceTheory

/-- The projection of a string onto an alpabet. Removes all symbols not in the Finset.-/
def proj (S : Finset α) (w : List α) : List α := w.filter (· ∈ S)

@[simp]
theorem proj_append {S : Finset α} {u v : List α} :
    proj S (u ++ v) = proj S u ++ proj S v := by
  simp [proj]

@[simp]
theorem proj_reverse {S : Finset α} {w : List α} :
    reverse (proj S w) = proj S (reverse w) := by
  simp [proj]

/-- Cancel the first occurrence of a symbol (if any) from the right of a word. -/
def cancelRight (w : List α) (a : α) : List α := reverse (List.erase (reverse w) a)

/-- Notation for right cancellation. -/
infixl:65 " ÷ " => cancelRight

@[simp]
theorem cancelRight_nil {a : α} : [] ÷ a = [] :=
  rfl

lemma append_singleton_cancelRight {w : List α} {a b : α} :
    (w ++ [b]) ÷ a = if b = a then w else w ÷ a ++ [b] := by
  split_ifs with heq <;> simp [cancelRight, heq]

@[simp]
theorem append_cancelRight {u v : List α} {a : α} :
    (u ++ v) ÷ a = if a ∈ v then u ++ (v ÷ a) else (u ÷ a) ++ v := by
  induction v using List.reverseRecOn with
  | nil =>
    simp
  | append_singleton v' b ih =>
    rw [← append_assoc, append_singleton_cancelRight]
    by_cases heq : b = a <;> by_cases h_mem : a ∈ v'
    · simp [heq, append_singleton_cancelRight]
    · simp [heq, append_singleton_cancelRight]
    · simp [heq, h_mem, ih, append_singleton_cancelRight]
    · simp [heq, h_mem, ih, Ne.symm]

@[simp]
theorem singleton_cancelRight {a : α} : [a] ÷ a = [] := by
  simp [cancelRight]

theorem proj_cancelRight {S : Finset α} {w : List α} {a : α} :
    proj S (w ÷ a) = if a ∈ S then proj S w ÷ a else proj S w := by
  induction w using List.reverseRecOn with
  | nil =>
    simp [proj]
  | append_singleton w' b ih =>
    split_ifs with ha <;> by_cases heq : b = a
    · simp [heq, ha, proj]
    · simp [heq, ha, ih, Ne.symm]
      by_cases hb : b ∈ S
      · simp [heq, hb, proj, Ne.symm]
      · simp [hb, proj]
    · simp [heq, ha, proj]
    · simp [heq, ha, ih, Ne.symm]

theorem rightmost_occurrence {w : List α} {a : α} (h : a ∈ w) :
    ∃ w' w'', w = w' ++ [a] ++ w'' ∧ a ∉ w'' := by
  induction w using List.reverseRecOn with
  | nil =>
    contradiction
  | append_singleton v b ih =>
    by_cases hab : a = b
    · use v, []
      simp [hab]
    · simp [hab] at h
      have ⟨w', w'', h_concat, h_in⟩ := ih h
      use w', w'' ++ [b]
      simp [h_concat, h_in, hab]

theorem leftmost_occurrence {w : List α} {a : α} (h : a ∈ w) :
    ∃ w' w'', w = w' ++ [a] ++ w'' ∧ a ∉ w' := by
  induction w with
  | nil =>
    contradiction
  | cons b v ih =>
    by_cases hab : a = b
    · use [], v
      simp [hab]
    · simp [hab] at h
      have ⟨w', w'', h_concat, h_in⟩ := ih h
      use [b] ++ w', w''
      simp [h_concat, h_in, hab]

omit [DecidableEq α] in
theorem exists_decomp_of_lt_of_len_eq {w x : List α} [LinearOrder α]
    (hlt : w < x) (h_len : w.length = x.length):
    ∃ p a b w' x',
      w = p ++ [a] ++ w' ∧
      x = p ++ [b] ++ x' ∧
      a < b := by
  induction w generalizing x with
  | nil =>
    cases x <;> contradiction
  | cons a w' ih =>
    cases x with
    | nil =>
      contradiction
    | cons b x' =>
      cases hlt with
      | rel hab =>
        use [], a, b, w', x'
        exact ⟨rfl, rfl, hab⟩
      | cons h_lex =>
        simp at h_len
        have ⟨p', a', b', w'', x'', hw', hx', hlt'⟩ := ih (List.lex_lt.mp h_lex) h_len
        use a :: p', a', b', w'', x''
        simp [hw', hx', hlt']

end TraceTheory
