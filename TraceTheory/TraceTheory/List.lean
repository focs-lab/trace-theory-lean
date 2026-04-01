import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Lex

variable {α : Type*} [DecidableEq α]

namespace List

/-- The projection of a string onto an alpabet. Removes all symbols not in the Finset.-/
def proj (S : Finset α) (x : List α) : List α := x.filter (· ∈ S)

@[simp]
theorem proj_append {S : Finset α} {x y : List α} :
    (x ++ y).proj S = x.proj S ++ y.proj S := by
  simp [proj]

@[simp]
theorem proj_reverse {S : Finset α} {x : List α} :
    (x.proj S).reverse = x.reverse.proj S := by
  simp [proj]

/-- Cancel the first occurrence of a symbol (if any) from the right of a word. -/
def cancelRight (x : List α) (a : α) : List α := (x.reverse.erase a).reverse

/-- Notation for right cancellation. -/
infixl:65 " ÷ " => cancelRight

@[simp]
theorem cancelRight_nil {a : α} : [] ÷ a = [] := rfl

lemma append_singleton_cancelRight {x : List α} {a b : α} :
    (x ++ [b]) ÷ a = if b = a then x else x ÷ a ++ [b] := by
  split_ifs with heq <;> simp [cancelRight, heq]

@[simp]
theorem append_cancelRight {x y : List α} {a : α} :
    (x ++ y) ÷ a = if a ∈ y then x ++ (y ÷ a) else (x ÷ a) ++ y := by
  induction y using List.reverseRecOn with
  | nil => simp
  | append_singleton y' b ih =>
    rw [← append_assoc, append_singleton_cancelRight]
    by_cases heq : b = a <;> by_cases h_mem : a ∈ y'
    · simp [heq, append_singleton_cancelRight]
    · simp [heq, append_singleton_cancelRight]
    · simp [heq, h_mem, ih, append_singleton_cancelRight]
    · simp [heq, h_mem, ih, Ne.symm]

@[simp]
theorem singleton_cancelRight {a : α} : [a] ÷ a = [] := by simp [cancelRight]

theorem proj_cancelRight {S : Finset α} {x : List α} {a : α} :
    (x ÷ a).proj S = if a ∈ S then x.proj S ÷ a else x.proj S := by
  induction x using List.reverseRecOn with
  | nil => simp [proj]
  | append_singleton x' b ih =>
    split_ifs with ha <;> by_cases heq : b = a
    · simp [heq, ha, proj]
    · simp [heq, ha, ih, Ne.symm]
      by_cases hb : b ∈ S
      · simp [heq, hb, proj, Ne.symm]
      · simp [hb, proj]
    · simp [heq, ha, proj]
    · simp [heq, ha, ih, Ne.symm]

theorem rightmost_occurrence {x : List α} {a : α} (h : a ∈ x) :
    ∃ x' x'', x = x' ++ [a] ++ x'' ∧ a ∉ x'' := by
  induction x using List.reverseRecOn with
  | nil => contradiction
  | append_singleton y b ih =>
    by_cases heq : a = b
    · use y, []
      simp [heq]
    · simp only [mem_append, mem_cons, heq, not_mem_nil, or_self, or_false] at h
      rcases ih h with ⟨x', x'', h_concat, h_in⟩
      use x', x'' ++ [b]
      simp [h_concat, h_in, heq]

theorem leftmost_occurrence {x : List α} {a : α} (h : a ∈ x) :
    ∃ x' x'', x = x' ++ [a] ++ x'' ∧ a ∉ x' := by
  induction x with
  | nil => contradiction
  | cons b y ih =>
    by_cases hab : a = b
    · use [], y
      simp [hab]
    · simp only [mem_cons, hab, false_or] at h
      rcases ih h with ⟨x', x'', h_concat, h_in⟩
      use [b] ++ x', x''
      simp [h_concat, h_in, hab]

omit [DecidableEq α] in
theorem exists_decomp_of_lt_of_len_eq {w x : List α} [LinearOrder α]
    (hlt : w < x) (h_len : w.length = x.length):
    ∃ p a b w' x',
      w = p ++ [a] ++ w' ∧
      x = p ++ [b] ++ x' ∧
      a < b := by
  induction w generalizing x with
  | nil => cases x <;> contradiction
  | cons a w' ih =>
    cases x with
    | nil => contradiction
    | cons b x' =>
      cases hlt with
      | rel hab =>
        use [], a, b, w', x'
        exact ⟨rfl, rfl, hab⟩
      | cons h_lex =>
        simp at h_len
        rcases ih (List.lex_lt.mp h_lex) h_len with ⟨p', a', b', w'', x'', hw', hx', hlt'⟩
        use a :: p', a', b', w'', x''
        simp [hw', hx', hlt']

end List
