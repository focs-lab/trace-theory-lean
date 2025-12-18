import Mathlib.Computability.Language
import Mathlib.Data.Finset.Basic
namespace List

variable {α : Type} [DecidableEq α]

/-- The projection of a string onto an alpabet. Removes all symbols not in the Finset.-/
def proj (S : Finset α) (w : List α) : List α := w.filter (· ∈ S)

@[simp]
lemma proj_append (S : Finset α) (w₁ w₂ : List α) :
    proj S (w₁ ++ w₂) = proj S w₁ ++ proj S w₂ := by
  simp [proj]

@[simp]
lemma proj_reverse (S : Finset α) (w : List α) :
    reverse (proj S w) = proj S (reverse w) := by
  simp [proj]

/-- Cancel the first occurrence of a symbol (if any) from the right of a word. -/
def cancelRight (w : List α) (a : α) : List α := reverse (List.erase (reverse w) a)

/-- Notation for right cancellation. -/
infixl:65 " ÷ " => List.cancelRight

@[simp]
lemma cancelRight_nil (a : α) : [] ÷ a = [] := by rfl

@[simp]
lemma cancelRight_snoc (w : List α) (a b : α) :
    w ++ [b] ÷ a = if b = a then w else w ÷ a ++ [b] := by
  split_ifs with heq <;> simp [cancelRight, heq]

lemma append_cancelRight {w₁ w₂ : List α} (a : α) :
    (w₁ ++ w₂) ÷ a = if a ∈ w₂ then w₁ ++ (w₂ ÷ a) else (w₁ ÷ a) ++ w₂ := by
  induction w₂ using List.reverseRecOn with
  | nil =>
    simp
  | append_singleton w₂' b ih =>
    rw [← List.append_assoc, cancelRight_snoc]
    by_cases heq : b = a <;> by_cases h_mem : a ∈ w₂'
    · simp [heq]
    · simp [heq]
    · simp [heq, h_mem, ih]
    · simp [heq, h_mem, ih, Ne.symm]

@[simp]
lemma singleton_cancelRight {a : α} : [a] ÷ a = [] := by simp [cancelRight]

lemma proj_cancel_right (S : Finset α) (w : List α) (a : α) :
    proj S (w ÷ a) = if a ∈ S then proj S w ÷ a else proj S w := by
  induction w using List.reverseRecOn with
  | nil =>
    simp [proj]
  | append_singleton w' b ih =>
    split_ifs with ha <;> by_cases heq : b = a
    · simp [heq, ha, proj]
    · simp [heq, ha, ih]
      by_cases hb : b ∈ S
      · simp [proj, hb, heq]
      · simp [proj, hb]
    · simp [heq, ha, proj]
    · simp [heq, ha, ih]

end List

#lint
