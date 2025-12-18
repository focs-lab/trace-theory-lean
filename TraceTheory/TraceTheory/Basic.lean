import Mathlib.Computability.Language
import Mathlib.Data.Finset.Basic

variable {α : Type*}

namespace List

/-- This theorem provides an induction principle for lists where the inductive step
appends an element to the right (i.e., builds lists by snoc rather than cons).

The intuition is that, instead of the usual head recursion, we want to prove a property
for all lists by showing:
- the property holds for the empty list, and
- if it holds for a list `l`, then it holds for `l ++ [a]` for any `a`. -/
theorem induction_right {P : List α → Prop}
    (nil : P [])
    (snoc : ∀ (l : List α) (a : α), P l → P (l ++ [a])) :
    ∀ l : List α, P l := by
  /-
    We want to prove P l for all lists l, using right induction.
    However, Lean's built-in induction on lists is left-sided (on cons), not right-sided (on snoc).
    To overcome this, we use a classic strengthening technique:
    instead of proving just P l, we prove a stronger property
      Q l := ∀ k, P k → P (k ++ l)
    This means: if we know P holds for any prefix k, then it also holds for k ++ l.
    Proving Q l for all l is strictly stronger than just P l, but it allows us to perform induction on l (using cons),
    and at the end, we recover the original goal by taking k = [].
  -/
  intro l
  let Q := fun (l : List α) => ∀ (k : List α), P k → P (k ++ l)
  -- Base case: l = []. We must show Q []: ∀ k, P k → P (k ++ []).
  have h_base : Q [] := by
    intro k hk
    -- In this case, k ++ [] = k, so P (k ++ []) = P k, which is exactly hk.
    rw [append_nil]
    exact hk
  -- Inductive step: assume Q l', show Q (a :: l') for any a.
  have h_step : ∀ (a : α) (l' : List α), Q l' → Q (a :: l') := by
    intros a l' IH k hk
    /-
      Goal: P (k ++ (a :: l')) given P k.
      Observe: k ++ (a :: l') = (k ++ [a]) ++ l'.
      By the snoc hypothesis, from P k we get P (k ++ [a]).
      By the induction hypothesis (IH), from P (k ++ [a]) we get P ((k ++ [a]) ++ l').
      Thus, we chain these two steps to get the result.
    -/
    have hka : P (k ++ [a]) := snoc k a hk
    have : k ++ (a :: l') = (k ++ [a]) ++ l' := by simp [append_assoc]
    rw [this]
    exact IH (k ++ [a]) hka
  -- Now, by induction on l (using the usual left induction), we get Q l for all l.
  have hQ : ∀ l, Q l := by
    intro l'
    induction l' with
    | nil => exact h_base
    | cons a l'' IH => exact h_step a l'' IH
  -- Finally, to recover the original goal, specialize to k = [] and use h_nil : P [].
  exact hQ l [] nil

variable [DecidableEq α]

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

lemma cancelRight_append {w₁ w₂ : List α} (a : α) :
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
