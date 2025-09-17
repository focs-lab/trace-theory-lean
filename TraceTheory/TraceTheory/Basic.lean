import Mathlib.Data.Finset.Basic

variable {α : Type*} [DecidableEq α]

-- An alphabet is a finite set of symbols.
abbrev Alphabet α := Finset α

namespace List

/--
  This theorem provides an induction principle for lists where the inductive step
  appends an element to the right (i.e., builds lists by snoc rather than cons).
  The intuition is that, instead of the usual head recursion, we want to prove a property
  for all lists by showing:
    - the property holds for the empty list, and
    - if it holds for a list `l`, then it holds for `l ++ [a]` for any `a`.
-/
theorem induction_right {α} {P : List α → Prop}
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

/--
  Every nonempty list `w` can be written as `w' ++ [a]` for some `w'` and `a`.
  This is a canonical example where right induction is natural:
  at each step, we peel off the last element, reducing the problem to a shorter list.
-/
example (w : List α) (h : w ≠ []) : ∃ (w' : List α) (a : α), w = w' ++ [a] := by
  induction w using induction_right with
  | nil =>
    -- Base case: contradiction, since w = [].
    contradiction
  | snoc w' a IH =>
    -- Inductive step: w = w' ++ [a]
    use w', a

/--
  The projection of a word onto an alphabet: remove all symbols not in the alphabet.
  This is a standard operation in trace theory.
-/
def proj (Sigma : Alphabet α) (w : List α) : List α :=
  match w with
  | [] => []
  | a :: w' => if a ∈ Sigma then a :: proj Sigma w' else proj Sigma w'

/--
  Projection distributes over concatenation: projecting a concatenation is the same as concatenating the projections.
-/
@[simp]
lemma proj_distrib_over_concat (Sigma : Alphabet α) (w₁ w₂ : List α) :
    proj Sigma (w₁ ++ w₂) = proj Sigma w₁ ++ proj Sigma w₂ :=
  by
    -- We proceed by induction on w₁.
    induction w₁ with
    | nil =>
      -- Base case: w₁ = [].
      -- proj Sigma ([] ++ w₂) = proj Sigma w₂, and proj Sigma [] = [], so the equality holds.
      simp [proj]
    | cons a w₁' IH =>
      -- Inductive step: w₁ = a :: w₁'.
      -- We consider whether a ∈ Sigma.
      by_cases h : a ∈ Sigma
      · -- If a ∈ Sigma, then proj Sigma (a :: (w₁' ++ w₂)) = a :: proj Sigma (w₁' ++ w₂)
        -- By induction, proj Sigma (w₁' ++ w₂) = proj Sigma w₁' ++ proj Sigma w₂
        -- So the result is a :: (proj Sigma w₁' ++ proj Sigma w₂) = (a :: proj Sigma w₁') ++ proj Sigma w₂
        simp [proj, h, IH]
      · -- If a ∉ Sigma, then a is skipped in the projection.
        -- So proj Sigma (a :: (w₁' ++ w₂)) = proj Sigma (w₁' ++ w₂)
        -- By induction, this is proj Sigma w₁' ++ proj Sigma w₂
        simp [proj, h, IH]

/--
  Projection commutes with reversal: projecting then reversing is the same as reversing then projecting.
-/
@[simp]
lemma proj_commutes_with_reverse (Sigma : Alphabet α) (w : List α) :
    reverse (proj Sigma w) = proj Sigma (reverse w) := by
  -- We proceed by induction on w.
  induction w with
  | nil =>
    -- Base case: w = [].
    -- Both sides are reverse [] = [] and proj Sigma [] = [], so equality holds.
    rfl
  | cons a w' IH =>
    -- Inductive step: w = a :: w'.
    -- Consider whether a ∈ Sigma.
    by_cases h : a ∈ Sigma
    · -- If a ∈ Sigma, then proj Sigma (a :: w') = a :: proj Sigma w'.
      -- reverse (a :: proj Sigma w') = reverse (proj Sigma w') ++ [a]
      -- By induction, reverse (proj Sigma w') = proj Sigma (reverse w')
      -- So left side is proj Sigma (reverse w') ++ [a]
      -- On the right, reverse (a :: w') = reverse w' ++ [a], so proj Sigma (reverse w' ++ [a])
      -- By proj_distrib_over_concat, this is proj Sigma (reverse w') ++ proj Sigma [a]
      -- Since a ∈ Sigma, proj Sigma [a] = [a], so both sides match.
      simp [proj, h, IH]
    · -- If a ∉ Sigma, then proj Sigma (a :: w') = proj Sigma w'.
      -- So reverse (proj Sigma w') = proj Sigma (reverse w') by induction.
      -- On the right, reverse (a :: w') = reverse w' ++ [a], proj Sigma (reverse w' ++ [a])
      -- By proj_distrib_over_concat, this is proj Sigma (reverse w') ++ proj Sigma [a]
      -- Since a ∉ Sigma, proj Sigma [a] = [], so right side is proj Sigma (reverse w')
      simp [proj, h, IH]

/--
  Cancel the first occurrence of a symbol from the left of a word.
  If the symbol is not present, the word is unchanged.
-/
def cancel_left (w : List α) (a : α) : List α :=
  match w with
  | [] => []
  | b :: w' => if a = b then w' else b :: cancel_left w' a

/--
  Left-cancelling from an empty list yields an empty list.
-/
@[simp]
lemma cancel_left_nil (a : α) : cancel_left [] a = [] := by
  -- By definition, cancel_left [] a = []
  rfl

/--
  Left-cancelling from a nonempty list: if the head matches the target, remove it; otherwise, cancellation recurses on the tail and preserves the head.
-/
@[simp]
lemma cancel_left_cons (w : List α) (a b : α) :
    cancel_left (b :: w) a = if a = b then w else b :: cancel_left w a := by
  -- By definition, cancel_left (b :: w) a = if a = b then w else b :: cancel_left w a
  rfl

/--
  If the symbol `a` is not in the alphabet, then projecting and then cancelling `a` from the left does nothing.
-/
@[simp]
lemma cancel_left_proj_eq_self_when_symb_notin_alph (Sigma : Alphabet α) (w : List α) (a : α) :
    a ∉ Sigma → cancel_left (proj Sigma w) a = proj Sigma w := by
  intro h
  -- We proceed by induction on w.
  induction w with
  | nil =>
    -- Base case: w = [].
    -- Both sides are cancel_left [] a = [] and proj Sigma [] = [], so equality holds.
    rfl
  | cons b w' IH =>
    -- Inductive step: w = b :: w'.
    -- Consider whether a = b.
    by_cases h_ab : a = b
    · -- If a = b, then in proj Sigma w, b will only appear if b ∈ Sigma.
      -- But since a ∉ Sigma, b ∉ Sigma, so proj Sigma (b :: w') = proj Sigma w'.
      -- cancel_left (proj Sigma w') a = proj Sigma w' by induction.
      have h_bS : b ∉ Sigma := h_ab ▸ h
      simp [proj, h_bS]
      exact IH
    · -- If a ≠ b, consider whether b ∈ Sigma.
      by_cases h_bS : b ∈ Sigma
      · -- If b ∈ Sigma, then proj Sigma (b :: w') = b :: proj Sigma w'.
        -- cancel_left (b :: proj Sigma w') a = b :: cancel_left (proj Sigma w') a
        -- By induction, cancel_left (proj Sigma w') a = proj Sigma w', so both sides match.
        simp [proj, h_bS]
        simp [h_ab]
        exact IH
      · -- If b ∉ Sigma, then proj Sigma (b :: w') = proj Sigma w'.
        -- cancel_left (proj Sigma w') a = proj Sigma w' by induction.
        simp [proj, h_bS]
        exact IH

/--
  Projection commutes with left-cancellation: projecting then cancelling is the same as cancelling then projecting.
-/
@[simp]
lemma proj_commutes_with_cancel_left (Sigma : Alphabet α) (w : List α) (a : α) :
    cancel_left (proj Sigma w) a = proj Sigma (cancel_left w a) := by
  -- We prove by induction on w.
  induction w with
  | nil =>
    -- Base case: w = [].
    -- Both sides are cancel_left [] a = [] and proj Sigma [] = [], so equality holds.
    rfl
  | cons b w' IH =>
    -- Inductive step: w = b :: w'.
    -- Consider whether b ∈ Sigma.
    by_cases h_bS : b ∈ Sigma
    · -- If b ∈ Sigma, then proj Sigma (b :: w') = b :: proj Sigma w'.
      simp [proj, h_bS]
      -- Now consider whether a = b.
      by_cases h_ab : a = b
      · -- If a = b, then cancel_left (b :: proj Sigma w') a = proj Sigma w'.
        -- On the right, cancel_left (b :: w') a = w', so proj Sigma w' = proj Sigma w'.
        simp [h_ab]
      · -- If a ≠ b, then cancel_left (b :: proj Sigma w') a = b :: cancel_left (proj Sigma w') a
        -- By induction, cancel_left (proj Sigma w') a = proj Sigma (cancel_left w' a)
        -- On the right, cancel_left (b :: w') a = b :: cancel_left w' a, so proj Sigma (b :: cancel_left w' a) = b :: proj Sigma (cancel_left w' a)
        simp [h_ab]
        simp [proj, h_bS]
        exact IH
    · -- If b ∉ Sigma, then proj Sigma (b :: w') = proj Sigma w'.
      by_cases h_ab : a = b
      · -- If a = b, then cancel_left (b :: w') a = w', so proj Sigma w' = proj Sigma w'.
        simp [cancel_left, h_ab]
        simp [proj, h_bS]
      · -- If a ≠ b, then cancel_left (b :: w') a = b :: cancel_left w' a, but b ∉ Sigma so proj Sigma (b :: cancel_left w' a) = proj Sigma (cancel_left w' a)
        -- By induction, cancel_left (proj Sigma w') a = proj Sigma (cancel_left w' a)
        simp [cancel_left, h_ab]
        simp [proj, h_bS]
        exact IH

/--
  Cancel the first occurrence of a symbol from the right of a word.
-/
def cancel_right (w : List α) (a : α) : List α :=
  reverse (cancel_left (reverse w) a)

/--
  Right-cancelling from an empty list yields an empty list.
-/
@[simp]
lemma cancel_right_nil (a : α) : cancel_right [] a = [] := by
  -- By definition, cancel_right [] a = reverse (cancel_left (reverse []) a) = reverse (cancel_left [] a) = reverse [] = []
  simp [cancel_right]

/--
  Right-cancelling from a nonempty list: if the last element matches the target, remove it; otherwise, cancellation recurses on the prefix and preserves the last element.
-/
@[simp]
lemma cancel_right_snoc (w : List α) (a b : α) :
    cancel_right (w ++ [b]) a = if a = b then w else cancel_right w a ++ [b] := by
  by_cases h : a = b
  · -- If a = b, then cancel_right (w ++ [b]) a = reverse (cancel_left (reverse (w ++ [b])) a)
    -- = reverse (cancel_left (reverse [b] ++ reverse w) a) = reverse (cancel_left ([b] ++ reverse w) a)
    -- = reverse (cancel_left (b :: reverse w) a) = reverse (reverse w) = w
    simp [cancel_right, h]
  · -- If a ≠ b, then cancel_right (w ++ [b]) a = reverse (cancel_left (reverse (w ++ [b])) a)
    -- = reverse (cancel_left (reverse [b] ++ reverse w) a) = reverse (cancel_left ([b] ++ reverse w) a)
    -- = reverse (cancel_left (b :: reverse w) a) = reverse (b :: cancel_left (reverse w) a) = reverse (cancel_left (reverse w) a) ++ [b] = cancel_right w a ++ [b]
    simp [cancel_right, h]

/--
  If the symbol `a` is not in the alphabet, then projecting and then cancelling `a` from the right does nothing.
-/
@[simp]
lemma cancel_right_proj_eq_self_when_symb_notin_alph (Sigma : Alphabet α) (w : List α) (a : α) :
    a ∉ Sigma → cancel_right (proj Sigma w) a = proj Sigma w := by
  induction w using induction_right with
  | nil =>
    -- Base case: w = [].
    -- Both sides are cancel_right [] a = [] and proj Sigma [] = [], so equality holds.
    simp [cancel_right, proj]
  | snoc w' b IH =>
    intro h
    by_cases h_ab : a = b
    · -- Case 1: a = b. Since a ∉ Sigma, b ∉ Sigma as well.
      -- The projection removes b, so proj Sigma (w' ++ [b]) = proj Sigma w'.
      -- Right-cancelling a from proj Sigma w is the same as right-cancelling from proj Sigma w',
      -- which by the induction hypothesis is just proj Sigma w'.
      have h_bS : b ∉ Sigma := h_ab ▸ h
      simp [proj, h_bS]
      exact IH h
    · -- Case 2: a ≠ b. Now consider whether b ∈ Sigma.
      by_cases h_bS : b ∈ Sigma
      · -- Subcase: b ∈ Sigma. Then proj Sigma (w' ++ [b]) = proj Sigma w' ++ [b].
        -- Right-cancelling a from proj Sigma w is cancel_right (proj Sigma w') a ++ [b].
        -- By the induction hypothesis, cancel_right (proj Sigma w') a = proj Sigma w', so both sides match.
        simp [proj, h_bS]
        simp [h_ab]
        exact IH h
      · -- Subcase: b ∉ Sigma. Then proj Sigma (w' ++ [b]) = proj Sigma w'.
        -- Right-cancelling a from proj Sigma w is the same as right-cancelling from proj Sigma w',
        -- which by the induction hypothesis is just proj Sigma w'.
        simp [proj, h_bS]
        exact IH h

/--
  Projection commutes with right-cancellation: projecting then cancelling is the same as cancelling then projecting.
-/
@[simp]
lemma proj_commutes_with_cancel_right (Sigma : Alphabet α) (w : List α) (a : α) :
    cancel_right (proj Sigma w) a = proj Sigma (cancel_right w a) := by
  -- The right-cancellation is defined as reversing, left-cancelling, then reversing again.
  -- Since proj and reverse commute (by proj_and_reverse_commute), the operations can be swapped.
  simp [cancel_right, proj_commutes_with_reverse]

end List
