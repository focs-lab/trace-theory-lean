namespace List

/--
  This theorem provides an induction principle for lists where the inductive step
  appends an element to the right (i.e., builds lists by snoc rather than cons).
  The intuition is that, instead of the usual head recursion, we want to prove a property
  for all lists by showing:
    - the property holds for the empty list, and
    - if it holds for a list `l`, then it holds for `l ++ [a]` for any `a`.
-/
theorem induction_right {α : Type u} {P : List α → Prop}
    (h_nil : P [])
    (h_snoc : ∀ (l : List α) (a : α), P l → P (l ++ [a])) :
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
    rw [List.append_nil]
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
    have hka : P (k ++ [a]) := h_snoc k a hk
    have : k ++ (a :: l') = (k ++ [a]) ++ l' := by simp [List.append_assoc]
    rw [this]
    exact IH (k ++ [a]) hka
  -- Now, by induction on l (using the usual left induction), we get Q l for all l.
  have hQ : ∀ l, Q l := by
    intro l'
    induction l' with
    | nil => exact h_base
    | cons a l'' IH => exact h_step a l'' IH
  -- Finally, to recover the original goal, specialize to k = [] and use h_nil : P [].
  exact hQ l [] h_nil

end List
