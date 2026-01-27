import TraceTheory.Trace

namespace Trace

variable {α : Type} {I : Independence α}

lemma foldl_append_eq (a : List α) (bs : List (List α)) :
    List.foldl List.append a bs = a ++ List.foldl List.append [] bs := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bsuf b ih => simp [ih]

lemma indep_of_foldl {u : List α} {vs : List (List α)} (i : Fin vs.length) (h : independent I u (vs.foldl List.append [])) :
    independent I u vs[i] := by
  replace ⟨i, hi⟩ := i
  induction vs generalizing i with
  | nil =>
    simp at hi
  | cons v vs' ih =>
    simp at h ⊢
    rw [foldl_append_eq] at h
    cases i with
    | zero => exact (indep_of_concat h).left
    | succ i =>
      simp at hi
      exact ih (indep_of_concat h).right i hi

/-- (i) → (ii) of Corollary (2.3) in `Partial Commutation and Traces`.
  Note that t₁, t₂, …, tₙ is expressed as a list [ts], and (t₁ ++ t₂ ++ … ++ tₙ) via [ts.foldl].
  Similarly, p₁, …, pₙ is [ps] and q₁, …, qₙ is [qs]. -/
theorem levi_lemma_gen (u v : List α) (ts : List (List α)) [DecidableEq α] (h : TraceEquiv I (u ++ v) (ts.foldl List.append [])) :
    ∃ (ps qs : List (List α)),
    ps.length = ts.length
    ∧ qs.length = ts.length
    ∧ TraceEquiv I u (ps.foldl List.append [])
    ∧ TraceEquiv I v (qs.foldl List.append [])
    ∧ (∀ i : Fin (min ts.length (min ps.length qs.length)), TraceEquiv I ts[i] (ps[i] ++ qs[i]))
    ∧ ∀ i : Fin qs.length, ∀ j : Fin ps.length, i.val < j.val → independent I qs[i] ps[j] := by
  induction ts generalizing u v with
  | nil =>
    simp at h ⊢
    replace h := length_eq_of_equiv h
    simp at h
    simp [h, TraceEquiv.refl]
    intro ⟨i, hi⟩
    simp at hi
  | cons t tsuf ih =>
    have equiv_split : TraceEquiv I (u ++ v) (t ++ (tsuf.foldl List.append [])) := by
      unfold List.foldl at h
      simp at h
      rw [foldl_append_eq _ _] at h
      exact h
    have ⟨p, psuf, q, qsuf, h_ind, h_up, h_vq, h_tpq, h_tpq_suf⟩ := levi_lemma equiv_split
    replace ih := ih psuf qsuf h_tpq_suf.symm
    have ⟨ps_i, qs_i, ih_p_len, ih_q_len, ih_p, ih_q, ih_tpq, ih_ind⟩ := ih
    clear ih
    use p :: ps_i, q :: qs_i
    repeat' apply And.intro
    · simp [ih_p_len]
    · simp [ih_q_len]
    · apply TraceEquiv.trans h_up
      simp
      rw [foldl_append_eq]
      exact TraceEquiv.compat (TraceEquiv.refl p) ih_p
    · apply TraceEquiv.trans h_vq
      simp
      rw [foldl_append_eq]
      exact TraceEquiv.compat (TraceEquiv.refl q) ih_q
    · intro ⟨i, hi⟩
      by_cases hzi : i = 0
      · simp [hzi, h_tpq]
      · cases i with
        | zero => contradiction
        | succ i =>
          simp at hi ⊢
          exact ih_tpq ⟨i, by simp; exact hi⟩
    · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      cases j with
      | zero => contradiction
      | succ j =>
        cases i with
        | zero =>
          simp at hj ⊢
          have h_ind_ps := indep_of_indep_of_equiv (indep_symm h_ind) ih_p
          exact indep_of_foldl ⟨j, hj⟩ h_ind_ps
        | succ i =>
          simp at hi hj hij ⊢
          exact ih_ind ⟨i, hi⟩ ⟨j, hj⟩ hij




-- temporary scratchwork for decidable levi lemma
-- (defining a levi lemma decomposition, and then proving properties as separate theorems)

/-

def left_most_occurrence_split {w : List α} {a : α} [DecidableEq α] (h : a ∈ w) : List α × List α :=
  match w with
  | [] => by
    exfalso
    exact (List.mem_nil_iff a).mp h
  | b :: u =>
    if hab : a = b then ([], u) else
      let suf := left_most_occurrence_split (List.mem_of_ne_of_mem hab h)
      (b :: suf.1, suf.2)

lemma left_most_occurrence_eq {w : List α} {a : α} [DecidableEq α] (h : a ∈ w) :
    w = (left_most_occurrence_split h).1 ++ [a] ++ (left_most_occurrence_split h).2 ∧ a ∉ (left_most_occurrence_split h).1 := by
  induction w with
  | nil =>
    exfalso
    exact (List.mem_nil_iff a).mp h
  | cons b u ih =>
    by_cases hab : a = b
    · simp [left_most_occurrence_split, hab]
    · replace ih := (ih (List.mem_of_ne_of_mem (of_eq_false (eq_false hab)) h))
      apply And.intro
      · simp [left_most_occurrence_split, hab]
        replace ih := ih.left
        revert ih
        simp
      · simp [left_most_occurrence_split, hab]
        exact ih.right

def right_most_occurrence_split {w : List α} {a : α} [DecidableEq α] (h : a ∈ w) : List α × List α :=
  let rev_split := left_most_occurrence_split (List.mem_reverse.mpr h)
  (rev_split.2.reverse, rev_split.1.reverse)

lemma right_most_occurrence_eq {w : List α} {a : α} [DecidableEq α] (h : a ∈ w) :
    w = (right_most_occurrence_split h).1 ++ [a] ++ (right_most_occurrence_split h).2 ∧ a ∉ (right_most_occurrence_split h).2 := by
  simp [right_most_occurrence_split]
  have rev_result := left_most_occurrence_eq (List.mem_reverse.mpr h)
  simp at rev_result
  exact rev_result

structure levi_pair_result (α : Type) where
  z₁ : List α
  z₂ : List α
  z₃ : List α
  z₄ : List α

def levi_pair_decomp {u v x y : List α} [DecidableEq α] (h : TraceEquiv I (u ++ v) (x ++ y)) : levi_pair_result α :=
  match u with
  | [] => {z₁ := [], z₂ := [], z₃ := x, z₄ := y}
  | a :: u' =>
    if hax : a ∈ x then
      let (x', x'') := right_most_occurrence_split hax
      let h' : TraceEquiv I u' (x' ++ x'') := by

      let res := levi_pair_decomp ()

      sorry
    else
      sorry
  sorry


def levi_decomp (u v : List α) (ts : List (List α)) [DecidableEq α] (h : TraceEquiv I (u ++ v) (ts.foldl List.append [])) :
    List (List α) × List (List α) :=
  match ts with
  | [] => ([], [])
  | t :: tsuf =>
    let equiv_split : TraceEquiv I (u ++ v) (t ++ (tsuf.foldl List.append [])) := by
      unfold List.foldl at h
      simp at h
      rw [foldl_append_eq _ _] at h
      exact h
    let lv := levi_lemma equiv_split
    let ⟨p, psuf, q, qsuf, ⟨h_ind, h_up, h_vq, h_t, h_ih⟩⟩ := lv
    let ⟨ps, qs⟩ := levi_decomp psuf qsuf tsuf h_ih.symm
    (p :: ps, q :: qs)

lemma levi_decomp_len {u v : List α} {ts : List (List α)} {h : TraceEquiv I (u ++ v) (ts.foldl List.append [])} :
    (levi_decomp u v ts h).1.length = ts.length ∧ (levi_decomp u v ts h).2.length = ts.length := by sorry

lemma levi_decomp_UEqP {u v : List α} {ts : List (List α)} {h : TraceEquiv I (u ++ v) (ts.foldl List.append [])} :
    TraceEquiv I u ((levi_decomp u v ts h).1.foldl List.append []) := by sorry

lemma levi_decomp_VEqQ {u v : List α} {ts : List (List α)} {h : TraceEquiv I (u ++ v) (ts.foldl List.append [])} :
    TraceEquiv I v ((levi_decomp u v ts h).2.foldl List.append []) := by sorry

lemma levi_decomp_TEqPQ {u v : List α} {ts : List (List α)} {h : TraceEquiv I (u ++ v) (ts.foldl List.append [])} :
    ∀ i : Fin ts.length, TraceEquiv I ts[i]
    ((levi_decomp u v ts h).1[i]'(by simp [levi_decomp_len]) ++ (levi_decomp u v ts h).2[i]'(by simp [levi_decomp_len])) := by sorry

lemma levi_decomp_ind {u v : List α} {ts : List (List α)} {h : TraceEquiv I (u ++ v) (ts.foldl List.append [])} :
    ∀ i j : Fin ts.length, i < j →
    independent I ((levi_decomp u v ts h).1[i]'(by simp [levi_decomp_len])) ((levi_decomp u v ts h).2[i]'(by simp [levi_decomp_len])) := by sorry

-/

end Trace
