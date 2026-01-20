import Mathlib.Data.List.Lex
import TraceTheory.Trace

open Trace

namespace Language

variable {α : Type} [LinearOrder α]

/-- Lexicographic Normal Form.
A word x is in normal form if it is minimal among all words equivalent to it. -/
def IsLexNf (I : Independence α) (x : List α) : Prop :=
  ∀ w, TraceEquiv I x w → x ≤ w

/-- The condition to be in Lexicographic Normal Form.
For all factorizations x = ybuaz, where (a, b) ∈ I, and a < b,
there exists a letter of u which does not commute with a. -/
def SatisfiesFactorCondition (I : Independence α) (x : List α) : Prop :=
  ∀ (y u z : List α) (a b : α),
    x = y ++ [b] ++ u ++ [a] ++ z →
    I.rel a b →
    a < b →
    ∃ c ∈ u, ¬ I.rel a c

lemma factorCondition_of_lexNf (I : Independence α) (x : List α) (h : IsLexNf I x) :
    SatisfiesFactorCondition I x := by
  intro y u z a b hx h_indep hlt
  contrapose! h
  unfold IsLexNf
  push_neg
  use y ++ [a] ++ [b] ++ u ++ z
  rw [hx]
  constructor
  · have h_comm_au : TraceEquiv I ([a] ++ u) (u ++ [a]) := by
      apply equiv_comm_append_of_indep
      intro c hc
      simp at hc
      rw [hc]
      exact h
    apply TraceEquiv.compat _ (TraceEquiv.refl z)
    simp only [List.append_assoc]
    apply TraceEquiv.compat (TraceEquiv.refl y)
    apply TraceEquiv.trans (TraceEquiv.compat (TraceEquiv.refl [b]) (TraceEquiv.symm h_comm_au))
    simp only [← List.append_assoc]
    exact TraceEquiv.compat (TraceEquiv.swap b a (I.symm a b h_indep)) (TraceEquiv.refl u)
  · simp
    apply List.append_left_lt
    apply List.cons_lt_cons_iff.mpr
    left
    exact hlt

lemma exists_decomp_of_lt_of_len_eq {w x : List α} (hlt : w < x) (h_len : w.length = x.length):
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

-- TODO: Move somewhere else?
lemma leftmost_occurrence {w : List α} {a : α} (h : a ∈ w) :
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

-- TODO: Move somewhere else?
lemma indep_and_decomp_of_equiv_of_head_ne {a b : α} {w x : List α}
    (I : Independence α) (h : TraceEquiv I ([a] ++ w) ([b] ++ x)) (hne : a ≠ b) :
    I.rel a b ∧ ∃ u v, x = u ++ [a] ++ v ∧ independent I [a] u := by
  have h_rev := mirror_rule h
  simp at h_rev
  have ⟨h_indep, w_rev', _, hx_rev⟩ := indep_and_decomp_of_equiv_of_tail_ne h_rev hne
  constructor
  · exact h_indep
  · have ha := (mem_iff_mem a hx_rev).mpr
    simp at ha
    have ⟨u, v, hx⟩ := leftmost_occurrence ha
    use u, v
    constructor
    · exact hx.left
    · rw [hx.left] at hx_rev
      simp only [List.reverse_append, List.reverse_cons] at hx_rev
      simp only [List.reverse_nil, List.nil_append] at hx_rev
      rw [← List.append_assoc] at hx_rev
      have h_mem_rev : a ∉ u.reverse := by
        rw [List.mem_reverse]
        exact hx.right
      have h_indep_rev := indep_of_equiv_rightmost_symbol hx_rev h_mem_rev
      simp [List.mem_reverse] at h_indep_rev ⊢
      exact h_indep_rev

lemma lexNf_of_factorCondition
    (I : Independence α) (x : List α) (h : SatisfiesFactorCondition I x) :
    IsLexNf I x := by
  unfold IsLexNf
  contrapose! h
  have ⟨w, h_equiv, hlt⟩ := h
  have ⟨p, a, b, w', x', hw, hx, hlt'⟩ :=
    exists_decomp_of_lt_of_len_eq hlt (length_eq_of_equiv h_equiv).symm
  rw [hw, hx, List.append_assoc, List.append_assoc] at h_equiv
  replace h_equiv := (equiv_cancel_left h_equiv).symm
  have ⟨h_indep, u, v, hx', hu⟩ := indep_and_decomp_of_equiv_of_head_ne I h_equiv (ne_of_lt hlt')
  unfold SatisfiesFactorCondition
  push_neg
  simp only [hx', ← List.append_assoc] at hx
  use p, u, v, a, b
  apply And.intro hx
  apply And.intro h_indep
  apply And.intro hlt'
  simp at hu
  exact hu

/-- The characterization of strings in Lexicographic Normal Form. -/
theorem isLexNf_iff_factorCondition (I : Independence α) (x : List α) :
    IsLexNf I x ↔ SatisfiesFactorCondition I x := by
  constructor
  · apply factorCondition_of_lexNf
  · apply lexNf_of_factorCondition

-- TODO proof that both NF are regular

#lint
