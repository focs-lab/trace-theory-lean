import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import TraceTheory.Basic
import TraceTheory.Computability

namespace TraceTheory

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
      apply comm_append_of_indep
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

-- TODO: Move somewhere else?
lemma indep_and_exists_of_equiv_of_head_ne {a b : α} {w x : List α}
    (I : Independence α) (h : TraceEquiv I ([a] ++ w) ([b] ++ x)) (hne : a ≠ b) :
    I.rel a b ∧ ∃ u v, x = u ++ [a] ++ v ∧ Independent I [a] u := by
  have h_rev := reverse_equiv_of_equiv h
  simp at h_rev
  have ⟨h_indep, w_rev', _, hx_rev⟩ := indep_and_exists_of_equiv_of_tail_ne h_rev hne
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
      have h_indep_rev := indep_of_comm_singleton hx_rev h_mem_rev
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
  replace h_equiv := (append_cancel_left h_equiv).symm
  have ⟨h_indep, u, v, hx', hu⟩ := indep_and_exists_of_equiv_of_head_ne I h_equiv (ne_of_lt hlt')
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

open Computability

variable (I : Independence α) [DecidableEq α] [Fintype α] [DecidableRel I.rel]

/-- A single symbol. -/
def Letter (a : α) : Language α :=
  { [a] }

/-- The set of all symbols. -/
def Sigma : Language α :=
  ⊤

/-- The language consisting of single letters that are independent of `a`. -/
def IndependentLetters (a : α) : Language α :=
  ∑ c ∈ (Finset.univ.filter (fun c => I.rel a c)), Letter c

/-- The language of words formed only by letters independent of 'a'. -/
def IndependentStar (a : α) : Language α :=
  (IndependentLetters I a)∗

/-- The "Forbidden Pattern" for a specific pair (a, b).
Pattern: Σ* b (independent of a)* a Σ* -/
def ForbiddenPattern (a b : α) : Language α :=
  Sigma∗ * Letter b * IndependentStar I a * Letter a * Sigma∗

/-- Union of all forbidden patterns for (a,b) ∈ I with a < b. -/
def AllForbiddenPatterns : Language α :=
  ∑ p ∈ (Finset.univ.filter (fun (p : α × α) => p.1 < p.2 ∧ I.rel p.1 p.2)),
    ForbiddenPattern I p.1 p.2

/-- LexNF is the complement of the forbidden patterns. -/
def LexNfLanguage : Language α :=
  (AllForbiddenPatterns I)ᶜ

omit [LinearOrder α] in
lemma isRegular_independentStar (a : α) : Language.IsRegular (IndependentStar I a) := by
  unfold IndependentStar IndependentLetters
  apply Language.IsRegular.kstar
  apply Finset.sum_induction
  · apply Language.IsRegular.add
  · apply Language.IsRegular.zero
  · intro b _
    exact Language.IsRegular.singleton

omit [LinearOrder α] in
lemma isRegular_forbiddenPattern (a b : α) : Language.IsRegular (ForbiddenPattern I a b) := by
  unfold ForbiddenPattern Sigma Letter
  repeat apply Language.IsRegular.mul
  · apply Language.IsRegular.kstar
    exact Language.IsRegular.top
  · exact Language.IsRegular.singleton
  · apply isRegular_independentStar
  · exact Language.IsRegular.singleton
  · apply Language.IsRegular.kstar
    exact Language.IsRegular.top

lemma isRegular_allForbiddenPatterns : Language.IsRegular (AllForbiddenPatterns I) := by
  unfold AllForbiddenPatterns
  apply Finset.sum_induction
  · apply Language.IsRegular.add
  · apply Language.IsRegular.zero
  · intro ⟨a, b⟩ _
    simp
    apply isRegular_forbiddenPattern

theorem isRegular_lexNf : Language.IsRegular (LexNfLanguage I) := by
  apply Language.IsRegular.compl
  apply isRegular_allForbiddenPatterns
