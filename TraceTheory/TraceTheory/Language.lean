import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import Mathlib.Data.List.Permutation
import Mathlib.Data.Set.Finite.Basic
import TraceTheory.Basic
import TraceTheory.Computability

namespace TraceTheory

section LexNf

variable {α : Type*} [LinearOrder α]

/-- Lexicographic Normal Form.
A word x is in normal form if it is minimal among all words equivalent to it. -/
def IsLexNf (I : Independence α) (x : List α) : Prop :=
  ∀ w, TraceEqv I x w → x ≤ w

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
  · have h_comm_au : TraceEqv I ([a] ++ u) (u ++ [a]) := by
      apply comm_append_of_indep
      intro c hc
      simp at hc
      rw [hc]
      exact h
    apply TraceEqv.compat _ (TraceEqv.refl z)
    simp only [List.append_assoc]
    apply TraceEqv.compat (TraceEqv.refl y)
    apply TraceEqv.trans (TraceEqv.compat (TraceEqv.refl [b]) (TraceEqv.symm h_comm_au))
    simp only [← List.append_assoc]
    exact TraceEqv.compat (TraceEqv.swap b a (I.symm a b h_indep)) (TraceEqv.refl u)
  · simp
    apply List.append_left_lt
    apply List.cons_lt_cons_iff.mpr
    left
    exact hlt

-- TODO: Move somewhere else?
lemma indep_and_exists_of_equiv_of_head_ne {a b : α} {w x : List α}
    (I : Independence α) (h : TraceEqv I ([a] ++ w) ([b] ++ x)) (hne : a ≠ b) :
    I.rel a b ∧ ∃ u v, x = u ++ [a] ++ v ∧ Independent I [a] u := by
  have h_rev := reverse_eqv_of_eqv h
  simp at h_rev
  have ⟨h_indep, w_rev', _, hx_rev⟩ := indep_and_exists_of_eqv_of_tail_ne h_rev hne
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
    exists_decomp_of_lt_of_len_eq hlt (length_eq_of_eqv h_equiv).symm
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

variable (I : Independence α) [Fintype α] [DecidableRel I.rel]

/-- A single symbol. -/
def Letter (a : α) : Language α :=
  { [a] }

/-- The set of all symbols. -/
def Sigma : Language α :=
  ⊤

/-- The language consisting of single letters that are independent of `a`. -/
def IndependentLetters (a : α) : Language α :=
  ∑ c ∈ (Finset.univ.filter (fun c => I.rel a c)), Letter c

/-- The "Forbidden Pattern" for a specific pair (a, b).
Pattern: Σ* b (independent of a)* a Σ* -/
def ForbiddenPattern (a b : α) : Language α :=
  Sigma∗ * Letter b * (IndependentLetters I a)∗ * Letter a * Sigma∗

/-- Union of all forbidden patterns for (a,b) ∈ I with a < b. -/
def AllForbiddenPatterns : Language α :=
  ∑ p ∈ (Finset.univ.filter (fun (p : α × α) => p.1 < p.2 ∧ I.rel p.1 p.2)),
    ForbiddenPattern I p.1 p.2

/-- LexNF is the complement of the forbidden patterns. -/
def LexNfLanguage : Language α :=
  (AllForbiddenPatterns I)ᶜ

omit [LinearOrder α] in
lemma isRegular_independentLetters (a : α) : Language.IsRegular (IndependentLetters I a) := by
  unfold IndependentLetters
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
  · apply Language.IsRegular.kstar
    apply isRegular_independentLetters
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

omit [LinearOrder α] [Fintype α] in
lemma mem_sigma (x : List α) : x ∈ (Sigma : Language α)∗ := by
  rw [Language.mem_kstar]
  use [x]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false, Sigma, forall_eq, true_and]
  apply Set.mem_univ

omit [Fintype α] [LinearOrder α] in
lemma mem_sum_language
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {f : ι → Language α} {x : List α} :
    x ∈ ∑ i ∈ S, f i ↔ ∃ i ∈ S, x ∈ f i := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi, Language.mem_add]
    rw [ih]
    constructor
    · rintro (hx | ⟨j, hj, hxj⟩)
      · exact ⟨i, Finset.mem_insert_self i S, hx⟩
      · exact ⟨j, Finset.mem_insert_of_mem hj, hxj⟩
    · rintro ⟨j, hj, hxj⟩
      simp only [Finset.mem_insert] at hj
      rcases hj with (rfl | hj)
      · left
        exact hxj
      · right
        exact ⟨j, hj, hxj⟩

lemma mem_forbiddenPattern_iff {x : List α} {a b : α} :
    x ∈ ForbiddenPattern I a b ↔
    ∃ y u z : List α, x = y ++ [b] ++ u ++ [a] ++ z ∧ (∀ c ∈ u, I.rel a c) := by
  unfold ForbiddenPattern IndependentLetters
  constructor
  · intro h
    simp [Language.mem_mul] at h
    rcases h with ⟨a1, b1, b2, b3, ⟨⟨ha1, hb1, hb2⟩, hb3⟩, ⟨x, hx, rfl⟩⟩
    use a1, b2, x
    constructor
    · simp only [Letter] at hb3 hb1
      rw [Set.mem_singleton_iff] at hb3 hb1
      subst hb3 hb1
      simp
    · intro c hc
      rw [Language.mem_kstar] at hb2
      rcases hb2 with ⟨L, rfl, hL⟩
      unfold Letter at hL
      simp only [List.mem_flatten] at hc
      rcases hc with ⟨y, hy, hcy⟩
      have hy_indep := hL y hy
      rw [mem_sum_language] at hy_indep
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy_indep
      rcases hy_indep with ⟨c', hc'_rel, hc'_eq⟩
      rw [Set.mem_singleton_iff] at hc'_eq
      subst hc'_eq
      simp only [List.mem_singleton] at hcy
      subst hcy
      exact hc'_rel
  · intro h
    rcases h with ⟨y, u, z, rfl, h_indep⟩
    simp [Language.mem_mul]
    use y, [b], u, [a]
    unfold Letter
    and_intros
    · apply mem_sigma
    · rfl
    · rw [Language.mem_kstar]
      use u.map (fun c => [c])
      constructor
      · induction u with
        | nil => rfl
        | cons hd tl ih =>
          simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
            List.cons.injEq, true_and]
          simp only [List.mem_cons, forall_eq_or_imp] at h_indep
          rw [← ih h_indep.right]
      · intro y hy
        simp only [List.mem_map] at hy
        rcases hy with ⟨c, hc, rfl⟩
        rw [mem_sum_language]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        use c, h_indep c hc
        rfl
    · rfl
    · use z
      constructor
      · apply mem_sigma
      · simp

lemma mem_allForbiddenPatterns_iff {x : List α} :
    x ∈ AllForbiddenPatterns I ↔
    ∃ a b, a < b ∧ I.rel a b ∧ x ∈ ForbiddenPattern I a b := by
  unfold AllForbiddenPatterns
  rw [mem_sum_language]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists, and_assoc]

/-- The language LexNfLanguage contains exactly the strings satisfying the factor condition. -/
theorem mem_lexNfLanguage_iff_factorCondition (x : List α) :
    x ∈ LexNfLanguage I ↔ SatisfiesFactorCondition I x := by
  unfold LexNfLanguage SatisfiesFactorCondition
  rw [Set.mem_compl_iff, mem_allForbiddenPatterns_iff]
  push_neg
  constructor
  · intro h y u z a b hx h_indep hlt
    by_contra h_all_indep
    push_neg at h_all_indep
    have h_in_pattern : x ∈ ForbiddenPattern I a b := by
      rw [mem_forbiddenPattern_iff]
      exact ⟨y, u, z, hx, h_all_indep⟩
    exact h a b hlt h_indep h_in_pattern
  · intro h a b hlt h_indep h_in_pattern
    rw [mem_forbiddenPattern_iff] at h_in_pattern
    rcases h_in_pattern with ⟨y, u, z, hx, h_all_indep⟩
    rcases h y u z a b hx h_indep hlt with ⟨c, hc_mem, hc_not_indep⟩
    exact hc_not_indep (h_all_indep c hc_mem)

omit [LinearOrder α] [Fintype α] [DecidableRel I.rel] in
lemma perm_of_traceEqv {w x : List α} (h : TraceEqv I w x) : w.Perm x := by
  induction h with
  | swap _ _ _ => apply List.Perm.swap
  | refl _ => apply List.Perm.refl
  | symm _ ih => exact List.Perm.symm ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => exact List.Perm.append ih₁ ih₂

omit [LinearOrder α] [Fintype α] [DecidableRel I.rel] in
lemma finite_traceEqv_class (w : List α) : {x : List α | TraceEqv I w x}.Finite := by
  have h_sub : {x : List α | TraceEqv I w x} ⊆ {x : List α | x ∈ w.permutations} := by
    intro x hx
    rw [Set.mem_setOf] at hx ⊢
    rw [List.mem_permutations, List.perm_comm]
    exact perm_of_traceEqv I hx
  exact Set.Finite.subset w.permutations.finite_toSet h_sub

theorem exists_lexNf_rep (t : Trace I) : ∃ s : List α, ⟦s⟧ = t ∧ s ∈ LexNfLanguage I := by
  rcases t with ⟨u⟩
  change ∃ s, ⟦s⟧ = ⟦u⟧ ∧ s ∈ LexNfLanguage I
  let S : Set (List α) := {x | TraceEqv I u x}
  have h_fin : S.Finite := finite_traceEqv_class I u
  have h_nonempty : S.Nonempty := ⟨u, TraceEqv.refl u⟩
  haveI : Fintype S := h_fin.fintype
  let S_finset := S.toFinset
  have h_finset_nonempty : S_finset.Nonempty := Set.toFinset_nonempty.mpr h_nonempty
  let s := S_finset.min' h_finset_nonempty
  have hs_mem_finset : s ∈ S_finset := Finset.min'_mem S_finset h_finset_nonempty
  have hs_eqv : TraceEqv I u s := by
    simpa [S_finset, S] using hs_mem_finset
  use s
  constructor
  · symm
    apply Quotient.sound
    exact hs_eqv
  · rw [mem_lexNfLanguage_iff_factorCondition, ← isLexNf_iff_factorCondition]
    intro s' hs'
    have hs'_mem : s' ∈ S_finset := by
      simp [S_finset, S, hs_eqv.trans hs']
    exact Finset.min'_le S_finset s' hs'_mem

end LexNf

section rank

variable {α : Type} {I : Independence α}

/-- The `Language` of all strings trace equivalent to strings in language `X`. -/
def traceClosure (I : Independence α) (X : Language α) : Language α :=
  { y | ∃ x ∈ X, TraceEqv I x y }

/-- A language is `I`-closed if its trace closure under `I` is equal to itself. -/
def IsClosed (I : Independence α) (X : Language α) : Prop :=
  traceClosure I X = X

theorem traceClosure.le_closure {X : Language α} : X ≤ traceClosure I X := by
  intro x hx
  exact ⟨x, hx, TraceEqv.refl x⟩

theorem traceClosure.mono {X Y : Language α} (h : X ≤ Y) :
    traceClosure I X ≤ traceClosure I Y := by
  intro x hx
  rcases hx with ⟨w, hw, heqv⟩
  exact ⟨w, h hw, heqv⟩

theorem traceClosure.idem {X : Language α} :
    traceClosure I (traceClosure I X) = traceClosure I X := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, ⟨z, hz, heqv_zy⟩, heqv_yx⟩
    exact ⟨z, hz, TraceEqv.trans heqv_zy heqv_yx⟩
  · apply mono
    apply le_closure

/-- Helper to define rank. -/
def IsValidFactorization
    (I : Independence α) (X : Language α) (x y : List α) (xs ys : List (List α)) : Prop :=
  xs.length = ys.length ∧
  (List.zipWith (· ++ ·) xs ys).flatten ∈ X ∧
  TraceEqv I x xs.flatten ∧
  TraceEqv I y ys.flatten ∧
  ∀ i : ℕ, ∀ (h : i + 1 < xs.length),
    Independent I (xs[i]'(Nat.lt_of_succ_lt h)) ((ys.drop i).flatten)

/-- Predicate for language `X` having rank at most `k`. -/
def HasRankAtMost (I : Independence α) (X : Language α) (k : ℕ) : Prop :=
  ∀ x y : List α, (x ++ y) ∈ traceClosure I X →
    ∃ xs ys : List (List α),
      xs.length ≤ k + 1 ∧
      IsValidFactorization I X x y xs ys

/-- Predicate for language `X` having finite rank. -/
def HasFiniteRank (I : Independence α) (X : Language α) : Prop :=
  ∃ k : ℕ, HasRankAtMost I X k

theorem concat_closed_rank (X₁ X₂ : Language α) (h₁ : IsClosed I X₁) (h₂ : IsClosed I X₂) :
    HasRankAtMost I (X₁ * X₂) 1 := by
  sorry

end rank

end TraceTheory
