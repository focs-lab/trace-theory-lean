import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.Set.Finite.Basic
import TraceTheory.Basic
import TraceTheory.Computability

namespace TraceTheory

open Computability List Trace

variable {α : Type*} {I : Independence α}

section LexNF

variable [LinearOrder α] (I : Independence α)

/-- Lexicographic Normal Form.
  A word x is in normal form if it is minimal among all words equivalent to it. -/
def IsLexNF (x : List α) : Prop :=
  ∀ w, TraceEqv I x w → x ≤ w

/-- The condition to be in Lexicographic Normal Form.
  For all factorizations x = ybuaz, where (a, b) ∈ I, and a < b,
  there exists a letter of u which does not commute with a. -/
def SatisfiesFactorCondition (x : List α) : Prop :=
  ∀ (y u z : List α) (a b : α),
    x = y ++ [b] ++ u ++ [a] ++ z →
    I.rel a b →
    a < b →
    ∃ c ∈ u, ¬ I.rel a c

lemma factorCondition_of_lexNF (x : List α) (h : IsLexNF I x) :
    SatisfiesFactorCondition I x := by
  intro y u z a b hx h_indep hlt
  contrapose! h
  unfold IsLexNF
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
    simp only [append_assoc]
    apply TraceEqv.compat (TraceEqv.refl y)
    apply TraceEqv.trans (TraceEqv.compat (TraceEqv.refl [b]) (TraceEqv.symm h_comm_au))
    simp only [← append_assoc]
    exact TraceEqv.compat (TraceEqv.swap b a (I.symm a b h_indep)) (TraceEqv.refl u)
  · simp
    apply append_left_lt
    apply cons_lt_cons_iff.mpr
    left
    exact hlt

lemma lexNF_of_factorCondition (x : List α) (h : SatisfiesFactorCondition I x) :
    IsLexNF I x := by
  unfold IsLexNF
  contrapose! h
  have ⟨w, h_equiv, hlt⟩ := h
  have ⟨p, a, b, w', x', hw, hx, hlt'⟩ :=
    exists_decomp_of_lt_of_len_eq hlt (length_eq_of_eqv h_equiv).symm
  rw [hw, hx, append_assoc, append_assoc] at h_equiv
  replace h_equiv := (append_cancel_left h_equiv).symm
  have ⟨h_indep, u, v, hx', hu⟩ := indep_and_exists_of_equiv_of_head_ne I h_equiv (ne_of_lt hlt')
  unfold SatisfiesFactorCondition
  push_neg
  simp only [hx', ← append_assoc] at hx
  use p, u, v, a, b
  apply And.intro hx
  apply And.intro h_indep
  apply And.intro hlt'
  simp at hu
  exact hu

/-- The characterization of strings in Lexicographic Normal Form. -/
theorem isLexNF_iff_factorCondition (x : List α) :
    IsLexNF I x ↔ SatisfiesFactorCondition I x := by
  constructor
  · apply factorCondition_of_lexNF
  · apply lexNF_of_factorCondition

variable [Fintype α] [DecidableRel I.rel]

/-- A single symbol. -/
def char (a : α) : Language α := { [a] }

/-- The set of all symbols. -/
def sigma : Language α := ⊤

/-- The language consisting of single letters that are independent of `a`. -/
def independentLetters (a : α) : Language α :=
  ∑ c ∈ (Finset.univ.filter (fun c => I.rel a c)), char c

/-- The "Forbidden Pattern" for a specific pair (a, b).
Pattern: Σ* b (independent of a)* a Σ* -/
def forbiddenPattern (a b : α) : Language α :=
  sigma∗ * char b * (independentLetters I a)∗ * char a * sigma∗

/-- Union of all forbidden patterns for (a,b) ∈ I with a < b. -/
def allForbiddenPatterns : Language α :=
  ∑ p ∈ (Finset.univ.filter (fun (p : α × α) => p.1 < p.2 ∧ I.rel p.1 p.2)),
    forbiddenPattern I p.1 p.2

/-- LexNF is the complement of the forbidden patterns. -/
def lexNFLanguage : Language α := (allForbiddenPatterns I)ᶜ

omit [LinearOrder α] in
lemma isRegular_independentLetters (a : α) : Language.IsRegular (independentLetters I a) := by
  unfold independentLetters
  apply Finset.sum_induction
  · apply Language.IsRegular.add
  · apply Language.IsRegular.zero
  · intro b _
    exact Language.IsRegular.singleton

omit [LinearOrder α] in
lemma isRegular_forbiddenPattern (a b : α) : Language.IsRegular (forbiddenPattern I a b) := by
  unfold forbiddenPattern sigma char
  repeat apply Language.IsRegular.mul
  · apply Language.IsRegular.kstar
    exact Language.IsRegular.top
  · exact Language.IsRegular.singleton
  · apply Language.IsRegular.kstar
    apply isRegular_independentLetters
  · exact Language.IsRegular.singleton
  · apply Language.IsRegular.kstar
    exact Language.IsRegular.top

lemma isRegular_allForbiddenPatterns : Language.IsRegular (allForbiddenPatterns I) := by
  unfold allForbiddenPatterns
  apply Finset.sum_induction
  · apply Language.IsRegular.add
  · apply Language.IsRegular.zero
  · intro ⟨a, b⟩ _
    simp
    apply isRegular_forbiddenPattern

theorem isRegular_lexNF : Language.IsRegular (lexNFLanguage I) := by
  apply Language.IsRegular.compl
  apply isRegular_allForbiddenPatterns

omit [Fintype α] [LinearOrder α] in
lemma mem_sigma (x : List α) : x ∈ (sigma : Language α)∗ := by
  rw [Language.mem_kstar]
  use [x]
  simp only [flatten_cons, flatten_nil, append_nil, mem_cons,
    not_mem_nil, or_false, sigma, forall_eq, true_and]
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
    x ∈ forbiddenPattern I a b ↔
    ∃ y u z : List α, x = y ++ [b] ++ u ++ [a] ++ z ∧ (∀ c ∈ u, I.rel a c) := by
  unfold forbiddenPattern independentLetters
  constructor
  · intro h
    simp [Language.mem_mul] at h
    rcases h with ⟨a1, b1, b2, b3, ⟨⟨ha1, hb1, hb2⟩, hb3⟩, ⟨x, hx, rfl⟩⟩
    use a1, b2, x
    constructor
    · simp only [char] at hb3 hb1
      rw [Set.mem_singleton_iff] at hb3 hb1
      subst hb3 hb1
      simp
    · intro c hc
      rw [Language.mem_kstar] at hb2
      rcases hb2 with ⟨L, rfl, hL⟩
      unfold char at hL
      simp only [mem_flatten] at hc
      rcases hc with ⟨y, hy, hcy⟩
      have hy_indep := hL y hy
      rw [mem_sum_language] at hy_indep
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy_indep
      rcases hy_indep with ⟨c', hc'_rel, hc'_eq⟩
      rw [Set.mem_singleton_iff] at hc'_eq
      subst hc'_eq
      simp only [mem_singleton] at hcy
      subst hcy
      exact hc'_rel
  · intro h
    rcases h with ⟨y, u, z, rfl, h_indep⟩
    simp [Language.mem_mul]
    use y, [b], u, [a]
    unfold char
    and_intros
    · apply mem_sigma
    · rfl
    · rw [Language.mem_kstar]
      use u.map (fun c => [c])
      constructor
      · induction u with
        | nil => rfl
        | cons hd tl ih =>
          simp only [map_cons, flatten_cons, cons_append, nil_append,
            cons.injEq, true_and]
          simp only [mem_cons, forall_eq_or_imp] at h_indep
          rw [← ih h_indep.right]
      · intro y hy
        simp only [mem_map] at hy
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
    x ∈ allForbiddenPatterns I ↔
    ∃ a b, a < b ∧ I.rel a b ∧ x ∈ forbiddenPattern I a b := by
  unfold allForbiddenPatterns
  rw [mem_sum_language]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists, and_assoc]

/-- The language LexNFLanguage contains exactly the strings satisfying the factor condition. -/
theorem mem_lexNFLanguage_iff_factorCondition (x : List α) :
    x ∈ lexNFLanguage I ↔ SatisfiesFactorCondition I x := by
  unfold lexNFLanguage SatisfiesFactorCondition
  rw [Set.mem_compl_iff, mem_allForbiddenPatterns_iff]
  push_neg
  constructor
  · intro h y u z a b hx h_indep hlt
    by_contra h_all_indep
    push_neg at h_all_indep
    have h_in_pattern : x ∈ forbiddenPattern I a b := by
      rw [mem_forbiddenPattern_iff]
      exact ⟨y, u, z, hx, h_all_indep⟩
    exact h a b hlt h_indep h_in_pattern
  · intro h a b hlt h_indep h_in_pattern
    rw [mem_forbiddenPattern_iff] at h_in_pattern
    rcases h_in_pattern with ⟨y, u, z, hx, h_all_indep⟩
    rcases h y u z a b hx h_indep hlt with ⟨c, hc_mem, hc_not_indep⟩
    exact hc_not_indep (h_all_indep c hc_mem)

/-- Words in LexNF are exactly the members of `LexNFLanguage`. -/
theorem isLexNF_iff_mem_lexNFLanguage {x : List α} :
    IsLexNF I x ↔ x ∈ lexNFLanguage I := by
  rw [mem_lexNFLanguage_iff_factorCondition]
  apply isLexNF_iff_factorCondition

omit [LinearOrder α] [Fintype α] [DecidableRel I.rel] in
lemma perm_of_traceEqv {w x : List α} (h : TraceEqv I w x) : w.Perm x := by
  induction h with
  | swap _ _ _ => apply Perm.swap
  | refl _ => apply Perm.refl
  | symm _ ih => exact Perm.symm ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => exact Perm.append ih₁ ih₂

omit [LinearOrder α] [Fintype α] [DecidableRel I.rel] in
lemma finite_traceEqv_class (w : List α) : {x : List α | TraceEqv I w x}.Finite := by
  have h_sub : {x : List α | TraceEqv I w x} ⊆ {x : List α | x ∈ w.permutations} := by
    intro x hx
    rw [Set.mem_setOf] at hx ⊢
    rw [mem_permutations, perm_comm]
    exact perm_of_traceEqv I hx
  exact Set.Finite.subset w.permutations.finite_toSet h_sub

theorem exists_lexNF_rep (t : Trace I) : ∃ s : List α, ⟦s⟧ = t ∧ s ∈ lexNFLanguage I := by
  rcases t with ⟨u⟩
  change ∃ s, ⟦s⟧ = ⟦u⟧ ∧ s ∈ lexNFLanguage I
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
  · rw [mem_lexNFLanguage_iff_factorCondition, ← isLexNF_iff_factorCondition]
    intro s' hs'
    have hs'_mem : s' ∈ S_finset := by
      simp [S_finset, S, hs_eqv.trans hs']
    exact Finset.min'_le S_finset s' hs'_mem

end LexNF

section Language

/-- A string $t$ is an iterative factor of word language $X$ if there exists left and right
  extends $u$ and $v$ such that $ut^*v$ is a subset of X. -/
def IsIterativeFactor (X : Language α) (t : List α) :=
  ∃ u v, ∀ n : ℕ, u ++ t ^ n ++ v ∈ X

/-- Maps a word language to a trace language. -/
def toTrace (I : Independence α) (X : Language α) : Set (Trace I) := Trace.mk' I '' X

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

theorem kstar_diff_one (X : Language α) : (X \ {[]})∗ = X∗ := by
  ext x
  constructor
  · intro ⟨ls, hx, hls⟩
    use ls
    simp [hx]
    exact fun y hy => Set.diff_subset (hls y hy)
  · intro ⟨ls, hls, ht⟩
    use ls.filter (!·.isEmpty)
    simp
    apply And.intro
    · simp [hls, List.flatten_filter_not_isEmpty]
    · intro y hy hyz
      exact Set.mem_diff_singleton.mpr ⟨ht y hy, hyz⟩

/-- Helper to define rank. -/
def IsValidFactorization
    (I : Independence α) (X : Language α) (x y : List α) (xs ys : List (List α)) : Prop :=
  xs.length = ys.length ∧
  (zipWith (· ++ ·) xs ys).flatten ∈ traceClosure I X ∧
  TraceEqv I x xs.flatten ∧
  TraceEqv I y ys.flatten ∧
  ∀ i j (hi : i < ys.length) (hj : j < xs.length), i < j →
    I.Independent ys[i] xs[j]

/-- Predicate for language `X` having rank at most `k`. -/
def HasRankAtMost (I : Independence α) (X : Language α) (k : ℕ) : Prop :=
  ∀ x y : List α, (x ++ y) ∈ traceClosure I X →
    ∃ xs ys : List (List α),
      xs.length ≤ k + 1 ∧
      IsValidFactorization I X x y xs ys

/-- Predicate for language `X` having finite rank. -/
def HasFiniteRank (I : Independence α) (X : Language α) : Prop :=
  ∃ k : ℕ, HasRankAtMost I X k

theorem concat_closed_rank [DecidableEq α]
    (X₁ X₂ : Language α) (h₁ : IsClosed I X₁) (h₂ : IsClosed I X₂) :
    HasRankAtMost I (X₁ * X₂) 1 := by
  intro x y hxy
  rcases hxy with ⟨w, hw, heqv⟩
  rcases hw with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  unfold IsClosed traceClosure at h₁ h₂
  rw [Language.ext_iff] at h₁ h₂
  simp only at heqv
  replace heqv := heqv.symm
  have ⟨z₁, z₂, z₃, z₄, h_indep, hx, hy, hx₁_eqv, hx₂_eqv⟩ := levi_lemma heqv
  use [z₁, z₂], [z₃, z₄]
  unfold IsValidFactorization
  and_intros
  · simp
  · simp
  · simp only [zipWith_cons_cons, zipWith_self, map_nil, flatten_cons,flatten_nil, append_nil]
    replace h₁ := h₁ (z₁ ++ z₃)
    replace h₂ := h₂ (z₂ ++ z₄)
    rw [Set.mem_setOf] at h₁ h₂
    use z₁ ++ z₃ ++ (z₂ ++ z₄)
    constructor
    · rw [Language.mem_mul]
      exact ⟨z₁ ++ z₃, h₁.mp ⟨x₁, hx₁, hx₁_eqv⟩, z₂ ++ z₄, h₂.mp ⟨x₂, hx₂, hx₂_eqv⟩, rfl⟩
    · apply TraceEqv.refl
  · simpa
  · simpa
  · intro i j
    simp only [length_cons, length_nil, zero_add, Nat.reduceAdd]
    intro hi hj hlt
    cases i with
    | zero =>
      cases j with
      | zero => contradiction
      | succ j' =>
        simp only [getElem_cons_zero, getElem_cons_succ, getElem_singleton]
        exact independent_symm h_indep
    | succ i' => omega

end Language

section TraceLanguage

/-- Kleene closure on trace languages. -/
def kstar (T : Set (Trace I)) :=
  {r | ∃ ts : List (Trace I), (∀ t' ∈ ts, t' ∈ T) ∧ r = ts.prod}

instance : KStar (Set (Trace I)) where
  kstar := kstar

/-- The connected components operator.
  Returns the language of connected components of a trace language `T`. -/
def connectedComponents (T : Set (Trace I)) : Set (Trace I) :=
  {u | Trace.IsConnected I u ∧ u ≠ 1 ∧ ∃ v, u * v ∈ T ∧ Trace.Independent u v}

theorem toTrace_kstar_comm (X : Language α) :
    toTrace I (X∗) = (toTrace I X)∗ := by
  simp [Language.kstar_def, Set.image, toTrace]
  ext t
  constructor
  · intro ⟨ws, hws, ht⟩
    induction ws generalizing t with
    | nil => exact ⟨[], by simp_all⟩
    | cons w ws' ih =>
      rw [forall_apply_eq_imp_iff] at ih
      simp only [List.mem_cons, forall_eq_or_imp] at hws
      rcases ih hws.right with ⟨ts, hts, hws'⟩
      use ⟦w⟧ :: ts
      constructor
      · rw [List.forall_mem_cons]
        exact ⟨⟨w, hws.left, rfl⟩, hts⟩
      · rw [← ht, List.prod_cons, ← hws']
        rfl
  · intro ⟨ts, hts, ht⟩
    induction ts generalizing t with
    | nil => exact ⟨[], by simp_all⟩
    | cons s ts' ih =>
      rw [forall_eq_apply_imp_iff] at ih
      simp only [List.mem_cons, forall_eq_or_imp] at hts
      rcases ih hts.right with ⟨ws, hws, hws'⟩
      rcases hts.left with ⟨w, hw⟩
      use [w] ++ ws
      constructor
      · simp only [List.cons_append, List.nil_append, List.mem_cons, forall_eq_or_imp]
        exact ⟨hw.left, hws⟩
      · rw [ht, List.prod_cons, ← hws', ← hw.right]
        rfl

theorem connectedComponents_eq_diff_one (T : Set (Trace I)) (h : ∀ t ∈ T, t.IsConnected I) :
    connectedComponents T = T \ {1} := by
  apply Set.ext
  intro t
  apply Iff.intro
  · intro ⟨ht, htz, v, htv, htv_id⟩
    simp [htz]
    replace h := h (t * v) htv
    have hvz : v = 1 := by
      by_contra hvz
      exact not_isConnected_mul_of_indep htv_id htz hvz h
    rw [hvz, mul_one] at htv
    exact htv
  · intro ⟨ht, htz⟩
    use (h t ht), htz, 1
    rw [mul_one]
    use ht
    unfold Independent
    simp [not_mem_one]

theorem kstar_diff_one' (T : Set (Trace I)) : (T \ {1})∗ = T∗ := by
  ext t
  constructor
  · intro ⟨ls, hls, ht⟩
    use ls
    simp [ht]
    exact fun y hy => Set.diff_subset (hls y hy)
  · intro ⟨ls, hls, ht⟩
    use ls.filter (!Trace.isEmpty ·)
    simp
    constructor
    · intro y hy hyz
      exact ⟨hls y hy, isEmpty_iff.ne.mp (ne_true_of_eq_false hyz)⟩
    · simp [prod_filter_not_isEmpty, ht]

end TraceLanguage

end TraceTheory
