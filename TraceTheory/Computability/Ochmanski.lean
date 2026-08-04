import Mathlib.Algebra.Group.PUnit
import TraceTheory.Computability.Hashiguchi
import TraceTheory.Computability.RegularExpressions
import TraceTheory.Computability.ConnectedComponents

namespace TraceTheory

open scoped Pointwise

open Computability Dependence RegularExpression Trace Independence

variable {α : Type} {I : Independence α}

set_option backward.isDefEq.respectTransparency false

/-
  Main component of Theorem 4.1 (ii) => (iii).

  For a rational expression X, if every iterative factor of L(X) is connected,
  then X' is star-connected (for some rational expression X' with L(X) = L(X')).

  It is strictly necessary that we use an X' not necessarily equal to X.
  Consider X = {a ∪ b}∗ · ∅; where `a` and `b` are not connected. Then L(X) = ∅ so every
  iterative factor is connected, but X is not star-connected.

  Note that P · ∅ or ∅ · P are the only cases where this patch is needed.
-/
lemma exists_starConnected_of_connectedIterativeFactors_aux
    (X : RegularExpression α)
    (hconn : ∀ s, IsIterativeFactor X.matches' s → Trace.IsConnected I ⟦s⟧) :
    ∃ Y, IsStarConnected I Y ∧ X.matches' = Y.matches' := by
  induction X with
  | zero => use zero, trivial
  | epsilon => use epsilon, trivial
  | char a => use .char a, trivial
  | plus P Q ihP ihQ =>
    obtain ⟨P', hP'⟩ := ihP fun s ⟨u, v, h⟩ => hconn s ⟨u, v, fun n => .inl (h n)⟩
    obtain ⟨Q', hQ'⟩ := ihQ fun s ⟨u, v, h⟩ => hconn s ⟨u, v, fun n => .inr (h n)⟩
    exact ⟨P' + Q', by simp [IsStarConnected, hP', hQ']⟩
  | comp P Q ihP ihQ =>
    rcases P.matches'.eq_empty_or_nonempty with hp | ⟨p, hp⟩
    · use zero
      simp only [IsStarConnected, matches', hp, true_and]
      rw [Set.empty_mul]
      rfl
    rcases Q.matches'.eq_empty_or_nonempty with hq | ⟨q, hq⟩
    · use zero
      simp only [IsStarConnected, matches', hq, true_and]
      rw [Set.mul_empty]
      rfl
    obtain ⟨P', hP'⟩ :=
      ihP fun s ⟨u, v, h⟩ =>
      hconn s ⟨u, v ++ q, fun n => ⟨_, h n, q, hq, by simp [← List.append_assoc]⟩⟩
    obtain ⟨Q', hQ'⟩ :=
      ihQ fun s ⟨u, v, h⟩ =>
      hconn s ⟨p ++ u, v, fun n => ⟨p, hp, _, h n, by simp [List.append_assoc]⟩⟩
    exact ⟨P' * Q', by simp [IsStarConnected, hP', hQ']⟩
  | star P ih =>
    obtain ⟨P', hP'⟩ :=
      ih fun s ⟨u, v, h⟩ =>
      hconn s ⟨u, v, fun n => ⟨[u ++ s ^ n ++ v], by simp_all [List.append_assoc]⟩⟩
    use P'.star
    simp [IsStarConnected, hP']
    intro s hs
    apply hconn s
    use [], []
    intro n
    simp only [matches', List.nil_append, List.append_nil, Language.mem_kstar]
    use List.replicate n s
    constructor
    · induction n with
      | zero =>
        simp only [pow_zero, List.replicate_zero, List.flatten_nil]
        rfl
      | succ n' ih =>
        rw [add_comm, pow_add, List.replicate_add, ih]
        rfl
    · simp_all

/-- Theorem 4.1 (ii) => (iii) -/
theorem exists_starConnected_of_connectedIterativeFactors
    (T : Set (Trace I)) (X : RegularExpression α)
    (himg : T = toTrace I X.matches')
    (hconn : ∀ s, IsIterativeFactor X.matches' s → Trace.IsConnected I ⟦s⟧) :
    ∃ P, IsStarConnected I P ∧ T = P.traceMatches I := by
  simp only [traceMatches_toTrace]
  rcases exists_starConnected_of_connectedIterativeFactors_aux X hconn with ⟨P, hP⟩
  use P
  simp [hP, himg]

/-- Theorem 4.1 (iii) => (iv) -/
theorem cRational_of_isStarConnected (X : RegularExpression α) (h : IsStarConnected I X) :
    X.traceMatches I = X.cRatMatches I := by
  induction X with
  | zero => simp [traceMatches, cRatMatches]
  | epsilon => simp [traceMatches, cRatMatches]
  | char _ => simp [traceMatches, cRatMatches]
  | plus P Q ihP ihQ => simp [traceMatches, cRatMatches, ihP h.1, ihQ h.2]
  | comp P Q ihP ihQ => simp [traceMatches, cRatMatches, ihP h.1, ihQ h.2]
  | star P ih =>
    unfold traceMatches cRatMatches
    unfold IsStarConnected at h
    rw [← ih h.left]
    have hP_conn : ∀ t ∈ traceMatches I P, t.IsConnected I := by
      intro t ht
      rw [traceMatches_toTrace] at ht
      simp only [toTrace, Set.mem_image] at ht
      rcases ht with ⟨s, hs, rfl⟩
      exact h.right s hs
    rw [connectedComponents_eq_diff_one _ hP_conn]
    rw [kstar_diff_one']

lemma recognizable_zero : IsRecognizable (∅ : Set (Trace I)) :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, by simp⟩

inductive EpsMonoid
  | one
  | dead
deriving DecidableEq, Fintype

instance : Monoid EpsMonoid where
  one := .one
  mul
  | .one, x => x
  | .dead, _ => .dead
  mul_one x := by cases x <;> rfl
  one_mul x := by cases x <;> rfl
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl

def eps_map_aux : List α → EpsMonoid
  | [] => .one
  | _ :: _ => .dead

lemma eps_map_aux_append (x y : List α) :
    eps_map_aux (x ++ y) = eps_map_aux x * eps_map_aux y := by
  cases x <;> cases y <;> rfl

def eps_map : Trace I →* EpsMonoid where
  toFun := Quotient.lift
    eps_map_aux
    (by
      intro a b
      cases a <;> cases b
      · simp
      · intro heqv
        apply length_eq_of_eqv at heqv
        simp at heqv
      · intro heqv
        apply length_eq_of_eqv at heqv
        simp at heqv
      · simp [eps_map_aux]
    )
  map_one' := rfl
  map_mul' := by
    rintro ⟨x⟩ ⟨y⟩
    exact eps_map_aux_append x y

lemma recognizable_epsilon : IsRecognizable ({ 1 } : Set (Trace I)) := by
  use EpsMonoid, inferInstance, inferInstance, inferInstance, eps_map
  simp only [Set.image_singleton, map_one]
  ext t
  rcases t with ⟨w⟩
  change ⟦w⟧ ∈ {1} ↔ ⟦w⟧ ∈ ⇑eps_map ⁻¹' {1}
  constructor
  · intro h
    rw [h, Set.mem_preimage, map_one, Set.mem_singleton_iff]
  · intro h
    cases w with
    | nil =>
      rw [Set.mem_singleton_iff]
      rfl
    | cons a w' =>
      have h_map : eps_map (I := I) ⟦a :: w'⟧ = eps_map (I := I) ⟦[a]⟧ * eps_map (I := I) ⟦w'⟧ := rfl
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h
      rw [h_map] at h
      have h_dead : eps_map (I := I) ⟦[a]⟧ = EpsMonoid.dead := rfl
      rw [h_dead] at h
      contradiction

inductive CharMonoid
  | one
  | saw_a
  | dead
deriving DecidableEq, Fintype

instance : Monoid CharMonoid where
  one := .one
  mul
  | .one, x => x
  | x, .one => x
  | _, _ => .dead
  mul_one x := by cases x <;> rfl
  one_mul x := by cases x <;> rfl
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl

def char_map_aux [DecidableEq α] (a : α) : List α → CharMonoid
  | [] => .one
  | c :: w => (if c = a then .saw_a else .dead) * char_map_aux a w

lemma char_map_aux_append [DecidableEq α] (a : α) (x y : List α) :
    char_map_aux a (x ++ y) = char_map_aux a x * char_map_aux a y := by
  induction x with
  | nil =>
    simp only [char_map_aux]
    rfl
  | cons b x' ih => simp [char_map_aux, ih, mul_assoc]

def char_map [DecidableEq α] (a : α) : Trace I →* CharMonoid where
  toFun := Quotient.lift
    (char_map_aux a)
    (by
      intro b c heqv
      induction heqv with
      | swap e f hrel =>
        by_cases hea : e = a <;> by_cases hfa : f = a
        · subst hea hfa
          rfl
        · subst hea
          simp only [char_map_aux, ↓reduceIte, hfa]
          rfl
        · subst hfa
          simp only [char_map_aux, ↓reduceIte, hea]
          rfl
        · simp only [char_map_aux, ↓reduceIte, hea, hfa]
      | refl => rfl
      | symm _ ih => exact ih.symm
      | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
      | compat _ _ ih₁ ih₂ => rw [char_map_aux_append, char_map_aux_append, ih₁, ih₂]
    )
  map_one' := rfl
  map_mul' := by
    rintro ⟨x⟩ ⟨y⟩
    exact char_map_aux_append a x y

lemma recognizable_char [DecidableEq α] (a : α) : IsRecognizable ({ ⟦[a]⟧ } : Set (Trace I)) := by
  use CharMonoid, inferInstance, inferInstance, inferInstance, char_map a
  simp only [Set.image_singleton]
  ext t
  rcases t with ⟨w⟩
  change ⟦w⟧ ∈ {⟦[a]⟧} ↔ ⟦w⟧ ∈ ⇑(char_map a) ⁻¹' {(char_map a) ⟦[a]⟧}
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro h
    rw [h]
  · intro h
    rcases w with _ | ⟨b, _ | ⟨c, w'⟩⟩
    · simp [char_map, char_map_aux, -mk_nil] at h
    · simp_all [char_map, char_map_aux]
    · simp [char_map, char_map_aux] at h
      split_ifs at h
      all_goals (
        generalize hw' : char_map_aux a w' = x at h
        cases x
        all_goals (simp at h)
      )

lemma recognizable_union {M : Type} [Monoid M] {P Q : Set M}
    (hP : IsRecognizable P) (hQ : IsRecognizable Q) : IsRecognizable (P ∪ Q) := by
  rcases hP with ⟨F_P, hFin_P, hMon_P, hDec_P, f_P, hP_eq⟩
  rcases hQ with ⟨F_Q, hFin_Q, hMon_Q, hDec_Q, f_Q, hQ_eq⟩
  use F_P × F_Q, inferInstance, inferInstance, inferInstance, MonoidHom.prod f_P f_Q
  ext x
  simp only [Set.mem_union, MonoidHom.prod_apply, Set.mem_preimage, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro (h | h)
    · exact ⟨x, Or.inl h, rfl, rfl⟩
    · exact ⟨x, Or.inr h, rfl, rfl⟩
  · rintro ⟨y, (hy | hy), hyp, hyq⟩
    · left
      rw [hP_eq, Set.mem_preimage]
      exact ⟨y, hy, hyp⟩
    · right
      rw [hQ_eq, Set.mem_preimage]
      exact ⟨y, hy, hyq⟩

lemma recognizable_mul {P Q : Set (Trace I)} [DecidableEq α] [Fintype α]
    (hP : IsRecognizable P) (hQ : IsRecognizable Q) : IsRecognizable (P * Q) := by
  let L_P : Language α := Trace.mk' I ⁻¹' P
  let L_Q : Language α := Trace.mk' I ⁻¹' Q
  have hL_P_reg : L_P.IsRegular :=
    isRegular_of_recognizable (recognizable_has_recognizablePreImage _ hP)
  have hL_Q_reg : L_Q.IsRegular :=
    isRegular_of_recognizable (recognizable_has_recognizablePreImage _ hQ)
  have hL_P_closed : IsClosed I L_P := by
    apply le_antisymm
    · rintro x ⟨y, hy, heqv⟩
      simp only [L_P, Set.mem_preimage] at hy ⊢
      have heq : Trace.mk' I y = Trace.mk' I x := Quotient.sound heqv
      rw [← heq]
      exact hy
    · exact traceClosure.le_closure
  have hL_Q_closed : IsClosed I L_Q := by
    apply le_antisymm
    · rintro x ⟨y, hy, heqv⟩
      simp only [L_Q, Set.mem_preimage] at hy ⊢
      have heq : Trace.mk' I y = Trace.mk' I x := Quotient.sound heqv
      rw [← heq]
      exact hy
    · exact traceClosure.le_closure
  have h_mul_reg : (L_P * L_Q).IsRegular := Language.IsRegular.mul hL_P_reg hL_Q_reg
  have h_rank : HasFiniteRank I (L_P * L_Q) :=
    ⟨1, concat_closed_rank L_P L_Q hL_P_closed hL_Q_closed⟩
  have h_hash := recognizable_image_of_regular_finite_rank h_mul_reg h_rank
  have h_image_eq : Trace.mk' I '' (L_P * L_Q) = P * Q := by
    ext t
    constructor
    · rintro ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
      exact ⟨⟦u⟧, hu, ⟦v⟧, hv, rfl⟩
    · rintro ⟨⟨u⟩, ht₁, ⟨v⟩, ht₂, rfl⟩
      exact ⟨u ++ v, ⟨u, ht₁, v, ht₂, rfl⟩, rfl⟩
  rw [← h_image_eq]
  exact h_hash

abbrev AlphMonoid (α : Type) := Finset α

instance [DecidableEq α] : Monoid (AlphMonoid α) where
  one := ∅
  mul x y := x ∪ y
  mul_assoc x y z := Finset.union_assoc x y z
  one_mul x := Finset.empty_union x
  mul_one x := Finset.union_empty x

def alph_map_aux [DecidableEq α] (w : List α) : AlphMonoid α :=
  w.toFinset

lemma alph_map_aux_append [DecidableEq α] (x y : List α) :
    alph_map_aux (x ++ y) = alph_map_aux x * alph_map_aux y := by
  apply List.toFinset_append

def alph_map [DecidableEq α] : Trace I →* AlphMonoid α where
  toFun := Quotient.lift
    alph_map_aux
    (by
      intro u v heqv
      dsimp [alph_map_aux]
      ext a
      simp only [List.mem_toFinset]
      exact mem_iff_mem a heqv
    )
  map_one' := rfl
  map_mul' := by
    rintro ⟨x⟩ ⟨y⟩
    exact alph_map_aux_append x y

lemma alph_map_eq_iff_mems_eq [DecidableEq α] {t t' : Trace I} :
    alph_map t = alph_map t' ↔ ∀ a, a ∈ t ↔ a ∈ t' := by
  rcases t with ⟨w⟩
  rcases t' with ⟨w'⟩
  change w.toFinset = w'.toFinset ↔ _
  simp only [Finset.ext_iff, List.mem_toFinset]
  rfl

lemma lift_dependency_path [DecidableEq α] {t t' : Trace I} (h_mem_eq : ∀ a, a ∈ t' ↔ a ∈ t)
    (x y : α) (h_path : t'.DepPath x y) :
    t.DepPath x y := by
  induction h_path with
  | single h_dep =>
    apply Relation.TransGen.single
    have ⟨hxz, hx, hz⟩ := h_dep
    exact ⟨hxz, (h_mem_eq x).mp hx, (h_mem_eq _).mp hz⟩
  | tail path step ih =>
    apply Relation.TransGen.tail ih
    have ⟨hxz, hx, hz⟩ := step
    exact ⟨hxz, (h_mem_eq _).mp hx, (h_mem_eq _).mp hz⟩

lemma recognizable_connectedComponents {P : Set (Trace I)} [DecidableEq α] [Fintype α]
    (hP : IsRecognizable P) : IsRecognizable (connectedComponents P) := by
  rcases hP with ⟨M, hFin, hMon, hDec, f_P, hP_eq⟩
  use M × AlphMonoid α, inferInstance, inferInstance, inferInstance
  use MonoidHom.prod f_P (alph_map (I := I))
  ext t
  simp only [MonoidHom.prod_apply, Set.mem_preimage, Set.mem_image, Prod.ext_iff]
  constructor
  · intro h
    exact ⟨t, h, rfl, rfl⟩
  · rintro ⟨t', ht', h_f_eq, h_alph_eq⟩
    have h_mem_eq : ∀ a, a ∈ t' ↔ a ∈ t := by
      intro a
      have h_alph := alph_map_eq_iff_mems_eq.mp h_alph_eq
      exact h_alph a
    have h_conn : t.IsConnected I := by
      intro a ha b hb
      apply lift_dependency_path h_mem_eq
      rw [← h_mem_eq] at ha hb
      exact ht'.1 a ha b hb
    have h_neq_1 : t ≠ 1 := by
      intro ht_eq_1
      subst ht_eq_1
      have ht'_eq_1 : t' = 1 := by
        by_contra ht'_neq_1
        rcases t'.exists_mem_of_ne_one ht'_neq_1 with ⟨a, ha⟩
        exact not_mem_one a ((h_mem_eq a).mp ha)
      exact ht'.2.1 ht'_eq_1
    rcases ht'.2.2 with ⟨v, hv_in_P, h_indep_t'_v⟩
    have hv_in_P_t : t * v ∈ P := by
      have h_f_mul : f_P (t * v) = f_P (t' * v) := by
        simp only [map_mul, h_f_eq.symm]
      rw [hP_eq, Set.mem_preimage] at hv_in_P ⊢
      rw [← h_f_mul] at hv_in_P
      exact hv_in_P
    have h_indep_t_v : t.Independent v := by
      intro a ha b hb
      exact h_indep_t'_v a ((h_mem_eq a).mpr ha) b hb
    exact ⟨h_conn, h_neq_1, v, hv_in_P_t, h_indep_t_v⟩

lemma dependent_letters_of_connected [DecidableEq α] {u v : List α}
    (h_conn : IsConnected I ⟦u ++ v⟧)
    (hu : u ≠ []) (hv : v ≠ []) :
    ∃ a ∈ u, ∃ b ∈ v, ¬ I.rel a b := by
  by_contra h_all_indep
  push Not at h_all_indep
  have h_indep_trace : Independent (I := I) ⟦u⟧ ⟦v⟧ := by
    intro a ha b hb
    exact h_all_indep a ha b hb
  have hu_trace : ⟦u⟧ ≠ (1 : Trace I) := by simpa [mk'_eq_one_iff]
  have hv_trace : ⟦v⟧ ≠ (1 : Trace I) := by simpa [mk'_eq_one_iff]
  exact not_isConnected_mul_of_indep h_indep_trace hu_trace hv_trace h_conn

lemma split_indices_bound [Fintype α] [DecidableEq α] {ps qs : List (List α)}
    (h_len : ps.length = qs.length)
    (hpq_conn : ∀ i (hi : i < ps.length), IsConnected I ⟦ps[i] ++ qs[i]⟧)
    (h_indep : ∀ i j (hi : i < qs.length) (hj : j < ps.length), i < j → I.Independent qs[i] ps[j]) :
    ((ps.zip qs).filter (fun (p, q) => p ≠ [] ∧ q ≠ [])).length ≤ Fintype.card α := by
  let S := Finset.univ.filter (fun (i : Fin ps.length) => ps[i.val] ≠ [] ∧ qs[i.val] ≠ [])
  have h_ex' : ∀ i : S, ∃ b ∈ qs[i.val.val], ∃ a ∈ ps[i.val.val], ¬ I.rel a b := by
    intro ⟨i, hi⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have ⟨a, ha, b, hb, hrel⟩ := dependent_letters_of_connected (hpq_conn i.val i.isLt) hi.1 hi.2
    exact ⟨b, hb, a, ha, hrel⟩
  let f : S → α := fun i => Classical.choose (h_ex' i)
  have hf_spec : ∀ i : S, f i ∈ qs[i.val.val] ∧ ∃ a ∈ ps[i.val.val], ¬ I.rel a (f i) :=
    fun i => Classical.choose_spec (h_ex' i)
  have h_inj : Function.Injective f := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    by_contra h_neq
    have h_neq_val : i.val ≠ j.val := by
      intro h_eq_val
      apply h_neq
      exact Subtype.ext (Fin.ext h_eq_val)
    rcases lt_trichotomy i.val j.val with hlt | heq_val | hgt
    · have h_indep_ij := h_indep i.val j.val (by rw [← h_len]; exact i.isLt) j.isLt hlt
      have h_bi_in := (hf_spec ⟨i, hi⟩).1
      rcases (hf_spec ⟨j, hj⟩).2 with ⟨aj, haj, hdep⟩
      have h_rel := h_indep_ij (f ⟨i, hi⟩) h_bi_in aj haj
      have h_symm := I.symm (f ⟨i, hi⟩) aj h_rel
      rw [heq] at h_symm
      exact hdep h_symm
    · contradiction
    · have h_indep_ji := h_indep j.val i.val (by rw [← h_len]; exact j.isLt) i.isLt hgt
      have h_bj_in := (hf_spec ⟨j, hj⟩).1
      rcases (hf_spec ⟨i, hi⟩).2 with ⟨ai, hai, hdep⟩
      have h_rel := h_indep_ji (f ⟨j, hj⟩) h_bj_in ai hai
      have h_symm := I.symm (f ⟨j, hj⟩) ai h_rel
      rw [← heq] at h_symm
      exact hdep h_symm
  have h_card : S.card ≤ Fintype.card α := by
    rw [← Fintype.card_coe S]
    exact Fintype.card_le_of_injective f h_inj
  have h_len_eq : ((ps.zip qs).filter (fun (p, q) => p ≠ [] ∧ q ≠ [])).length = S.card := by
    have h_zip : ps.zip qs = (List.finRange ps.length).map (fun i => (ps[i.val], qs[i.val])) := by
      apply List.ext_getElem <;> simp [h_len]
    rw [h_zip, ← List.countP_eq_length_filter, List.countP_map, List.countP_eq_length_filter]
    rfl
  rw [h_len_eq]
  exact h_card

/-- Helper for `group_split_factors`. -/
def IsValidBlock (X : Language α) (p q : List α) : Prop :=
  (p ∈ X∗ ∧ q ∈ X∗) ∨ (p ++ q ∈ X)

lemma block_concat_in_kstar {X : Language α} {p q : List α} (h : IsValidBlock X p q) :
    p ++ q ∈ X∗ := by
  cases h with
  | inl h_non_split =>
    simp only [Language.mem_kstar] at *
    rcases h_non_split with ⟨⟨L₁, rfl, hL₁⟩, ⟨L₂, rfl, hL₂⟩⟩
    use L₁ ++ L₂
    simp only [List.flatten_append, List.mem_append, true_and]
    rintro y (hy₁ | hy₂)
    · exact hL₁ y hy₁
    · exact hL₂ y hy₂
  | inr h_split =>
    simp only [Language.mem_kstar]
    use [p ++ q]
    simpa

structure SplitFactorization (I : Independence α) (X : Language α) (ps qs : List (List α)) where
  x_star : List α
  y_star : List α
  hx_star : x_star ∈ X∗
  hy_star : y_star ∈ X∗
  xs : List (List α)
  ys : List (List α)
  len_eq : xs.length = ys.length
  bound : xs.length ≤ 2 * ((ps.zip qs).filter (fun (p, q) => p ≠ [] ∧ q ≠ [])).length
  valid_blocks : ∀ i (hi : i < xs.length) (hi' : i < ys.length), IsValidBlock X xs[i] ys[i]
  trace_x : TraceEqv I ps.flatten (x_star :: xs).flatten
  trace_y : TraceEqv I qs.flatten (y_star :: ys).flatten
  indep_star : ∀ j (hj : j < xs.length), I.Independent y_star xs[j]
  indep_blocks : ∀ (i j : ℕ) (hi : i < ys.length) (hj : j < xs.length), i < j → I.Independent ys[i] xs[j]

def SplitFactorization.cons_split {X : Language α} {ps qs : List (List α)}
    (sf : SplitFactorization I X ps qs) {p q : List α}
    (h_split : p ≠ [] ∧ q ≠ [])
    (hpq_in_X : p ++ q ∈ X)
    (h_indep : ∀ j (hj : j < ps.length), I.Independent q ps[j]) :
    SplitFactorization I X (p :: ps) (q :: qs) :=
  {
    x_star := []
    y_star := []
    hx_star := by simp [Language.nil_mem_kstar]
    hy_star := by simp [Language.nil_mem_kstar]
    xs := p :: sf.x_star :: sf.xs
    ys := q :: sf.y_star :: sf.ys
    len_eq := by simp [sf.len_eq]
    bound := by
      have h_bound := sf.bound
      have h_filter : ((p :: ps).zip (q :: qs)).filter (fun (x, y) => x ≠ [] ∧ y ≠ []) =
          (p, q) :: (ps.zip qs).filter (fun (x, y) => x ≠ [] ∧ y ≠ []) := by
        rcases p with _ | ⟨a, p'⟩ <;> rcases q with _ | ⟨b, q'⟩ <;> simp_all
      rw [h_filter, List.length_cons, List.length_cons, List.length_cons]
      omega
    valid_blocks := by
      intro i hi hi'
      cases i with
      | zero => exact Or.inr hpq_in_X
      | succ i' =>
        cases i' with
        | zero => exact Or.inl ⟨sf.hx_star, sf.hy_star⟩
        | succ i'' => exact sf.valid_blocks i'' (by simp_all) (by simp_all)
    trace_x := by simpa using TraceEqv.compat (TraceEqv.refl p) sf.trace_x
    trace_y := by simpa using TraceEqv.compat (TraceEqv.refl q) sf.trace_y
    indep_star := by simp
    indep_blocks := by
      have hq_ps_flat : I.Independent q ps.flatten := by
        intro a ha b hb
        simp only [List.mem_flatten] at hb
        rcases hb with ⟨p_k, hp_k_in, hb_in⟩
        rcases List.mem_iff_getElem.mp hp_k_in with ⟨k, hk_lt, rfl⟩
        exact h_indep k hk_lt a ha b hb_in
      have hq_xs_flat : I.Independent q (sf.x_star :: sf.xs).flatten :=
        indep_of_indep_of_eqv hq_ps_flat sf.trace_x
      intro i j hi hj hij
      cases i with
      | zero =>
        cases j with
        | zero => contradiction
        | succ j' =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          exact indep_of_indep_flatten_right j' (by simp_all) hq_xs_flat
      | succ i' =>
        cases j with
        | zero => contradiction
        | succ j' =>
          cases i' with
          | zero =>
            cases j' with
            | zero => contradiction
            | succ j'' =>
              simp only [List.getElem_cons_succ, List.getElem_cons_zero]
              exact sf.indep_star j'' (by simp_all)
          | succ i'' =>
            cases j' with
            | zero => contradiction
            | succ j'' =>
              simp only [List.getElem_cons_succ]
              exact sf.indep_blocks i'' j'' (by simp_all) (by simp_all) (by simp_all)
  }

def SplitFactorization.cons_merge {X : Language α} {ps qs : List (List α)}
    (sf : SplitFactorization I X ps qs) {p q : List α}
    (h_not_split : ¬(p ≠ [] ∧ q ≠ []))
    (hpq_in_X : p ++ q ∈ X)
    (h_indep : ∀ j (hj : j < ps.length), I.Independent q ps[j]) :
    SplitFactorization I X (p :: ps) (q :: qs) := by
  have hpq_star : p ∈ X∗ ∧ q ∈ X∗ := by
    by_cases hp : p = []
    · have hq : q ∈ X∗ := by
        rw [Language.mem_kstar]
        use [q]
        simpa [hp] using hpq_in_X
      exact ⟨by simp [hp, Language.nil_mem_kstar], hq⟩
    · have hq : q = [] := by
        by_contra hq
        exact h_not_split ⟨hp, hq⟩
      have hp_star : p ∈ X∗ := by
        rw [Language.mem_kstar]
        use [p]
        simpa [hq] using hpq_in_X
      exact ⟨hp_star, by simp [hq, Language.nil_mem_kstar]⟩
  have h_star_mul : ∀ {u v : List α}, u ∈ X∗ → v ∈ X∗ → u ++ v ∈ X∗ := by
    intro u v hu hv
    rw [Language.mem_kstar] at hu hv ⊢
    rcases hu with ⟨L₁, rfl, hL₁⟩
    rcases hv with ⟨L₂, rfl, hL₂⟩
    use L₁ ++ L₂
    simp only [List.flatten_append, List.mem_append, true_and]
    rintro y (hy₁ | hy₂)
    · exact hL₁ y hy₁
    · exact hL₂ y hy₂
  refine {
    x_star := p ++ sf.x_star
    y_star := q ++ sf.y_star
    hx_star := h_star_mul hpq_star.left sf.hx_star
    hy_star := h_star_mul hpq_star.right sf.hy_star
    xs := sf.xs
    ys := sf.ys
    len_eq := sf.len_eq
    bound := by
      have h_bound := sf.bound
      have h_zip : ((p :: ps).zip (q :: qs)).filter (fun (x, y) => x ≠ [] ∧ y ≠ []) =
          if p ≠ [] ∧ q ≠ [] then (p, q) :: (ps.zip qs).filter (fun (x, y) => x ≠ [] ∧ y ≠ [])
          else (ps.zip qs).filter (fun (x, y) => x ≠ [] ∧ y ≠ []) := by
        rcases p with _ | ⟨a, p'⟩ <;> rcases q with _ | ⟨b, q'⟩ <;> simp_all
      rw [h_zip]
      split_ifs
      omega
    valid_blocks := sf.valid_blocks
    trace_x := by
      have h := TraceEqv.compat (TraceEqv.refl p) sf.trace_x
      simpa only [List.flatten_cons, List.append_assoc] using h
    trace_y := by
      have h := TraceEqv.compat (TraceEqv.refl q) sf.trace_y
      simpa only [List.flatten_cons, List.append_assoc] using h
    indep_star := by
      have hq_ps_flat : I.Independent q ps.flatten := by
        intro a ha b hb
        simp only [List.mem_flatten] at hb
        rcases hb with ⟨p_k, hp_k_in, hb_in⟩
        rcases List.mem_iff_getElem.mp hp_k_in with ⟨k, hk_lt, rfl⟩
        exact h_indep k hk_lt a ha b hb_in
      have hq_xs_flat : I.Independent q (sf.x_star :: sf.xs).flatten :=
        indep_of_indep_of_eqv hq_ps_flat sf.trace_x
      intro j hj a ha b hb
      simp only [List.mem_append] at ha
      rcases ha with ha_q | ha_star
      · exact indep_of_indep_flatten_right (j + 1) (by simpa) hq_xs_flat a ha_q b hb
      · exact sf.indep_star j hj a ha_star b hb
    indep_blocks := sf.indep_blocks
  }

def group_split_factors_aux {X : Language α} {ps qs : List (List α)}
    (h_len : ps.length = qs.length)
    (hpq_in_X : ∀ i (hi : i < ps.length), ps[i] ++ qs[i] ∈ X)
    (h_indep : ∀ i j (hi : i < qs.length) (hj : j < ps.length), i < j → I.Independent qs[i] ps[j]) :
    SplitFactorization I X ps qs := by
  induction ps generalizing qs with
  | nil =>
    have hqs : qs = [] := List.length_eq_zero_iff.mp h_len.symm
    subst hqs
    exact {
      x_star := [],
      y_star := [],
      hx_star := by simp [Language.nil_mem_kstar],
      hy_star := by simp [Language.nil_mem_kstar],
      xs := [],
      ys := [],
      len_eq := rfl,
      bound := by simp,
      valid_blocks := by simp,
      trace_x := by simp [TraceEqv.refl],
      trace_y := by simp [TraceEqv.refl],
      indep_star := by simp,
      indep_blocks := by simp
    }
  | cons p ps' ih =>
    cases qs with | nil => contradiction | cons q qs' =>
      have h_len' : ps'.length = qs'.length := by simpa using h_len
      have hpq_in_X' : ∀ i (hi : i < ps'.length), ps'[i] ++ qs'[i] ∈ X := fun i hi => hpq_in_X (i + 1) (by simpa)
      have h_indep' : ∀ i j (hi : i < qs'.length) (hj : j < ps'.length), i < j → I.Independent qs'[i] ps'[j] :=
        fun i j hi hj hij => h_indep (i + 1) (j + 1) (by simpa) (by simpa) (by simpa)
      have sf_tail := ih h_len' hpq_in_X' h_indep'
      by_cases h_split : p ≠ [] ∧ q ≠ []
      · exact sf_tail.cons_split h_split (hpq_in_X 0 (by simp)) (fun j hj => h_indep 0 (j + 1) (by simp) (by simpa) (by simp))
      · exact sf_tail.cons_merge h_split (hpq_in_X 0 (by simp)) (fun j hj => h_indep 0 (j + 1) (by simp) (by simpa) (by simp))

lemma flatten_mem_kstar {X : Language α} (L : List (List α)) (h : ∀ w ∈ L, w ∈ X∗) :
    L.flatten ∈ X∗ := by
  induction L with
  | nil => simp [Language.nil_mem_kstar]
  | cons w L' ih =>
    simp only [Language.mem_kstar, List.flatten_cons]
    simp only [List.mem_cons, forall_eq_or_imp] at h
    rcases h.left with ⟨L₁, rfl, hL₁⟩
    rcases ih h.right with ⟨L₂, heq, hL₂⟩
    use L₁ ++ L₂
    rw [heq]
    simp only [List.flatten_append, List.mem_append, true_and]
    rintro y (hy₁ | hy₂)
    · exact hL₁ y hy₁
    · exact hL₂ y hy₂

lemma zipWith_append_mem_kstar {X : Language α} {xs ys : List (List α)}
    (h_len : xs.length = ys.length)
    (h_blocks : ∀ i (hi : i < xs.length) (hi' : i < ys.length), IsValidBlock X xs[i] ys[i] ∧
      (i = 0 → xs[i] ∈ X∗ ∧ ys[i] ∈ X∗)) :
    (List.zipWith (· ++ ·) xs ys).flatten ∈ X∗ := by
  apply flatten_mem_kstar
  intro w hw
  rcases List.mem_iff_getElem.mp hw with ⟨i, hi_zip, rfl⟩
  have hi_xs : i < xs.length := by
    rw [List.length_zipWith, h_len, min_self, ← h_len] at hi_zip
    exact hi_zip
  rw [List.getElem_zipWith]
  exact block_concat_in_kstar (h_blocks i hi_xs (by simp_all)).left

lemma group_split_factors
    {x y : List α} {X : Language α} {ps qs : List (List α)} [Fintype α] [DecidableEq α]
    (h_len : ps.length = qs.length)
    (hx_eqv : TraceEqv I x ps.flatten)
    (hy_eqv : TraceEqv I y qs.flatten)
    (hpq_in_X : ∀ i (hi : i < ps.length), ps[i] ++ qs[i] ∈ X)
    (h_indep : ∀ i j (hi : i < qs.length) (hj : j < ps.length), i < j → I.Independent qs[i] ps[j])
    (h_bound : ((ps.zip qs).filter (fun (p, q) => p ≠ [] ∧ q ≠ [])).length ≤ Fintype.card α) :
    ∃ xs ys : List (List α),
      xs.length ≤ 2 * Fintype.card α + 1 ∧
      IsValidFactorization I X∗ x y xs ys := by
  have sf := group_split_factors_aux h_len hpq_in_X h_indep
  use (sf.x_star :: sf.xs), (sf.y_star :: sf.ys)
  constructor
  · have h_sf_bound := sf.bound
    simp only [List.length_cons]
    omega
  · refine ⟨by simp [sf.len_eq], ?_, ?_, ?_, ?_⟩
    · apply zipWith_append_mem_kstar (by simp [sf.len_eq])
      intro i hi hi'
      cases i with
      | zero =>
        exact ⟨Or.inl ⟨sf.hx_star, sf.hy_star⟩, fun _ => ⟨sf.hx_star, sf.hy_star⟩⟩
      | succ i' =>
        refine ⟨sf.valid_blocks i' (by simp_all) (by simp_all), fun h => by contradiction⟩
    · exact hx_eqv.trans sf.trace_x
    · exact hy_eqv.trans sf.trace_y
    · intro i j hi hj hij
      cases i with
      | zero =>
        cases j with
        | zero => contradiction
        | succ j' =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          exact sf.indep_star j' (by simp_all)
      | succ i' =>
        cases j with
        | zero => contradiction
        | succ j' =>
          simp only [List.getElem_cons_succ]
          exact sf.indep_blocks i' j' (by simp_all) (by simp_all) (by simp_all)

theorem star_connected_closed_rank {X : Language α} [Fintype α] [DecidableEq α]
    (hX_closed : IsClosed I X)
    (hX_conn : ∀ w ∈ X, IsConnected I ⟦w⟧) :
    HasFiniteRank I X∗ := by
  use 2 * Fintype.card α
  intro x y hxy
  rcases hxy with ⟨w, hw, heqv⟩
  rw [Language.mem_kstar] at hw
  rcases hw with ⟨ts, rfl, hts⟩
  have ⟨ps, qs, hps_len, hqs_len, hx_eqv, hy_eqv, h_pq_eqv, h_indep⟩ :=
    levi_lemma_gen heqv.symm

  have h_len : ps.length = qs.length := hps_len.trans hqs_len.symm

  have hpq_in_X : ∀ i (hi : i < ps.length), ps[i] ++ qs[i] ∈ X := by
    intro i hi
    have hi_ts : i < ts.length := by omega
    have h_t_in_X : ts[i] ∈ X := hts (ts[i]) (List.getElem_mem hi_ts)
    have h_eqv_i := h_pq_eqv i hi_ts hi (by omega)
    rw [← hX_closed]
    exact ⟨ts[i], h_t_in_X, h_eqv_i⟩

  have hpq_conn : ∀ i (hi : i < ps.length), IsConnected I ⟦ps[i] ++ qs[i]⟧ := by
    intro i hi
    have hi_ts : i < ts.length := by omega
    have h_t_conn := hX_conn ts[i] (hts ts[i] (List.getElem_mem hi_ts))
    have h_eqv_i := h_pq_eqv i hi_ts hi (by omega)
    have h_trace_eq : (⟦ts[i]⟧ : Trace I) = ⟦ps[i] ++ qs[i]⟧ := Quotient.sound h_eqv_i
    rw [← h_trace_eq]
    exact h_t_conn

  have h_bound := split_indices_bound h_len hpq_conn h_indep
  have ⟨xs, ys, h_len_res, h_valid⟩ :=
    group_split_factors h_len hx_eqv hy_eqv hpq_in_X h_indep h_bound
  use xs, ys

lemma recognizable_cstar {P : Set (Trace I)} [DecidableEq α] [Fintype α]
    (hP : IsRecognizable P) : IsRecognizable (connectedComponents P)∗ := by
  let C := connectedComponents P
  let L_C : Language α := Trace.mk' I ⁻¹' C
  have hC_recog : IsRecognizable C := recognizable_connectedComponents hP
  have hL_C_reg : L_C.IsRegular :=
    isRegular_of_recognizable (recognizable_has_recognizablePreImage _ hC_recog)
  have hL_C_closed : IsClosed I L_C := by
    apply le_antisymm
    · rintro x ⟨y, hy, heqv⟩
      simp only [L_C, Set.mem_preimage] at hy ⊢
      have heq : Trace.mk' I y = Trace.mk' I x := Quotient.sound heqv
      rw [← heq]
      exact hy
    · exact traceClosure.le_closure
  have hL_C_conn : ∀ w ∈ L_C, IsConnected I ⟦w⟧ := by
    intro w hw
    simp only [L_C, C, connectedComponents] at hw
    rw [Set.preimage_ofPred_eq, Set.mem_ofPred] at hw
    exact hw.left
  have h_star_reg : (L_C∗).IsRegular := Language.IsRegular.kstar hL_C_reg
  have h_rank : HasFiniteRank I (L_C∗) := star_connected_closed_rank hL_C_closed hL_C_conn
  have h_hash := recognizable_image_of_regular_finite_rank h_star_reg h_rank
  have h_image_eq : Trace.mk' I '' ((L_C∗) : Language α) = C∗ := by
    change toTrace I (L_C∗) = C∗
    rw [toTrace_kstar_comm]
    have h_surj : toTrace I L_C = C := by
      ext t
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro ht
        rcases t with ⟨w⟩
        exact ⟨w, ht, rfl⟩
    rw [h_surj]
  rw [← h_image_eq]
  exact h_hash

/-- Theorem 4.1 (iv) => (i) -/
theorem recognizable_of_cRational [DecidableEq α] [Fintype α] (X : RegularExpression α) :
    IsRecognizable (cRatMatches I X) := by
  induction X with
  | zero => exact recognizable_zero
  | epsilon => exact recognizable_epsilon
  | char a => exact recognizable_char a
  | plus P Q ihP ihQ => exact recognizable_union ihP ihQ
  | comp P Q ihP ihQ => exact recognizable_mul ihP ihQ
  | star P ih => exact recognizable_cstar ih

-----

variable [Fintype α] [LinearOrder α] [DecidableRel I.rel]

omit [LinearOrder α] in
lemma forbidden_of_subword {u w v : List α} {a b : α}
    (hw : w ∈ forbiddenPattern I a b) :
    u ++ w ++ v ∈ forbiddenPattern I a b := by
  unfold forbiddenPattern at *
  simp [Language.mem_mul] at hw
  rcases hw with ⟨a1, b1, b2, b3, ⟨⟨ha1, hb1, hb2⟩, hb3⟩, ⟨x, hx, rfl⟩⟩
  simp [Language.mem_mul]
  use u ++ a1, b1, b2, b3
  and_intros
  · apply mem_sigma
  · exact hb1
  · exact hb2
  · exact hb3
  · use x ++ v
    simp [mem_sigma]

lemma sum_forbidden_of_subword {S : Finset (α × α)} {u w v : List α}
    (hw : w ∈ ∑ p ∈ S, forbiddenPattern I p.1 p.2) :
    u ++ w ++ v ∈ ∑ p ∈ S, forbiddenPattern I p.1 p.2 := by
  induction S using Finset.induction_on generalizing w with
  | empty =>
    simp only [Finset.sum_empty] at hw
    contradiction
  | insert p' S' hp ih =>
    rw [Finset.sum_insert hp] at hw ⊢
    cases hw with
    | inl h_left =>
      left
      exact forbidden_of_subword h_left
    | inr h_right =>
      right
      exact ih h_right

lemma lexNF_of_subword {u w v : List α} (h : u ++ w ++ v ∈ lexNFLanguage I) :
    w ∈ lexNFLanguage I := by
  unfold lexNFLanguage at h ⊢
  rw [Set.mem_compl_iff] at h ⊢
  unfold allForbiddenPatterns at h ⊢
  contrapose! h
  exact sum_forbidden_of_subword h

lemma connected_iterativeFactor_of_subset_lexNF {X : Language α}
    (hX : X ≤ lexNFLanguage I) {w : List α}
    (hw : IsIterativeFactor X w) :
    IsConnected I ⟦w⟧ := by
  rcases hw with ⟨u, v, hw⟩
  have h_lex1 : u ++ w ++ v ∈ lexNFLanguage I := hX (hw 1)
  have h_lex2 : u ++ (w ++ w) ++ v ∈ lexNFLanguage I := hX (hw 2)
  have h_w_lex : w ∈ lexNFLanguage I := lexNF_of_subword h_lex1
  have h_ww_lex : w ++ w ∈ lexNFLanguage I := lexNF_of_subword h_lex2
  exact connected_of_lexNF_sq h_w_lex h_ww_lex

/-- Theorem 4.1 (i) => (ii) -/
theorem connectedIterativeFactors_of_recognizable {T : Set (Trace I)}
    (hT : IsRecognizable T) :
    ∃ X : RegularExpression α,
      (∀ s, IsIterativeFactor X.matches' s → IsConnected I ⟦s⟧) ∧
      toTrace I X.matches' = T := by
  let L : Language α := (Trace.mk' I ⁻¹' T) ⊓ lexNFLanguage I
  have hL_reg : L.IsRegular := by
    apply Language.IsRegular.inf
    · apply isRegular_of_recognizable
      apply recognizable_has_recognizablePreImage
      exact hT
    · apply isRegular_lexNF
  have ⟨R, hR_matches⟩ : ∃ R : RegularExpression α, R.matches' = L := by
    classical
    have ⟨σ, h_fin, M, hL⟩ : ∃ (σ : Type) (_ : Fintype σ) (M : DFA α σ), M.accepts = L :=
      Language.isRegular_iff.mp hL_reg
    have : FinEnum σ := FinEnum.ofEquiv (Fin (Fintype.card σ)) (Fintype.equivFin σ)
    use M.toNFA.toεNFA.toRegex
    rw [← hL, εNFA.accepts_toRegex, NFA.toεNFA_correct, DFA.toNFA_correct]
  use R
  constructor
  · intro s hs
    have h_subset : R.matches' ≤ lexNFLanguage I := by
      simp_all only [inf_le_right, L]
    exact connected_iterativeFactor_of_subset_lexNF h_subset hs
  · rw [hR_matches]
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs.left
    · intro ht
      rcases exists_lexNF_rep I t with ⟨s, hs_eq, hs_lex⟩
      refine ⟨s, ?_, hs_eq⟩
      unfold L
      change s ∈ Trace.mk' I ⁻¹' T ∩ lexNFLanguage I
      constructor
      · rw [Set.mem_preimage]
        subst hs_eq
        exact ht
      · exact hs_lex

end TraceTheory
