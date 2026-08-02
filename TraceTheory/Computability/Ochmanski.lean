import Mathlib.Algebra.Group.PUnit
import TraceTheory.Computability.Hashiguchi
import TraceTheory.Computability.RegularExpressions

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

noncomputable instance : ∀ w x y, Decidable (List.DepPath I w x y) :=
  fun w x y => Classical.propDecidable (List.DepPath I w x y)

noncomputable def ccDec_aux (I : Independence α) (w₀ w : List α) : List (List α) :=
  match w with
  | [] => [[]]
  | a :: w =>
    match ccDec_aux I w₀ w with
    | [] => [] -- dummy value, unreachable by construction
    | v :: vs =>
      match v with
      | [] => [a] :: vs
      | b :: v =>
        if List.DepPath I w₀ a b
          then (a :: b :: v) :: vs
          else [a] :: (b :: v) :: vs

noncomputable def ccDec (I : Independence α) (w : List α) : List (List α) := ccDec_aux I w w

noncomputable def ccDec_aux_conn (I : Independence α) (w₀ w : List α) : Prop :=
  match w with
  | [] => True -- by convention
  | a :: w =>
    match ccDec_aux I w₀ w with
    | [] => False
    | v :: _ =>
      match v with
      | [] => True -- by convention to make casework easier (first char is inserted as `[[·]]` and not `[·] :: _`)
      | b :: _ => List.DepPath I w₀ a b

lemma ccDec_aux_nonempty (w₀ w : List α) : (ccDec_aux I w₀ w) ≠ [] := by
  induction w with
  | nil => simp [ccDec_aux]
  | cons a u ih =>
    simp [ccDec_aux]
    cases hs : ccDec_aux I w₀ u
    · simp [hs] at ih
    · simp
      rename_i c_head c_tail
      cases c_head with
      | nil => simp
      | cons b c_head =>
        simp
        by_cases hab : List.DepPath I w₀ a b
        all_goals simp [hab]

lemma ccDec_aux_zero_idx {w₀ w : List α} : 0 < (ccDec_aux I w₀ w).length := List.length_pos_iff.mpr (ccDec_aux_nonempty _ _)

lemma ccDec_aux_nonempty_head (I : Independence α) (u w : List α) (h : w ≠ []) :
    (ccDec_aux I u w)[0]'(ccDec_aux_zero_idx) ≠ [] := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    suffices hs_dec : ∃ _1 _2 _3, (ccDec_aux I u (a :: w)) = (_1 ::_2) :: _3 from by
      replace ⟨_1, _2, _3, hs_dec⟩ := hs_dec
      rw [List.getElem_of_eq hs_dec]
      simp
    simp [ccDec_aux]
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact ccDec_aux_nonempty _ _ ht
    · rename_i c_head c_tail
      simp [ht]
      cases c_head with
      | nil => simp
      | cons b c_head =>
        simp
        by_cases hab : List.DepPath I u a b
        all_goals simp [hab]

lemma ccDec_aux_len_C {u w : List α} {a : α} (h : ccDec_aux_conn I u (a :: w)) :
    (ccDec_aux I u (a :: w)).length = (ccDec_aux I u w).length := by
  simp [ccDec_aux_conn] at h
  let t := ccDec_aux I u w
  have ht : ccDec_aux I u w = t := rfl
  rcases t
  · simp [ht] at h
  · rename_i c_head c_tail
    simp [ht] at h
    cases c_head with
    | nil => simp [ccDec_aux, ht]
    | cons b c_head =>
      simp at h
      simp [ccDec_aux, ht, h]

lemma ccDec_aux_len_D {u w : List α} {a : α} (h : ¬ ccDec_aux_conn I u (a :: w)) :
    (ccDec_aux I u (a :: w)).length = (ccDec_aux I u w).length + 1 := by
  simp [ccDec_aux_conn] at h
  let t := ccDec_aux I u w
  have ht : ccDec_aux I u w = t := rfl
  rcases t
  · exfalso
    exact ccDec_aux_nonempty _ _ ht
  · rename_i c_head c_tail
    simp [ht] at h
    cases c_head with
    | nil =>
      cases w with
      | nil => simp at h
      | cons b w =>
        have := ccDec_aux_nonempty_head I u (b :: w) (List.cons_ne_nil b w)
        simp [List.getElem_of_eq ht] at this
    | cons b c_head =>
      simp at h
      simp [ccDec_aux, ht, h]

lemma ccDec_aux_len_D' {u w : List α} {a : α} (h : ¬ ccDec_aux_conn I u (a :: w)) :
    (ccDec_aux I u (a :: w)).length - 1 = (ccDec_aux I u w).length := by
  simp [ccDec_aux_len_D h]

lemma ccDec_aux_tail_C {u w : List α} {a : α} (h : ccDec_aux_conn I u (a :: w))
    (i : ℕ) (hi : i < (ccDec_aux I u (a :: w)).length) (hiz : i > 0) :
    (ccDec_aux I u (a :: w))[i] = (ccDec_aux I u w)[i]'(by rw [← ccDec_aux_len_C h]; exact hi) := by
  by_cases hw : w = []
  · simp [hw, ccDec_aux] at hi
    simp [hi] at hiz
  simp [ccDec_aux_conn] at h
  let t := ccDec_aux I u w
  have ht : ccDec_aux I u w = t := rfl
  rcases t
  · rw [ccDec_aux_len_C h] at hi
    simp [ht] at hi
  · rename_i c_head c_tail
    simp [ht] at h
    have : c_head ≠ [] := by
      have := ccDec_aux_nonempty_head I u w hw
      rw [List.getElem_of_eq ht] at this
      exact this
    cases c_head with
    | nil => simp at this
    | cons b c_head =>
      simp at h
      simp [ccDec_aux, ht, h] at hi ⊢
      have : ((a :: b :: c_head) :: c_tail)[i] =
          ((a :: b :: c_head) :: c_tail)[i - 1 + 1]'(Nat.add_lt_of_lt_sub (Nat.sub_lt_right_of_lt_add hiz hi)) := by
        rw [getElem_congr _ (show i - 1 + 1 = i from Nat.sub_add_cancel (Nat.succ_le_of_lt hiz))]
        simp
      rw [this]
      have : ((b :: c_head) :: c_tail)[i] =
          ((b :: c_head) :: c_tail)[i - 1 + 1]'(Nat.add_lt_of_lt_sub (Nat.sub_lt_right_of_lt_add hiz hi)) := by
        rw [getElem_congr _ (show i - 1 + 1 = i from Nat.sub_add_cancel (Nat.succ_le_of_lt hiz))]
        simp
      rw [this]
      simp

lemma ccDec_aux_tail_D {u w : List α} {a : α} (h : ¬ ccDec_aux_conn I u (a :: w))
    (i : ℕ) (hi : i + 1 < (ccDec_aux I u (a :: w)).length) :
    (ccDec_aux I u (a :: w))[i + 1] = (ccDec_aux I u w)[i]'(by rw [← ccDec_aux_len_D' h]; exact Nat.lt_sub_of_add_lt hi) := by
  by_cases hw : w = []
  · simp [hw, ccDec_aux_conn, ccDec_aux] at h
  simp [ccDec_aux_conn] at h
  let t := ccDec_aux I u w
  have ht : ccDec_aux I u w = t := rfl
  rcases t
  · rw [ccDec_aux_len_D h] at hi
    simp [ht] at hi
  · rename_i c_head c_tail
    simp [ht] at h
    have : c_head ≠ [] := by
      have := ccDec_aux_nonempty_head I u w hw
      rw [List.getElem_of_eq ht] at this
      exact this
    cases c_head with
    | nil => simp at this
    | cons b c_head =>
      simp at h
      simp [ccDec_aux, ht, h] at ⊢

lemma ccDec_aux_tail_D' {u w : List α} {a : α} (h : ¬ ccDec_aux_conn I u (a :: w))
    (i : ℕ) (hi : i - 1 < (ccDec_aux I u w).length) (hiz : i ≠ 0) :
    (ccDec_aux I u (a :: w))[i]'(by rw [ccDec_aux_len_D h]; exact lt_add_of_tsub_lt_right hi) = (ccDec_aux I u w)[i - 1] := by
  cases i with
  | zero => simp at hiz
  | succ i => apply ccDec_aux_tail_D h i

lemma ccDec_aux_elem_nonempty (u w : List α) (i : ℕ) (hi : i < (ccDec_aux I u w).length) (hz : w ≠ []) :
    (ccDec_aux I u w)[i] ≠ [] := by
  induction w generalizing i with
  | nil => simp at hz
  | cons a w ih =>
    clear hz
    by_cases hiz : i = 0
    · suffices hs_dec : (∃ _1 _2 _3, (ccDec_aux I u (a :: w)) = (_1 :: _2) :: _3) ∨ (ccDec_aux I u (a :: w)) = [] from by
        rcases hs_dec with ⟨hs_dec⟩
        · replace ⟨_1, _2, _3, hs_dec⟩ := hs_dec
          simp [hs_dec, hiz]
        · rename_i hs_dec
          simp [hs_dec] at hi
      simp [ccDec_aux]
      cases ccDec_aux I u w
      · simp
      · rename_i c_head c_tail
        simp
        cases c_head with
        | nil => simp
        | cons b c_head =>
          simp
          by_cases hab : List.DepPath I u a b
          all_goals simp [hab]
    · have hw : w ≠ [] := by
        by_contra hw
        simp [hw, ccDec_aux] at hi
        exact hiz hi
      by_cases hab : ccDec_aux_conn I u (a :: w)
      · rw [ccDec_aux_tail_C hab i hi (Nat.zero_lt_of_ne_zero hiz)]
        apply ih
        exact hw
      · rw [ccDec_aux_tail_D' hab i (by rw [ccDec_aux_len_D hab] at hi; omega) hiz]
        apply ih
        exact hw

lemma ccDec_aux_elem_nonempty_len (u w : List α) (i : ℕ) (hi : i < (ccDec_aux I u w).length) (hz : w ≠ []) :
    0 < (ccDec_aux I u w)[i].length :=
  List.length_pos_iff.mpr (@ccDec_aux_elem_nonempty α I _ _ _ hi hz)

lemma ccDec_aux_flatten (I : Independence α) (u w : List α) :
    (ccDec_aux I u w).flatten = w := by
  induction w with
  | nil => simp [ccDec_aux]
  | cons a w ih =>
    simp [ccDec_aux]
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact (ccDec_aux_nonempty _ _) ht
    · rename_i c_head c_tail
      simp [ht] at ih ⊢
      cases c_head with
      | nil => simp at ih ⊢; exact ih
      | cons b c_head =>
        by_cases hab : List.DepPath I u a b
        all_goals simp [hab] at ih ⊢; exact ih

lemma ccDec_flatten_prefix2 (L : List (List α)) (h : 1 < L.length) :
    List.IsPrefix (L[0] ++ L[1]) L.flatten := by
  cases L with
  | nil => simp at h
  | cons w L =>
    cases L with
    | nil => simp at h
    | cons v L => simp

lemma List.flatten_infix (L : List (List α)) (i : ℕ) (hi : i < L.length) :
    List.IsInfix L[i] L.flatten := by
  induction L generalizing i with
  | nil => simp at hi
  | cons w L ih =>
    cases i with
    | zero => exact List.infix_append_left
    | succ i =>
      simp
      exact List.infix_append_of_infix_right (ih i (Nat.succ_lt_succ_iff.mp hi))

lemma List.flatten_adj_infix (L : List (List α)) (i : ℕ) (hi : i + 1 < L.length) :
    List.IsInfix (L[i] ++ L[i + 1]) L.flatten := by
  induction L generalizing i with
  | nil => simp at hi
  | cons w L ih =>
    cases i with
    | zero =>
      cases L with
      | nil => simp at hi
      | cons v L =>
        simp [← List.append_assoc]
        exact List.infix_append_left
    | succ i =>
      simp
      exact List.infix_append_of_infix_right (ih i (Nat.succ_lt_succ_iff.mp hi))

lemma List.flatten_suffix (L : List (List α)) (h : L ≠ []) :
    List.IsSuffix (L.getLast h) L.flatten := by
  induction L with
  | nil => simp at h
  | cons w L ih =>
    cases L with
    | nil => simp
    | cons v L =>
      simp at ih ⊢
      exact List.suffix_append_of_suffix ih

lemma ccDec_aux_infix (I : Independence α) (u w : List α) (i : ℕ) (hi : i < (ccDec_aux I u w).length) :
    List.IsInfix (ccDec_aux I u w)[i] w := by
  nth_rw 2 [← ccDec_aux_flatten I u w]
  exact List.flatten_infix (ccDec_aux I u w) i hi

lemma ccDec_aux_adj_infix (I : Independence α) (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) :
    List.IsInfix ((ccDec_aux I u w)[i] ++ (ccDec_aux I u w)[i + 1]) w := by
  nth_rw 7 [← ccDec_aux_flatten I u w]
  exact List.flatten_adj_infix (ccDec_aux I u w) i hi

lemma ccDec_aux_prefix2 (I : Independence α) (u w : List α) (h : 1 < (ccDec_aux I u w).length) :
    List.IsPrefix ((ccDec_aux I u w)[0] ++ (ccDec_aux I u w)[1]) w := by
  nth_rw 7 [← ccDec_aux_flatten I u w]
  exact ccDec_flatten_prefix2 (ccDec_aux I u w) h

lemma ccDec_aux_suffix (I : Independence α) (u w : List α) :
    List.IsSuffix ((ccDec_aux I u w).getLast (ccDec_aux_nonempty u w)) w := by
  nth_rw 3 [← ccDec_aux_flatten I u w]
  exact List.flatten_suffix (ccDec_aux I u w) (ccDec_aux_nonempty u w)

lemma ccDec_across_infix (I : Independence α) (w : List α) (h : 1 < (ccDec I w).length) :
    List.IsInfix (
      ((ccDec I w).getLast (ccDec_aux_nonempty w w)) ++ (ccDec I w)[0] ++ (ccDec I w)[1]
    ) (w ++ w) := by
  unfold ccDec
  have ⟨s, hs⟩ := ccDec_aux_suffix I w w
  have ⟨t, ht⟩ := ccDec_aux_prefix2 I w w h
  use s, t
  simp only [List.append_assoc] at ht ⊢
  simp [ht]
  simp only [← List.append_assoc]
  rw [hs]

lemma ccDec_aux_head_conn (u w : List α) (hwu : w ⊆ u) :
    ∀ m n, m ∈ (ccDec_aux I u w)[0]'(ccDec_aux_zero_idx) → n ∈ (ccDec_aux I u w)[0]'(ccDec_aux_zero_idx) →
    List.DepPath I u m n := by
  induction w with
  | nil => simp [ccDec_aux]
  | cons a w ih =>
    intro m n hm hn
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact (ccDec_aux_nonempty _ _) ht
    · rename_i c_head c_tail
      cases c_head with
      | nil =>
        simp [ccDec_aux, ht] at hm hn
        rw [hm, hn]
        exact List.depPath_refl (hwu List.mem_cons_self)
      | cons b c_head =>
        simp [ccDec_aux, ht] at hm hn
        by_cases hab : List.DepPath I u a b
        · simp [hab] at hm hn
          simp [ht] at ih
          replace ih := ih (List.subset_of_cons_subset hwu)
          by_cases hma : m = a <;> by_cases hna : n = a
          · rw [hma, hna]
            exact List.depPath_refl (hwu List.mem_cons_self)
          · rw [hma]
            simp [hna] at hn
            cases hn with
            | inl hn =>
              rw [hn]
              exact hab
            | inr hn =>
              replace ih := ih b n (by simp) (by simp [hn])
              exact Relation.TransGen.trans hab ih
          · rw [hna]
            simp [hma] at hm
            cases hm with
            | inl hm =>
              rw [hm, List.depPath_symm]
              exact hab
            | inr hm =>
              replace ih := ih b m (by simp) (by simp [hm])
              rw [List.depPath_symm]
              exact Relation.TransGen.trans hab ih
          · simp [hma, hna] at hm hn
            exact ih m n hm hn
        · simp [hab] at hm hn
          rw [hm, hn]
          exact List.depPath_refl (hwu List.mem_cons_self)

lemma ccDec_aux_elem_conn (u w : List α) (hwu : w ⊆ u) (i : ℕ) (hi : i < (ccDec_aux I u w).length) :
    ∀ m n, m ∈ (ccDec_aux I u w)[i] → n ∈ (ccDec_aux I u w)[i] →
    List.DepPath I u m n := by
  induction w generalizing i with
  | nil => simp [ccDec_aux]
  | cons a w ih =>
    by_cases hiz : i = 0
    · simp [hiz]
      apply ccDec_aux_head_conn
      exact hwu
    · by_cases hab : ccDec_aux_conn I u (a :: w)
      · rw [ccDec_aux_tail_C hab]
        apply ih (List.subset_of_cons_subset hwu)
        exact Nat.zero_lt_of_ne_zero hiz
      · replace hi : i - 1 < (ccDec_aux I u w).length := by
          rw [ccDec_aux_len_D hab] at hi
          cases i with
          | zero => simp at hiz
          | succ i => exact Nat.succ_lt_succ_iff.mp hi
        rw [ccDec_aux_tail_D' hab i hi hiz]
        apply ih (List.subset_of_cons_subset hwu)

lemma ccDec_aux_adj_head_char_indep (u w : List α) (h : 1 < (ccDec_aux I u w).length) (hw : w ≠ []) :
    ¬List.DepPath I u
    ((ccDec_aux I u w)[0].getLast (ccDec_aux_elem_nonempty u w 0 ccDec_aux_zero_idx hw))
    ((ccDec_aux I u w)[1][0]'(List.length_pos_iff.mpr (ccDec_aux_elem_nonempty u w 1 h hw))) := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact (ccDec_aux_nonempty _ _) ht
    · rename_i c_head c_tail
      by_cases hw' : w = []
      · simp [hw', ccDec_aux] at h -- #1 of 3 actually useful parts?
      cases c_head with
      | nil =>
        have := ccDec_aux_nonempty_head I u w hw'
        simp [List.getElem_of_eq ht] at this
      | cons b c_head =>
        simp [ccDec_aux, ht]
        by_cases hab : List.DepPath I u a b
        · simp [hab] -- #2 of 3 actually useful parts?
          simp [ht] at ih
          simp [ccDec_aux, ht, hab] at h
          exact ih h hw'
        · simp [hab] -- #3 of 3 actually useful parts?

lemma ccDec_aux_adj_char_indep (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) (hw : w ≠ []) :
    ¬List.DepPath I u
    ((ccDec_aux I u w)[i].getLast (ccDec_aux_elem_nonempty u w i (Nat.lt_of_succ_lt hi) hw))
    ((ccDec_aux I u w)[i + 1][0]'(List.length_pos_iff.mpr (ccDec_aux_elem_nonempty u w (i + 1) hi hw))) := by
  induction w generalizing i with
  | nil => simp at hw
  | cons a w ih =>
    by_cases hw : w = []
    · simp [hw, ccDec_aux] at hi
    cases i with
    | zero => exact ccDec_aux_adj_head_char_indep u (a :: w) (Nat.lt_of_succ_le hi) (List.cons_ne_nil a w)
    | succ i =>
      by_cases hab : ccDec_aux_conn I u (a :: w)
      · rw [List.getLast.congr_simp _ _ (ccDec_aux_tail_C hab (i + 1) (Nat.lt_of_succ_lt hi) (Nat.zero_lt_succ i))]
        rw [List.getElem_of_eq (ccDec_aux_tail_C hab (i + 2) hi (Nat.zero_lt_succ (i + 1)))]
        exact ih _ _ hw
      · rw [List.getLast.congr_simp _ _ (ccDec_aux_tail_D hab i (Nat.lt_of_succ_lt hi))]
        rw [List.getElem_of_eq (ccDec_aux_tail_D hab (i + 1) hi)]
        exact ih _ _ hw

lemma ccDec_aux_adj_indep (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) (hwu : w ⊆ u) :
    I.Independent (ccDec_aux I u w)[i] (ccDec_aux I u w)[i + 1] := by
  by_cases hw : w = []
  · simp [hw, ccDec_aux] at hi
  intro p hp q hq
  by_contra hpq
  apply ccDec_aux_adj_char_indep u w i hi hw
  rw [List.getLast_eq_getElem]
  have hqR : List.DepPath I u q (((ccDec_aux I u w)[i + 1]'hi)[0]'(List.length_pos_of_mem hq)) :=
    ccDec_aux_elem_conn u w hwu (i + 1) hi _ _ hq (List.getElem_mem (List.length_pos_of_mem hq))
  refine Relation.TransGen.trans ?_ hqR
  replace hpq : List.DepPath I u p q := by
    unfold List.DepPath List.DepEdge inducedDependence
    simp
    apply Relation.TransGen.single
    use hpq
    use hwu (List.IsInfix.mem hp (ccDec_aux_infix I u w i (Nat.lt_of_succ_lt hi)))
    exact hwu (List.IsInfix.mem hq (ccDec_aux_infix I u w (i + 1) hi))
  refine Relation.TransGen.trans ?_ hpq
  exact ccDec_aux_elem_conn u w hwu i (Nat.lt_of_succ_lt hi) _ _ (by simp) hp

lemma ccDec_disconnected_len (w : List α) (h : ¬ List.IsConnected I w) :
    (ccDec I w).length ≥ 2 := by
  by_contra h_len
  simp at h_len
  replace h_len : (ccDec I w).length = 1 := Nat.eq_of_le_of_lt_succ ccDec_aux_zero_idx h_len
  let t := ccDec I w
  have ht : ccDec I w = t := rfl
  rcases t
  · simp [ht] at h_len
  · rename_i c_head c_tail
    have h_conn := @ccDec_aux_head_conn α I w w (List.Subset.refl _)
    unfold ccDec at ht h_len
    simp [ht] at h_conn
    simp [ht] at h_len
    rw [h_len] at ht
    replace ht : (ccDec_aux I w w).flatten = c_head := by simp [ht]
    rw [ccDec_aux_flatten] at ht
    rw [ht] at h
    simp [List.IsConnected] at h
    replace ⟨m, hm, n, hn, h⟩ := h
    replace h_conn := (h_conn m n hm hn)
    rw [← ht] at h
    exact h h_conn

-----

variable [Fintype α] [LinearOrder α] [DecidableRel I.rel]

omit [Fintype α] [DecidableRel I.rel] in
lemma lexNF_infix_is_lexNF {s t : List α} (hst : List.IsInfix s t) (ht : IsLexNF I t) :
    IsLexNF I s := by
  apply (isLexNF_iff_factorCondition _ _).mp at ht
  apply (isLexNF_iff_factorCondition _ _).mpr
  replace ⟨s', s'', hst⟩ := hst
  intro y u z a b hs
  replace ht := ht (s' ++ y) u (z ++ s'') a b
  simp [← hst, hs] at ht
  exact ht

omit [Fintype α] [DecidableRel I.rel] in
lemma lexNF_concat_of_indep {u v : List α} (h_indep : I.Independent u v) (huv : IsLexNF I (u ++ v))
    (hu : u ≠ []) (hv : v ≠ []) :
    (u[0]'(List.length_pos_iff.mpr hu) < v[0]'(List.length_pos_iff.mpr hv)) := by
  apply (isLexNF_iff_factorCondition _ _).mp at huv

  rcases u
  · simp at hu
  rename_i a u

  rcases v
  · simp at hv
  rename_i b v

  replace huv := huv [] u v b a
  simp at huv h_indep ⊢

  by_contra h_ge
  have h_ne : a ≠ b := by
    by_contra h_eq
    rw [h_eq] at h_indep
    exact (I.irrefl _) h_indep.1.1
  have h_gt : b < a := by
    simp at h_ge
    exact lt_of_le_of_ne h_ge (Ne.symm h_ne)

  have ⟨c, hcs, hac⟩ := huv (I.symm _ _ h_indep.1.1) h_gt
  exact hac (I.symm _ _ (h_indep.2 c hcs).1)

lemma lexNF_ccDec_adj_order {w : List α} (hw : w ∈ lexNFLanguage I) (hz : w ≠ []) (i : ℕ)
    (hi : i + 1 < (ccDec_aux I w w).length) :
    (ccDec_aux I w w)[i][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) <
    (ccDec_aux I w w)[i + 1][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) := by
  apply (mem_lexNFLanguage_iff_factorCondition _ _).mp at hw
  apply (isLexNF_iff_factorCondition _ _).mpr at hw
  have h_infix := lexNF_infix_is_lexNF (ccDec_aux_adj_infix I w w i hi) hw

  apply lexNF_concat_of_indep (ccDec_aux_adj_indep w w i hi (by simp)) h_infix
  use (ccDec_aux_elem_nonempty w w i (Nat.lt_of_succ_lt hi) hz)
  exact ccDec_aux_elem_nonempty w w (i + 1) hi hz

lemma lexNF_ccDec_order {w : List α} (hw : w ∈ lexNFLanguage I) (hz : w ≠ []) (i j : ℕ)
    (hij : i < j) (hj : j < (ccDec_aux I w w).length) :
    (ccDec_aux I w w)[i][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) <
    (ccDec_aux I w w)[j][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) := by
  induction hij with
  | refl => exact lexNF_ccDec_adj_order hw hz i hj
  | step hij ih =>
    clear j
    rename_i j
    exact lt_trans (ih (Nat.lt_of_succ_lt hj)) (lexNF_ccDec_adj_order hw hz j hj)

instance {I : Independence α} {u : List α} :
    Trans (List.DepPath I u) (List.DepPath I u) (List.DepPath I u) where
  trans := Relation.TransGen.trans

omit [Fintype α] [LinearOrder α] in
lemma ccDec_aux_across_indep (I : Independence α) (u w : List α) (hi : 1 < (ccDec_aux I u w).length) (hwu : w ⊆ u) :
    I.Independent ((ccDec_aux I u w).getLast (ccDec_aux_nonempty _ _)) (ccDec_aux I u w)[0] ∨
    (I.Independent ((ccDec_aux I u w).getLast (ccDec_aux_nonempty _ _) ++ (ccDec_aux I u w)[0]) (ccDec_aux I u w)[1] ∧
    2 < (ccDec_aux I u w).length) := by
  by_cases hw : w = []
  · simp [hw, ccDec_aux]
  by_contra h
  rw [not_or] at h
  rcases h with ⟨hs, hl⟩
  apply hl
  clear hl

  apply And.intro
  · by_contra hl
    apply @ccDec_aux_adj_char_indep α I u w 0 (Nat.add_lt_of_lt_sub' hi) hw
    simp at hl hs ⊢
    have ⟨a, ha, b, hb, hab⟩ := hl
    have ⟨c, hc, d, hd, hcd⟩ := hs
    clear hl hs
    cases ha with
    | inl ha =>
      calc
        List.DepPath I u ((ccDec_aux I u w)[0].getLast (ccDec_aux_nonempty_head I u w hw)) d :=
          ccDec_aux_elem_conn u w hwu _ _ _ _ (List.getLast_mem _) hd
        List.DepPath I u d c := by
          apply Relation.TransGen.single
          use fun h => hcd (I.symm _ _ h)
          apply And.intro
          · exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) hd)
          · rw [List.getLast_eq_getElem _] at hc
            exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) hc)
        List.DepPath I u c a := by
          rw [List.getLast_eq_getElem _] at ha hc
          exact ccDec_aux_elem_conn u w hwu _ _ _ _ hc ha
        List.DepPath I u a b := by
          apply Relation.TransGen.single
          use hab
          apply And.intro
          · rw [List.getLast_eq_getElem _] at ha
            exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) ha)
          · exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) hb)
        List.DepPath I u b ((ccDec_aux I u w)[1][0]'(ccDec_aux_elem_nonempty_len u w 1 hi hw)) :=
          ccDec_aux_elem_conn u w hwu _ _ _ _ hb (List.getElem_mem _)
    | inr ha =>
      calc
        List.DepPath I u ((ccDec_aux I u w)[0].getLast (ccDec_aux_nonempty_head I u w hw)) a :=
          ccDec_aux_elem_conn u w hwu _ _ _ _ (List.getLast_mem _) ha
        List.DepPath I u a b := by
          apply Relation.TransGen.single
          use hab
          apply And.intro
          · exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) ha)
          · exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) hb)
        List.DepPath I u b ((ccDec_aux I u w)[1][0]'(ccDec_aux_elem_nonempty_len u w 1 hi hw)) :=
          ccDec_aux_elem_conn u w hwu _ _ _ _ hb (List.getElem_mem _)
  · by_contra hl
    simp at hl
    replace hi := Nat.le_antisymm hl hi
    replace hi : (ccDec_aux I u w).length - 1 = 1 := Eq.symm (Nat.eq_sub_of_add_eq' (Eq.symm hi))
    have hs' : I.Independent (ccDec_aux I u w)[0] (ccDec_aux I u w)[1] := ccDec_aux_adj_indep u w 0 _ hwu
    rw [List.getLast_eq_getElem, getElem_congr rfl hi _] at hs
    exact hs (independent_symm hs')

lemma connected_of_lexNF_sq {w : List α}
    (hw : w ∈ lexNFLanguage I)
    (hww : w ++ w ∈ lexNFLanguage I) :
    Trace.IsConnected I ⟦w⟧ := by
  rw [← Trace.isConnected_eq]
  apply (mem_lexNFLanguage_iff_factorCondition _ _).mp at hww
  apply (isLexNF_iff_factorCondition _ _).mpr at hww

  by_cases hz : w = []
  · simp [hz, List.IsConnected]
  by_contra h_con
  have h_con_ww : ¬List.IsConnected I (w ++ w) := by
    contrapose h_con
    intro a ha b hb
    replace h_con := h_con a (List.mem_append_left w ha) b (List.mem_append_left w hb)
    exact List.depPath_sub (List.append_subset_of_subset_of_subset (by simp) (by simp)) h_con
  have h_dec_w_len := @ccDec_disconnected_len α I w h_con
  have h_dec_ww_len := @ccDec_disconnected_len α I (w ++ w) h_con_ww
  unfold ccDec at h_dec_ww_len

  have h_across_indep := ccDec_aux_across_indep I w w (Nat.lt_of_succ_le h_dec_w_len) (by simp)
  cases h_across_indep with
  | inl h_across_indep =>
    have h_across_infix := ccDec_across_infix I w (Nat.lt_of_succ_le h_dec_w_len)
    replace h_across_infix : List.IsInfix
        (((ccDec_aux I w w).getLast (ccDec_aux_nonempty _ _)) ++
        ((ccDec_aux I w w)[0]'(ccDec_aux_zero_idx)))
        (w ++ w) := by
      unfold ccDec at h_across_infix
      replace ⟨s, t, h_across_infix⟩ := h_across_infix
      use s, (ccDec_aux I w w)[1] ++ t
      simp only [← List.append_assoc] at h_across_infix ⊢
      exact h_across_infix
    have h_across_lexNF := lexNF_infix_is_lexNF h_across_infix hww
    have h_last_ne : (ccDec_aux I w w).getLast (ccDec_aux_nonempty _ _) ≠ [] := by
      rw [List.getLast_eq_getElem]
      exact ccDec_aux_elem_nonempty w w _ _ hz
    rw [List.getLast_eq_getElem] at h_across_indep h_across_lexNF
    have h_gt := lexNF_concat_of_indep h_across_indep h_across_lexNF
        (ccDec_aux_elem_nonempty w w _ _ hz) (ccDec_aux_nonempty_head I w w hz)
    have h_lt := lexNF_ccDec_order hw hz 0 ((ccDec_aux I w w).length - 1) (Nat.zero_lt_sub_of_lt h_dec_w_len)
        (Nat.sub_one_lt_of_lt h_dec_w_len)
    exact LT.lt.asymm h_gt h_lt
  | inr h_across_indep =>
    replace ⟨h_across_indep, h_dec_w_len2⟩ := h_across_indep
    have h_across_infix := ccDec_across_infix I w (Nat.lt_of_succ_le h_dec_w_len)
    have h_across_lexNF := lexNF_infix_is_lexNF h_across_infix hww
    rw [List.getLast_eq_getElem] at h_across_indep h_across_lexNF
    have h_across_ne : (ccDec I w)[(ccDec I w).length - 1] ++ (ccDec I w)[0] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (ccDec_aux_nonempty_head I w w hz)
    have h_gt := lexNF_concat_of_indep
      h_across_indep h_across_lexNF
      h_across_ne
      (ccDec_aux_elem_nonempty w w 1 (Nat.lt_of_succ_le h_dec_w_len) hz)
    have h_eq : ((ccDec_aux I w w)[(ccDec_aux I w w).length - 1] ++ (ccDec_aux I w w)[0])[0]'(List.length_pos_iff.mpr h_across_ne) =
        ((ccDec_aux I w w)[(ccDec_aux I w w).length - 1])[0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) := by
      rw [List.getElem_append_left]
    rw [h_eq] at h_gt
    have h_lt := lexNF_ccDec_order hw hz 1 ((ccDec_aux I w w).length - 1) (Nat.lt_sub_of_add_lt h_dec_w_len2)
        (Nat.sub_one_lt_of_lt h_dec_w_len)
    exact LT.lt.asymm h_gt h_lt

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
