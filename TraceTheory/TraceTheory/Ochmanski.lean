import Mathlib.Algebra.Group.PUnit
import TraceTheory.Language
import TraceTheory.Lemmas
import TraceTheory.MyhillNerode
import TraceTheory.RegularExpressions

namespace TraceTheory

open scoped Pointwise

open RegularExpression Computability

variable {α : Type} {I : Independence α}

/-- Main component of Theorem 4.1 (ii) => (iii).

  For a rational expression X, if every iterative factor of L(X) is connected,
  then X' is star-connected (for some rational expression X' with L(X) = L(X')).

  It is strictly necessary that we use an X' not necessarily equal to X.
  Consider X = {a ∪ b}∗ · ∅; where `a` and `b` are not connected. Then L(X) = ∅ so every
  iterative factor is connected, but X is not star-connected.

  Note that P · ∅ or ∅ · P are the only cases where this patch is needed.
-/
lemma exists_starConnected_of_connectedIterativeFactors'
    (X : RegularExpression α)
    (hconn : ∀ s, IsIterativeFactor X.matches' s → IsConnected I ⟦s⟧) :
    ∃ Y, IsStarConnected I Y ∧ X.matches' = Y.matches' := by
  induction X with
  | zero => use zero, trivial
  | epsilon => use epsilon, trivial
  | char a => use char a, trivial
  | plus P Q ihP ihQ =>
    have condP : ∀ s, IsIterativeFactor P.matches' s → IsConnected I ⟦s⟧ := by
      intro s ⟨u, v, h⟩
      exact hconn s ⟨u, v, fun n => Or.inl (h n)⟩
    have condQ : ∀ s, IsIterativeFactor Q.matches' s → IsConnected I ⟦s⟧ := by
      intro s ⟨u, v, h⟩
      exact hconn s ⟨u, v, fun n => Or.inr (h n)⟩
    rcases ihP condP with ⟨P', hP'⟩
    rcases ihQ condQ with ⟨Q', hQ'⟩
    use P' + Q'
    simp [IsStarConnected, hP', hQ']
  | comp P Q ihP ihQ =>
    rcases Set.eq_empty_or_nonempty P.matches' with hp_emp | ⟨p, hp⟩
    · use zero
      simp only [IsStarConnected, matches', hp_emp, true_and]
      rw [Set.empty_mul]
      rfl
    rcases Set.eq_empty_or_nonempty Q.matches' with hq_emp | ⟨q, hq⟩
    · use zero
      simp only [IsStarConnected, matches', hq_emp, true_and]
      rw [Set.mul_empty]
      rfl
    have condP : ∀ s, IsIterativeFactor P.matches' s → IsConnected I ⟦s⟧ := by
      intro s ⟨u, v, h⟩
      exact hconn s ⟨u, v ++ q, fun n => by
        simp only [matches', Language.mem_mul]
        exact ⟨u ++ s ^ n ++ v, h n, q, hq, by simp [← List.append_assoc]⟩⟩
    have condQ : ∀ s, IsIterativeFactor Q.matches' s → IsConnected I ⟦s⟧ := by
      intro s ⟨u, v, h⟩
      exact hconn s ⟨p ++ u, v, fun n => by
        simp only [matches', Language.mem_mul]
        exact ⟨p, hp, u ++ s ^ n ++ v, h n, by simp [List.append_assoc]⟩⟩
    rcases ihP condP with ⟨P', hP'⟩
    rcases ihQ condQ with ⟨Q', hQ'⟩
    use P' * Q'
    simp [IsStarConnected, hP', hQ']
  | star P ih =>
    have condP : ∀ s, IsIterativeFactor P.matches' s → IsConnected I ⟦s⟧ := by
      intro s ⟨u, v, h⟩
      exact hconn s ⟨u, v, fun n => by
        simp only [matches', Language.mem_kstar]
        exact ⟨[u ++ s ^ n ++ v], by simp_all [List.append_assoc]⟩⟩
    rcases ih condP with ⟨P', hP'⟩
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
      | zero => simp; rfl
      | succ n' ih =>
        rw [add_comm, pow_add, List.replicate_add, ih]
        rfl
    · intro y hy
      simp_all only [implies_true, forall_const, matches', List.mem_replicate, ne_eq]

/-- Theorem 4.1 (ii) => (iii) -/
theorem exists_starConnected_of_connectedIterativeFactors
    (T : Set (Trace I)) (X : RegularExpression α)
    (himg : T = toTrace I X.matches')
    (hconn : ∀ s, IsIterativeFactor X.matches' s → IsConnected I ⟦s⟧) :
    ∃ P, IsStarConnected I P ∧ T = (matches_trace I P) := by
  simp [matches_toTrace]
  rcases exists_starConnected_of_connectedIterativeFactors' X hconn with ⟨P, hP⟩
  use P
  simp [hP, himg]

/-- Theorem 4.1 (iii) => (iv) -/
theorem cRational_of_isStarConnected (X : RegularExpression α) (h : IsStarConnected I X) :
    matches_trace I X = matches_cstar_trace I X := by
  induction X with
  | zero => simp [matches_trace, matches_cstar_trace]
  | epsilon => simp [matches_trace, matches_cstar_trace]
  | char _ => simp [matches_trace, matches_cstar_trace]
  | plus P Q ihP ihQ => simp [matches_trace, matches_cstar_trace, ihP h.1, ihQ h.2]
  | comp P Q ihP ihQ => simp [matches_trace, matches_cstar_trace, ihP h.1, ihQ h.2]
  | star P ih =>
    unfold matches_trace matches_cstar_trace
    unfold IsStarConnected at h
    rw [<- ih h.left]
    have hP_conn : ∀ t ∈ matches_trace I P, IsConnected I t := by
      intro t ht
      rw [matches_toTrace] at ht
      simp only [toTrace, Set.mem_image] at ht
      rcases ht with ⟨s, hs, rfl⟩
      exact h.right s hs
    rw [connectedComponents_of_connected _ hP_conn]
    rw [kstar_eq_minusEps_trace]

theorem recognizable_image_of_regular_finite_rank {X : Language α}
    (hX_reg : X.IsRegular)
    (hX_rank : HasFiniteRank I X) :
    IsRecognizable (⇑(mk' (I := I)) '' X) := by
  sorry

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
    · simp [char_map, char_map_aux] at h
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

lemma isRegular_of_recognizable {L : Language α} (h : IsRecognizable L) :
    L.IsRegular := by
  rcases recognizable_is_recognizableDFMA L h with ⟨σ, h_fin, h_decide, M, hM⟩
  rw [Language.isRegular_iff]
  let M_DFA : DFA α σ := {
    step := fun q a => M.step q [a]
    start := M.start
    accept := M.accept
  }
  use σ, h_fin, M_DFA
  rw [hM]
  ext w
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  unfold DFMA.accepts DFMA.eval
  rw [Set.mem_setOf, Set.mem_setOf]
  have h_eval : ∀ q, List.foldl M_DFA.step q w = M.step q w := by
    induction w with
    | nil =>
      intro q
      simp only [List.foldl_nil]
      exact (M.idempotent q).symm
    | cons a ws ih =>
      intro q
      simp only [List.foldl_cons]
      rw [ih (M.step q [a])]
      exact (M.composition q [a] ws)
  rw [h_eval M_DFA.start]

lemma recognizable_mul {P Q : Set (Trace I)} [DecidableEq α]
    (hP : IsRecognizable P) (hQ : IsRecognizable Q) : IsRecognizable (P * Q) := by
  let L_P : Language α := ⇑(mk' (I := I)) ⁻¹' P
  let L_Q : Language α := ⇑(mk' (I := I)) ⁻¹' Q
  have hL_P_reg : L_P.IsRegular :=
    isRegular_of_recognizable (recognizable_has_recognizablePreImage _ _ hP)
  have hL_Q_reg : L_Q.IsRegular :=
    isRegular_of_recognizable (recognizable_has_recognizablePreImage _ _ hQ)
  have hL_P_closed : IsClosed I L_P := by
    apply le_antisymm
    · rintro x ⟨y, hy, heqv⟩
      simp only [L_P, Set.mem_preimage] at hy ⊢
      have heq : mk' (I := I) y = mk' (I := I) x := Quotient.sound heqv
      rw [← heq]
      exact hy
    · exact traceClosure.le_closure
  have hL_Q_closed : IsClosed I L_Q := by
    apply le_antisymm
    · rintro x ⟨y, hy, heqv⟩
      simp only [L_Q, Set.mem_preimage] at hy ⊢
      have heq : mk' (I := I) y = mk' (I := I) x := Quotient.sound heqv
      rw [← heq]
      exact hy
    · exact traceClosure.le_closure
  have h_mul_reg : (L_P * L_Q).IsRegular := Language.IsRegular.mul hL_P_reg hL_Q_reg
  have h_rank : HasFiniteRank I (L_P * L_Q) :=
    ⟨1, concat_closed_rank L_P L_Q hL_P_closed hL_Q_closed⟩
  have h_hash := recognizable_image_of_regular_finite_rank h_mul_reg h_rank
  have h_image_eq : mk' (I := I) '' (L_P * L_Q) = P * Q := by
    ext t
    constructor
    · rintro ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
      exact ⟨mk' u, hu, mk' v, hv, rfl⟩
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
    alph_map (I := I) t = alph_map (I := I) t' ↔ ∀ a, a ∈ t ↔ a ∈ t' := by
  rcases t with ⟨w⟩
  rcases t' with ⟨w'⟩
  change w.toFinset = w'.toFinset ↔ _
  simp only [Finset.ext_iff, List.mem_toFinset]
  rfl

lemma lift_dependency_path [DecidableEq α] {t t' : Trace I} (h_mem_eq : ∀ a, a ∈ t' ↔ a ∈ t)
    (x y : α) (h_path : dependencyTransClosureIn t' x y) :
    dependencyTransClosureIn t x y := by
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
    have h_conn : IsConnected I t := by
      intro a b
      let a' : {x // x ∈ t'} := ⟨a.1, (h_mem_eq a.1).mpr a.2⟩
      let b' : {x // x ∈ t'} := ⟨b.1, (h_mem_eq b.1).mpr b.2⟩
      have h_path := ht'.1 a' b'
      exact lift_dependency_path h_mem_eq a' b' h_path
    have h_neq_1 : t ≠ 1 := by
      intro ht_eq_1
      subst ht_eq_1
      have ht'_eq_1 : t' = 1 := by
        by_contra ht'_neq_1
        rcases empty_is_eps t' ht'_neq_1 with ⟨a, ha⟩
        exact eps_is_empty a ((h_mem_eq a).mp ha)
      exact ht'.2.1 ht'_eq_1
    rcases ht'.2.2 with ⟨v, hv_in_P, h_indep_t'_v⟩
    have hv_in_P_t : t * v ∈ P := by
      have h_f_mul : f_P (t * v) = f_P (t' * v) := by
        simp only [map_mul, h_f_eq.symm]
      rw [hP_eq, Set.mem_preimage] at hv_in_P ⊢
      rw [← h_f_mul] at hv_in_P
      exact hv_in_P
    have h_indep_t_v : IndependentT t v := by
      intro a b ha hb
      exact h_indep_t'_v a b ((h_mem_eq a).mpr ha) hb
    exact ⟨h_conn, h_neq_1, v, hv_in_P_t, h_indep_t_v⟩

lemma dependent_letters_of_connected [DecidableEq α] {u v : List α}
    (h_conn : IsConnected I ⟦u ++ v⟧)
    (hu : u ≠ []) (hv : v ≠ []) :
    ∃ a ∈ u, ∃ b ∈ v, ¬ I.rel a b := by
  by_contra h_all_indep
  push_neg at h_all_indep
  have h_indep_trace : IndependentT (I := I) ⟦u⟧ ⟦v⟧ := by
    intro a b ha hb
    change a ∈ u at ha
    change b ∈ v at hb
    exact h_all_indep a ha b hb
  have hu_trace : ⟦u⟧ ≠ (1 : Trace I) := by simpa [empty_iff]
  have hv_trace : ⟦v⟧ ≠ (1 : Trace I) := by simpa [empty_iff]
  exact append_indep_is_disconnected ⟦u⟧ ⟦v⟧ h_indep_trace hu_trace hv_trace h_conn

lemma split_indices_bound [Fintype α] [DecidableEq α] {n : ℕ} {ps qs : List (List α)}
    (hps_len : ps.length = n) (hqs_len : qs.length = n)
    (hpq_conn : ∀ i (hi : i < n), IsConnected I ⟦ps[i] ++ qs[i]⟧)
    (h_indep : ∀ i j (hi : i < n) (hj : j < n), i < j → Independent I qs[i] ps[j]) :
    (Finset.univ.filter (fun (i : Fin n) => ps[i.val] ≠ [] ∧ qs[i.val] ≠ [])).card ≤
    Fintype.card α := by
  let S := Finset.univ.filter (fun (i : Fin n) => ps[i.val] ≠ [] ∧ qs[i.val] ≠ [])
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
    · have h_indep_ij := h_indep i.val j.val i.isLt j.isLt hlt
      have h_bi_in := (hf_spec ⟨i, hi⟩).1
      rcases (hf_spec ⟨j, hj⟩).2 with ⟨aj, haj, hdep⟩
      have h_rel := h_indep_ij (f ⟨i, hi⟩) h_bi_in aj haj
      have h_symm := I.symm (f ⟨i, hi⟩) aj h_rel
      rw [heq] at h_symm
      exact hdep h_symm
    · contradiction
    · have h_indep_ji := h_indep j.val i.val j.isLt i.isLt hgt
      have h_bj_in := (hf_spec ⟨j, hj⟩).1
      rcases (hf_spec ⟨i, hi⟩).2 with ⟨ai, hai, hdep⟩
      have h_rel := h_indep_ji (f ⟨j, hj⟩) h_bj_in ai hai
      have h_symm := I.symm (f ⟨j, hj⟩) ai h_rel
      rw [← heq] at h_symm
      exact hdep h_symm
  have h_card := Fintype.card_le_of_injective f h_inj
  rw [← Fintype.card_coe S]
  exact h_card

lemma group_split_factors_aux {n : ℕ} {X : Language α} [DecidableEq α]
    (ps qs : List (List α))
    (hps_len : ps.length = n) (hqs_len : qs.length = n)
    (hpq_in_X : ∀ i (hi : i < n), ps[i] ++ qs[i] ∈ X)
    (h_indep : ∀ i j (hi : i < n) (hj : j < n), i < j → Independent I qs[i] ps[j]) :
    ∃ xs ys : List (List α),
      xs.length = ys.length ∧
      xs.length ≤
        2 * (Finset.univ.filter (fun (i : Fin n) => ps[i.val] ≠ [] ∧ qs[i.val] ≠ [])).card + 1 ∧
      (List.zipWith (· ++ ·) xs ys).flatten ∈ traceClosure I X∗ ∧
      TraceEqv I ps.flatten xs.flatten ∧
      TraceEqv I qs.flatten ys.flatten ∧
      ∀ (i j : ℕ) (hi : i < ys.length) (hj : j < xs.length), i < j →
        Independent I ys[i] xs[j] := by
  induction n generalizing ps qs with
  | zero =>
    have hps : ps = [] := List.length_eq_zero_iff.mp hps_len
    have hqs : qs = [] := List.length_eq_zero_iff.mp hqs_len
    subst hps hqs
    use [[]], [[]]
    simp [TraceEqv.refl]
    unfold traceClosure
    use []
    simp [TraceEqv.refl, Language.nil_mem_kstar]
  | succ n' ih =>
    cases ps with | nil => contradiction | cons p ps' =>
    cases qs with | nil => contradiction | cons q qs' =>
      have hps'_len : ps'.length = n' := by simpa using hps_len
      have hqs'_len : qs'.length = n' := by simpa using hqs_len
      have hpq_in_X' : ∀ i (hi : i < n'), ps'[i] ++ qs'[i] ∈ X := by
        intro i hi
        simpa using hpq_in_X (i + 1) (by omega)
      have h_indep' : ∀ i j (hi : i < n') (hj : j < n'), i < j → Independent I qs'[i] ps'[j] := by
        intro i j hi hj hlt
        simpa using h_indep (i + 1) (j + 1) (by omega) (by omega) (by omega)
      have ⟨xs', ys', h_len_eq, h_bound, h_zip_in, h_ps_eqv, h_qs_eqv, h_xs_indep⟩ :=
        ih ps' qs' hps'_len hqs'_len hpq_in_X' h_indep'
      by_cases h_split : p ≠ [] ∧ q ≠ []
      · use (p :: xs'), (q :: ys')
        and_intros
        · simp [h_len_eq]
        · simp only [List.length_cons]
          have h_S_eq : Finset.univ.filter (fun (i : Fin (n' + 1)) => (p :: ps')[i.val] ≠ [] ∧ (q :: qs')[i.val] ≠ []) =
            insert (0 : Fin (n' + 1)) ((Finset.univ.filter (fun (i : Fin n') => ps'[i.val] ≠ [] ∧ qs'[i.val] ≠ [])).image Fin.succ) := by
            ext x
            simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            cases x using Fin.cases with
            | zero =>
              simp only [Fin.val_zero, List.getElem_cons_zero]
              apply iff_of_true h_split
              left
              trivial
            | succ x' =>
              simp only [Fin.val_succ, List.getElem_cons_succ]
              have h_ne : Fin.succ x' ≠ 0 := Fin.succ_ne_zero x'
              simp only [h_ne, false_or]
              constructor
              · intro h
                exact ⟨x', h, rfl⟩
              · rintro ⟨y, hy, h_eq⟩
                injection h_eq with h_eq
                simp only [Nat.add_right_cancel_iff] at h_eq
                simp_rw [← h_eq]
                exact hy
          have h_card : (Finset.univ.filter (fun (i : Fin (n' + 1)) => (p :: ps')[i.val] ≠ [] ∧ (q :: qs')[i.val] ≠ [])).card =
            (Finset.univ.filter (fun (i : Fin n') => ps'[i.val] ≠ [] ∧ qs'[i.val] ≠ [])).card + 1 := by
            rw [h_S_eq, Finset.card_insert_of_notMem]
            · rw [Finset.card_image_of_injective _ (Fin.succ_injective _)]
            · intro h_mem
              simp only [Finset.mem_image] at h_mem
              rcases h_mem with ⟨y, _, hy_eq⟩
              exact Fin.succ_ne_zero y hy_eq
          rw [h_card]
          omega
        · simp only [List.zipWith_cons_cons, List.flatten_cons]
          unfold traceClosure at h_zip_in ⊢
          sorry
        · simp only [List.flatten_cons]
          exact TraceEqv.compat (TraceEqv.refl _) h_ps_eqv
        · simp only [List.flatten_cons]
          exact TraceEqv.compat (TraceEqv.refl _) h_qs_eqv
        · intro i j hi hj hlt
          cases i with
          | zero =>
            cases j with
            | zero => contradiction
            | succ j' =>
              simp only [List.getElem_cons_zero, List.getElem_cons_succ]
              have hq_ps_flat : Independent I q ps'.flatten := by
                intro a ha b hb
                simp only [List.mem_flatten] at hb
                rcases hb with ⟨p_k, hp_k_in, hb_in⟩
                rcases List.mem_iff_getElem.mp hp_k_in with ⟨k, hk_lt, rfl⟩
                exact h_indep 0 (k + 1) (by omega) (by omega) (by omega) a ha b hb_in
              have hq_xs_flat : Independent I q xs'.flatten :=
                indep_of_indep_of_eqv hq_ps_flat h_ps_eqv
              exact indep_of_flatten j' (by simpa using hj) hq_xs_flat
          | succ i' =>
            cases j with
            | zero => contradiction
            | succ j' =>
              simp only [List.getElem_cons_succ]
              exact h_xs_indep i' j' (by simpa using hi) (by simpa using hj) (by omega)
      · rcases xs' with _ | ⟨x_head, xs_tail⟩
        · sorry
        rcases ys' with _ | ⟨y_head, ys_tail⟩
        · sorry

        use ((p ++ x_head) :: xs_tail), ((q ++ y_head) :: ys_tail)

        -- To prove the zip is in traceClosure I (X*):
        -- 1. The new zipped head is `p ++ x_head ++ q ++ y_head`.
        -- 2. Because `q` is independent of `x_head` (from h_indep), this is equivalent to `p ++ q ++ x_head ++ y_head`.
        -- 3. `p ++ q` is in X, and `x_head ++ y_head` (attached to the tail) is in traceClosure I (X*) from the IH.
        -- 4. Therefore, the whole sequence belongs to traceClosure I (X*).
        sorry

lemma group_split_factors
    {x y : List α} {X : Language α} {n : ℕ} {ps qs : List (List α)} [Fintype α] [DecidableEq α]
    (hps_len : ps.length = n) (hqs_len : qs.length = n)
    (hx_eqv : TraceEqv I x ps.flatten)
    (hy_eqv : TraceEqv I y qs.flatten)
    (hpq_in_X : ∀ i (hi : i < n), ps[i] ++ qs[i] ∈ X)
    (h_indep : ∀ i j (hi : i < n) (hj : j < n), i < j → Independent I qs[i] ps[j])
    (h_bound : (Finset.univ.filter (fun (i : Fin n) => ps[i.val] ≠ [] ∧ qs[i.val] ≠ [])).card ≤
      Fintype.card α) :
    ∃ xs ys : List (List α),
      xs.length ≤ 2 * Fintype.card α + 1 ∧
      IsValidFactorization I X∗ x y xs ys := by
  have ⟨xs, ys, h_len_eq, h_len_bound, h_zip_in, h_ps_eqv, h_qs_eqv, h_xs_indep⟩ :=
    group_split_factors_aux ps qs hps_len hqs_len hpq_in_X h_indep
  use xs, ys
  constructor
  · omega
  · unfold IsValidFactorization
    refine ⟨h_len_eq, h_zip_in, ?_, ?_, h_xs_indep⟩
    · exact TraceEqv.trans hx_eqv h_ps_eqv
    · exact TraceEqv.trans hy_eqv h_qs_eqv

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
  have hpq_in_X : ∀ i (hi : i < ts.length),
      ps[i] ++ qs[i] ∈ X := by
    intro i hi
    have h_t_in_X : ts[i] ∈ X := hts (ts[i]) (List.getElem_mem hi)
    have h_eqv_i := h_pq_eqv i hi (by omega) (by omega)
    rw [← hX_closed]
    exact ⟨ts[i], h_t_in_X, h_eqv_i⟩
  have hpq_conn : ∀ i (hi : i < ts.length),
      IsConnected I ⟦ps[i] ++ qs[i]⟧ := by
    intro i hi
    have h_t_conn := hX_conn ts[i] (hts ts[i] (List.getElem_mem hi))
    have h_eqv_i := h_pq_eqv i hi (by omega) (by omega)
    have h_trace_eq : (⟦ts[i]⟧ : Trace I) = ⟦ps[i] ++ qs[i]⟧ := by
      apply Quotient.sound
      exact h_eqv_i
    rw [← h_trace_eq]
    exact h_t_conn
  have h_indep_adapted : ∀ i j (hi : i < ts.length) (hj : j < ts.length), i < j →
      Independent I qs[i] ps[j] := by
    intro i j hi hj hij
    exact h_indep i j (by omega) (by omega) hij
  have h_bound := split_indices_bound hps_len hqs_len hpq_conn h_indep_adapted
  have ⟨xs, ys, h_len, h_valid⟩ :=
    group_split_factors hps_len hqs_len hx_eqv hy_eqv hpq_in_X h_indep_adapted h_bound
  use xs, ys

lemma recognizable_cstar {P : Set (Trace I)} [DecidableEq α] [Fintype α]
    (hP : IsRecognizable P) : IsRecognizable (kstar (connectedComponents P)) := by
  let C := connectedComponents P
  let L_C : Language α := ⇑(mk' (I := I)) ⁻¹' C
  have hC_recog : IsRecognizable C := recognizable_connectedComponents hP
  have hL_C_reg : L_C.IsRegular :=
    isRegular_of_recognizable (recognizable_has_recognizablePreImage _ _ hC_recog)
  have hL_C_closed : IsClosed I L_C := by
    apply le_antisymm
    · rintro x ⟨y, hy, heqv⟩
      simp only [L_C, Set.mem_preimage] at hy ⊢
      have heq : mk' (I := I) y = mk' (I := I) x := Quotient.sound heqv
      rw [← heq]
      exact hy
    · exact traceClosure.le_closure
  have hL_C_conn : ∀ w ∈ L_C, IsConnected I ⟦w⟧ := by
    intro w hw
    simp only [L_C, C, connectedComponents] at hw
    rw [Set.preimage_setOf_eq, Set.mem_setOf] at hw
    exact hw.left
  have h_star_reg : (L_C∗).IsRegular := Language.IsRegular.kstar hL_C_reg
  have h_rank : HasFiniteRank I (L_C∗) := star_connected_closed_rank hL_C_closed hL_C_conn
  have h_hash := recognizable_image_of_regular_finite_rank h_star_reg h_rank
  have h_image_eq : mk' (I := I) '' ((L_C∗) : Language α) = kstar C := by
    change toTrace I (L_C∗) = kstar C
    rw [kstar_toTrace_comm]
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
    IsRecognizable (matches_cstar_trace I X) := by
  induction X with
  | zero => exact recognizable_zero
  | epsilon => exact recognizable_epsilon
  | char a => exact recognizable_char a
  | plus P Q ihP ihQ => exact recognizable_union ihP ihQ
  | comp P Q ihP ihQ => exact recognizable_mul ihP ihQ
  | star P ih => exact recognizable_cstar ih



-----

def dependencyInL (I : Independence α) (w : List α) (a b : α) :=
  (inducedDependence I).rel a b ∧ a ∈ w ∧ b ∈ w

def dependencyTransClosureInL (I : Independence α) (w : List α) (a b : α) :=
  Relation.TransGen (dependencyInL I w) a b

def IsConnectedL (I : Independence α) (w : List α) :=
  ∀ a b : {a : α // a ∈ w}, dependencyTransClosureInL I w a b

lemma IsConnected_eq (I : Independence α) (w : List α) : IsConnectedL I w = IsConnected I ⟦w⟧ := rfl

lemma depTrClIn_refl {w : List α} {a : α} (h : a ∈ w) : dependencyTransClosureInL I w a a := by
  unfold dependencyTransClosureInL dependencyInL
  apply Relation.TransGen.single
  simp [Dependence.refl, h]

lemma depIn_symm {w : List α} {a b : α} : dependencyInL I w a b = dependencyInL I w b a := by
  simp [dependencyInL, inducedDependence]
  apply Iff.intro
  · exact fun ⟨h, ha, hb⟩ => ⟨(by contrapose h; exact I.symm b a h), hb, ha⟩
  · exact fun ⟨h, hb, ha⟩ => ⟨(by contrapose h; exact I.symm a b h), ha, hb⟩

lemma depTrClIn_symm {w : List α} {a b : α} : dependencyTransClosureInL I w a b = dependencyTransClosureInL I w b a := by
  unfold dependencyTransClosureInL
  rw [Relation.transGen_swap]
  have h_symm : (fun x y => dependencyInL I w y x) = (dependencyInL I w) := by
    ext a' b'
    rw [depIn_symm]
  rw [h_symm]

lemma depIn_sub {u w : List α} {a b : α} (huw : u ⊆ w) :
    dependencyInL I u a b → dependencyInL I w a b := by
  intro ⟨hab, ha, hb⟩
  exact ⟨hab, huw ha, huw hb⟩

lemma depTrClIn_sub {u w : List α} {a b : α} (huw : u ⊆ w) :
    dependencyTransClosureInL I u a b → dependencyTransClosureInL I w a b := by
  intro h
  induction h with
  | single hab => exact Relation.TransGen.single (depIn_sub huw hab)
  | tail hac hcb ih => exact Relation.TransGen.tail ih (depIn_sub huw hcb)

--- variable [DecidableRel I.rel]

---
noncomputable instance : ∀ w x y, Decidable (dependencyTransClosureInL I w x y) :=
  fun w x y => Classical.propDecidable (dependencyTransClosureInL I w x y)

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
        if dependencyTransClosureInL I w₀ a b
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
      | b :: _ => dependencyTransClosureInL I w₀ a b

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
        by_cases hab : dependencyTransClosureInL I w₀ a b
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
        by_cases hab : dependencyTransClosureInL I u a b
        all_goals simp [hab]

--#check List.reverseRecOn
--todo: make this work?
theorem ccDec_cases {motive : List (List α) → Prop} (u w : List α)
    (nil : motive [[]])
    (char : ∀ (a : α), motive [[a]])
    (cons_conn : ∀ (a : α) (v : List α) (_h_conn : ccDec_aux_conn I u (a :: v)), motive (ccDec_aux I u v) → motive (ccDec_aux I u (a :: v)))
    (cons_disc : ∀ (a : α) (v : List α) (_h_disc : ¬ ccDec_aux_conn I u (a :: v)), motive (ccDec_aux I u v) → motive (ccDec_aux I u (a :: v))) :
    motive (ccDec_aux I u w) := by
  induction w with
  | nil => simp [ccDec_aux]; exact nil
  | cons a w ih =>
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact (ccDec_aux_nonempty _ _) ht
    · rename_i c_head c_tail
      by_cases hw : w = []
      · simp [hw, ccDec_aux]
        exact char a
      cases c_head with
      | nil =>
        have := ccDec_aux_nonempty_head I u w hw
        simp [List.getElem_of_eq ht] at this
      | cons b c_head =>
        by_cases hab : dependencyTransClosureInL I u a b
        · apply cons_conn _ _ _ ih
          simp [ccDec_aux_conn, ht, hab]
        · apply cons_disc _ _ _ ih
          simp [ccDec_aux_conn, ht, hab]

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
    (ccDec_aux I u (a :: w))[i] = (ccDec_aux I u w)[i]'(by rw [<- ccDec_aux_len_C h]; exact hi) := by
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
    (ccDec_aux I u (a :: w))[i + 1] = (ccDec_aux I u w)[i]'(by rw [<- ccDec_aux_len_D' h]; exact Nat.lt_sub_of_add_lt hi) := by
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
          by_cases hab : dependencyTransClosureInL I u a b
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
        by_cases hab : dependencyTransClosureInL I u a b
        all_goals simp [hab] at ih ⊢; exact ih

lemma List.flatten_prefix (L : List (List α)) (h : L ≠ []) :
    List.IsPrefix (L[0]'(List.length_pos_iff.mpr h)) L.flatten := by
  cases L with
  | nil => simp at h
  | cons w L => simp

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
        simp [<- List.append_assoc]
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


lemma ccDec_aux_prefix (I : Independence α) (u w : List α) :
    List.IsPrefix ((ccDec_aux I u w)[0]'(ccDec_aux_zero_idx)) w := by
  nth_rw 3 [<- ccDec_aux_flatten I u w]
  exact List.flatten_prefix _ (ccDec_aux_nonempty u w)

lemma ccDec_aux_infix (I : Independence α) (u w : List α) (i : ℕ) (hi : i < (ccDec_aux I u w).length) :
    List.IsInfix (ccDec_aux I u w)[i] w := by
  nth_rw 2 [<- ccDec_aux_flatten I u w]
  exact List.flatten_infix (ccDec_aux I u w) i hi

lemma ccDec_aux_adj_infix (I : Independence α) (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) :
    List.IsInfix ((ccDec_aux I u w)[i] ++ (ccDec_aux I u w)[i + 1]) w := by
  nth_rw 7 [<- ccDec_aux_flatten I u w]
  exact List.flatten_adj_infix (ccDec_aux I u w) i hi

lemma ccDec_aux_prefix2 (I : Independence α) (u w : List α) (h : 1 < (ccDec_aux I u w).length) :
    List.IsPrefix ((ccDec_aux I u w)[0] ++ (ccDec_aux I u w)[1]) w := by
  nth_rw 7 [<- ccDec_aux_flatten I u w]
  exact ccDec_flatten_prefix2 (ccDec_aux I u w) h

lemma ccDec_aux_suffix (I : Independence α) (u w : List α) :
    List.IsSuffix ((ccDec_aux I u w).getLast (ccDec_aux_nonempty u w)) w := by
  nth_rw 3 [<- ccDec_aux_flatten I u w]
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
  simp only [<- List.append_assoc]
  rw [hs]

lemma ccDec_aux_head_conn (u w : List α) (hwu : w ⊆ u) :
    ∀ m n, m ∈ (ccDec_aux I u w)[0]'(ccDec_aux_zero_idx) → n ∈ (ccDec_aux I u w)[0]'(ccDec_aux_zero_idx) →
    dependencyTransClosureInL I u m n := by
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
        exact depTrClIn_refl (hwu List.mem_cons_self)
      | cons b c_head =>
        simp [ccDec_aux, ht] at hm hn
        by_cases hab : dependencyTransClosureInL I u a b
        · simp [hab] at hm hn
          simp [ht] at ih
          replace ih := ih (List.subset_of_cons_subset hwu)
          by_cases hma : m = a <;> by_cases hna : n = a
          · rw [hma, hna]
            exact depTrClIn_refl (hwu List.mem_cons_self)
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
              rw [hm, depTrClIn_symm]
              exact hab
            | inr hm =>
              replace ih := ih b m (by simp) (by simp [hm])
              rw [depTrClIn_symm]
              exact Relation.TransGen.trans hab ih
          · simp [hma, hna] at hm hn
            exact ih m n hm hn
        · simp [hab] at hm hn
          rw [hm, hn]
          exact depTrClIn_refl (hwu List.mem_cons_self)

lemma ccDec_aux_elem_conn (u w : List α) (hwu : w ⊆ u) (i : ℕ) (hi : i < (ccDec_aux I u w).length) :
    ∀ m n, m ∈ (ccDec_aux I u w)[i] → n ∈ (ccDec_aux I u w)[i] →
    dependencyTransClosureInL I u m n := by
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
    ¬dependencyTransClosureInL I u
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
        by_cases hab : dependencyTransClosureInL I u a b
        · simp [hab] -- #2 of 3 actually useful parts?
          simp [ht] at ih
          simp [ccDec_aux, ht, hab] at h
          exact ih h hw'
        · simp [hab] -- #3 of 3 actually useful parts?

lemma ccDec_aux_adj_char_indep (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) (hw : w ≠ []) :
    ¬dependencyTransClosureInL I u
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
    Independent I (ccDec_aux I u w)[i] (ccDec_aux I u w)[i + 1] := by
  by_cases hw : w = []
  · simp [hw, ccDec_aux] at hi
  intro p hp q hq
  by_contra hpq
  apply ccDec_aux_adj_char_indep u w i hi hw
  rw [List.getLast_eq_getElem]
  have hqR : dependencyTransClosureInL I u q (((ccDec_aux I u w)[i + 1]'hi)[0]'(List.length_pos_of_mem hq)) :=
    ccDec_aux_elem_conn u w hwu (i + 1) hi _ _ hq (List.getElem_mem (List.length_pos_of_mem hq))
  refine Relation.TransGen.trans ?_ hqR
  replace hpq : dependencyTransClosureInL I u p q := by
    unfold dependencyTransClosureInL dependencyInL inducedDependence
    simp
    apply Relation.TransGen.single
    use hpq
    use hwu (List.IsInfix.mem hp (ccDec_aux_infix I u w i (Nat.lt_of_succ_lt hi)))
    exact hwu (List.IsInfix.mem hq (ccDec_aux_infix I u w (i + 1) hi))
  refine Relation.TransGen.trans ?_ hpq
  exact ccDec_aux_elem_conn u w hwu i (Nat.lt_of_succ_lt hi) _ _ (by simp) hp

lemma ccDec_disconnected_len (w : List α) (h : ¬ IsConnectedL I w) :
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
    simp [IsConnectedL] at h
    replace ⟨m, hm, n, hn, h⟩ := h
    replace h_conn := (h_conn m n hm hn)
    rw [<- ht] at h
    exact h h_conn

-----

variable [Fintype α] [LinearOrder α] [DecidableRel I.rel]

omit [Fintype α] [DecidableRel I.rel] in
lemma lexNf_infix_is_lexNf {s t : List α} (hst : List.IsInfix s t) (ht : IsLexNf I t) :
    IsLexNf I s := by
  apply (isLexNf_iff_factorCondition _ _).mp at ht
  apply (isLexNf_iff_factorCondition _ _).mpr
  replace ⟨s', s'', hst⟩ := hst
  intro y u z a b hs
  replace ht := ht (s' ++ y) u (z ++ s'') a b
  simp [<- hst, hs] at ht
  exact ht

omit [Fintype α] [LinearOrder α] [DecidableRel I.rel] in
lemma connected_dep_concat {u v : List α} (hu : IsConnectedL I u) (hv : IsConnectedL I v) (huv : ¬Independent I u v) :
    IsConnectedL I (u ++ v) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩
  simp at ha hb
  cases ha with
  | inl ha =>
    cases hb with
    | inl hb => exact depTrClIn_sub (List.subset_append_of_subset_left v (by simp)) (hu ⟨a, ha⟩ ⟨b, hb⟩)
    | inr hb =>
      simp at huv
      have ⟨a', ha', b', hb', hab⟩ := huv
      have haa' : dependencyTransClosureInL I (u ++ v) a a' :=
        depTrClIn_sub (List.subset_append_of_subset_left v (by simp)) (hu ⟨a, ha⟩ ⟨a', ha'⟩)
      have hb'b : dependencyTransClosureInL I (u ++ v) b' b :=
        depTrClIn_sub (List.subset_append_of_subset_right u (by simp)) (hv ⟨b', hb'⟩ ⟨b, hb⟩)
      have ha'b' : dependencyTransClosureInL I (u ++ v) a' b' := by
        apply Relation.TransGen.single
        simp [dependencyInL, inducedDependence]
        exact ⟨hab, Or.inl ha', Or.inr hb'⟩
      exact Relation.TransGen.trans haa' (Relation.TransGen.trans ha'b' hb'b)
  | inr ha =>
    cases hb with
    | inl hb =>
      simp at huv
      have ⟨b', hb', a', ha', hab⟩ := huv
      have haa' : dependencyTransClosureInL I (u ++ v) a a' :=
        depTrClIn_sub (List.subset_append_of_subset_right u (by simp)) (hv ⟨a, ha⟩ ⟨a', ha'⟩)
      have hb'b : dependencyTransClosureInL I (u ++ v) b' b :=
        depTrClIn_sub (List.subset_append_of_subset_left v (by simp)) (hu ⟨b', hb'⟩ ⟨b, hb⟩)
      have ha'b' : dependencyTransClosureInL I (u ++ v) a' b' := by
        apply Relation.TransGen.single
        simp [dependencyInL, inducedDependence]
        exact ⟨fun h => hab (I.symm _ _ h), Or.inr ha', Or.inl hb'⟩
      exact Relation.TransGen.trans haa' (Relation.TransGen.trans ha'b' hb'b)
    | inr hb => exact depTrClIn_sub (List.subset_append_of_subset_right u (by simp)) (hv ⟨a, ha⟩ ⟨b, hb⟩)

/- omit [Fintype α] [LinearOrder α] [DecidableRel I.rel] in
lemma connected_dup_is_connected {w : List α} (hw : IsConnectedL I w) :
    IsConnectedL I (w ++ w) := by
  cases w with
  | nil => simp [hw]
  | cons a w =>
    have h_dep : ¬Independent I (a :: w) (a :: w) := by
      simp
      intro ha
      exfalso
      exact I.irrefl a ha
    exact connected_dep_concat hw hw h_dep -/

lemma lexNf_sq_is_lexNf {w : List α} (h : w ++ w ∈ LexNfLanguage I) :
    w ∈ LexNfLanguage I := by
  apply (mem_lexNfLanguage_iff_factorCondition _ _).mp at h
  apply (isLexNf_iff_factorCondition _ _).mpr at h
  apply (TraceTheory.mem_lexNfLanguage_iff_factorCondition _ _).mpr
  apply (isLexNf_iff_factorCondition _ _).mp
  contrapose h
  simp [IsLexNf] at h ⊢
  rcases h with ⟨u, h⟩
  use w ++ u
  exact ⟨TraceEqv.compat (TraceEqv.refl w) h.1, List.append_left_lt h.right⟩

omit [Fintype α] [DecidableRel I.rel] in
lemma lexNf_concat_of_indep {u v : List α} (h_indep : Independent I u v) (huv : IsLexNf I (u ++ v))
    (hu : u ≠ []) (hv : v ≠ []) :
    (u[0]'(List.length_pos_iff.mpr hu) < v[0]'(List.length_pos_iff.mpr hv)) := by
  apply (isLexNf_iff_factorCondition _ _).mp at huv

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

lemma lexNf_ccDec_adj_order {w : List α} (hw : w ∈ LexNfLanguage I) (hz : w ≠ []) (i : ℕ)
    (hi : i + 1 < (ccDec_aux I w w).length) :
    (ccDec_aux I w w)[i][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) <
    (ccDec_aux I w w)[i + 1][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) := by
  apply (mem_lexNfLanguage_iff_factorCondition _ _).mp at hw
  apply (isLexNf_iff_factorCondition _ _).mpr at hw
  have h_infix := lexNf_infix_is_lexNf (ccDec_aux_adj_infix I w w i hi) hw

  apply lexNf_concat_of_indep (ccDec_aux_adj_indep w w i hi (by simp)) h_infix
  use (ccDec_aux_elem_nonempty w w i (Nat.lt_of_succ_lt hi) hz)
  exact ccDec_aux_elem_nonempty w w (i + 1) hi hz

lemma lexNf_ccDec_order {w : List α} (hw : w ∈ LexNfLanguage I) (hz : w ≠ []) (i j : ℕ)
    (hij : i < j) (hj : j < (ccDec_aux I w w).length) :
    (ccDec_aux I w w)[i][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) <
    (ccDec_aux I w w)[j][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) := by
  induction hij with
  | refl => exact lexNf_ccDec_adj_order hw hz i hj
  | step hij ih =>
    clear j
    rename_i j
    exact lt_trans (ih (Nat.lt_of_succ_lt hj)) (lexNf_ccDec_adj_order hw hz j hj)

lemma ccDec_aux_across_indep (I : Independence α) (u w : List α) (hi : 1 < (ccDec_aux I u w).length) (hwu : w ⊆ u) :
    Independent I ((ccDec_aux I u w).getLast (ccDec_aux_nonempty _ _)) (ccDec_aux I u w)[0] ∨
    (Independent I ((ccDec_aux I u w).getLast (ccDec_aux_nonempty _ _) ++ (ccDec_aux I u w)[0]) (ccDec_aux I u w)[1] ∧
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
    have hs' : Independent I (ccDec_aux I u w)[0] (ccDec_aux I u w)[1] := ccDec_aux_adj_indep u w 0 _ hwu
    simp at hl hs ⊢
    have ⟨a, ha, b, hb, hab⟩ := hl
    have ⟨c, hc, d, hd, hcd⟩ := hs
    clear hl hs
    cases ha with
    | inl ha => sorry
    | inr ha => sorry
  · by_contra hl
    simp at hl
    replace hi := Nat.le_antisymm hl hi
    replace hi : (ccDec_aux I u w).length - 1 = 1 := Eq.symm (Nat.eq_sub_of_add_eq' (Eq.symm hi))
    have hs' : Independent I (ccDec_aux I u w)[0] (ccDec_aux I u w)[1] := ccDec_aux_adj_indep u w 0 _ hwu
    rw [List.getLast_eq_getElem, getElem_congr rfl hi _] at hs
    exact hs (independent_symm hs')


lemma connected_of_lexNf_sq {w : List α}
    (hw : w ∈ LexNfLanguage I)
    (hww : w ++ w ∈ LexNfLanguage I) :
    IsConnected I ⟦w⟧ := by
  rw [<- IsConnected_eq]
  -- apply (mem_lexNfLanguage_iff_factorCondition _ _).mp at hw
  -- apply (isLexNf_iff_factorCondition _ _).mpr at hw
  apply (mem_lexNfLanguage_iff_factorCondition _ _).mp at hww
  apply (isLexNf_iff_factorCondition _ _).mpr at hww

  by_cases hz : w = []
  · simp [hz, IsConnectedL]
  by_contra h_con
  have h_con_ww : ¬IsConnectedL I (w ++ w) := by
    contrapose h_con
    intro ⟨a, ha⟩ ⟨b, hb⟩
    replace h_con := h_con ⟨a, List.mem_append_left w ha⟩ ⟨b, List.mem_append_left w hb⟩
    exact depTrClIn_sub (List.append_subset_of_subset_of_subset (by simp) (by simp)) h_con
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
      simp only [<- List.append_assoc] at h_across_infix ⊢
      exact h_across_infix
    have h_across_lexNf := lexNf_infix_is_lexNf h_across_infix hww
    have h_last_ne : (ccDec_aux I w w).getLast (ccDec_aux_nonempty _ _) ≠ [] := by
      rw [List.getLast_eq_getElem]
      exact ccDec_aux_elem_nonempty w w _ _ hz
    rw [List.getLast_eq_getElem] at h_across_indep h_across_lexNf
    have h_gt := lexNf_concat_of_indep h_across_indep h_across_lexNf
        (ccDec_aux_elem_nonempty w w _ _ hz) (ccDec_aux_nonempty_head I w w hz)
    have h_lt := lexNf_ccDec_order hw hz 0 ((ccDec_aux I w w).length - 1) (Nat.zero_lt_sub_of_lt h_dec_w_len)
        (Nat.sub_one_lt_of_lt h_dec_w_len)
    exact LT.lt.asymm h_gt h_lt
  | inr h_across_indep =>
    replace ⟨h_across_indep, h_dec_w_len2⟩ := h_across_indep
    have h_across_infix := ccDec_across_infix I w (Nat.lt_of_succ_le h_dec_w_len)
    have h_across_lexNf := lexNf_infix_is_lexNf h_across_infix hww
    rw [List.getLast_eq_getElem] at h_across_indep h_across_lexNf
    have h_across_ne : (ccDec I w)[(ccDec I w).length - 1] ++ (ccDec I w)[0] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (ccDec_aux_nonempty_head I w w hz)
    have h_gt := lexNf_concat_of_indep
      h_across_indep h_across_lexNf
      h_across_ne
      (ccDec_aux_elem_nonempty w w 1 (Nat.lt_of_succ_le h_dec_w_len) hz)
    have h_eq : ((ccDec_aux I w w)[(ccDec_aux I w w).length - 1] ++ (ccDec_aux I w w)[0])[0]'(List.length_pos_iff.mpr h_across_ne) =
        ((ccDec_aux I w w)[(ccDec_aux I w w).length - 1])[0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) := by
      rw [List.getElem_append_left]
    rw [h_eq] at h_gt
    have h_lt := lexNf_ccDec_order hw hz 1 ((ccDec_aux I w w).length - 1) (Nat.lt_sub_of_add_lt h_dec_w_len2)
        (Nat.sub_one_lt_of_lt h_dec_w_len)
    exact LT.lt.asymm h_gt h_lt

lemma connected_of_lexNf_sq' {w : List α}
    (hww : w ++ w ∈ LexNfLanguage I) :
    IsConnected I ⟦w⟧ :=
  connected_of_lexNf_sq (lexNf_sq_is_lexNf hww) hww

omit [LinearOrder α] in
lemma forbidden_of_subword {u w v : List α} {a b : α}
    (hw : w ∈ ForbiddenPattern I a b) :
    u ++ w ++ v ∈ ForbiddenPattern I a b := by
  unfold ForbiddenPattern at *
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
    (hw : w ∈ ∑ p ∈ S, ForbiddenPattern I p.1 p.2) :
    u ++ w ++ v ∈ ∑ p ∈ S, ForbiddenPattern I p.1 p.2 := by
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

lemma lexNf_of_subword {u w v : List α} (h : u ++ w ++ v ∈ LexNfLanguage I) :
    w ∈ LexNfLanguage I := by
  unfold LexNfLanguage at h ⊢
  rw [Set.mem_compl_iff] at h ⊢
  unfold AllForbiddenPatterns at h ⊢
  contrapose! h
  exact sum_forbidden_of_subword h

lemma connected_iterativeFactor_of_subset_lexNf {X : Language α}
    (hX : X ≤ LexNfLanguage I) {w : List α}
    (hw : IsIterativeFactor X w) :
    IsConnected I ⟦w⟧ := by
  rcases hw with ⟨u, v, hw⟩
  have h_lex1 : u ++ w ++ v ∈ LexNfLanguage I := hX (hw 1)
  have h_lex2 : u ++ (w ++ w) ++ v ∈ LexNfLanguage I := hX (hw 2)
  have h_w_lex : w ∈ LexNfLanguage I := lexNf_of_subword h_lex1
  have h_ww_lex : w ++ w ∈ LexNfLanguage I := lexNf_of_subword h_lex2
  exact connected_of_lexNf_sq h_w_lex h_ww_lex

/-- Theorem 4.1 (i) => (ii) -/
theorem connectedIterativeFactors_of_recognizable {T : Set (Trace I)}
    (hT : IsRecognizable T) :
    ∃ X : RegularExpression α,
      (∀ s, IsIterativeFactor X.matches' s → IsConnected I ⟦s⟧) ∧
      toTrace I X.matches' = T := by
  let L : Language α := (mk' (I := I) ⁻¹' T) ⊓ LexNfLanguage I
  have hL_reg : L.IsRegular := by
    apply Language.IsRegular.inf
    · apply isRegular_of_recognizable
      apply recognizable_has_recognizablePreImage
      exact hT
    · apply isRegular_lexNf
  have ⟨R, hR_matches⟩ : ∃ R : RegularExpression α, R.matches' = L := by
    classical
    have ⟨σ, h_fin, M, hL⟩ : ∃ (σ : Type) (_ : Fintype σ) (M : DFA α σ), M.accepts = L :=
      Language.isRegular_iff.mp hL_reg
    haveI : FinEnum σ := FinEnum.ofEquiv (Fin (Fintype.card σ)) (Fintype.equivFin σ)
    use M.toNFA.toεNFA.toRegex
    rw [← hL, εNFA.accepts_toRegex, NFA.toεNFA_correct, DFA.toNFA_correct]
  use R
  constructor
  · intro s hs
    have h_subset : R.matches' ≤ LexNfLanguage I := by
      simp_all only [inf_le_right, L]
    exact connected_iterativeFactor_of_subset_lexNf h_subset hs
  · rw [hR_matches]
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs.left
    · intro ht
      rcases exists_lexNf_rep I t with ⟨s, hs_eq, hs_lex⟩
      refine ⟨s, ?_, hs_eq⟩
      unfold L
      change s ∈ ⇑mk' ⁻¹' T ∩ LexNfLanguage I
      constructor
      · rw [Set.mem_preimage]
        subst hs_eq
        exact ht
      · exact hs_lex

end TraceTheory
