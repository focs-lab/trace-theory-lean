import Mathlib.Algebra.Group.PUnit
import TraceTheory.Language
import TraceTheory.Lemmas
import TraceTheory.MyhillNerode
import TraceTheory.RegularExpressions

namespace TraceTheory

open scoped Pointwise

open RegularExpression

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

/-- Hashiguchi's Theorem. -/
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
    (x y : {a // a ∈ t'}) (h_path : dependencyTransClosureIn t' x y) :
    dependencyTransClosureIn t ⟨x.1, (h_mem_eq x.1).mp x.2⟩ ⟨y.1, (h_mem_eq y.1).mp y.2⟩ := by
  induction h_path with
  | single h_dep =>
    apply Relation.TransGen.single
    exact h_dep
  | tail path step ih =>
    apply Relation.TransGen.tail ih
    exact step

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
    have h_indep_t_v : Independent' t v := by
      intro a b ha hb
      exact h_indep_t'_v a b ((h_mem_eq a).mpr ha) hb
    exact ⟨h_conn, h_neq_1, v, hv_in_P_t, h_indep_t_v⟩

open Computability in
theorem star_connected_closed_rank {X : Language α}
    (hX_closed : IsClosed I X)
    (hX_conn : ∀ w ∈ X, IsConnected I ⟦w⟧) :
    HasFiniteRank I X∗ := by
  sorry

open Computability in
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

variable [Fintype α] [LinearOrder α] [DecidableRel I.rel]

lemma connected_of_lexNf_sq {w : List α}
    (hw : w ∈ LexNfLanguage I)
    (hww : w ++ w ∈ LexNfLanguage I) :
    IsConnected I ⟦w⟧ := by
  sorry

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
