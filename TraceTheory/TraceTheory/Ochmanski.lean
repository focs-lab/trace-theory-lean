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

open Computability in
theorem star_connected_closed_rank {X : Language α}
    (hX_closed : IsClosed I X)
    (hX_conn : ∀ w ∈ X, IsConnected I ⟦w⟧) :
    HasFiniteRank I X∗ := by
  sorry

open Computability in
lemma recognizable_cstar {P : Set (Trace I)}
    (hP : IsRecognizable P) : IsRecognizable (kstar (connectedComponents P)) := by
  let C := connectedComponents P
  let L_C : Language α := ⇑(mk' (I := I)) ⁻¹' C
  have hC_recog : IsRecognizable C := sorry -- Requires a lemma that connected components of recognizable sets are recognizable
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
    unfold kstar
    ext t
    constructor
    · rintro ⟨w, ⟨ws, rfl, hws⟩, rfl⟩
      use ws.map (mk' (I := I))
      constructor
      · intro t' ht'
        simp only [List.mem_map] at ht'
        rcases ht' with ⟨w', hw', rfl⟩
        exact hws w' hw'
      · induction ws with
        | nil => rfl
        | cons w' ws' ih =>
          simp only [List.flatten_cons, List.map_cons, List.prod_cons]
          have h_mul : mk' (I := I) (w' ++ ws'.flatten) =
                       mk' (I := I) w' * mk' (I := I) ws'.flatten := rfl
          simp only [List.mem_cons, forall_eq_or_imp] at hws
          rw [h_mul, ih hws.right]
    · rintro ⟨ts, hts, rfl⟩
      induction ts with
      | nil => exact ⟨[], by apply Language.nil_mem_kstar, rfl⟩
      | cons t' ts' ih =>
        have ht' : t' ∈ C := hts t' (by simp)
        have hts' : ∀ x ∈ ts', x ∈ C := fun x hx => hts x (by simp [hx])
        rcases ih hts' with ⟨w', hw'_star, hw'_eq⟩
        rcases t' with ⟨u⟩
        have hu_in_LC : u ∈ L_C := ht'
        use u ++ w'
        constructor
        · rw [Language.mem_kstar] at hw'_star ⊢
          rcases hw'_star with ⟨ws', rfl, hws'⟩
          use u :: ws'
          simp only [List.flatten_cons, List.mem_cons, forall_eq_or_imp, true_and]
          exact ⟨hu_in_LC, hws'⟩
        · have h_mul : mk' (I := I) (u ++ w') = mk' (I := I) u * mk' (I := I) w' := rfl
          rw [h_mul, hw'_eq]
          rfl
  rw [← h_image_eq]
  exact h_hash

/-- Theorem 4.1 (iv) => (i) -/
theorem recognizable_of_cRational [DecidableEq α] (X : RegularExpression α) :
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

/-
lemma ccDec'_aux_len (u w : List α) (a : α) :
    (ccDec_aux' I u (a :: w)).length = (ccDec_aux' I u w).length ∨
    (ccDec_aux' I u (a :: w)).length = (ccDec_aux' I u w).length + 1 := by
  simp [ccDec_aux']
  cases ccDec_aux' I u w
  · simp
  · rename_i c_head c_tail
    simp
    cases c_head with
    | nil => simp
    | cons b c_head =>
      simp
      by_cases hab : dependencyTransClosureInL I u a b
      all_goals simp [hab]

lemma ccDec'_aux_len_le (u w : List α) (a : α) :
    (ccDec_aux' I u w).length ≤ (ccDec_aux' I u (a :: w)).length := by
  cases ccDec'_aux_len u w a with
  | inl h => rw [h]
  | inr h => simp [h]

lemma ccDec'_aux_sub_idx (u w : List α) (a : α) (i : Fin (ccDec_aux' I u (a :: w)).length) (hiz : i.1 > 0) :
    ∃ j : Fin (ccDec_aux' I u w).length, (ccDec_aux' I u (a :: w))[i] = (ccDec_aux' I u w)[j] := by
  sorry
-/

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

lemma ccDec_aux_prefix (I : Independence α) (u w : List α) :
    List.IsPrefix ((ccDec_aux I u w)[0]'(ccDec_aux_zero_idx)) w := by
  induction w with
  | nil => simp [ccDec_aux]
  | cons a w ih =>
    suffices hs_dec : ∃ _1 _2, (ccDec_aux I u (a :: w)) = _1 :: _2 ∧ List.IsPrefix _1 (a :: w) from by
      replace ⟨_1, _2, ⟨hs_dec, hs⟩⟩ := hs_dec
      simp [List.getElem_of_eq hs_dec, hs]
    simp [ccDec_aux]
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact (ccDec_aux_nonempty _ _) ht
    · rename_i c_head c_tail
      simp [ht]
      cases c_head with
      | nil => simp
      | cons b c_head =>
        simp
        by_cases hab : dependencyTransClosureInL I u a b
        · simp [hab]
          simp [List.getElem_of_eq ht] at ih
          exact ih
        · simp [hab]

lemma ccDec_aux_infix (I : Independence α) (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) :
    List.IsInfix ((ccDec_aux I u w)[i] ++ (ccDec_aux I u w)[i + 1]) w := by
  induction w generalizing i with
  | nil => simp [ccDec_aux] at hi
  | cons a w ih =>
    by_cases hiz : i = 0
    · simp [hiz]
      by_cases hab : ccDec_aux_conn I u (a :: w)
      · sorry
      · sorry
    · by_cases hab : ccDec_aux_conn I u (a :: w)
      · simp [ccDec_aux_len_C hab] at hi
        rw [ccDec_aux_tail_C hab i (by omega) (Nat.zero_lt_of_ne_zero hiz)]
        rw [ccDec_aux_tail_C hab (i + 1) (by omega) (Nat.zero_lt_succ i)]
        apply List.infix_cons
        apply ih
      · simp [ccDec_aux_len_D hab] at hi
        rw [ccDec_aux_tail_D' hab i (by omega) hiz]
        rw [ccDec_aux_tail_D' hab (i + 1) (by omega) (Ne.symm (Nat.zero_ne_add_one i))]
        simp
        apply List.infix_cons
        replace ih := ih (i - 1) (by omega)
        have : (ccDec_aux I u w)[i - 1 + 1]'(by omega) = (ccDec_aux I u w)[i]'(by omega) := by
          simp [getElem_congr _ (show i - 1 + 1 = i from Nat.succ_pred_eq_of_ne_zero hiz)]
        rw [this] at ih
        exact ih

lemma ccDec_aux_prefix2 (I : Independence α) (u w : List α) (h : 1 < (ccDec_aux I u w).length) :
    List.IsPrefix ((ccDec_aux I u w)[0] ++ (ccDec_aux I u w)[1]) w := by
  induction w with
  | nil => simp [ccDec_aux] at h
  | cons a w ih =>
    suffices hs_dec : ∃ _1 _2 _3, (ccDec_aux I u (a :: w)) = _1 :: _2 :: _3 ∧ List.IsPrefix (_1 ++ _2) (a :: w) from by
      replace ⟨_1, _2, _3, ⟨hs_dec, hs⟩⟩ := hs_dec
      simp [List.getElem_of_eq hs_dec, hs]
    simp [ccDec_aux]
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact (ccDec_aux_nonempty _ _) ht
    · rename_i c_head c_tail
      simp [ht]
      cases c_head with
      | nil =>
        simp
        sorry
      | cons b c_head =>
        simp
        by_cases hab : dependencyTransClosureInL I u a b
        · simp [hab]
          simp [List.getElem_of_eq ht] at ih
          sorry
          --by_cases hct : c_tail = []
          --· simp [hct] at ht
          --use c_tail[0]
          --exact ih
        · simp [hab]
          have := List.getElem_of_eq ht ccDec_aux_zero_idx
          simp at this
          rw [<- this]
          exact ccDec_aux_prefix I u w

lemma ccDec_aux_suffix (I : Independence α) (u w : List α) :
    List.IsSuffix ((ccDec_aux I u w).getLast (ccDec_aux_nonempty u w)) w := by
  induction w with
  | nil => simp [ccDec_aux]
  | cons a w ih =>
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · simp [ccDec_aux, ht] at ih ⊢
      exact List.suffix_cons_iff.mpr (Or.inr ih)
    · rename_i c_head c_tail

      /- by_cases hab : ccDec_aux_conn I u (a :: w)
      · rw [List.getLast_eq_getElem]
        rw [ccDec_aux_tail_C hab _ (by sorry) (by exact?)]
        have : (ccDec_aux I u (a :: w)).length - 1 = (ccDec_aux I u w).length - 1 := by
          rw [ccDec_aux_len_C hab]
        rw [getElem_congr rfl this]
        rw [<- List.getLast_eq_getElem]
        apply List.suffix_cons_iff.mpr -/

      by_cases hw : w = []
      · simp [hw, ccDec_aux]
      have hch : c_head ≠ [] := by
        by_contra hcon
        rw [hcon] at ht
        replace ht := List.getElem_of_eq ht ccDec_aux_zero_idx
        simp at ht
        exact (ccDec_aux_nonempty_head _ _ _ hw) ht
      simp [ccDec_aux, ht]
      cases c_head with
      | nil => simp at hch
      | cons b c_head =>
        simp
        by_cases hab : dependencyTransClosureInL I u a b
        · simp [hab]
          sorry
          /- induction c_tail using List.reverseRecOn with
          | nil => simp
          | append_singleton c_tail d ih2 =>
            simp
            rw [List.getLast_congr ht] at ih -/
        · simp [hab]
          sorry

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
  by_cases hiz : i = 0
  · simp [hiz] at hi ⊢
    exact ccDec_aux_adj_head_char_indep u w hi hw
  · induction w generalizing i with
    | nil => simp at hw
    | cons a w ih =>
      sorry
      /- by_cases hab : ccDec_aux_conn I u (a :: w)
      · rw [ccDec_aux_tail_C hab]
        apply ih (List.subset_of_cons_subset hwu)
        exact Nat.zero_lt_of_ne_zero hiz
      · rw [ccDec_aux_tail_D' hab]
        apply ih (List.subset_of_cons_subset hwu)
        rw [ccDec_aux_len_D hab] at hi
        cases i with
        | zero => simp at hiz
        | succ i => exact Nat.succ_lt_succ_iff.mp hi -/

lemma ccDec_aux_adj_indep (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) :
    Independent I (ccDec_aux I u w)[i] (ccDec_aux I u w)[i + 1] := by
  induction w generalizing i with
  | nil => simp [ccDec_aux]
  | cons a w ih =>
    intro p hp q hq
    sorry

lemma ccDec_aux_flatten (u w : List α) :
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

lemma connected_of_lexNf_sq {w : List α}
    (hw : w ∈ LexNfLanguage I)
    (hww : w ++ w ∈ LexNfLanguage I) :
    IsConnected I ⟦w⟧ := by
  rw [<- IsConnected_eq]
  cases w with
  | nil => simp [IsConnectedL]
  | cons a w' =>
    let w := a :: w'
    have hz : w ≠ [] := List.cons_ne_nil a w'
    rw [show a :: w' = w from rfl] at hw hww ⊢
    by_contra h_con
    sorry

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
