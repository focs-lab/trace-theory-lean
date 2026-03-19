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

lemma recognizable_zero : IsRecognizable (∅ : Set (Trace I)) :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, by simp⟩

lemma recognizable_epsilon : IsRecognizable ({ 1 } : Set (Trace I)) := by
  sorry

lemma recognizable_char (a : α) : IsRecognizable ({ ⟦[a]⟧ } : Set (Trace I)) := by
  sorry

lemma recognizable_union {M : Type} [Monoid M] {P Q : Set M}
    (hP : IsRecognizable P) (hQ : IsRecognizable Q) : IsRecognizable (P ∪ Q) := by
  sorry

lemma recognizable_mul {P Q : Set (Trace I)}
    (hP : IsRecognizable P) (hQ : IsRecognizable Q) : IsRecognizable (P * Q) := by
  sorry

lemma recognizable_cstar {P : Set (Trace I)}
    (hP : IsRecognizable P) : IsRecognizable (kstar (connectedComponents P)) := by
  sorry

/-- Theorem 4.1 (iv) => (i) -/
theorem recognizable_of_cRational (X : RegularExpression α) :
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

--- variable [DecidableRel I.rel]

---
noncomputable instance : ∀ w x y, Decidable (dependencyTransClosureInL I w x y) :=
  fun w x y => Classical.propDecidable (dependencyTransClosureInL I w x y)

noncomputable def ccDec_aux' (I : Independence α) (w₀ w : List α) : List (List α) :=
  match w with
  | [] => [[]]
  | a :: w =>
    match ccDec_aux' I w₀ w with
    | [] => [] -- dummy value, unreachable by construction
    | v :: vs =>
      match v with
      | [] => [a] :: vs
      | b :: v =>
        if dependencyTransClosureInL I w₀ a b
          then (a :: b :: v) :: vs
          else [a] :: (b :: v) :: vs

lemma ccDec'_aux_nonempty' (w₀ w : List α) : (ccDec_aux' I w₀ w) ≠ [] := by
  induction w with
  | nil => simp [ccDec_aux']
  | cons a u ih =>
    simp [ccDec_aux']
    cases hs : ccDec_aux' I w₀ u
    · simp [hs] at ih
    · simp
      rename_i c_head c_tail
      cases c_head with
      | nil => simp
      | cons b c_head =>
        simp
        by_cases hab : dependencyTransClosureInL I w₀ a b
        all_goals simp [hab]

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

lemma ccDec'_aux_nonempty (u w : List α) (i : ℕ) (hi : i < (ccDec_aux' I u w).length) (hz : w ≠ []) :
    (ccDec_aux' I u w)[i] ≠ [] := by
  induction w generalizing i with
  | nil => simp at hz
  | cons a w ih =>
    clear hz
    by_cases hiz : i = 0
    · suffices hs_dec : (∃ _1 _2 _3, (ccDec_aux' I u (a :: w)) = (_1 :: _2) :: _3) ∨ (ccDec_aux' I u (a :: w)) = [] from by
        rcases hs_dec with ⟨hs_dec⟩
        · replace ⟨_1, _2, _3, hs_dec⟩ := hs_dec
          simp [hs_dec, hiz]
        · rename_i hs_dec
          simp [hs_dec] at hi
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
    · -- cases a
      have : (ccDec_aux' I u (a :: w))[i] = (ccDec_aux' I u w)[i]'sorry ∨ (ccDec_aux' I u (a :: w))[i] = (ccDec_aux' I u w)[i - 1]'sorry := by
        simp [ccDec_aux']
        /- cases ccDec_aux' I u w
        · simp
        · rename_i c_head c_tail
          simp
          cases c_head with
          | nil => simp
          | cons b c_head =>
            simp
            by_cases hab : dependencyTransClosureInL I u a b
            all_goals simp [hab] -/
        sorry
      cases this with
      | inl h =>
        rw [h]
        apply ih
        by_contra hz
        simp [ccDec_aux', hz] at hi
        exact hiz hi
      | inr h =>
        rw [h]
        have : i - 1 < (ccDec_aux' I u w).length := by sorry
        apply ih (i - 1) this
        by_contra hz
        simp [ccDec_aux', hz] at hi
        exact hiz hi




noncomputable def ccDec_aux (I : Independence α) (w₀ w : List α) (p : α) : List (List α × List α) :=
  match w with
  | [] => [⟨[], []⟩]
  | a :: w =>
    match ccDec_aux I w₀ w p with
    | [] => [] -- dummy value, unreachable by construction
    | v :: vs =>
      if dependencyTransClosureInL I w₀ a p
        then match v.2 with
        | [] => ⟨a :: v.1, v.2⟩ :: vs
        | _ :: _ => ⟨[a], []⟩ :: v :: vs
        else ⟨v.1, a :: v.2⟩ :: vs

noncomputable def ccDec (I : Independence α) (w : List α) (p : α) : List (List α × List α) := ccDec_aux I w w p

lemma ccDec_aux_nonempty (w₀ w : List α) (p : α) : (ccDec_aux I w₀ w p) ≠ [] := by
  induction w with
  | nil => simp [ccDec_aux]
  | cons a u ih =>
    simp [ccDec_aux]
    cases hs : ccDec_aux I w₀ u p
    · simp [hs] at ih
    · simp
      by_cases ha : dependencyTransClosureInL I w₀ a p
      · rename_i s_head s_tail
        cases s_head.2
        all_goals simp [ha]
      · simp [ha]

lemma ccDec_aux_zero_idx {w₀ w : List α} {p : α} : 0 < (ccDec_aux I w₀ w p).length := List.length_pos_iff.mpr (ccDec_aux_nonempty _ _ _)

lemma ccDEc_nonempty (w : List α) (p : α) : (ccDec I w p) ≠ [] := ccDec_aux_nonempty w w p

/- lemma ccDec_invar (u w : List α) (a p : α) (i : Fin (ccDec_aux I (u ++ [p]) (w ++ [p]) p).length) :
    (ccDec_aux I (u ++ [p]) (a :: w ++ [p]) p)[i] = (ccDec_aux I (u ++ [p]) (w ++ [p]) p)[i] ∨
    (ccDec_aux I (u ++ [p]) (a :: w ++ [p]) p)[i] = (ccDec_aux I (u ++ [p]) (w ++ [p]) p)[i]
  := by
  simp [ccDec_aux] -/

lemma ccDec_aux_1_nonempty_head (u w : List α) (p : α) (h : w ≠ []) :
    ((ccDec_aux I (u ++ [p]) (w ++ [p]) p)[0]'(ccDec_aux_zero_idx)).1 ≠ [] := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    clear h
    by_cases hw : w = []
    · simp [hw, ccDec_aux, depTrClIn_refl]
      by_cases hau : dependencyTransClosureInL I (u ++ [p]) a p
      all_goals simp [hau]
    · simp [hw] at ih
      let t := ccDec_aux I (u ++ [p]) (w ++ [p]) p
      have ht : ccDec_aux I (u ++ [p]) (w ++ [p]) p = t := rfl
      rcases t
      · exfalso
        exact ccDec_aux_nonempty _ _ _ ht
      · rename_i s_head s_tail
        by_cases hau : dependencyTransClosureInL I (u ++ [p]) a p
        · suffices hs_dec : ∃ _1 _2 _3 _4, (ccDec_aux I (u ++ [p]) (a :: w ++ [p]) p) = (_1 ::_2, _3) :: _4 from by
            replace ⟨_1, _2, _3, _4, hs_dec⟩ := hs_dec
            rw [List.getElem_of_eq hs_dec]
            simp
          simp [ccDec_aux, ht, hau]
          cases s_head.2
          · simp
          · simp
        · simp [ccDec_aux, ht, hau]
          have hs_dec : (ccDec_aux I (u ++ [p]) (w ++ [p]) p)[0]'(ccDec_aux_zero_idx) = (s_head :: s_tail)[0] := List.getElem_of_eq ht _
          simp [hs_dec] at ih
          exact ih

lemma ccDec_aux_1_nonempty (u w : List α) (p : α) (i : Fin (ccDec_aux I (u ++ [p]) (w ++ [p]) p).length) :
    (ccDec_aux I (u ++ [p]) (w ++ [p]) p)[i].1 ≠ [] := by
  induction w with
  | nil =>
    suffices hs_dec : ccDec_aux I (u ++ [p]) ([] ++ [p]) p = [([p], [])] from by
      rw [Fin.getElem_fin]
      rw [List.getElem_of_eq hs_dec]
      simp
    simp [ccDec_aux, dependencyTransClosureInL]
    unfold dependencyInL
    apply Relation.TransGen.single
    simp [inducedDependence, Independence.irrefl]
  | cons a w ih =>
    by_cases hw : w = []
    · rcases i with ⟨i, hi⟩
      simp [hw, ccDec_aux, depTrClIn_refl]
      by_cases hau : dependencyTransClosureInL I (u ++ [p]) a p
      all_goals simp [hau]
    · simp [hw] at ih
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => exact ccDec_aux_1_nonempty_head _ _ _ (by simp)
      | succ i =>
        by_cases hau : dependencyTransClosureInL I (u ++ [p]) a p
        · let temp := ccDec_aux I (u ++ [p]) (w ++ [p]) p
          have htemp : ccDec_aux I (u ++ [p]) (w ++ [p]) p = temp := rfl
          rcases temp
          · exfalso
            exact ccDec_aux_nonempty _ _ _ htemp
          · rename_i s_head s_tail
            suffices hs_dec : (∃ _1 _2, (ccDec_aux I (u ++ [p]) (a :: w ++ [p]) p) = _1 :: _2) from by
              replace ⟨_1, _2, hs_dec⟩ := hs_dec
              have h_2ne : (_2[i]'(by rw [hs_dec] at hi; exact Nat.succ_lt_succ_iff.mp hi)).1 ≠ [] := by
                simp [ccDec_aux, htemp, hau] at hs_dec
                contrapose hs_dec
                cases s_head.2
                · simp
                  intro _
                  contrapose hs_dec
                  rw [<- List.getElem_of_eq hs_dec]
                  all_goals sorry
                · simp
                  intro _
                  contrapose hs_dec
                  rw [<- List.getElem_of_eq hs_dec, <- List.getElem_of_eq htemp]
                  · exact ih ⟨i, by sorry⟩
                  · rw [<- htemp]
                    sorry
              rw [Fin.getElem_fin]
              rw [List.getElem_of_eq hs_dec]
              simp [h_2ne]
            simp [ccDec_aux, htemp, hau]
            cases s_head.2
            · simp
            · simp
        · suffices hs_dec : (∃ _1 _2, (ccDec_aux I (u ++ [p]) (a :: w ++ [p]) p) = _1 :: _2) from by
            replace ⟨_1, _2, hs_dec⟩ := hs_dec
            have h_2ne : (_2[i]'(by rw [hs_dec] at hi; exact Nat.succ_lt_succ_iff.mp hi)).1 ≠ [] := by
              sorry
            rw [Fin.getElem_fin]
            rw [List.getElem_of_eq hs_dec]
            simp [h_2ne]
          simp [ccDec_aux, hau]
          let temp := ccDec_aux I (u ++ [p]) (w ++ [p]) p
          have htemp : ccDec_aux I (u ++ [p]) (w ++ [p]) p = temp := rfl
          rcases temp
          · exfalso
            exact ccDec_aux_nonempty _ _ _ htemp
          · simp [htemp]

lemma ccDec_aux_2_nonempty (u w : List α) (p : α) (i : Fin (ccDec_aux I (u ++ [p]) (w ++ [p]) p).length) (hi : i.1 > 0) :
    (ccDec_aux I (u ++ [p]) (w ++ [p]) p)[i].2 ≠ [] := by sorry

lemma ccDec_aux_disconn_2_nonempty (u w : List α) (p : α) (h : ¬ IsConnectedL I (w ++ [p])) :
    ((ccDec_aux I (u ++ [p]) (w ++ [p]) p).getLast (ccDec_aux_nonempty _ _ _)).2 ≠ [] := by
  induction w with
  | nil => simp [IsConnectedL, depTrClIn_refl] at h
  | cons a w ih =>
    by_cases hpa : dependencyTransClosureInL I (u ++ [p]) a p
    · suffices hs_dec : ∃ _1 _2 _3 _4, ccDec_aux I (u ++ [p]) (a :: w ++ [p]) p = _1 ++ [(_2, _3 :: _4)] from by
        replace ⟨_1, _2, _3, _4, hs_dec⟩ := hs_dec
        rw [List.getLast.congr_simp _ _ hs_dec]
        simp
      simp [ccDec_aux, hpa]
      let temp := ccDec_aux I (u ++ [p]) (w ++ [p]) p
      have htemp : ccDec_aux I (u ++ [p]) (w ++ [p]) p = temp := rfl
      rcases temp
      · exfalso; exact ccDec_aux_nonempty _ _ _ htemp
      · rename_i c_head c_tail
        simp [htemp]
        cases c_head.2
        · simp
          -- ccDec_aux_2_nonempty
          sorry
        · simp
          -- ccDec_aux_2_nonempty
          sorry
    · have ih_cond : ¬IsConnectedL I (w ++ [p]) := by sorry
      replace ih := ih ih_cond
      suffices hs_dec : ∃ _1 _2 _3 _4, ccDec_aux I (u ++ [p]) (a :: w ++ [p]) p = _1 ++ [(_2, _3 :: _4)] from by
        replace ⟨_1, _2, _3, _4, hs_dec⟩ := hs_dec
        rw [List.getLast.congr_simp _ _ hs_dec]
        simp
      have hr_dec : ∃ _1 _2 _3 _4, ccDec_aux I (u ++ [p]) (w ++ [p]) p = _1 ++ [(_2, _3 :: _4)] := by
        sorry
      replace ⟨_1, _2, _3, _4, hr_dec⟩ := hr_dec
      simp [ccDec_aux, hr_dec]
      sorry

lemma ccDec_1_2_subst (w : List α) (p : α) (i : ℕ) (hi : i < (ccDec I (w ++ [p]) p).length) :
    List.Sublist ((ccDec I (w ++ [p]) p)[i].1 ++ (ccDec I (w ++ [p]) p)[i].2) w := by sorry

lemma ccDec_2_1_subst (w : List α) (p : α) (i : ℕ) (hi : i + 1 < (ccDec I (w ++ [p]) p).length) :
    List.Sublist ((ccDec I (w ++ [p]) p)[i].2 ++ (ccDec I (w ++ [p]) p)[i + 1].1) w := by sorry

lemma ccDec_across_substr (w : List α) (p : α) (i : ℕ) (hi : i + 1 < (ccDec I (w ++ [p]) p).length) :
    List.Sublist (
      ((ccDec I (w ++ [p]) p).getLast (ccDEc_nonempty _ _)).1 ++
      ((ccDec I (w ++ [p]) p).getLast (ccDEc_nonempty _ _)).2 ++
      (ccDec I (w ++ [p]) p)[0].1 ++
      (ccDec I (w ++ [p]) p)[0].2
    ) (w ++ w) := by sorry

/-
def proj2 (S : Set α) (hd : ∀ x, Decidable (x ∈ S)) (w : List α) : List α := w.filter (· ∈ S)

lemma proj2_prop {S : Set α} {hd : ∀ x, Decidable (x ∈ S)} {w : List α} {a : α} : a ∈ proj2 S hd w → a ∈ S := by
  induction w with
  | nil => simp [proj2]
  | cons b u ih =>
    intro h
    by_cases hab : a = b
    · simp [proj2, <- hab] at h
      exact h
    · simp [proj2] at h
      exact h.2

variable [LinearOrder α] in
theorem lexNf_dup_lexNf_isConnected {w : List α} (h : IsLexNf I (w ++ w)) : IsConnectedL I w := by
  have h' : IsLexNf I w := by
    contrapose h
    simp [IsLexNf] at h ⊢
    rcases h with ⟨u, h⟩
    use w ++ u
    exact ⟨TraceEqv.compat (TraceEqv.refl w) h.1, List.append_left_lt h.right⟩

  by_contra h_con
  simp [IsConnectedL] at h_con
  choose a b h_con using h_con
  let A := {x | dependencyTransClosureInL I w a x}
  let B := {x | ¬ dependencyTransClosureInL I w a x}
  have hA_dec : ∀ x, Decidable (x ∈ A) := fun x => Classical.propDecidable (x ∈ A)
  have hB_dec : ∀ x, Decidable (x ∈ B) := fun x => Classical.propDecidable (x ∈ B)
  let u := proj2 A hA_dec w
  let v := proj2 B hB_dec w
  have : Independent I u v := by
    intro j hj k hk
    have hjw : j ∈ w := List.mem_of_mem_filter hj
    have hkw : k ∈ w := List.mem_of_mem_filter hk
    unfold u at hj
    unfold v at hk
    replace hj := proj2_prop hj
    replace hk := proj2_prop hk
    replace hj : dependencyTransClosureInL I w a j := hj
    replace hk : ¬ dependencyTransClosureInL I w a k := hk
    by_contra hjk

    have : dependencyTransClosureInL I w a k := by
      have : dependencyInL I w j k := ⟨hjk, hjw, hkw⟩
      exact Relation.TransGen.tail hj this

    exact hk this

  /- have : a ∈ u := by
    have ha_A : a ∈ A := ⟨ha, ha, Relation.TransGen.single ((inducedDependence I).refl a)⟩
    exact List.mem_filter_of_mem ha (decide_eq_true ha_A)
  have : b ∈ v := by
    have hb_B : b ∈ B := by simp [B, dependencyTransClosureInL, h_con]
    exact List.mem_filter_of_mem hb (decide_eq_true hb_B) -/
  sorry

-/

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

omit [Fintype α] [LinearOrder α] in
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
