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

theorem recognizable_image_of_regular_finite_rank {X : Language α}
    (hX_reg : X.IsRegular)
    (hX_rank : HasFiniteRank I X) :
    IsRecognizable (⇑(mk' (I := I)) '' X) := by
  sorry

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
    (i : ℕ) (hi : i - 1 < (ccDec_aux I u w).length) :
    (ccDec_aux I u (a :: w))[i]'(by rw [ccDec_aux_len_D h]; exact lt_add_of_tsub_lt_right hi) = (ccDec_aux I u w)[i - 1] := by
  -- cases i with
  by_cases hw : w = []
  · simp [hw, ccDec_aux_conn, ccDec_aux] at h
  simp [ccDec_aux_conn] at h
  let t := ccDec_aux I u w
  have ht : ccDec_aux I u w = t := rfl
  rcases t
  · simp [ht] at hi
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
      have : ([a] :: (b :: c_head) :: c_tail)[i]'(sorry) =
          ([a] :: (b :: c_head) :: c_tail)[i - 1 + 1]'(sorry) := by
        sorry
        --rw [getElem_congr _ (show i - 1 + 1 = i from Nat.sub_add_cancel (Nat.succ_le_of_lt hiz))]
        --simp
      simp [this]

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
      · rw [ccDec_aux_tail_D' hab i (by rw [ccDec_aux_len_D hab] at hi; omega)]
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
        rw [ccDec_aux_tail_D' hab i (by omega)]
        rw [ccDec_aux_tail_D' hab (i + 1) (by omega)]
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

lemma ccDec_across_substr (I : Independence α) (w : List α) (h : 1 < (ccDec I w).length) :
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

lemma ccDec_aux_indep (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) :
    Independent I (ccDec_aux I u w)[i] (ccDec_aux I u w)[i + 1] := by
  sorry

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
