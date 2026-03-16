import TraceTheory.Lemmas
import TraceTheory.MyhillNerode
import TraceTheory.RegularExpressions

namespace TraceTheory

variable {α : Type*} {I : Independence α}


/-- Main component of Theorem 4.1 (ii) => (iii).

  For a rational expression X, if every iterative factor of L(X) is connected,
  then X' is star-connected (for some rational expression X' with L(X) = L(X')).

  It is strictly necessary that we use an X' not necessarily equal to X.
  Consider X = {a ∪ b}∗ · ∅; where `a` and `b` are not connected. Then L(X) = ∅ so every
  iterative factor is connected, but X is not star-connected.

  Note that P · ∅ or ∅ · P are the only cases where this patch is needed.
-/
theorem connectedIterativeFactors_equiv_starConnected' (X : RegularExpression α)
    (hconn : ∀ s, IsIterativeFactor X.matches' s → IsConnected I ⟦s⟧) :
    ∃ Y, RegularExpression.isStarConnected I Y ∧ X.matches' = Y.matches' := by
  induction X with
  | zero => use RegularExpression.zero, trivial
  | epsilon => use RegularExpression.epsilon, trivial
  | char a => use RegularExpression.char a, trivial
  | plus P Q ihP ihQ =>
    have ihP_cond : (∀ s, IsIterativeFactor P.matches' s → IsConnected I ⟦s⟧) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      use u, v
      simp only [RegularExpression.matches', Language.mem_add]
      intro n
      left
      exact h n
    have ⟨P', hP'⟩ := ihP ihP_cond
    have ihQ_cond : (∀ s, IsIterativeFactor Q.matches' s → IsConnected I ⟦s⟧) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      use u, v
      simp only [RegularExpression.matches', Language.mem_add]
      intro n
      right
      exact h n
    have ⟨Q', hQ'⟩ := ihQ ihQ_cond
    use P' + Q'
    simp [RegularExpression.isStarConnected, hP', hQ']
  | comp P Q ihP ihQ =>
    by_cases hpe : ¬ ∃ p, p ∈ P.matches'
    · use RegularExpression.zero
      simp [RegularExpression.isStarConnected]
      rw [Language.zero_def]
      apply Language.ext
      intro x
      apply Iff.intro
      all_goals intro h
      · rw [Language.mul_def] at h
        replace ⟨u, hu, v, hv, h⟩ := h
        exact hpe ⟨u, hu⟩
      · exact False.elim h
    by_cases hqe : ¬ ∃ q, q ∈ Q.matches'
    · use RegularExpression.zero
      simp [RegularExpression.isStarConnected]
      rw [Language.zero_def]
      apply Language.ext
      intro x
      apply Iff.intro
      all_goals intro h
      · rw [Language.mul_def] at h
        replace ⟨u, hu, v, hv, h⟩ := h
        exact hqe ⟨v, hv⟩
      · exact False.elim h
    simp at hpe hqe
    have ihP_cond : (∀ s, IsIterativeFactor P.matches' s → IsConnected I ⟦s⟧) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      rcases hpe with ⟨p, hp⟩
      rcases hqe with ⟨q, hq⟩
      use u, v ++ q
      simp only [RegularExpression.matches', Language.mem_mul]
      intro n
      rw [← List.append_assoc]
      use u ++ s ^ n ++ v, h n, q, hq
    have ⟨P', hP'⟩ := ihP ihP_cond
    have ihQ_cond : (∀ s, IsIterativeFactor Q.matches' s → IsConnected I ⟦s⟧) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      rcases hpe with ⟨p, hp⟩
      rcases hqe with ⟨q, hq⟩
      use p ++ u, v
      simp only [RegularExpression.matches', Language.mem_mul]
      intro n
      use p, hp, u ++ s ^ n ++ v, h n
      simp
    have ⟨Q', hQ'⟩ := ihQ ihQ_cond
    use P' * Q'
    simp [RegularExpression.isStarConnected, hP', hQ']
  | star P ih =>
    have ih_cond : ∀ (s : List α), IsIterativeFactor P.matches' s → IsConnected I ⟦s⟧ := by
      intro s ⟨u, v, h⟩
      apply hconn
      use u, v
      intro n
      simp only [RegularExpression.matches', Language.mem_kstar]
      use [u ++ s ^ n ++ v]
      simp_rw [List.append_assoc] at h
      simp_all
    have ⟨P', hP'⟩ := ih ih_cond
    use P'.star
    simp [RegularExpression.isStarConnected, hP']
    intro s hs
    apply hconn
    use [], []
    intro n
    simp only [RegularExpression.matches', List.nil_append, List.append_nil, Language.mem_kstar]
    use List.replicate n s
    constructor
    · rw [← List.prod_replicate]
      induction n with
      | zero =>
        simp only [List.replicate_zero, List.prod_nil, List.flatten_nil]
        rfl
      | succ n' ih =>
        rw [List.replicate_succ]
        simp only [List.prod_cons, ih, List.flatten_cons]
        rfl
    · simp only [List.mem_replicate, ne_eq, and_imp, forall_eq_apply_imp_iff]
      rw [hP'.right]
      intro
      exact hs

/-- Theorem 4.1 (ii) => (iii) -/
theorem connectedIterativeFactors_equiv_starConnected (T : Set (Trace I)) (X : RegularExpression α) (himg : T = toTrace I X.matches')
    (hconn : ∀ s, IsIterativeFactor X.matches' s → IsConnected I ⟦s⟧) :
    ∃ P, RegularExpression.isStarConnected I P ∧ T = (RegularExpression.matches_trace I P) := by
  simp [RegularExpression.matches_toTrace]
  have ⟨P, hP⟩ := connectedIterativeFactors_equiv_starConnected' X hconn
  use P
  simp [hP, himg]

/-- Theorem 4.1 (iii) => (iv) -/
theorem starConnected_is_cRational (X : RegularExpression α) (h : RegularExpression.isStarConnected I X) :
    RegularExpression.matches_trace I X = RegularExpression.matches_cstar_trace I X := by
  induction X with
  | zero => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace]
  | epsilon => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace]
  | char _ => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace]
  | plus P Q ihP ihQ => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace, ihP h.1, ihQ h.2]
  | comp P Q ihP ihQ => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace, ihP h.1, ihQ h.2]
  | star P ih =>
    unfold RegularExpression.matches_trace RegularExpression.matches_cstar_trace
    simp [<- ih h.1]
    unfold RegularExpression.isStarConnected at h
    have hP_conn : (∀ t ∈ RegularExpression.matches_trace I P, IsConnected I t) := by
      intro t ht
      rcases t with ⟨w₀⟩
      rw [show Quot.mk (⇑(TraceSetoid I)) w₀ = ⟦w₀⟧ from rfl] at ht ⊢
      rw [RegularExpression.matches_toTrace] at ht
      simp [toTrace] at ht
      rcases ht with ⟨w, hw⟩
      rw [← hw.2]
      exact h.2 w hw.1
    rw [connectedComponents_of_connected _ hP_conn]
    rw [kstar_eq_minusEps_trace]

end TraceTheory
