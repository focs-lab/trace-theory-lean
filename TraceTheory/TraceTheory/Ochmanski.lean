import TraceTheory.Lemmas
import TraceTheory.MyhillNerode
import TraceTheory.RegularExpressions

namespace TraceTheory

variable {α : Type} {I : Independence α}


/-- Main component of Theorem 4.1 (ii) => (iii).

  For a rational expression X, if every iterative factor of L(X) is connected,
  then X' is star-connected (for some rational expression X' with L(X) = L(X')).

  It is strictly necessary that we use an X' not necessarily equal to X.
  Consider X = {a ∪ b}∗ · ∅; where `a` and `b` are not connected. Then L(X) = ∅ so every
  iterative factor is connected, but X is not star-connected.

  Note that P · ∅ or ∅ · P are the only cases where this patch is needed.
-/
theorem connectedIterativeFactors_equiv_starConnected' (X : RegularExpression α)
    (hconn : ∀ s, isIterativeFactor X.matches' s → @isConnected α I s) :
    ∃ Y, RegularExpression.isStarConnected I Y ∧ X.matches' = Y.matches' := by
  induction X with
  | zero => use RegularExpression.zero, trivial
  | epsilon => use RegularExpression.epsilon, trivial
  | char a => use RegularExpression.char a, trivial
  | plus P Q ihP ihQ =>
    have ihP_cond : (∀ s, isIterativeFactor P.matches' s → @isConnected α I s) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      use u, v
      intro ts hts
      replace h := h ts hts
      have h_match_subset : ∀ p ∈ P.matches', p ∈ P.matches' + Q.matches' := by
        simp [Language.add_def]
        intro p hp
        apply (Set.mem_union _ _ _).mpr
        simp [hp]
      exact h_match_subset _ h
    have ⟨P', hP'⟩ := ihP ihP_cond

    have ihQ_cond : (∀ s, isIterativeFactor Q.matches' s → @isConnected α I s) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      use u, v
      intro ts hts
      replace h := h ts hts
      have h_match_subset : ∀ q ∈ Q.matches', q ∈ P.matches' + Q.matches' := by
        simp [Language.add_def]
        intro q hq
        apply (Set.mem_union _ _ _).mpr
        simp [hq]
      exact h_match_subset _ h
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

    have ihP_cond : (∀ s, isIterativeFactor P.matches' s → @isConnected α I s) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      have ⟨q, hq⟩ := hqe
      use u, v ++ q
      intro ts hts
      replace h := h ts hts
      unfold RegularExpression.matches'
      use u ++ ts.flatten ++ v, h, q, hq
      simp
    have ⟨P', hP'⟩ := ihP ihP_cond

    have ihQ_cond : (∀ s, isIterativeFactor Q.matches' s → @isConnected α I s) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      have ⟨p, hp⟩ := hpe
      use p ++ u, v
      intro ts hts
      replace h := h ts hts
      unfold RegularExpression.matches'
      use p, hp, u ++ ts.flatten ++ v, h
      simp
    have ⟨Q', hQ'⟩ := ihQ ihQ_cond

    use P' * Q'
    simp [RegularExpression.isStarConnected, hP', hQ']
  | star P ih =>
    have ih_cond : ∀ (s : List α), isIterativeFactor P.matches' s → @isConnected α I s := by
      intro s ⟨u, v, h⟩
      apply hconn
      use u, v
      intro ts hts
      replace h := h ts hts
      simp [Language.kstar_def]
      use [u ++ ts.flatten ++ v]
      simp [<- List.append_assoc]
      exact h
    have ⟨P', hP'⟩ := ih ih_cond
    use P'.star
    simp [RegularExpression.isStarConnected, hP']
    intro s hs
    apply hconn
    use [], []
    intro ts hts
    simp [Language.kstar_def]
    use ts
    simp
    intro y hy
    rw [hts y hy, hP'.right]
    exact hs

/-- Theorem 4.1 (ii) => (iii) -/
theorem connectedIterativeFactors_equiv_starConnected (T : Set (Trace I)) (X : RegularExpression α) (himg : T = toTrace X.matches')
    (hconn : ∀ s, isIterativeFactor X.matches' s → @isConnected α I s) :
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
    have hP_conn : (∀ t ∈ RegularExpression.matches_trace I P, isConnectedT t) := by
      intro t ht
      rcases t with ⟨w₀⟩
      rw [show Quot.mk (⇑(TraceSetoid I)) w₀ = ⟦w₀⟧ from rfl] at ht ⊢
      rw [RegularExpression.matches_toTrace] at ht
      simp [toTrace] at ht
      rcases ht with ⟨w, hw⟩
      rw [<- hw.2, <- isConnected_toTrace]
      exact h.2 w hw.1
    rw [connectedComponents_of_connected _ hP_conn]
    rw [kstar_eq_minusEps_trace]


end TraceTheory
