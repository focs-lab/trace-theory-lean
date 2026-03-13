import TraceTheory.Lemmas
import TraceTheory.MyhillNerode
import TraceTheory.RegularExpressions

namespace Trace

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
    (hconn : ∀ s, isIterativeFactor X.matches' s → @isConnected' α I s) :
    ∃ Y, RegularExpression.isStarConnected I Y ∧ X.matches' = Y.matches' := by
  induction X with
  | zero => use RegularExpression.zero, trivial
  | epsilon => use RegularExpression.epsilon, trivial
  | char a => use RegularExpression.char a, trivial
  | plus P Q ihP ihQ =>
    have ihP_cond : (∀ s, isIterativeFactor P.matches' s → @isConnected' α I s) := by
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

    have ihQ_cond : (∀ s, isIterativeFactor Q.matches' s → @isConnected' α I s) := by
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

    have ihP_cond : (∀ s, isIterativeFactor P.matches' s → @isConnected' α I s) := by
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

    have ihQ_cond : (∀ s, isIterativeFactor Q.matches' s → @isConnected' α I s) := by
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
    have ih_cond : ∀ (s : List α), isIterativeFactor P.matches' s → @isConnected' α I s := by
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
    (hconn : ∀ s, isIterativeFactor X.matches' s → @isConnected' α I s) :
    ∃ P, RegularExpression.isStarConnected I P ∧ T = (RegularExpression.matches_trace I P) := by
  simp [RegularExpression.matches_toTrace]
  have ⟨P, hP⟩ := connectedIterativeFactors_equiv_starConnected' X hconn
  use P
  simp [hP, himg]

lemma append_indep_is_disconnected_chars (u v : Trace I) (huv : independent' u v)
    (a b : { a // a ∈ u * v }) (ha : a.1 ∈ u) (hb : b.1 ∈ v) :
    ¬ (dependencyTransClosureIn (u * v)) a b := by
  intro h
  induction h with
  | single h =>
    rename_i b
    apply h
    exact huv a b ha hb
  | tail h h_tail ih =>
    rename_i b c
    simp at ih
    have hbu : b.1 ∈ u :=  by
      have hb_uv := mem_append.mp b.2
      simp [ih] at hb_uv
      exact hb_uv
    simp [dependencyIn, inducedDependence] at h_tail
    unfold independent' at huv
    exact h_tail (huv b c hbu hb)

lemma append_indep_is_disconnected (u v : Trace I) (h : independent' u v) (hu : u ≠ ⟦[]⟧) (hv : v ≠ ⟦[]⟧) :
    ¬isConnected (u * v) := by
  by_contra h_con
  have ⟨a, ha⟩ := empty_is_eps u hu
  have ⟨b, hb⟩ := empty_is_eps v hv
  have h_ab_con := h_con ⟨a, mem_append.mpr (Or.inl ha)⟩ ⟨b, mem_append.mpr (Or.inr hb)⟩
  have h_ab_dis := append_indep_is_disconnected_chars u v h ⟨a, mem_append.mpr (Or.inl ha)⟩ ⟨b, mem_append.mpr (Or.inr hb)⟩ ha hb
  exact h_ab_dis h_ab_con

lemma connectedComponents_of_connected (T : Set (Trace I)) (h : ∀ t ∈ T, isConnected t) :
    connectedComponents T = T \ {⟦[]⟧} := by
  apply Set.ext
  intro t
  apply Iff.intro
  · intro ⟨ht, htz, v, htv, htv_id⟩
    simp [htz]
    replace h := h (t * v) htv
    have hvz : v = ⟦[]⟧ := by
      by_contra hvz
      exact append_indep_is_disconnected t v htv_id htz hvz h
    rw [hvz, right_id] at htv
    exact htv
  · intro ⟨ht, htz⟩
    use (h t ht), htz, ⟦[]⟧
    rw [right_id]
    use ht
    unfold independent'
    simp [show ⟦[]⟧ = mk' [] from rfl, eps_is_empty]


lemma empty_iff {w : List α} : (⟦w⟧ : Trace I) = ⟦[]⟧ ↔ w = [] := by
  cases w with
  | nil => simp
  | cons a u =>
    apply Iff.intro
    · intro h
      have h_au := length_eq_of_equiv (Quotient.exact h)
      simp at h_au
    · simp

def isEmpty : Trace I → Bool := Quotient.lift List.isEmpty (by
  intro u v huv
  cases u with
  | nil => rw [empty_iff.mp (Eq.symm (Quotient.sound huv))]
  | cons a u =>
    cases v with
    | nil => rw [empty_iff.mp (Quotient.sound huv)]
    | cons b v => rfl
)

lemma isEmpty_iff {t : Trace I} : t.isEmpty = true ↔ t = ⟦[]⟧ := by
  apply Iff.intro
  · intro h
    rcases t with ⟨s⟩
    rw [List.isEmpty_iff.mp h]
    rfl
  · intro h
    rw [h]
    rfl

lemma traceFlatten_filter_not_isEmpty :
    ∀ {L : List (Trace I)}, traceFlatten (List.filter (!·.isEmpty) L) = traceFlatten L
  | [] => rfl
  | t :: L => by
    by_cases ht : t.isEmpty
    · apply isEmpty_iff.mp at ht
      simp [ht]
      simp [show isEmpty ⟦[]⟧ = true from rfl]
      exact traceFlatten_filter_not_isEmpty (L := L)
    · simp [ht]
      repeat rw [traceFlatten_append]
      rw [traceFlatten_filter_not_isEmpty (L := L)]

lemma kstar_eq_minusEps (L : Language α) : KStar.kstar (L \ {[]}) = KStar.kstar L := by
  apply Set.ext
  intro w
  apply Iff.intro
  · intro ⟨ls, hw, hls⟩
    use ls
    simp [hw]
    exact fun y hy => Set.diff_subset (hls y hy)
  · intro ⟨ls, hls, ht⟩
    use ls.filter (!·.isEmpty)
    simp
    apply And.intro
    · simp [hls, List.flatten_filter_not_isEmpty]
    · intro y hy hyz
      exact Set.mem_diff_singleton.mpr ⟨ht y hy, hyz⟩

lemma kstar_eq_minusEps_trace (T : Set (Trace I)) : kstar (T \ {⟦[]⟧}) = kstar T := by
  apply Set.ext
  intro t
  apply Iff.intro
  · intro ⟨ls, hls, ht⟩
    use ls
    simp [ht]
    exact fun y hy => Set.diff_subset (hls y hy)
  · intro ⟨ls, hls, ht⟩
    use ls.filter (!·.isEmpty)
    simp
    apply And.intro
    · intro y hy hyz
      exact ⟨hls y hy, Trace.isEmpty_iff.ne.mp (ne_true_of_eq_false hyz)⟩
    · simp [traceFlatten_filter_not_isEmpty, ht]


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
    have hP_conn : (∀ t ∈ RegularExpression.matches_trace I P, t.isConnected) := by
      intro t ht
      rcases t with ⟨w₀⟩
      rw [show Quot.mk (⇑(traceSetoid I)) w₀ = ⟦w₀⟧ from rfl] at ht ⊢
      rw [RegularExpression.matches_toTrace] at ht
      simp [toTrace] at ht
      rcases ht with ⟨w, hw⟩
      rw [<- hw.2, <- isConnected_toTrace]
      exact h.2 w hw.1
    rw [connectedComponents_of_connected _ hP_conn]
    rw [kstar_eq_minusEps_trace]


end Trace
