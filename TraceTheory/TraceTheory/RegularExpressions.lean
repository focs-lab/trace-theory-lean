import TraceTheory.Lemmas
import Mathlib.Computability.RegularExpressions

open TraceTheory

namespace RegularExpression

variable {α : Type*} {I : Independence α}

def isStarConnected (I : Independence α) : RegularExpression α → Prop
  | 0 => True
  | 1 => True
  | char _ => True
  | P + Q => isStarConnected I P ∧ isStarConnected I Q
  | P * Q => isStarConnected I P ∧ isStarConnected I Q
  | star P => isStarConnected I P ∧ (∀ s ∈ P.matches', IsConnected I ⟦s⟧)

-- Interpretation of this RegularExpression as operating on trace languages.
def matches_trace (I : Independence α) : RegularExpression α → Set (Trace I)
  | 0 => {}
  | 1 => {1}
  | char a => {⟦[a]⟧}
  | P + Q => (matches_trace I P) ∪ (matches_trace I Q)
  | P * Q => {t | ∃ p : (matches_trace I P), ∃ q : (matches_trace I Q), t = p * q}
  | star P => kstar (matches_trace I P)

def isStarConnected_trace (I : Independence α) : RegularExpression α → Prop
  | 0 => True
  | 1 => True
  | char _ => True
  | P + Q => isStarConnected I P ∧ isStarConnected I Q
  | P * Q => isStarConnected I P ∧ isStarConnected I Q
  | star P => isStarConnected I P ∧ (∀ t ∈ matches_trace I P, @IsConnected α I t)

-- Interpretation of this RegularExpression as a <c-rational expression> operating on trace languages.
def matches_cstar_trace (I : Independence α) : RegularExpression α → Set (Trace I)
  | 0 => {}
  | 1 => {1}
  | char a => {⟦[a]⟧}
  | P + Q => (matches_cstar_trace I P) ∪ (matches_cstar_trace I Q)
  | P * Q => {t | ∃ p : (matches_cstar_trace I P), ∃ q : (matches_cstar_trace I Q), t = p * q}
  | star P => kstar (connectedComponents (matches_cstar_trace I P))

/-- Interpreting this RegularExpression as operating on Trace Languages gives the same matching set
  as interpreting (as usual) on String Languages and then projecting to Traces.
-/
theorem matches_toTrace (P : RegularExpression α) : (matches_trace I P) = toTrace I P.matches' := by
  induction P with
  | zero => simp [toTrace, matches_trace, Language.zero_def]
  | epsilon => simp [toTrace, matches_trace, Language.one_def]
  | char a =>
    simp [toTrace, matches_trace, Set.image]
    apply Set.ext_iff.mpr
    intro t
    apply Iff.intro
    · simp
      intro h
      use [a]
      exact ⟨rfl, Eq.symm h⟩
    · simp
      intro x hx hat
      replace hx : x = [a] := hx
      rw [<- hat, hx]
      rfl
  | plus P Q ihP ihQ =>
    unfold matches_trace matches'
    simp [ihP, ihQ]
    apply Set.ext_iff.mpr
    intro t
    apply Iff.intro
    · intro h
      cases h
      all_goals
        rename_i h
        simp [toTrace] at h
        have ⟨x, hx⟩ := h
        use x
        simp [hx, Language.add_def]
    · intro h
      simp [Language.add_def, toTrace] at h
      have ⟨x, ⟨hx, hxt⟩⟩ := h
      simp [<- hxt, toTrace]
      cases hx with
      | inl hx => apply Or.inl; use x
      | inr hx => apply Or.inr; use x
  | comp P Q ihP ihQ =>
    unfold matches_trace matches' toTrace
    rw [Set.image]
    apply Set.ext_iff.mpr
    intro t
    apply Iff.intro
    all_goals simp
    · simp [ihP, ihQ, toTrace]
      intro u hu v hv ht
      simp [Language.mul_def]
      use u; simp [hu]
      use v; simp [hv]
      rw [ht]
      rfl
    · simp [Language.mul_def]
      intro w u hu v hv hw ht
      simp [ihP, ihQ, toTrace]
      use u; simp [hu]
      use v; simp [hv]
      rw [<- ht, <- hw]
      rfl
  | star P ih =>
    unfold matches_trace matches'
    rw [kstar_toTrace_comm, ih]

@[simp]
lemma matches_toTrace_dist (P Q : RegularExpression α) :
    toTrace I (P.matches' + Q.matches') = toTrace I P.matches' ∪ toTrace I Q.matches' := by
  rw [show P.matches' + Q.matches' = (P + Q).matches' from rfl]
  repeat rw [<- matches_toTrace]
  simp [matches_trace]

end RegularExpression
