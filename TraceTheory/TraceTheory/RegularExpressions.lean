import TraceTheory.Lemmas
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Computability.RegularExpressions

open scoped Pointwise

open TraceTheory

namespace RegularExpression

variable {α : Type*} {I : Independence α}

def IsStarConnected (I : Independence α) : RegularExpression α → Prop
  | 0 => True
  | 1 => True
  | char _ => True
  | plus P Q => IsStarConnected I P ∧ IsStarConnected I Q
  | comp P Q => IsStarConnected I P ∧ IsStarConnected I Q
  | star P => IsStarConnected I P ∧ (∀ s ∈ P.matches', IsConnected I ⟦s⟧)

-- Interpretation of this RegularExpression as operating on trace languages.
def matches_trace (I : Independence α) : RegularExpression α → Set (Trace I)
  | 0 => ∅
  | 1 => { 1 }
  | char a => { ⟦[a]⟧ }
  | plus P Q => matches_trace I P ∪ matches_trace I Q
  | comp P Q => matches_trace I P * matches_trace I Q
  | star P => kstar (matches_trace I P)

def IsStarConnected_trace (I : Independence α) : RegularExpression α → Prop
  | 0 => True
  | 1 => True
  | char _ => True
  | plus P Q => IsStarConnected I P ∧ IsStarConnected I Q
  | comp P Q => IsStarConnected I P ∧ IsStarConnected I Q
  | star P => IsStarConnected I P ∧ (∀ t ∈ matches_trace I P, IsConnected I t)

-- Interpretation of this RegularExpression as a c-rational expression operating on trace languages.
def matches_cstar_trace (I : Independence α) : RegularExpression α → Set (Trace I)
  | 0 => ∅
  | 1 => { 1 }
  | char a => { ⟦[a]⟧ }
  | P + Q => matches_cstar_trace I P ∪ matches_cstar_trace I Q
  | P * Q => matches_cstar_trace I P * matches_cstar_trace I Q
  | star P => kstar (connectedComponents (matches_cstar_trace I P))

/-- Interpreting this RegularExpression as operating on Trace Languages gives the same matching set
  as interpreting (as usual) on String Languages and then projecting to Traces.
-/
theorem matches_toTrace (P : RegularExpression α) : matches_trace I P = toTrace I P.matches' := by
  induction P with
  | zero => simp [toTrace, matches_trace, Language.zero_def]
  | epsilon => simp [toTrace, matches_trace, Language.one_def]
  | char a =>
    unfold matches_trace matches' toTrace
    rw [Set.image_singleton]
    rfl
  | plus P Q ihP ihQ =>
    unfold matches_trace matches' toTrace
    rw [ihP, ihQ, Language.add_def, Set.image_union]
    rfl
  | comp P Q ihP ihQ =>
    unfold matches_trace matches' toTrace
    rw [ihP, ihQ, Set.image_mul]
    rfl
  | star P ih =>
    unfold matches_trace matches'
    rw [kstar_toTrace_comm, ih]

@[simp]
lemma matches_toTrace_dist (P Q : RegularExpression α) :
    toTrace I (P.matches' + Q.matches') = toTrace I P.matches' ∪ toTrace I Q.matches' := by
  apply Set.image_union

end RegularExpression
