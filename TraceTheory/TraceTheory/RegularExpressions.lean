import Mathlib.Algebra.Group.Pointwise.Set.Basic
import TraceTheory.Language

open scoped Pointwise

open Computability TraceTheory

namespace RegularExpression

variable {α : Type*} {I : Independence α}

/-- A regular language is star-connected if the Kleene star is
  used over connected languages only. -/
def IsStarConnected (I : Independence α) : RegularExpression α → Prop
  | zero => True
  | epsilon => True
  | char _ => True
  | plus P Q => IsStarConnected I P ∧ IsStarConnected I Q
  | comp P Q => IsStarConnected I P ∧ IsStarConnected I Q
  | star P => IsStarConnected I P ∧ (∀ s ∈ P.matches', Trace.IsConnected I ⟦s⟧)

/-- Interpretation of this RegularExpression on trace languages. -/
def traceMatches (I : Independence α) : RegularExpression α → Set (Trace I)
  | zero => ∅
  | epsilon => { 1 }
  | char a => { ⟦[a]⟧ }
  | plus P Q => traceMatches I P ∪ traceMatches I Q
  | comp P Q => traceMatches I P * traceMatches I Q
  | star P => (traceMatches I P)∗

/--- Interpretation of this RegularExpression as a c-rational expression on trace languages. --/
def cRatMatches (I : Independence α) : RegularExpression α → Set (Trace I)
  | zero => ∅
  | epsilon => { 1 }
  | char a => { ⟦[a]⟧ }
  | plus P Q => cRatMatches I P ∪ cRatMatches I Q
  | comp P Q => cRatMatches I P * cRatMatches I Q
  | star P => (connectedComponents (cRatMatches I P))∗

/-- Interpreting this RegularExpression as operating on trace languages gives the same matching set
  as projecting the language it matches to traces. -/
theorem traceMatches_toTrace (P : RegularExpression α) :
    traceMatches I P = toTrace I P.matches' := by
  induction P with
  | zero => simp [toTrace, traceMatches, Language.zero_def]
  | epsilon => simp [toTrace, traceMatches, Language.one_def]
  | char a =>
    unfold traceMatches matches' toTrace
    rw [Set.image_singleton]
    rfl
  | plus P Q ihP ihQ =>
    unfold traceMatches matches' toTrace
    rw [ihP, ihQ, Language.add_def, Set.image_union]
    rfl
  | comp P Q ihP ihQ =>
    unfold traceMatches matches' toTrace
    rw [ihP, ihQ, Set.image_mul]
    rfl
  | star P ih =>
    unfold traceMatches matches'
    rw [toTrace_kstar_comm, ih]

end RegularExpression
