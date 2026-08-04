import TraceTheory.Computability.Language

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
  | zero => simp [traceMatches, matches']
  | epsilon => simp [traceMatches, matches']
  | char a => simp [traceMatches, matches']
  | plus P Q ihP ihQ => simp [traceMatches, matches', ihP, ihQ]
  | comp P Q ihP ihQ => simp [traceMatches, matches', ihP, ihQ]
  | star P ih => simp [traceMatches, matches', ih, toTrace_kstar_comm]

end RegularExpression
