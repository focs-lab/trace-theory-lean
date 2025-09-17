import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Congruence.Defs
import TraceTheory.Basic

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace Trace

/--
  A dependence relation is a finite, reflexive, and symmetric relation.
-/
structure Dependence where
  r : α → α → Prop
  refl : ∀ a, r a a
  symm: ∀ a b, r a b → r b a

/--
  An independence relation is a finite, irreflexive, and symmetric relation.
-/
structure Independence where
  r : α → α → Prop
  irrefl : ∀ a, ¬ r a a
  symm : ∀ a b, r a b → r b a

variable {I : Independence}

/--
  The product of two traces (i.e. list of symbols) is the concatenation of the two traces.
-/
instance : Mul (List α) := ⟨List.append⟩

/--
  The trace equivalence relation is defined as the smallest multiplicative (i.e. concatenation) congruence relation induced by the independence relation `I.r`.
  That is, two traces (i.e. lists of symbols) are equivalent if one can be transformed into the other by a finite sequence of swaps of adjacent independent symbols.

  More precisely, `ConGen.Rel I.r` is the inductive closure of the following axioms:
  - **Base:** If `I.r a b`, then `[a, b]` is equivalent to `[b, a]` (i.e., swapping adjacent independent symbols).
  - **Reflexivity:** Every word is equivalent to itself.
  - **Symmetry:** If `u` is equivalent to `v`, then `v` is equivalent to `u`.
  - **Transitivity:** If `u` is equivalent to `v` and `v` is equivalent to `w`, then `u` is equivalent to `w`.
  - **Compatibility:** If `u₁` is equivalent to `v₁` and `u₂` is equivalent to `v₂`, then `u₁ ++ u₂` is equivalent to `v₁ ++ v₂`.

  Thus, two traces are equivalent if and only if one can be obtained from the other by a finite sequence of these operations (or their inverses).
-/
def trace_equiv : List α → List α → Prop :=
  ConGen.Rel I.r

end Trace
