import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence.Basic
import TraceTheory.List

namespace TraceTheory

variable {α : Type*}

/-- A dependence is a finite, reflexive, and symmetric relation. -/
structure Dependence (α : Type*) where
  /-- The dependence relation. -/
  rel : α → α → Prop
  refl : ∀ a, rel a a
  symm: ∀ a b, rel a b → rel b a

/-- An independence is a finite, irreflexive, and symmetric relation. -/
structure Independence (α : Type*) where
  /-- The independence relation. -/
  rel : α → α → Prop
  irrefl : ∀ a, ¬ rel a a
  symm : ∀ a b, rel a b → rel b a

/-- The Independence relation induced by a Dependence `D`. -/
def inducedIndependence {α : Type*} (D : Dependence α) : Independence α where
  rel := fun a b => ¬D.rel a b
  irrefl := by
    intro a h
    exact h (D.refl a)
  symm := by
    intro a b hab hba
    exact hab (D.symm b a hba)

instance : Coe α (FreeMonoid α) := ⟨FreeMonoid.of⟩

/-- The binary relation $~$ such that $u~v$ if and only if there exists strings $x,y$ and symbols
$a,b$ such that $u=xaby$ and $v=xbay$. -/
inductive SwapOnce (I : Independence α) : FreeMonoid α → FreeMonoid α → Prop
  | swap (a b : α) : I.rel a b → SwapOnce I (↑a * ↑b) (↑b * ↑a)

/-- Trace equivalence as the least congruence containing $~$. -/
def traceCon (I : Independence α) : Con (FreeMonoid α) := conGen (SwapOnce I)

/-- The trace monoid. -/
def TraceMonoid (I : Independence α) := (traceCon I).Quotient

variable {I : Independence α}

instance : Monoid (TraceMonoid I) := (traceCon I).monoid

theorem length_eq_of_con {u v : FreeMonoid α} (h : traceCon I u v) : u.length = v.length := by
  sorry

end TraceTheory
