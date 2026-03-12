import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence.Basic
import TraceTheory.List

open FreeMonoid

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

attribute [coe] FreeMonoid.of

/-- The binary relation $~$ such that $u~v$ if and only if there exists strings $x,y$ and symbols
$a,b$ such that $aIb$, $u=xaby$ and $v=xbay$. -/
inductive SwapOnce (I : Independence α) : FreeMonoid α → FreeMonoid α → Prop
  | swap (a b : α) : I.rel a b → SwapOnce I (↑a * ↑b) (↑b * ↑a)

/-- Trace equivalence defined as the least congruence containing $~$. -/
def TraceEqv (I : Independence α) : Con (FreeMonoid α) := conGen (SwapOnce I)

/-- The trace monoid defined as the quotient of the free monoid by the trace equivalence relation
induced by `I`. -/
def TraceMonoid (I : Independence α) := (TraceEqv I).Quotient

variable {I : Independence α}

instance : Monoid (TraceMonoid I) := (TraceEqv I).monoid

theorem length_eq_of_eqv {u v : FreeMonoid α} (h : TraceEqv I u v) : u.length = v.length := by
  induction h with
  | of _ _ h_swap     => cases h_swap; simp
  | refl w            => rfl
  | symm _ ih         => simp [ih]
  | trans _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | mul _ _ ih₁ ih₂   => simp [ih₁, ih₂]

theorem mem_iff_mem {u v : FreeMonoid α} (a : α) (h : TraceEqv I u v) : a ∈ u ↔ a ∈ v := by
  induction h with
  | of _ _ h_swap     => cases h_swap; simp [mem_mul, mem_of, Or.comm]
  | refl w            => rfl
  | symm _ ih         => simp [ih]
  | trans _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | mul _ _ ih₁ ih₂   => simp [ih₁, ih₂]

theorem rev_eqv_of_eqv {u v : FreeMonoid α} (h : TraceEqv I u v) :
    TraceEqv I u.reverse v.reverse := by
  induction h with
  | of _ _ h_swap =>
    cases h_swap with
    | swap a b h_indep =>
      simp only [reverse_mul]
      apply ConGen.Rel.of
      exact SwapOnce.swap b a (I.symm _ _ h_indep)
  | refl _ => apply (TraceEqv I).refl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [reverse_mul]
    exact ih₂.mul ih₁

theorem proj_eqv_of_eqv {u v : FreeMonoid α} {S : Finset α} [DecidableEq α] (h : TraceEqv I u v) :
    TraceEqv I (proj S u) (proj S v) := by
  sorry

theorem of_mul_cancel_left {a : α} {u v : FreeMonoid α} [DecidableEq α]
    (h : TraceEqv I (↑a * u) (↑a * v)) :
    TraceEqv I u v := by
  sorry

theorem of_mul_cancel_right {a : α} {u v : FreeMonoid α} [DecidableEq α]
    (h : TraceEqv I (u * ↑a) (v * ↑a)) :
    TraceEqv I u v := by
  sorry

theorem mul_cancel_left {w u v : FreeMonoid α} [DecidableEq α] (h : TraceEqv I (w * u) (w * v)) :
    TraceEqv I u v := by
  induction w using recOn with
  | h0 => exact h
  | ih _ _ ih =>
    rw [mul_assoc, mul_assoc] at h
    exact ih (of_mul_cancel_left h)

theorem mul_cancel_right {w u v : FreeMonoid α} [DecidableEq α] (h : TraceEqv I (u * w) (v * w)) :
    TraceEqv I u v := by
  induction w using List.reverseRecOn with
  | nil =>
    change TraceEqv I (u * 1) (v * 1) at h
    simp_all [mul_one]
  | append_singleton w' a ih =>
    change (TraceEqv I) (u * (↑w' * ↑a)) (v * (↑w' * ↑a)) at h
    rw [← mul_assoc, ← mul_assoc] at h
    exact ih (of_mul_cancel_right h)

instance [DecidableEq α] : CancelMonoid (TraceMonoid I) where
  mul_left_cancel := by
    intro a b c heq
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    apply Quotient.sound
    simp only at heq
    have heqv := by simpa using Quotient.exact heq
    exact mul_cancel_left heqv
  mul_right_cancel := by
    intro a b c heq
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    apply Quotient.sound
    simp only at heq
    have heqv := by simpa using Quotient.exact heq
    exact mul_cancel_right heqv

inductive SwapOnce' (I : Independence α) : List α → List α → Prop
  | swap (a b : α) : I.rel a b → SwapOnce' I [a, b] [b, a]

instance : Monoid (List α) where
  one := []
  mul := List.append
  mul_assoc := List.append_assoc
  mul_one := List.append_nil
  one_mul := List.nil_append

def TraceEqv' (I : Independence α) : Con (List α) := conGen (SwapOnce' I)

def TraceMonoid' (I : Independence α) := (TraceEqv' I).Quotient

instance : Monoid (TraceMonoid' I) := (TraceEqv' I).monoid

end TraceTheory
