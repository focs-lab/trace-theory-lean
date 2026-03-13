import Mathlib.Data.Finset.Prod
import TraceTheory.Trace
import TraceTheory.DependenceGraph
import TraceTheory

namespace List

variable {α : Type} [DecidableEq α]

lemma count_proj (Sigma : Alphabet α) (w : List α) (a : α) :
    (w.proj Sigma).count a = if a ∈ Sigma then w.count a else 0 := by
  induction w with
  | nil => simp [proj]
  | cons b u ih =>
    by_cases ha : a ∈ Sigma
    all_goals simp [ha] at ih
    · simp [proj, ha]
      by_cases hab : b = a
      · simp [hab, ha, ih]
      · simp [hab]
        by_cases hb : b ∈ Sigma
        all_goals simp [hb, count_cons_of_ne hab, <- ih]
    · simp [ha]
      by_cases hab : b = a
      · simp [hab, proj, ha, ih]
      · by_cases hb : b ∈ Sigma
        all_goals simp [proj, hb, count_cons_of_ne hab, ih]

end List


namespace DependenceGraph

open Trace
variable {α : Type} {D : Dependence α} [DecidableEq α]

def count (γ : DependenceGraph D) (a : α) := (Finset.filter (γ.φ · == a) Finset.univ).card

end DependenceGraph


namespace Occurrence

variable {α : Type} [DecidableEq α]

def occ (w : List α) : Finset (α × ℕ) :=
  match w with
  | [] => ∅
  | a :: u => (occ u) ∪ {(a, w.count a)}

def proj (A : Alphabet α) (R : Finset (α × ℕ)) : Finset (α × ℕ) :=
  R.filter (fun (a, _) => a ∈ A)

lemma occ_proj_commute {w : List α} {A : Alphabet α} : proj A (occ w) = occ (w.proj A) := by
  induction w with
  | nil => simp [occ, proj, List.proj]
  | cons a u ih =>
    by_cases ha : a ∈ A
    · simp [occ, proj, List.proj, ha, List.count_proj]
      simp [<- ih, proj]
      apply Finset.ext_iff.mpr
      intro p
      apply Iff.intro
      · intro hp
        have hpA : p.1 ∈ A := (Finset.mem_filter.mp hp).right
        replace hp : p = (a, List.count a u + 1) ∨ p ∈ (occ u) :=
          Finset.mem_insert.mp (Finset.mem_of_mem_filter p hp)
        apply Finset.mem_insert.mpr
        cases hp with
        | inl hp => exact Or.symm (Or.inr hp)
        | inr hp => exact Or.symm (Or.inl (Finset.mem_filter.mpr (And.intro hp hpA)))
      · intro hp
        replace hp := (Finset.mem_insert.mp hp)
        cases hp with
        | inl hp => simp [hp, ha]
        | inr hp =>
          apply Finset.mem_filter.mp at hp
          apply Finset.mem_filter.mpr
          exact And.intro (Finset.mem_insert_of_mem hp.left) hp.right
    · simp [occ, proj, List.proj, ha]
      rw [Finset.filter_insert]
      simp [<- ih, ha]
      rfl

def ord_rev (w : List α) : Finset ((α × ℕ) × (α × ℕ)) :=
  match w with
  | [] => ∅
  | a :: u => (ord_rev u) ∪ ((occ u) ×ˢ {(a, w.count a)})

def ord (w : List α) : Finset ((α × ℕ) × (α × ℕ)) :=
  ord_rev w.reverse

variable {I : Trace.Independence α}

def trace_intersect (I : Trace.Independence α) (w : List α) : (α × ℕ) × α × ℕ → Prop :=
  (∀ v : List α, Trace.TraceEquiv I v w → · ∈ (ord v))

noncomputable instance trace_intersect_decidable (w : List α) : DecidablePred (trace_intersect I w) := by
  exact Classical.decPred (trace_intersect I w)

noncomputable def ord_trace (T : Trace I) : Finset ((α × ℕ) × (α × ℕ)) :=
  Quotient.lift (fun w => (ord w).filter (trace_intersect I w)) (by
    intro a b hab
    simp
    apply Finset.ext_iff.mpr
    intro p
    apply Iff.intro
    · intro hp
      replace hp := (Finset.mem_filter.mp hp).right
      apply Finset.mem_filter.mpr
      apply And.intro
      · exact (hp b) hab.symm
      · intro v vb
        exact hp v (Trace.TraceEquiv.trans vb hab.symm)
    · intro hp
      replace hp := (Finset.mem_filter.mp hp).right
      apply Finset.mem_filter.mpr
      apply And.intro
      · exact (hp a) hab
      · intro v va
        exact hp v (Trace.TraceEquiv.trans va hab)
  ) T


end Occurrence

--#lint
