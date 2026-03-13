import Mathlib.Data.Finset.Prod
import TraceTheory.DependenceGraph


namespace TraceTheory

variable {α : Type} [DecidableEq α]

lemma count_proj (S : Finset α) (w : List α) (a : α) :
    (proj S w).count a = if a ∈ S then w.count a else 0 := by
  induction w with
  | nil => simp [proj]
  | cons b u ih =>
    by_cases ha : a ∈ S
    all_goals simp [ha] at ih
    · simp [proj, ha]
    · simp [ha]
      by_cases hab : b = a
      · simp [hab, proj, ha, <- ih]
      · by_cases hb : b ∈ S
        all_goals simp [proj, hb, List.count_cons_of_ne hab, <- ih]

end TraceTheory


namespace DependenceGraph

open TraceTheory
variable {α : Type} {D : Dependence α} [DecidableEq α]

def count (γ : DependenceGraph D) (a : α) := (Finset.filter (γ.φ · == a) Finset.univ).card

end DependenceGraph


namespace Occurrence

variable {α : Type} [DecidableEq α]

def occ (w : List α) : Finset (α × ℕ) :=
  match w with
  | [] => ∅
  | a :: u => (occ u) ∪ {(a, w.count a)}

def projOcc (A : Finset α) (R : Finset (α × ℕ)) : Finset (α × ℕ) :=
  R.filter (fun (a, _) => a ∈ A)

lemma occ_proj_commute {w : List α} {A : Finset α} : projOcc A (occ w) = occ (TraceTheory.proj A w) := by
  induction w with
  | nil => simp [occ, projOcc, TraceTheory.proj]
  | cons a u ih =>
    by_cases ha : a ∈ A
    · simp [occ, projOcc, TraceTheory.proj, ha] at ih ⊢
      simp [<- ih]
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
    · simp [occ, projOcc, TraceTheory.proj, ha] at ih ⊢
      rw [Finset.filter_insert]
      simp [<- ih, ha]

def ord_rev (w : List α) : Finset ((α × ℕ) × (α × ℕ)) :=
  match w with
  | [] => ∅
  | a :: u => (ord_rev u) ∪ ((occ u) ×ˢ {(a, w.count a)})

def ord (w : List α) : Finset ((α × ℕ) × (α × ℕ)) :=
  ord_rev w.reverse

variable {I : TraceTheory.Independence α}

def trace_intersect (I : TraceTheory.Independence α) (w : List α) : (α × ℕ) × α × ℕ → Prop :=
  (∀ v : List α, TraceTheory.TraceEqv I v w → · ∈ (ord v))

noncomputable instance trace_intersect_decidable (w : List α) : DecidablePred (trace_intersect I w) := by
  exact Classical.decPred (trace_intersect I w)

noncomputable def ord_trace (T : TraceTheory.Trace I) : Finset ((α × ℕ) × (α × ℕ)) :=
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
        exact hp v (TraceTheory.TraceEqv.trans vb hab.symm)
    · intro hp
      replace hp := (Finset.mem_filter.mp hp).right
      apply Finset.mem_filter.mpr
      apply And.intro
      · exact (hp a) hab
      · intro v va
        exact hp v (TraceTheory.TraceEqv.trans va hab)
  ) T


end Occurrence

--#lint
