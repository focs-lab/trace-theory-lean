import Mathlib.Tactic.FinCases
import TraceTheory.DependenceGraph

open TraceTheory

variable {V : Type} [Fintype V]

/-- Subset relation for arcs. -/
def RelSubset (R₁ R₂ : V → V → Prop) : Prop :=
  ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂

/-- Notation for subset of arcs. -/
notation:50 R₁ " ⊆ " R₂ => RelSubset R₁ R₂

/-- An auxiliary relation on `Fin 2` used to construct a counterexample. -/
def counterexample_D_rel : Fin 2 → Fin 2 → Prop
  | 0, 0 => True
  | 0, 1 => True
  | 1, 0 => True
  | 1, 1 => True

/-- A specific dependence relation on `Fin 2` (full relation) used for a counterexample. -/
def D₁ : Dependence (Fin 2) where
  rel := counterexample_D_rel
  refl := by
    intro a
    fin_cases a <;> simp [counterexample_D_rel]
  symm := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [counterexample_D_rel]

/-- A copy of `D₁` used for a counterexample. -/
def D₂ := D₁

/-- Identity labeling function for the counterexample. -/
def φ' : Fin 2 → Fin 2 := id

/-- A specific edge relation (0 -> 1) used for the counterexample. -/
def R₁ : Fin 2 → Fin 2 → Prop
  | 0, 1 => True
  | _, _ => False

/-- A specific edge relation (1 -> 0) used for the counterexample. -/
def R₂ : Fin 2 → Fin 2 → Prop
  | 1, 0 => True
  | _, _ => False

-- Falsity of Proposition (1.4.2) in The Book of Traces
theorem not_edge_subset_of_dep_subset :
  ¬ (∀ {V α : Type} [Fintype V] (φ : V → α) (R₁ R₂ : V → V → Prop) (D₁ D₂ : Dependence α),
    (∀ v, ¬ Relation.TransGen R₁ v v) →
    (∀ v₁ v₂, R₁ v₁ v₂ ∨ R₁ v₂ v₁ ∨ v₁ = v₂ ↔ D₁.rel (φ v₁) (φ v₂)) →
    (∀ v, ¬ Relation.TransGen R₂ v v) →
    (∀ v₁ v₂, R₂ v₁ v₂ ∨ R₂ v₂ v₁ ∨ v₁ = v₂ ↔ D₂.rel (φ v₁) (φ v₂)) →
    (D₁ ⊆ D₂) →
    (R₁ ⊆ R₂)) := by
  intro h
  have hce := h φ' R₁ R₂ D₁ D₂
  have hR₁ : ∀ u, ¬ Relation.TransGen R₁ 1 u := by
    intro u hu
    induction hu with
    | single h_step =>
      rename_i u
      simp [R₁] at h_step
    | tail h_before h_step ih =>
      exact ih
  have hR₂ : ∀ u, ¬ Relation.TransGen R₂ 0 u := by
    intro u hu
    induction hu with
    | single h_step =>
      rename_i u
      simp [R₂] at h_step
    | tail h_before h_step ih =>
      exact ih
  have h_acyclic₁ : ∀ v, ¬ Relation.TransGen R₁ v v := by
    intro v
    fin_cases v
    · intro hv
      cases hv with
      | single h_step =>
        simp [R₁] at h_step
      | tail h_before h_step =>
        rename_i u
        fin_cases u <;> simp [R₁] at h_step
    · intro hv
      cases hv with
      | single h_step =>
        simp [R₁] at h_step
      | tail h_before h_step =>
        rename_i u
        simp at h_before
        exact hR₁ u h_before
  have h_dconn₁ : ∀ v₁ v₂, R₁ v₁ v₂ ∨ R₁ v₂ v₁ ∨ v₁ = v₂ ↔ D₁.rel (φ' v₁) (φ' v₂) := by
    intro v₁ v₂
    fin_cases v₁ <;> fin_cases v₂
    all_goals (
      dsimp [D₁, counterexample_D_rel, φ', R₁]
      simp
    )
  have h_acyclic₂ : ∀ v, ¬ Relation.TransGen R₂ v v := by
    intro v
    fin_cases v
    · intro hv
      cases hv with
      | single h_step =>
        simp [R₂] at h_step
      | tail h_before h_step =>
        rename_i u
        simp at h_before
        exact hR₂ u h_before
    · intro hv
      cases hv with
      | single h_step =>
        simp [R₂] at h_step
      | tail h_before h_step =>
        rename_i u
        fin_cases u <;> simp [R₂] at h_step
  have h_dconn₂ : ∀ v₁ v₂, R₂ v₁ v₂ ∨ R₂ v₂ v₁ ∨ v₁ = v₂ ↔ D₂.rel (φ' v₁) (φ' v₂) := by
    intro v₁ v₂
    fin_cases v₁ <;> fin_cases v₂
    all_goals (
      dsimp [D₂, D₁, counterexample_D_rel, φ', R₁, R₂]
      simp
    )
  have h_subset : D₁ ⊆ D₂ := by
    intro a b
    simp [D₂]
  replace hce := hce h_acyclic₁ h_dconn₁ h_acyclic₂ h_dconn₂ h_subset
  replace hce := hce 0 1
  simp [R₁, R₂] at hce
