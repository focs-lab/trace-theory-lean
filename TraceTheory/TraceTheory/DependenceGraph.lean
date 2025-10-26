import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import TraceTheory.Trace

open Trace

variable {α : Type*} [DecidableEq α]
variable {D : Dependence α}

variable (D) in
structure DependenceGraph where
  V : Type
  [fintype : Fintype V]
  R : V → V → Prop
  φ : V → α
  acyclic : ∀ v, ¬ Relation.TransGen R v v
  d_conn : ∀ v₁ v₂, R v₁ v₂ ∨ R v₂ v₁ ∨ v₁ = v₂ ↔ D.rel (φ v₁) (φ v₂)

def Dependence.Subset (D₁ D₂ : Dependence α) : Prop :=
  ∀ a b, D₁.rel a b → D₂.rel a b

notation:50 D₁ " ⊆ " D₂ => Dependence.Subset D₁ D₂

namespace DependenceGraph

structure Iso (γ₁ γ₂: DependenceGraph D) where
  toEquiv : γ₁.V ≃ γ₂.V
  preserves_label' : ∀ v, γ₁.φ v = γ₂.φ (toEquiv v)
  preserves_arcs' : ∀ v₁ v₂, γ₁.R v₁ v₂ ↔ γ₂.R (toEquiv v₁) (toEquiv v₂)

instance (γ₁ γ₂ : DependenceGraph D) : CoeFun (γ₁.Iso γ₂) (fun _ => γ₁.V → γ₂.V) where
  coe f := f.toEquiv.toFun

section EdgeSubset

variable {V : Type} [Fintype V] (φ : V → α)
variable (R₁ R₂ : V → V → Prop)
variable (D₁ D₂ : Dependence α)

def RelSubset (R₁ R₂ : V → V → Prop) : Prop :=
  ∀ v₁ v₂, R₁ v₁ v₂ → R₂ v₁ v₂

notation:50 R₁ " ⊆ " R₂ => RelSubset R₁ R₂

lemma edge_subset_of_dep_subset {D₁ D₂ : Dependence α}
    (h_acyclic₁ : ∀ v, ¬ Relation.TransGen R₁ v v)
    (h_dconn₁ : ∀ v₁ v₂, R₁ v₁ v₂ ∨ R₁ v₂ v₁ ∨ v₁ = v₂ ↔ D₁.rel (φ v₁) (φ v₂))
    (h_acyclic₂ : ∀ v, ¬ Relation.TransGen R₂ v v)
    (h_dconn₂ : ∀ v₁ v₂, R₂ v₁ v₂ ∨ R₂ v₂ v₁ ∨ v₁ = v₂ ↔ D₂.rel (φ v₁) (φ v₂))
    (h_subset : D₁ ⊆ D₂) : -- (1.4.2)
    R₁ ⊆ R₂ := by
  intro v₁ v₂ hR₁
  have h_irref₁ : v₁ ≠ v₂ := by
    intro heq
    subst heq
    have h_trans := Relation.TransGen.single hR₁
    exact h_acyclic₁ v₁ h_trans
  have h_dconn₁_left : R₁ v₁ v₂ ∨ R₁ v₂ v₁ ∨ v₁ = v₂ := by
    left
    exact hR₁
  have hD₁ : D₁.rel (φ v₁) (φ v₂) := (h_dconn₁ v₁ v₂).mp h_dconn₁_left
  have hD₂ : D₂.rel (φ v₁) (φ v₂) := h_subset (φ v₁) (φ v₂) hD₁
  have h_dconn₂_left : R₂ v₁ v₂ ∨ R₂ v₂ v₁ ∨ v₁ = v₂ := (h_dconn₂ v₁ v₂).mpr hD₂
  rcases h_dconn₂_left with hR₂_v₁v₂ | hR₂_v₂v₁ | hR₂_eq
  · exact hR₂_v₁v₂
  · sorry
  · contradiction

end EdgeSubset

instance (γ : DependenceGraph D) : Fintype γ.V := γ.fintype

def compose (γ₁ γ₂ : DependenceGraph D) : DependenceGraph D := -- (1.4.4)
  let Vcomp := γ₁.V ⊕ γ₂.V
  let Rcomp := fun u v =>
    match u, v with
    | Sum.inl u, Sum.inl v => γ₁.R u v
    | Sum.inl u, Sum.inr v => D.rel (γ₁.φ u) (γ₂.φ v)
    | Sum.inr u, Sum.inl v => False
    | Sum.inr u, Sum.inr v => γ₂.R u v
  let φcomp := Sum.elim γ₁.φ γ₂.φ
  {
    V := Vcomp
    fintype := inferInstance
    R := Rcomp
    φ := φcomp
    acyclic := by
      intro v h
      cases v with
      | inl v₁ =>
        have hγ₁ : ∀ {x y u v},
            x = Sum.inl u →
            y = Sum.inl v →
            Relation.TransGen Rcomp x y →
            Relation.TransGen γ₁.R u v := by
          intro x y u v hx hy hxy
          induction hxy generalizing v with
          | single h_step =>
            rename_i y
            simp only [hx, hy, Rcomp] at h_step
            exact Relation.TransGen.single h_step
          | tail h_before h_step ih =>
            rename_i w y
            cases w with
            | inl w₁ =>
              simp only [hy, Rcomp] at h_step
              exact Relation.TransGen.tail (ih rfl) h_step
            | inr w₂ =>
              exfalso
              simp only [hy, Rcomp] at h_step
        generalize hv₁ : Sum.inl v₁ = v' at h
        exact γ₁.acyclic v₁ (hγ₁ hv₁.symm hv₁.symm h)
      | inr v₂ =>
        have h_right : ∀ (u : γ₂.V) (w : Vcomp),
            Relation.TransGen Rcomp (Sum.inr u) w → Sum.isRight w := by
          intro u w huw
          induction huw with
          | single h_step =>
            rename_i w
            cases w with
            | inl w₁ =>
              exfalso
              simp only [Rcomp] at h_step
            | inr w₂ =>
              exact Sum.isRight_inr
          | tail _ h_rest ih =>
            rename_i x w _
            cases w with
            | inl w₁ =>
              exfalso
              have ⟨y, hy⟩ := Sum.isRight_iff.mp ih
              simp only [Rcomp, hy] at h_rest
            | inr w₂ =>
              exact Sum.isRight_inr
        have hγ₂ : ∀ {x y u v},
            x = Sum.inr u →
            y = Sum.inr v →
            Relation.TransGen Rcomp x y →
            Relation.TransGen γ₂.R u v := by
          intro x y u v hx hy hxy
          induction hxy generalizing v with
          | single h_step =>
            rename_i y
            simp only [hx, hy, Rcomp] at h_step
            exact Relation.TransGen.single h_step
          | tail h_before h_step ih =>
            rename_i w y
            cases w with
            | inl w₁ =>
              exfalso
              rw [hx] at h_before
              have hw₁ := h_right u (Sum.inl w₁) h_before
              simp only [Sum.isRight_inl, Bool.false_eq_true] at hw₁
            | inr w₂ =>
              simp only [hy, Rcomp] at h_step
              exact Relation.TransGen.tail (ih rfl) h_step
        generalize hv₂ : Sum.inr v₂ = v' at h
        exact γ₂.acyclic v₂ (hγ₂ hv₂.symm hv₂.symm h)
    d_conn := by
      intro v₁ v₂
      cases v₁ with
      | inl v₁ =>
        cases v₂ with
        | inl v₂ =>
          simp [Vcomp, Rcomp, φcomp]
          exact γ₁.d_conn v₁ v₂
        | inr v₂ =>
          simp [Vcomp, Rcomp, φcomp]
      | inr v₁ =>
        cases v₂ with
        | inl v₂ =>
          simp [Vcomp, Rcomp, φcomp]
          exact ⟨D.symm _ _, D.symm _ _⟩
        | inr v₂ =>
          simp [Vcomp, Rcomp, φcomp]
          exact γ₂.d_conn v₁ v₂
  }

end DependenceGraph
