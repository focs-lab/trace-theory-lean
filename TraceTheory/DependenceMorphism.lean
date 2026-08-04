import TraceTheory.Basic

namespace TraceTheory

open List Trace

variable {α : Type*} {M N : Type*} {I : Independence α} [DecidableEq α] [Monoid M] [Monoid N]

/-- A dependence morphism is any homomophism from the free monoid of strings onto another monoid
  such that:

  - $\phi(w)=\phi(\epsilon) \implies w = \epsilon$
  - $(a,b)\in I \implies \phi(ab)=\phi(ba)$
  - $\phi(ua)=\phi(v) \implies \phi(u)=\phi(v\div a)$
  - $\phi(ua)=\phi(vb) \wedge a \neq b \implies (a,b)\in I$
-/
structure DependenceMorphism (I : Independence α) (M : Type*) [Monoid M] where
  /-- The underlying homomophism from the free monoid of strings to another monoid `M`. -/
  toFun : List α →* M
  A1 : ∀ w, toFun w = toFun 1 → w = []
  A2 : ∀ {a b}, I.rel a b → toFun [a, b] = toFun [b, a]
  A3 : ∀ {x y} {a}, toFun (x ++ [a]) = toFun y → toFun x = toFun (y ÷ a)
  A4 : ∀ {x y} {a b}, toFun (x ++ [a]) = toFun (y ++ [b]) ∧ a ≠ b → I.rel a b

instance {M : Type*} [Monoid M] :
    CoeFun (DependenceMorphism I M) (fun _ ↦ FreeMonoid α → M) where
  coe := fun morphism ↦ morphism.toFun

attribute [coe] DependenceMorphism.toFun

theorem DependenceMorphism.map_append {I : Independence α} {M : Type*} [Monoid M]
    (ϕ : DependenceMorphism I M) (x y : List α) :
    ϕ (x ++ y) = ϕ x * ϕ y :=
  ϕ.toFun.map_mul x y

/-- The natural homomorphism from the free monoid of strings to the trace monoid
  is a dependence morphism. -/
def traceDependenceMorphism : DependenceMorphism I (Trace I) where
  toFun := mk' I
  A1 := by
    intro x hx
    exact List.length_eq_zero_iff.mp (length_eq_of_eqv (Quotient.exact hx))
  A2 := by
    intro a b hab
    apply Quotient.sound
    exact TraceEqv.swap a b hab
  A3 := by
    intro x y a heq
    apply Quotient.sound
    have h_cancel := by simpa using cancelRight_congr a (Quotient.exact heq)
    exact h_cancel
  A4 := by
    rintro x y a b ⟨heq, hne⟩
    exact (indep_and_exists_of_eqv_of_tail_ne (Quotient.exact heq) hne).left

lemma exists_of_image_eq_of_tail_ne {ϕ : DependenceMorphism I M} {x y : List α} {a b : α}
    (heq : ϕ (x ++ [a]) = ϕ (y ++ [b])) (hne : a ≠ b) :
    ∃ w, ϕ x = ϕ (w ++ [b]) ∧ ϕ y = ϕ (w ++ [a]) := by
  have hu : ϕ x = ϕ (y ÷ a ++ [b]) := by simpa [append_cancelRight, hne] using ϕ.A3 heq
  have hu' : ϕ (x ÷ b) = ϕ (y ÷ a) := (ϕ.A3 hu.symm).symm
  use x ÷ b
  constructor
  · rw [hu, ϕ.map_append, ϕ.map_append, hu']
  · have hab : x ÷ b ++ [a] = x ++ [a] ÷ b := by simp [hne, Ne.symm]
    rw [hab]
    exact ϕ.A3 heq.symm

theorem image_eq_of_image_eq
    (ϕ : DependenceMorphism I M) (ψ : DependenceMorphism I N)
    (x y : List α) (h : ϕ x = ϕ y) :
    ψ x = ψ y := by
  induction x using List.reverseRecOn generalizing y with
  | nil =>
    replace h := ϕ.A1 y h.symm
    rw [h]
  | append_singleton x' a ihx =>
    induction y using List.reverseRecOn generalizing x' a with
    | nil =>
      replace h := ϕ.A1 (x' ++ [a]) h
      rw [h]
    | append_singleton v b ihy =>
      by_cases hab : a = b
      · replace h := ϕ.A3 h
        simp [hab] at h
        rw [ψ.map_append, ψ.map_append]
        rw [ihx v, hab]
        exact h
      · have h_indep := ϕ.A4 ⟨h, hab⟩
        have ⟨w, hw⟩ := exists_of_image_eq_of_tail_ne h hab
        have hwb := ihx (w ++ [b]) hw.left
        have h' : ∀ z, ϕ w = ϕ z → ψ w = ψ z := by
          intro z hz
          have hu := hw.left
          rw [ϕ.map_append, hz, ← ϕ.map_append] at hu
          replace hu := ihx (z ++ [b]) hu
          have hwz := ψ.A3 (hwb.symm.trans hu)
          simp at hwz
          exact hwz
        have hwa := (ihy w a h' hw.right.symm).symm
        rw [ψ.map_append, ψ.map_append, hwb, hwa, ← ψ.map_append, ← ψ.map_append]
        rw [List.append_assoc, List.append_assoc]
        rw [ψ.map_append, ψ.map_append w]
        rw [List.singleton_append, List.singleton_append]
        rw [ψ.A2 h_indep]

/-- Two monoids `M` and `N` are isomorphic given surjective dependence morphisms w.r.t. the
  same dependency into them. -/
noncomputable def dependenceMorphismIso
    (ϕ : DependenceMorphism I M) (hϕ_surj : Function.Surjective ϕ.toFun)
    (ψ : DependenceMorphism I N) (hψ_surj : Function.Surjective ψ.toFun) :
    M ≃* N := by
  let θ (m : M) : N := ψ (Classical.choose (hϕ_surj m))
  let θ_inv (n : N) : M := ϕ (Classical.choose (hψ_surj n))
  have θ_well_defined : ∀ (m : M) (w : List α) (h : ϕ w = m), θ m = ψ w := by
    intro m w h
    have h_choose := Classical.choose_spec (hϕ_surj m)
    rw [← h_choose, ] at h
    exact image_eq_of_image_eq ϕ ψ _ _ h.symm
  have θ_inv_well_defined : ∀ (n : N) (w : List α) (h : ψ w = n), θ_inv n = ϕ w := by
    intro n w h
    have h_choose := Classical.choose_spec (hψ_surj n)
    rw [← h_choose] at h
    exact image_eq_of_image_eq ψ ϕ _ _ h.symm
  refine' {
    toFun := θ
    invFun := θ_inv
    map_mul' := ?_
    left_inv := ?_
    right_inv := ?_
  }
  · intro m
    rcases hϕ_surj m with ⟨w, hw⟩
    rw [θ_well_defined m w hw]
    rw [θ_inv_well_defined (ψ w) w rfl]
    exact hw
  · intro n
    rcases hψ_surj n with ⟨w, hw⟩
    rw [θ_inv_well_defined n w hw]
    rw [θ_well_defined (ϕ w) w rfl]
    exact hw
  · intro m₁ m₂
    rcases hϕ_surj m₁ with ⟨w₁, hw₁⟩
    rcases hϕ_surj m₂ with ⟨w₂, hw₂⟩
    rw [θ_well_defined m₁ w₁ hw₁]
    rw [θ_well_defined m₂ w₂ hw₂]
    rw [← ψ.map_append]
    have h : ϕ (w₁ ++ w₂) = m₁ * m₂ := by
      rw [ϕ.map_append, hw₁, hw₂]
    exact θ_well_defined (m₁ * m₂) (w₁ ++ w₂) h

end TraceTheory
