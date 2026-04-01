import TraceTheory.Basic
import TraceTheory.Computability
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace TraceTheory

variable {α : Type*} {I : Independence α}
variable {M : Type} {σ : Type} [Monoid M] [Monoid α]

/-- A recognizable set of a monoid `M` is a subset that can be distinguished by some homomorphism
  onto a finite monoid. -/
def IsRecognizable (T : Set M) : Prop :=
  ∃ (N : Type) (_ : Monoid N) (_ : Fintype N) (_ : DecidableEq N) (φ : M →* N), T = φ⁻¹' (φ '' T)

variable (α σ) in
/-- (Deterministic) M-automaton. Following the convention of `Mathlib.Computability.DFA`,
  the finiteness of `σ` is not imposed here and should be handled separately. -/
structure DFMA extends DFA α σ where
  idempotent (q : σ) : step q 1 = q
  composition (q : σ) (u v : α) : step (step q u) v = step q (u * v)

/-- Evaluate `A` on `x`. -/
def DFMA.eval {A : DFMA α σ} (x : α) : σ := A.step A.start x

/-- The set of elements of `α` accepted by `A`. -/
def DFMA.accepts {A : DFMA α σ} : Set α := {x | A.eval x ∈ A.accept}

/-- There exists some M-automaton that accepts exactly `S`. -/
def IsRecognizableDFMA (S : Set M) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ) (A : DFMA M σ), S = A.accepts

/-- Prop 4.1 (i) => (iii) -/
theorem recognizable_is_recognizableDFMA (S : Set M) :
    IsRecognizable S → IsRecognizableDFMA S := by
  unfold IsRecognizable IsRecognizableDFMA
  intro ⟨N, N_mon, N_fin, N_dec, φ, h⟩
  use N, N_fin, N_dec
  use {
    step := fun n m => n * (φ m)
    start := 1
    accept := φ '' S
    idempotent := by simp
    composition := by
      intro q u v
      rw [map_mul φ u v]
      exact mul_assoc q (φ u) (φ v)
  }
  unfold DFMA.accepts DFMA.eval DFA.step
  simp only [one_mul, Set.mem_image]
  apply Set.ext_iff.mpr
  intro x
  constructor
  · intro hx
    apply Set.mem_setOf.mpr
    use x
  · intro hx
    apply Set.mem_setOf.mp at hx
    rcases hx with ⟨y, hy, hy_eq⟩
    rw [h, Set.mem_preimage, ← hy_eq]
    exact ⟨y, hy, rfl⟩

/-- Prop 4.1 (iii) => (i) -/
theorem recognizableDFMA_is_recognizable (S : Set M) :
    IsRecognizableDFMA S → IsRecognizable S := by
  unfold IsRecognizable IsRecognizableDFMA
  intro ⟨σ, σ_fin, σ_dec, A, hA⟩
  use σ → σ
  let fn_mon : Monoid (σ → σ) := {
    mul := fun f g => g ∘ f
    mul_assoc := fun f g h => rfl
    one := id
    one_mul := fun f => rfl
    mul_one := fun f => rfl
  }
  use fn_mon, inferInstance, inferInstance
  use {
    toFun := fun m => (fun x => A.step x m)
    map_one' := by apply funext A.idempotent
    map_mul' := by
      intro f g
      apply funext
      intro x
      rw [<- A.composition]
      rfl
  }
  simp [hA, DFMA.accepts, DFMA.eval]
  apply Set.ext_iff.mpr
  intro m
  apply Iff.intro
  · intro hm
    apply Set.mem_setOf.mp at hm
    apply Set.mem_setOf.mpr
    simp
    use m
  · intro hm
    apply Set.mem_setOf.mpr
    apply Set.mem_setOf.mp at hm
    simp at hm
    rcases hm with ⟨m', hm', hm_eq⟩
    replace hm_eq : (fun x => A.step x m') A.start = (fun x => A.step x m) A.start := by rw [hm_eq]
    simp at hm_eq
    rw [hm_eq] at hm'
    exact hm'

variable {T : Set M}

/-- `x` is syntatically congruent to `y` in `T` if `u * x * v` is in `T` if and only if
  `u * y * v` is in `T`. -/
def SyntacticCongr (T : Set M) (x y : M) :=
  ∀ u v, u * x * v ∈ T ↔ u * y * v ∈ T

/-- The setoid structure of the syntatic congruence in `T`. -/
def SyntacticSetoid (T : Set M) : Setoid (M) where
  r := SyntacticCongr T
  iseqv := Equivalence.mk
    (fun _ _ _ => Set.MapsTo.mem_iff (fun ⦃_⦄ a => a) fun ⦃_⦄ a => a)
    (fun {_ _} a u v => (fun {_ _} => iff_comm.mp) (a u v))
    (fun {_ _ _} a b u v => Iff.trans (a u v) (b u v))

/-- The quotient of `T` by the syntatic congruence. -/
def SyntacticMonoid (T : Set M) := Quotient (SyntacticSetoid T)

instance : Monoid (SyntacticMonoid T) where
  mul := Quotient.lift₂
    (fun w₁ w₂ => ⟦w₁ * w₂⟧)
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      apply Quotient.sound
      intro u v
      have hT₁ := ha u (b₁ * v)
      have hT₂ := hb (u * a₂) v
      rename_i hM _
      calc
        u * (a₁ * b₁) * v ∈ T ↔ u * a₁ * (b₁ * v) ∈ T := by simp only [hM.mul_assoc]
        _ ↔ u * a₂ * (b₁ * v) ∈ T := hT₁
        _ ↔ u * a₂ * b₁ * v ∈ T := by simp only [hM.mul_assoc]
        _ ↔ u * a₂ * b₂ * v ∈ T := hT₂
        _ ↔ u * (a₂ * b₂) * v ∈ T := by simp only [hM.mul_assoc]
    )
  one := Quotient.mk (SyntacticSetoid T) 1
  mul_assoc := by
    intro t₁ t₂ t₃
    refine Quotient.inductionOn₃ t₁ t₂ t₃ (fun w₁ w₂ w₃ => ?_)
    apply Quotient.sound
    rename_i hM _
    rw [hM.mul_assoc]
    intro u v
    rfl
  one_mul := by
    intro t
    refine Quotient.inductionOn t (fun w => ?_)
    apply Quotient.sound
    rename_i hM _
    rw [hM.one_mul]
    intro u v
    rfl
  mul_one := by
    intro t
    refine Quotient.inductionOn t (fun w => ?_)
    apply Quotient.sound
    rename_i hM _
    rw [hM.mul_one]
    intro u v
    rfl

/-- Prop 4.1 (ii) => (i) -/
theorem finSyntacticIndex_is_recognizable :
    Finite (SyntacticMonoid T) → IsRecognizable T := by
  classical
  intro h
  use SyntacticMonoid T, inferInstance, Fintype.ofFinite _, inferInstance
  use {
    toFun := fun m => ⟦m⟧
    map_one' := by rfl
    map_mul' := by intro x y; rfl
  }
  simp
  apply Set.ext_iff.mpr
  intro x
  simp
  apply Iff.intro
  · intro hx
    use x
  · intro ⟨y, ⟨hy, hxy⟩⟩
    apply @Quotient.exact _ _ y x at hxy
    replace hxy := hxy 1 1
    simp at hxy
    exact hxy.mp hy

/-- Prop 4.1 (i) => (ii) -/
theorem recognizable_is_finSyntacticIndex :
    IsRecognizable T → Finite (SyntacticMonoid T) := by
  unfold IsRecognizable
  intro ⟨N, N_mon, N_fin, N_dec, φ, h⟩
  have h_img_syn : ∀ a b, φ a = φ b → SyntacticCongr T a b := by
    intro a b hab u v
    rw [h]
    simp [hab]
  let f : φ '' Set.univ → SyntacticMonoid T := fun ⟨n, hn⟩ => ⟦Classical.choose hn⟧
  have f_surj : Function.Surjective f := by
    intro q
    have ⟨m, hm⟩ := Quotient.exists_rep q
    use ⟨φ m, Set.mem_image_of_mem φ trivial⟩
    rw [<- hm]
    apply Quotient.sound
    intro u v
    apply h_img_syn
    have hm : φ m ∈ ⇑φ '' Set.univ := Set.mem_image_of_mem (⇑φ) trivial
    exact (Classical.choose_spec hm).2
  exact Finite.of_surjective f f_surj

/-- Prop 4.1 (i) => (iv) -/
theorem recognizable_has_recognizablePreImage {L : Type} [Monoid L] (φ : L →* M) :
    IsRecognizable T → IsRecognizable (φ ⁻¹' T) := by
  intro h
  unfold IsRecognizable at h ⊢
  rcases h with ⟨N, N_mon, N_fin, N_dec, ψ, hψ⟩
  use N, N_mon, N_fin, N_dec
  use {
    toFun := ψ ∘ φ
    map_one' := by simp
    map_mul' := by simp
  }
  simp
  ext x
  apply Iff.intro
  · intro hx
    rw [Set.mem_preimage] at hx
    rw [Set.mem_preimage, Set.mem_image]
    use x
    simp [hx]
  · intro hx
    rw [Set.mem_preimage, Set.mem_image] at hx
    obtain ⟨y, hy, h⟩ := hx
    have hφy : φ y ∈ T := by rwa [Set.mem_preimage] at hy
    have : ψ (φ x) ∈ ψ '' T := by
      rw [Set.mem_image]
      exact ⟨φ y, hφy, h⟩
    have : φ x ∈ ψ ⁻¹' (ψ '' T) := by rwa [Set.mem_preimage]
    rw [← hψ] at this
    rw [Set.mem_preimage]
    exact this

/-- The syntatic monoid of the preimage of `T` under a surjective homomorphism
  is isomorphic to the syntatic monoid of `T`. -/
noncomputable def preImage_syntacticMonoid_iso {L : Type} [Monoid L]
    (φ : L →* M) (hφ : Function.Surjective φ) :
    SyntacticMonoid (φ ⁻¹' T) ≃* SyntacticMonoid T := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact Quotient.lift (fun l => ⟦φ l⟧) (by
        intro a b hab
        simp
        apply Quotient.sound
        intro u v
        have ⟨u', hu'⟩ := hφ u
        have ⟨v', hv'⟩ := hφ v
        replace hab := hab u' v'
        rw [Set.mem_preimage] at hab
        simp [hu', hv'] at hab
        exact hab
      )
    · exact Quotient.lift (fun m => ⟦Classical.choose (hφ m)⟧) (by
        intro a b hab
        simp
        apply Quotient.sound
        intro u v
        simp [Set.mem_preimage]
        rw [Classical.choose_spec (hφ a), Classical.choose_spec (hφ b)]
        exact hab (φ u) (φ v)
      )
    · intro x
      rcases x
      rename_i l
      simp
      apply Quotient.sound
      intro u v
      simp [Set.mem_preimage]
      rw [Classical.choose_spec (hφ (φ l))]
    · intro x
      rcases x
      rename_i m
      simp
      apply Quotient.sound
      intro u v
      rw [Classical.choose_spec (hφ m)]
  · intro x y
    rcases x
    rcases y
    rename_i l₁ l₂
    apply Quotient.sound
    intro u v
    rw [MonoidHom.map_mul φ l₁ l₂]

/-- Prop 4.1 (iv) => (i) -/
theorem recognizablePreImage_is_recognizable {L : Type} [Monoid L]
    (φ : L →* M) (hφ : Function.Surjective φ) :
    IsRecognizable (φ ⁻¹' T) → IsRecognizable T := by
  intro h
  apply recognizable_is_finSyntacticIndex at h
  apply finSyntacticIndex_is_recognizable
  have ψ := @preImage_syntacticMonoid_iso M _ T L _ φ hφ
  exact ψ.finite_iff.mp h

end TraceTheory
