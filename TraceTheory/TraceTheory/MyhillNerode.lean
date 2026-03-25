import TraceTheory.Basic
import TraceTheory.Computability
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace TraceTheory

variable {α : Type*} {I : Independence α}

lemma indep_of_flatten {u : List α} {vs : List (List α)}
    (i : ℕ) (hi : i < vs.length) (h : Independent I u vs.flatten) :
    Independent I u (vs[i]'(hi)) := by
  induction vs generalizing i with
  | nil => contradiction
  | cons v vs' ih =>
    cases i with
    | zero =>
      simp only [List.flatten_cons] at h
      exact (indep_of_indep_append_right h).left
    | succ i' =>
      simp only [List.flatten_cons] at h
      simp only [List.length_cons, add_lt_add_iff_right] at hi
      exact ih i' hi (indep_of_indep_append_right h).right

/-- (i) → (ii) of Corollary (2.3) in `Partial Commutation and Traces`.
  Note that t₁, t₂, …, tₙ is expressed as a list [ts], and (t₁ ++ t₂ ++ … ++ tₙ) via [ts.flatten].
  Similarly, p₁, …, pₙ is [ps] and q₁, …, qₙ is [qs]. -/
theorem levi_lemma_gen {u v : List α} {ts : List (List α)} [DecidableEq α]
    (h : TraceEqv I (u ++ v) ts.flatten) :
    ∃ ps qs : List (List α),
      ps.length = ts.length ∧
      qs.length = ts.length ∧
      TraceEqv I u ps.flatten ∧
      TraceEqv I v qs.flatten ∧
      (∀ i (ht : i < ts.length) (hp : i < ps.length) (hq : i < qs.length),
        TraceEqv I ts[i] (ps[i] ++ qs[i])) ∧
      (∀ i j (hi : i < qs.length) (hj : j < ps.length), i < j →
        Independent I qs[i] ps[j]) := by
  induction ts generalizing u v with
  | nil =>
    simp only [List.flatten_nil] at h
    have h_len := length_eq_of_eqv h
    simp only [List.length_append, List.length_nil] at h_len
    have hu : u = [] := List.length_eq_zero_iff.mp (by omega)
    have hv : v = [] := List.length_eq_zero_iff.mp (by omega)
    subst hu hv
    use [], []
    simp [TraceEqv.refl]
  | cons t tsuf ih =>
    rcases levi_lemma h with ⟨p, psuf, q, qsuf, h_ind, h_up, h_vq, h_tpq, h_tpq_suf⟩
    rcases ih h_tpq_suf.symm with ⟨ps_i, qs_i, ih_p_len, ih_q_len, ih_p, ih_q, ih_tpq, ih_ind⟩
    use p :: ps_i, q :: qs_i
    and_intros
    · simp [ih_p_len]
    · simp [ih_q_len]
    · apply TraceEqv.trans h_up
      simp only [List.flatten_cons]
      exact TraceEqv.compat (TraceEqv.refl p) ih_p
    · apply TraceEqv.trans h_vq
      simp only [List.flatten_cons]
      exact TraceEqv.compat (TraceEqv.refl q) ih_q
    · intro i ht hp hq
      cases i with
      | zero => exact h_tpq
      | succ i' => apply ih_tpq i'
    · intro i j hi hj hij
      cases j with
      | zero => contradiction
      | succ j' =>
        cases i with
        | zero =>
          simp only [List.length_cons, add_lt_add_iff_right] at hj
          exact indep_of_flatten j' hj (indep_of_indep_of_eqv (independent_symm h_ind) ih_p)
        | succ i' =>
          apply ih_ind i' j'
          exact Nat.succ_lt_succ_iff.mp hij

variable {M : Type} {σ : Type} [Monoid M] [Monoid α]

-- We need [DecidableEq N] to match the definition of `IsRecognizableDFMA`; see the latter.
def IsRecognizable (T : Set M) : Prop :=
  ∃ (N : Type) (_ : Monoid N) (_ : Fintype N) (_ : DecidableEq N) (φ : M →* N), T = φ⁻¹' (φ '' T)

variable (α σ) in
/-- (Deterministic) M-automaton. Following the convention of `Mathlib.Computability.DFA`,
  the finiteness of `σ` is not imposed here and should be handled separately. -/
structure DFMA extends DFA α σ where
  idempotent (q : σ) : step q 1 = q
  composition (q : σ) (u v : α) : step (step q u) v = step q (u * v)

namespace DFMA

def eval {A : DFMA α σ} (x : α) : σ := A.step A.start x

def accepts {A : DFMA α σ} : Set α := {x | A.eval x ∈ A.accept}

end DFMA

-- We need [DecidableEq σ] to derive the finiteness of (σ → σ) through `Finset.pi`.
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

def syntacticCongr (T : Set M) (x y : M) := ∀ u v : M, u * x * v ∈ T ↔ u * y * v ∈ T

def syntacticSetoid (T : Set M) : Setoid (M) where
  r := syntacticCongr T
  iseqv := Equivalence.mk
    (fun _ _ _ => Set.MapsTo.mem_iff (fun ⦃_⦄ a => a) fun ⦃_⦄ a => a)
    (fun {_ _} a u v => (fun {_ _} => iff_comm.mp) (a u v))
    (fun {_ _ _} a a_1 u v => Iff.trans (a u v) (a_1 u v))

def syntacticMonoid (T : Set M) := Quotient (syntacticSetoid T)

instance : Monoid (syntacticMonoid T) where
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
  one := Quotient.mk (syntacticSetoid T) 1
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
    Finite (syntacticMonoid T) → IsRecognizable T := by
  intro h
  use syntacticMonoid T, by infer_instance, Fintype.ofFinite _, Classical.typeDecidableEq (syntacticMonoid T)
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
    IsRecognizable T → Finite (syntacticMonoid T) := by
  unfold IsRecognizable
  intro ⟨N, N_mon, N_fin, N_dec, φ, h⟩
  have h_img_syn : ∀ a b, φ a = φ b → syntacticCongr T a b := by
    intro a b hab u v
    rw [h]
    simp [hab]
  let f : φ '' Set.univ → syntacticMonoid T := fun ⟨n, hn⟩ => ⟦Classical.choose hn⟧
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
theorem recognizable_has_recognizablePreImage (L : Type) [Monoid L] (φ : L →* M) :
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

noncomputable def preImage_syntacticMonoid_iso (L : Type) [Monoid L]
    (φ : L →* M) (hφ : Function.Surjective φ) :
    syntacticMonoid (φ ⁻¹' T) ≃* syntacticMonoid T := by
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
theorem recognizablePreImage_is_recognizable (L : Type) [Monoid L] (φ : L →* M) (hφ : Function.Surjective φ) :
    IsRecognizable (φ ⁻¹' T) → IsRecognizable T := by
  intro h
  apply recognizable_is_finSyntacticIndex at h
  apply finSyntacticIndex_is_recognizable
  have ψ := @preImage_syntacticMonoid_iso M _ T L _ φ hφ
  exact ψ.finite_iff.mp h

end TraceTheory
