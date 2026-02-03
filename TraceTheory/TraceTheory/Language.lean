import TraceTheory.Trace
import Mathlib.Data.Finset.Pi

namespace Trace

variable {α : Type} {I : Independence α}

lemma foldl_append_eq (a : List α) (bs : List (List α)) :
    List.foldl List.append a bs = a ++ List.foldl List.append [] bs := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bsuf b ih => simp [ih]

lemma indep_of_foldl {u : List α} {vs : List (List α)} (i : Fin vs.length) (h : independent I u (vs.foldl List.append [])) :
    independent I u vs[i] := by
  replace ⟨i, hi⟩ := i
  induction vs generalizing i with
  | nil =>
    simp at hi
  | cons v vs' ih =>
    simp at h ⊢
    rw [foldl_append_eq] at h
    cases i with
    | zero => exact (indep_of_concat h).left
    | succ i =>
      simp at hi
      exact ih (indep_of_concat h).right i hi

/-- (i) → (ii) of Corollary (2.3) in `Partial Commutation and Traces`.
  Note that t₁, t₂, …, tₙ is expressed as a list [ts], and (t₁ ++ t₂ ++ … ++ tₙ) via [ts.foldl].
  Similarly, p₁, …, pₙ is [ps] and q₁, …, qₙ is [qs]. -/
theorem levi_lemma_gen (u v : List α) (ts : List (List α)) [DecidableEq α] (h : TraceEquiv I (u ++ v) (ts.foldl List.append [])) :
    ∃ (ps qs : List (List α)),
    ps.length = ts.length
    ∧ qs.length = ts.length
    ∧ TraceEquiv I u (ps.foldl List.append [])
    ∧ TraceEquiv I v (qs.foldl List.append [])
    ∧ (∀ i : Fin (min ts.length (min ps.length qs.length)), TraceEquiv I ts[i] (ps[i] ++ qs[i]))
    ∧ ∀ i : Fin qs.length, ∀ j : Fin ps.length, i.val < j.val → independent I qs[i] ps[j] := by
  induction ts generalizing u v with
  | nil =>
    simp at h ⊢
    replace h := length_eq_of_equiv h
    simp at h
    simp [h, TraceEquiv.refl]
    intro ⟨i, hi⟩
    simp at hi
  | cons t tsuf ih =>
    have equiv_split : TraceEquiv I (u ++ v) (t ++ (tsuf.foldl List.append [])) := by
      unfold List.foldl at h
      simp at h
      rw [foldl_append_eq _ _] at h
      exact h
    have ⟨p, psuf, q, qsuf, h_ind, h_up, h_vq, h_tpq, h_tpq_suf⟩ := levi_lemma equiv_split
    replace ih := ih psuf qsuf h_tpq_suf.symm
    have ⟨ps_i, qs_i, ih_p_len, ih_q_len, ih_p, ih_q, ih_tpq, ih_ind⟩ := ih
    clear ih
    use p :: ps_i, q :: qs_i
    repeat' apply And.intro
    · simp [ih_p_len]
    · simp [ih_q_len]
    · apply TraceEquiv.trans h_up
      simp
      rw [foldl_append_eq]
      exact TraceEquiv.compat (TraceEquiv.refl p) ih_p
    · apply TraceEquiv.trans h_vq
      simp
      rw [foldl_append_eq]
      exact TraceEquiv.compat (TraceEquiv.refl q) ih_q
    · intro ⟨i, hi⟩
      by_cases hzi : i = 0
      · simp [hzi, h_tpq]
      · cases i with
        | zero => contradiction
        | succ i =>
          simp at hi ⊢
          exact ih_tpq ⟨i, by simp; exact hi⟩
    · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      cases j with
      | zero => contradiction
      | succ j =>
        cases i with
        | zero =>
          simp at hj ⊢
          have h_ind_ps := indep_of_indep_of_equiv (indep_symm h_ind) ih_p
          exact indep_of_foldl ⟨j, hj⟩ h_ind_ps
        | succ i =>
          simp at hi hj hij ⊢
          exact ih_ind ⟨i, hi⟩ ⟨j, hj⟩ hij




-- variable {M : Type} [Monoid M]

def IsRecognizable {M : Type} [Monoid M] (S : Set M) : Prop :=
  ∃ N : Type, ∃ _ : Monoid N, ∃ _ : Fintype N, ∃ φ : M →* N, S = φ⁻¹' (φ '' S)

-- (Deterministic) finite M-automaton.
structure DFMA (α : Type) [Monoid α] (σ : Type) [Fintype σ] where
  step : σ → α → σ
  start : σ
  accept : Set σ
  idempotent (q : σ) : step q 1 = q
  composition (q : σ) (u v : α) : step (step q u) v = step q (u * v)

namespace DFMA

variable {α : Type} [Monoid α] {σ : Type} [Fintype σ] (A : DFMA α σ)

def eval (x : α) : σ := A.step A.start x

def eval_set (S : Set α) : Set σ := S.image A.eval

def accepts : Set α := {x | A.eval x ∈ A.accept}

end DFMA

def IsRecognizableDFMA {M : Type} [Monoid M] (S : Set M) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ A : DFMA M σ, S = A.accepts

lemma recognizable_is_recognizableDFMA {M : Type} [Monoid M] (S : Set M) :
    IsRecognizable S → IsRecognizableDFMA S := by
  unfold IsRecognizable IsRecognizableDFMA
  intro ⟨N, N_mon, N_fin, φ, h⟩
  use N, N_fin
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
  unfold DFMA.accepts DFMA.eval DFMA.step
  simp
  apply Set.ext_iff.mpr
  intro x
  apply Iff.intro
  · intro hx
    apply Set.mem_setOf.mpr
    use x
  · intro hx
    apply Set.mem_setOf.mp at hx
    rcases hx with ⟨y, hy, hy_eq⟩
    rw [h, Set.mem_preimage, ← hy_eq]
    exact ⟨y, hy, rfl⟩

def fintype_to_fintype_is_fintype (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] :
    Fintype (α → β) := by
  rename_i hα hβ _
  refine ⟨?_, ?_⟩
  · have proj := (@Fintype.elems α).pi fun _ => @Fintype.elems β hβ
    exact proj.map {
      toFun f := fun a => f a (Fintype.complete a)
      inj' := by
        simp [Function.Injective]
        intro f g h
        apply funext
        intro a
        have h_eq_at : (fun a => f a (Fintype.complete a)) a = (fun a => g a (Fintype.complete a)) a := by rw[h]
        simp at h_eq_at
        exact funext fun x => h_eq_at
    }
  · intro f
    simp
    use fun a h => f a
    simp
    exact fun a h => Fintype.complete (f a)

lemma recognizableDFMA_is_recognizable {M : Type} [Monoid M] (S : Set M) :
    IsRecognizableDFMA S → IsRecognizable S := by
  unfold IsRecognizable IsRecognizableDFMA
  intro ⟨σ, σ_fin, A, hA⟩
  use σ → σ
  let fn_mon : Monoid (σ → σ) := {
    mul := fun f g => g ∘ f
    mul_assoc := fun f g h => rfl
    one := id
    one_mul := fun f => rfl
    mul_one := fun f => rfl
  }
  use fn_mon
  haveI : DecidableEq σ := by sorry
  use @fintype_to_fintype_is_fintype σ σ σ_fin σ_fin _
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

end Trace
