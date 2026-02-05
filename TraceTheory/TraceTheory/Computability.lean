import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Computability

variable {α : Type}

namespace Language

theorem IsRegular.zero : IsRegular (0 : Language α) := by
  apply isRegular_iff.mpr
  use Unit, inferInstance, ⟨fun _ _ => (), (), {}⟩
  rfl

theorem IsRegular.top : IsRegular (⊤ : Language α) := by
  rw [← compl_bot, bot_eq_zero]
  apply IsRegular.compl
  exact IsRegular.zero

theorem IsRegular.one : IsRegular (1 : Language α) := by
  apply isRegular_iff.mpr
  use Fin 2, inferInstance, ⟨fun _ _ => 1, 0, { 0 }⟩
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  ext x
  rw [Set.mem_setOf_eq]
  cases x with
  | nil =>
    simp
  | cons _ x' =>
    simp
    intro h
    have h_dead_state : ∀ w : List α, List.foldl (fun (_ : Fin 2) _ => 1) 1 w = 1 := by
      intro w
      induction w with
      | nil =>
        simp
      | cons b w' ih =>
        simp [ih]
    have h_absurd := h_dead_state x'
    rw [h] at h_absurd
    contradiction

theorem IsRegular.mul {L₁ L₂ : Language α} [DecidableEq α]
    (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) :
    IsRegular (L₁ * L₂) := by
  classical
  have ⟨σ₁, _, M₁, hM₁⟩ := h₁
  have ⟨σ₂, _, M₂, hM₂⟩ := h₂
  have εM₁ := M₁.toNFA.toεNFA
  have εM₂ := M₂.toNFA.toεNFA
  let step (q : σ₁ ⊕ σ₂) (ox : Option α) : Set (σ₁ ⊕ σ₂) :=
    match q, ox with
    | Sum.inl q₁, some x =>
      { Sum.inl (M₁.step q₁ x) }
    | Sum.inl q₁, none =>
      if (q₁ ∈ M₁.accept) then { Sum.inr M₂.start } else {}
    | Sum.inr q₂, some x =>
      { Sum.inr (M₂.step q₂ x)}
    | Sum.inr q₂, none =>
      {}
  let εM : εNFA α (σ₁ ⊕ σ₂) := {
    step := step
    start := { Sum.inl M₁.start }
    accept := { q | ∃ q₂, q = Sum.inr q₂ ∧ q₂ ∈ M₂.accept }
  }
  have M := εM.toNFA.toDFA
  apply isRegular_iff.mpr
  use Set (σ₁ ⊕ σ₂), inferInstance, M
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  sorry

theorem IsRegular.kstar {L : Language α} (h : IsRegular L) : IsRegular (L∗) := by
  sorry

theorem IsRegular.singleton {a : α} [DecidableEq α] : IsRegular ({ [a] }) := by
  apply isRegular_iff.mpr
  let step (n : Fin 3) (x : α) : Fin 3 :=
    match n.val with
    | Nat.zero =>
      if (x = a) then 1 else 2
    | Nat.succ n' =>
      2
  use Fin 3, inferInstance, ⟨step, 0, { 1 }⟩
  ext x
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  constructor
  · intro h
    rw [Set.mem_setOf_eq] at h
    cases x with
    | nil =>
      simp at h
    | cons b x' =>
      have h_dead_state : ∀ w, List.foldl step 2 w = 2 := by
        intro w
        induction w with
        | nil =>
          simp
        | cons b w' ih =>
          simp [step, ih]
      by_cases heq : b = a
      · subst heq
        cases x' with
        | nil =>
          rfl
        | cons c x'' =>
          grind
      · grind
  · grind

end Language
