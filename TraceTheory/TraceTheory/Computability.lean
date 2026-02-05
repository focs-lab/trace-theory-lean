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

theorem IsRegular.mul {L₁ L₂ : Language α}
    (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) :
    IsRegular (L₁ * L₂) := by
  sorry

theorem IsRegular.kstar {L : Language α} (h : IsRegular L) : IsRegular (L∗) := by
  sorry

theorem IsRegular.singleton {a : α} [DecidableEq α] : IsRegular ({ [a] }) := by
  apply isRegular_iff.mpr
  let σ (n : Fin 3) (x : α) : Fin 3 := match n.val with
  | Nat.zero =>
    if (x = a) then 1 else 2
  | Nat.succ n' =>
    2
  use Fin 3, inferInstance, ⟨σ, 0, { 1 }⟩
  ext x
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  constructor
  · intro h
    rw [Set.mem_setOf_eq] at h
    cases x with
    | nil =>
      simp at h
    | cons b x' =>
      have h_dead_state : ∀ w, List.foldl σ 2 w = 2 := by
        intro w
        induction w with
        | nil =>
          simp
        | cons b w' ih =>
          simp [σ, ih]
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
