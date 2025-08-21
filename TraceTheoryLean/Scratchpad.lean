import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import Mathlib.Computability.NFA
import Mathlib.Logic.Relation

universe u v
variable {α : Type u} {σ : Type v} {M : NFA α σ}

variable (M) in
def lang_reverse : (NFA α σ) where
  step := fun (s : σ) (a : α) => {x | s ∈ M.step x a}
  start := M.accept
  accept := M.start

variable (M) in
lemma reverse_reverse :
  lang_reverse (lang_reverse M) = M := by
  simp [lang_reverse]

variable (M) in
lemma forward_subset_reverse_nondisjoint (N : NFA α σ) (S : Set σ) (T : Set σ) (a : α) :
  (N = lang_reverse M) -> (T ⊆ M.stepSet S a ∧ T ≠ ∅) -> (S ∩ N.stepSet T a ≠ ∅) := by
  intro h1 h2
  simp [h1]
  simp [NFA.stepSet]
  simp [lang_reverse]
  obtain ⟨h_sub, h_ne⟩ := h2
  obtain ⟨t, ht⟩ := Set.nonempty_iff_ne_empty.mpr h_ne
  have ht_mem : t ∈ M.stepSet S a := h_sub ht
  simp [NFA.stepSet] at ht_mem
  obtain ⟨i, hi, ht_step⟩ := ht_mem
  have : i ∈ S ∩ ⋃ s ∈ T, {x | s ∈ M.step x a} :=
    ⟨hi, by
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨t, ht, ht_step⟩⟩
  rw [<- Set.not_nonempty_iff_eq_empty, Set.nonempty_def, Classical.not_not]
  use i
