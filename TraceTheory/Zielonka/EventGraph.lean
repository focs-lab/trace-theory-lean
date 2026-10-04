import TraceTheory.Zielonka.Events
import TraceTheory.DependenceGraph
import Mathlib.Logic.Equiv.Fin.Basic

namespace TraceTheory.Zielonka

set_option backward.isDefEq.respectTransparency false

variable {α : Type} (I : Independence α) (w : List α)

/-- The dependence graph whose vertices are the actual indexed occurrences in a word. -/
def eventGraph : DependenceGraph I.inducedDependence where
  V := Event w
  R := Edge I w
  φ := label w
  acyclic := by
    intro e h
    have hlt : ∀ {e f : Event w}, Relation.TransGen (Edge I w) e f → e < f := by
      intro e f h
      induction h with
      | single h => exact h.1
      | tail _ h ih => exact ih.trans h.1
    exact (lt_irrefl e) (hlt h)
  d_conn := by
    intro e f
    change (Edge I w e f ∨ Edge I w f e ∨ e = f) ↔ ¬ I.rel (label w e) (label w f)
    constructor
    · rintro (h | h | rfl)
      · exact h.2
      · exact fun hi => h.2 (I.symm _ _ hi)
      · exact I.irrefl _
    · intro hd
      rcases lt_trichotomy e f with h | h | h
      · exact Or.inl ⟨h, hd⟩
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl ⟨h, fun hi => hd (I.symm _ _ hi)⟩)

open DependenceGraph

/-- Appending a letter adds precisely its final indexed event. -/
def eventGraph_concat_iso (a : α) :
    Iso (compose (eventGraph I w) (singletonGraph I.inducedDependence a))
      (eventGraph I (w ++ [a])) := by
  let e : Fin w.length ⊕ Unit ≃ Fin (w ++ [a]).length :=
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1))).trans
      finSumFinEquiv).trans (finCongr (by simp))
  have hl (i : Fin w.length) : label (w ++ [a]) (e (.inl i)) = label w i := by
    simp [e, label, finSumFinEquiv_apply_left, List.getElem_append_left]
  have hr (u : Unit) : label (w ++ [a]) (e (.inr u)) = a := by
    cases u
    simp [e, label, finSumFinEquiv_apply_right, List.getElem_append_right]
  refine ⟨e, ?_, ?_⟩
  · intro v
    cases v with
    | inl i => exact (hl i).symm
    | inr u => exact (hr u).symm
  · intro v z
    cases v with
    | inl i =>
      cases z with
      | inl j =>
        change Edge I w i j ↔ Edge I (w ++ [a]) (e (.inl i)) (e (.inl j))
        unfold Edge
        rw [hl, hl]
        simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl,
          finSumFinEquiv_apply_left, finCongr_apply, Fin.lt_def, Fin.val_cast, Fin.val_castAdd]
      | inr u =>
        change ¬ I.rel (label w i) a ↔ Edge I (w ++ [a]) (e (.inl i)) (e (.inr u))
        unfold Edge
        rw [hl, hr]
        simp [e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        intro _
        exact i.isLt
    | inr u =>
      cases z with
      | inl j =>
        change False ↔ Edge I (w ++ [a]) (e (.inr u)) (e (.inl j))
        simp [Edge, e, Fin.lt_def, finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right, Nat.not_lt.mpr j.isLt.le]
      | inr t =>
        change False ↔ Edge I (w ++ [a]) (e (.inr u)) (e (.inr t))
        have : u = t := @Subsingleton.elim Unit inferInstance u t
        subst t
        simp [Edge]

/-- Indexed occurrence graphs represent the repository's canonical word graphs. -/
theorem eventGraph_isomorphic_fromString :
    eventGraph I w ≃g fromString I.inducedDependence w := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨⟨Equiv.equivOfIsEmpty (Fin 0) Empty, ?_, ?_⟩⟩
    · intro e; exact Fin.elim0 e
    · intro e; exact Fin.elim0 e
  | append_singleton w a ih =>
    rw [fromString_concat]
    exact isomorphic_trans (isomorphic_symm ⟨eventGraph_concat_iso I w a⟩)
      (compose_congr ih (isomorphic_refl _))

/-- The indexed graph and canonical word graph give the same graph-monoid element. -/
theorem eventGraph_quotient_eq :
    (⟦eventGraph I w⟧ : DGraph I.inducedDependence) =
      ⟦fromString I.inducedDependence w⟧ :=
  Quotient.sound (eventGraph_isomorphic_fromString I w)

end TraceTheory.Zielonka
