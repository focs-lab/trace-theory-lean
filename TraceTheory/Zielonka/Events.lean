import TraceTheory.Computability.AsyncAutomata
import Mathlib.Data.List.FinRange

namespace TraceTheory.Zielonka

set_option backward.isDefEq.respectTransparency false

variable {α β : Type} {I : Independence α}

/-- Move a downward-closed selection to the front by commuting independent letters.
The pairwise hypothesis says that a letter moved left never crosses a dependent one. -/
theorem filter_split (label : β → α) (s : β → Prop) [DecidablePred s]
    (w : List β)
    (h : w.Pairwise (fun e f => ¬ s e → s f → I.rel (label e) (label f))) :
    TraceEqv I (w.map label)
      (((w.filter s).map label) ++ ((w.filter (fun e => ¬ s e)).map label)) := by
  induction w with
  | nil => exact .refl []
  | cons e w ih =>
    obtain ⟨he, hw⟩ := List.pairwise_cons.mp h
    have ht := ih hw
    by_cases hs : s e
    · simpa [hs] using (TraceEqv.refl [label e]).compat ht
    · have hc : I.Independent [label e] ((w.filter s).map label) := by
        intro a ha b hb
        obtain rfl : a = label e := by simpa using ha
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
        obtain ⟨hfw, hfs⟩ := List.mem_filter.mp hf
        exact he f hfw hs (of_decide_eq_true hfs)
      have hswap := (comm_singleton_of_indep hc).symm.compat
        (TraceEqv.refl ((w.filter (fun e => ¬ s e)).map label))
      have htail := (TraceEqv.refl [label e]).compat ht
      apply htail.trans
      simpa [hs, List.append_assoc] using hswap

variable (I) (w : List α)

/-- Events are positions in a word, including distinct occurrences of the same letter. -/
abbrev Event := Fin w.length

def label (e : Event w) : α := w[e.val]

/-- The generating causal edges: an earlier dependent occurrence precedes a later one. -/
def Edge (e f : Event w) : Prop := e < f ∧ ¬ I.rel (label w e) (label w f)

/-- Causality is the reflexive transitive closure of the dependence edges. -/
def Before (e f : Event w) : Prop := Relation.ReflTransGen (Edge I w) e f

variable {I w}

theorem before_refl (e : Event w) : Before I w e e := .refl

theorem before_trans {e f g : Event w} (hef : Before I w e f)
    (hfg : Before I w f g) : Before I w e g := hef.trans hfg

theorem le_of_before {e f : Event w} (h : Before I w e f) : e ≤ f := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem before_antisymm {e f : Event w} (hef : Before I w e f)
    (hfe : Before I w f e) : e = f :=
  le_antisymm (le_of_before hef) (le_of_before hfe)

theorem before_of_lt_of_dependent {e f : Event w} (hlt : e < f)
    (hdep : ¬ I.rel (label w e) (label w f)) : Before I w e f :=
  Relation.ReflTransGen.single ⟨hlt, hdep⟩

/-- An ideal is a downward-closed set of events (PDF, section 1.7.1). -/
def IsIdeal (I : Independence α) (s : Finset (Event w)) : Prop :=
  ∀ ⦃e f⦄, Before I w e f → f ∈ s → e ∈ s

theorem isIdeal_empty : IsIdeal I (∅ : Finset (Event w)) := by simp [IsIdeal]

theorem isIdeal_univ : IsIdeal I (Finset.univ : Finset (Event w)) := by simp [IsIdeal]

theorem IsIdeal.union {s t : Finset (Event w)} (hs : IsIdeal I s) (ht : IsIdeal I t) :
    IsIdeal I (s ∪ t) := by
  intro e f hef hf
  rcases Finset.mem_union.mp hf with hf | hf
  · exact Finset.mem_union.mpr (.inl (hs hef hf))
  · exact Finset.mem_union.mpr (.inr (ht hef hf))

theorem IsIdeal.inter {s t : Finset (Event w)} (hs : IsIdeal I s) (ht : IsIdeal I t) :
    IsIdeal I (s ∩ t) := by
  intro e f hef hf
  exact Finset.mem_inter.mpr ⟨hs hef (Finset.mem_inter.mp hf).1,
    ht hef (Finset.mem_inter.mp hf).2⟩

variable (w)

/-- Project onto selected events in their original word order (PDF, page 22). -/
def project (s : Finset (Event w)) : List α :=
  ((List.finRange w.length).filter (fun e => e ∈ s)).map (label w)

@[simp]
theorem project_empty : project w ∅ = [] := by simp [project]

@[simp]
theorem project_univ : project w Finset.univ = w := by
  simp only [project, Finset.mem_univ, decide_true, List.filter_true]
  exact List.map_getElem_finRange w

variable {w}

/-- Lemma 1.28: split a larger ideal into a smaller ideal and its residue. -/
theorem ideal_factorization (s t : Finset (Event w)) (hs : IsIdeal I s) (hst : s ⊆ t) :
    TraceEqv I (project w t) (project w s ++ project w (t \ s)) := by
  have horder : ((List.finRange w.length).filter (fun e => e ∈ t)).Pairwise
      (fun e f => e < f) := (List.pairwise_lt_finRange _).filter _
  have hsplit := filter_split (I := I) (label w) (fun e => e ∈ s)
    ((List.finRange w.length).filter (fun e => e ∈ t))
    (horder.imp (fun {e f} hef he hf => by
      by_contra hdep
      exact he (hs (before_of_lt_of_dependent hef hdep) hf)))
  have hfilter : ((List.finRange w.length).filter (fun e => e ∈ t)).filter
      (fun e => e ∈ s) = (List.finRange w.length).filter (fun e => e ∈ s) := by
    simp only [List.filter_filter]
    congr 1
    funext e
    by_cases he : e ∈ s
    · simp [he, hst he]
    · simp [he]
  simpa [project, List.filter_filter, hfilter, Finset.mem_sdiff, and_comm] using hsplit

/-- Monoid effects compose in the same order as the ideal factors. -/
theorem ideal_factorization_effect {M : Type} [Monoid M] [DecidableEq α]
    (φ : Trace I →* M) (s t : Finset (Event w)) (hs : IsIdeal I s) (hst : s ⊆ t) :
    φ ⟦project w t⟧ = φ ⟦project w s⟧ * φ ⟦project w (t \ s)⟧ := by
  rw [← map_mul]
  exact congrArg φ (Quotient.sound (ideal_factorization s t hs hst))

end TraceTheory.Zielonka
