import TraceTheory.Zielonka.Construction

namespace TraceTheory

open Zielonka

variable {α : Type} {I : Independence α} {n : ℕ}

/-- Zielonka's theorem for any compatible distribution. The construction follows
Mukund's gossip and residue proof (Sections 1.7–1.8), using a finite recognizing
monoid in place of the minimal DFA's transition transformations. -/
theorem zielonka (d : Distribution α n) (hcompat : d.Compatible I)
    (T : Set (Trace I)) (hT : IsRecognizable T) :
    ∃ (Q : Fin n → Type) (_ : ∀ p, Fintype (Q p)) (A : AsyncDFA d Q),
      A.accepts = Trace.mk' I ⁻¹' T := by
  classical
  obtain ⟨M, hM, hfin, hdec, φ, hφ⟩ := hT
  refine ⟨fun _ => ResidueState n M, fun _ => inferInstance,
    residueAutomaton d φ (φ '' T), ?_⟩
  ext w
  change (residueAutomaton d φ (φ '' T)).accepts w ↔ ⟦w⟧ ∈ T
  rw [residueAutomaton_accepts d hcompat φ (φ '' T)]
  conv_rhs => rw [hφ]
  rfl

/-- Recognizable trace languages are exactly those accepted by finite
deterministic asynchronous automata over the given compatible distribution. -/
theorem recognizable_iff_async (d : Distribution α n) (hcompat : d.Compatible I)
    (T : Set (Trace I)) :
    IsRecognizable T ↔
      ∃ (Q : Fin n → Type) (_ : ∀ p, Fintype (Q p)) (A : AsyncDFA d Q),
        A.accepts = Trace.mk' I ⁻¹' T := by
  constructor
  · exact zielonka d hcompat T
  · rintro ⟨Q, hfin, A, hA⟩
    apply recognizablePreImage_is_recognizable (Trace.mk' I) Quotient.mk_surjective
    rw [← hA]
    exact recognizable_of_isRegular A.accepts_isRegular

end TraceTheory
