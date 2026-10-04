import TraceTheory.Zielonka.GossipSemantics

namespace TraceTheory.Zielonka

open Classical

noncomputable section

variable {α : Type} {n : ℕ} {I : Independence α} {w : List α}
variable (d : Distribution α n) (hcompat : d.Compatible I)

include hcompat in
/-- Lemma 1.23: every participant retains every primary event as secondary information.
Choose a maximal common-view event above it; this is primary to `q`, and its
causal past retains the original event as the latest `r`-event. -/
theorem primary_secondary_coverage (p q r : Fin n) {e : Event w}
    (he : primary d I w p r = some e) (hq : q ∈ d.loc (label w e)) :
    ∃ s, secondary d I w q s r = some e := by
  obtain ⟨hep, her, hmax⟩ := (latest_eq_some_iff d _ r e).mp he
  have heq := mem_view_of_participates (I := I) d q e hq
  obtain ⟨f, hf, hef, hfmax⟩ := exists_maximal_above
    (view d I w p ∩ view d I w q) (Finset.mem_inter.mpr ⟨hep, heq⟩)
  obtain ⟨hfp, hfq⟩ := Finset.mem_inter.mp hf
  have hprimary := primary_of_maximal_intersection d hcompat p q f hfp hfq hfmax
  obtain ⟨s, hs⟩ := (mem_primaryEvents d q f).mp hprimary
  refine ⟨s, ?_⟩
  unfold secondary
  rw [hs]
  simp only [Option.toFinset_some]
  apply (latest_eq_some_iff d _ r e).mpr
  refine ⟨(mem_down _ e).mpr ⟨f, Finset.mem_singleton_self f, hef⟩, her, ?_⟩
  intro g hg hgr
  obtain ⟨f', hf', hgf⟩ := (mem_down _ g).mp hg
  obtain rfl := Finset.mem_singleton.mp hf'
  exact hmax g (isIdeal_view d p hgf hfp) hgr

/-- The secondary events visible to a process, forgetting both process indices. -/
def secondaryEvents (I : Independence α) (w : List α) (p : Fin n) : Finset (Event w) :=
  Finset.univ.filter (fun e => ∃ q r, secondary d I w p q r = some e)

@[simp]
theorem mem_secondaryEvents (p : Fin n) (e : Event w) :
    e ∈ secondaryEvents d I w p ↔ ∃ q r, secondary d I w p q r = some e := by
  simp [secondaryEvents]

include hcompat in
/-- Corollary 1.24: a participant missing an event from its secondary information
can conclude that no process has that event in its primary information. -/
theorem not_primary_of_not_secondary (q : Fin n) {e : Event w}
    (hq : q ∈ d.loc (label w e)) (he : e ∉ secondaryEvents d I w q) :
    ∀ p, e ∉ primaryEvents d I w p := by
  intro p hp
  obtain ⟨r, hr⟩ := (mem_primaryEvents d p e).mp hp
  obtain ⟨s, hs⟩ := primary_secondary_coverage d hcompat p q r hr hq
  exact he ((mem_secondaryEvents d q e).mpr ⟨s, r, hs⟩)

end

end TraceTheory.Zielonka
