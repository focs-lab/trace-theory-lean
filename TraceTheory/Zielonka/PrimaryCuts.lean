import TraceTheory.Zielonka.GossipSemantics

namespace TraceTheory.Zielonka

open Classical
noncomputable section

variable {α : Type} {n : ℕ} {I : Independence α} {w : List α}
variable (d : Distribution α n)

/-- Latest events in an ideal, forgetting their process indices. -/
def latestEvents (s : Finset (Event w)) : Finset (Event w) :=
  Finset.univ.filter (fun e => ∃ r, latest d s r = some e)

@[simp] theorem mem_latestEvents (s : Finset (Event w)) (e : Event w) :
    e ∈ latestEvents d s ↔ ∃ r, latest d s r = some e := by
  simp [latestEvents]

theorem latestEvents_subset (s : Finset (Event w)) : latestEvents d s ⊆ s := by
  intro e he
  obtain ⟨r, hr⟩ := (mem_latestEvents d s e).mp he
  exact ((latest_eq_some_iff d s r e).mp hr).1

/-- A maximal common event is latest in the other ideal, provided the principal
endpoint bounds its own process events there. -/
theorem maximal_intersection_latest (hcompat : d.Compatible I)
    (s : Finset (Event w)) (hs : IsIdeal I s) (m : Event w) (p : Fin n)
    (hmp : p ∈ d.loc (label w m))
    (hbound : ∀ f ∈ s, p ∈ d.loc (label w f) → f ≤ m)
    (e : Event w) (hes : e ∈ s) (hem : Before I w e m)
    (hmax : ∀ f ∈ s ∩ down I {m}, Before I w e f → f = e) :
    e ∈ latestEvents d s := by
  rcases Relation.ReflTransGen.cases_head hem with hem | ⟨f, hef, hfm⟩
  · subst m
    exact (mem_latestEvents d s e).mpr
      ⟨p, (latest_eq_some_iff d s p e).mpr ⟨hes, hmp, hbound⟩⟩
  · have hfd : f ∈ down I {m} :=
      (mem_down {m} f).mpr ⟨m, Finset.mem_singleton_self m, hfm⟩
    have hfs : f ∉ s := by
      intro hfs
      have hfe := hmax f (Finset.mem_inter.mpr ⟨hfs, hfd⟩) (.single hef)
      exact (ne_of_lt hef.1) hfe.symm
    obtain ⟨r, her, hfr⟩ := exists_process_of_edge d hcompat hef
    apply (mem_latestEvents d s e).mpr
    refine ⟨r, (latest_eq_some_iff d s r e).mpr ⟨hes, her, ?_⟩⟩
    intro g hg hgr
    apply le_of_not_gt
    intro heg
    by_cases hgf : g < f
    · have hgd := isIdeal_down {m}
        (before_of_same_process hcompat r hgr hfr hgf.le) hfd
      have hge := hmax g (Finset.mem_inter.mpr ⟨hg, hgd⟩)
        (before_of_same_process hcompat r her hgr heg.le)
      exact (ne_of_lt heg) hge.symm
    · exact hfs (hs (before_of_same_process hcompat r hfr hgr (le_of_not_gt hgf)) hg)

/-- Latest information at an event, indexed by process. -/
def eventInformation (I : Independence α) (w : List α) (e : Event w) :
    Finset (Event w) := latestEvents d (down I {e})

/-- Primary information of `p` bounds its process events below the cut endpoint. -/
theorem process_bound_of_primary (hcompat : d.Compatible I) (p r : Fin n)
    (e : Event w)
    (h : primary d I w p r = none ∨
      ∃ f, primary d I w p r = some f ∧ Before I w f e) :
    ∀ f ∈ view d I w p, r ∈ d.loc (label w f) → f ≤ e := by
  intro f hf hfr
  rcases h with h | ⟨g, hg, hge⟩
  · have hempty := (latest_eq_none_iff d _ r).mp h
    have : f ∈ view d I w p ∩ processEvents d w r :=
      Finset.mem_inter.mpr ⟨hf, (mem_processEvents d r f).mpr hfr⟩
    simp [hempty] at this
  · exact (le_of_before (before_latest d hcompat _ r hg hf hfr)).trans (le_of_before hge)

/-- Corollary 1.33(iii): the intersection with a primary event's past is generated
by common primary and secondary information. -/
theorem view_inter_primary_cut (hcompat : d.Compatible I) (p q r : Fin n)
    (e : Event w) (he : primary d I w q r = some e)
    (hpr : primary d I w p r = none ∨
      ∃ f, primary d I w p r = some f ∧ Before I w f e) :
    view d I w p ∩ down I {e} =
      down I (primaryEvents d I w p ∩ eventInformation d I w e) := by
  have her := ((latest_eq_some_iff d _ r e).mp he).2.1
  apply Finset.Subset.antisymm
  · intro g hg
    obtain ⟨f, hf, hgf, hmax⟩ := exists_maximal_above _ hg
    obtain ⟨hfp, hfe⟩ := Finset.mem_inter.mp hf
    have hfprim : f ∈ primaryEvents d I w p := by
      apply (mem_primaryEvents d p f).mpr
      have hfm : Before I w f e := by simpa using (mem_down {e} f).mp hfe
      have hlatest := maximal_intersection_latest d hcompat
        (view d I w p) (isIdeal_view d p) e r her
        (process_bound_of_primary d hcompat p r e hpr) f hfp hfm hmax
      exact (mem_latestEvents d _ f).mp hlatest
    have hfinfo : f ∈ eventInformation d I w e := by
      obtain ⟨m, hm, hfm⟩ := exists_latest_view d hcompat p hfp
      obtain ⟨_, hmp, hbound⟩ := (latest_eq_some_iff d _ p m).mp hm
      apply maximal_intersection_latest d hcompat
        (down I {e}) (isIdeal_down {e}) m p hmp
        (fun g _ hgp => hbound g (Finset.mem_univ g) hgp) f hfe hfm
      intro g hg hfg
      apply hmax g
      · have hgm : g ∈ view d I w p := by
          rw [view_eq_down_latest d hcompat p hm]
          exact (Finset.mem_inter.mp hg).2
        exact Finset.mem_inter.mpr ⟨hgm, (Finset.mem_inter.mp hg).1⟩
      · exact hfg
    exact (mem_down _ g).mpr ⟨f, Finset.mem_inter.mpr ⟨hfprim, hfinfo⟩, hgf⟩
  · intro g hg
    obtain ⟨f, hf, hgf⟩ := (mem_down _ g).mp hg
    obtain ⟨hfp, hfe⟩ := Finset.mem_inter.mp hf
    exact Finset.mem_inter.mpr
      ⟨isIdeal_view d p hgf (primaryEvents_subset_view d p hfp),
        isIdeal_down {e} hgf (latestEvents_subset d _ hfe)⟩

/-- The secondary row, forgetting its process indices. -/
def secondaryRowEvents (I : Independence α) (w : List α) (q r : Fin n) :
    Finset (Event w) := Finset.univ.filter (fun e => ∃ s, secondary d I w q r s = some e)

@[simp] theorem mem_secondaryRowEvents (q r : Fin n) (e : Event w) :
    e ∈ secondaryRowEvents d I w q r ↔ ∃ s, secondary d I w q r s = some e := by
  simp [secondaryRowEvents]

theorem secondaryRowEvents_eq_eventInformation (q r : Fin n) (e : Event w)
    (he : primary d I w q r = some e) :
    secondaryRowEvents d I w q r = eventInformation d I w e := by
  ext f
  simp [secondaryRowEvents, eventInformation, latestEvents, secondary, he]

/-- The cut formula expressed directly in the indexed secondary row. -/
theorem view_inter_eq_down_primary_secondary (hcompat : d.Compatible I)
    (p q r : Fin n) (e : Event w) (he : primary d I w q r = some e)
    (hpr : primary d I w p r = none ∨
      ∃ f, primary d I w p r = some f ∧ Before I w f e) :
    view d I w p ∩ down I {e} =
      down I (primaryEvents d I w p ∩ secondaryRowEvents d I w q r) := by
  rw [secondaryRowEvents_eq_eventInformation d q r e he]
  exact view_inter_primary_cut d hcompat p q r e he hpr

/-- The primary indices selected by matching a secondary row. -/
def primaryCutIndices (I : Independence α) (w : List α) (p q r : Fin n) :
    Finset (Fin n) := Finset.univ.filter (fun s =>
      ∃ t e, primary d I w p s = some e ∧ secondary d I w q r t = some e)

theorem primaryCutIndices_generators (p q r : Fin n) :
    (primaryCutIndices d I w p q r).biUnion
      (fun s => (primary d I w p s).toFinset) =
        primaryEvents d I w p ∩ secondaryRowEvents d I w q r := by
  ext e
  simp only [Finset.mem_biUnion, primaryCutIndices, Finset.mem_filter,
    Finset.mem_univ, true_and, Option.mem_toFinset, Finset.mem_inter,
    mem_primaryEvents, mem_secondaryRowEvents]
  constructor
  · rintro ⟨s, ⟨t, f, hsf, htf⟩, hse⟩
    have hfe : f = e := Option.some.inj (hsf.symm.trans hse)
    subst f
    exact ⟨⟨s, hse⟩, ⟨t, htf⟩⟩
  · rintro ⟨⟨s, hse⟩, ⟨t, hte⟩⟩
    exact ⟨s, ⟨t, e, hse, hte⟩, hse⟩

theorem view_inter_eq_down_cutIndices (hcompat : d.Compatible I)
    (p q r : Fin n) (e : Event w) (he : primary d I w q r = some e)
    (hpr : primary d I w p r = none ∨
      ∃ f, primary d I w p r = some f ∧ Before I w f e) :
    view d I w p ∩ down I {e} =
      down I ((primaryCutIndices d I w p q r).biUnion
        (fun s => (primary d I w p s).toFinset)) := by
  rw [primaryCutIndices_generators]
  exact view_inter_eq_down_primary_secondary d hcompat p q r e he hpr

end
end TraceTheory.Zielonka
