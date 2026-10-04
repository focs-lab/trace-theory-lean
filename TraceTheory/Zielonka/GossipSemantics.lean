import TraceTheory.Zielonka.Views

namespace TraceTheory.Zielonka

open Classical

noncomputable section

variable {α : Type} {n : ℕ} {I : Independence α} {w : List α}
variable (d : Distribution α n) (hcompat : d.Compatible I)

/-- The primary events, forgetting their process indices. -/
def primaryEvents (I : Independence α) (w : List α) (p : Fin n) : Finset (Event w) :=
  Finset.univ.filter (fun e => ∃ q, primary d I w p q = some e)

@[simp]
theorem mem_primaryEvents (p : Fin n) (e : Event w) :
    e ∈ primaryEvents d I w p ↔ ∃ q, primary d I w p q = some e := by
  simp [primaryEvents]

theorem primaryEvents_subset_view (p : Fin n) : primaryEvents d I w p ⊆ view d I w p := by
  intro e he
  obtain ⟨q, hq⟩ := (mem_primaryEvents d p e).mp he
  exact ((latest_eq_some_iff d _ q e).mp hq).1

theorem exists_latest (s : Finset (Event w)) (p : Fin n) {e : Event w}
    (he : e ∈ s) (hp : p ∈ d.loc (label w e)) : ∃ f, latest d s p = some f := by
  cases hf : latest d s p with
  | some f => exact ⟨f, rfl⟩
  | none =>
    have hempty := (latest_eq_none_iff d s p).mp hf
    have hmem : e ∈ s ∩ processEvents d w p :=
      Finset.mem_inter.mpr ⟨he, (mem_processEvents d p e).mpr hp⟩
    simp [hempty] at hmem

include hcompat in
theorem exists_latest_view (p : Fin n) {e : Event w} (he : e ∈ view d I w p) :
    ∃ f, latest d Finset.univ p = some f ∧ Before I w e f := by
  obtain ⟨g, hgp, heg⟩ := (mem_view d p e).mp he
  obtain ⟨f, hf⟩ := exists_latest d Finset.univ p (Finset.mem_univ g) hgp
  exact ⟨f, hf, heg.trans (before_latest d hcompat _ p hf (Finset.mem_univ g) hgp)⟩

include hcompat in
/-- A causal edge synchronizes at least one common process. -/
theorem exists_process_of_edge {e f : Event w} (h : Edge I w e f) :
    ∃ p, p ∈ d.loc (label w e) ∧ p ∈ d.loc (label w f) := by
  have hnot : ¬ Disjoint (d.loc (label w e)) (d.loc (label w f)) :=
    fun hd => h.2 ((hcompat _ _).mpr hd)
  simpa [Finset.disjoint_left, not_forall] using hnot

include hcompat in
/-- One half of Lemma 1.19: an intersection-maximal event is primary to `q`.
Following a causal path toward the last `p`-event exposes a common process. -/
theorem primary_of_maximal_intersection (p q : Fin n) (e : Event w)
    (hep : e ∈ view d I w p) (heq : e ∈ view d I w q)
    (hmax : ∀ f ∈ view d I w p ∩ view d I w q, Before I w e f → f = e) :
    e ∈ primaryEvents d I w q := by
  obtain ⟨m, hm, hem⟩ := exists_latest_view d hcompat p hep
  rcases Relation.ReflTransGen.cases_head hem with hem | ⟨f, hef, hfm⟩
  · subst m
    have hep' := ((latest_eq_some_iff d _ p e).mp hm).2.1
    apply (mem_primaryEvents d q e).mpr
    refine ⟨p, (latest_eq_some_iff d _ p e).mpr ⟨heq, hep', ?_⟩⟩
    intro f hf hfp
    have hle := ((latest_eq_some_iff d _ p e).mp hm).2.2 f (Finset.mem_univ f) hfp
    exact hle
  · have hfp : f ∈ view d I w p := by
      rw [view_eq_down_latest d hcompat p hm]
      exact (mem_down {m} f).mpr ⟨m, Finset.mem_singleton_self m, hfm⟩
    have hfq : f ∉ view d I w q := by
      intro hfq
      have hfe := hmax f (Finset.mem_inter.mpr ⟨hfp, hfq⟩) (.single hef)
      exact (ne_of_lt hef.1) hfe.symm
    obtain ⟨r, her, hfr⟩ := exists_process_of_edge d hcompat hef
    apply (mem_primaryEvents d q e).mpr
    refine ⟨r, (latest_eq_some_iff d _ r e).mpr ⟨heq, her, ?_⟩⟩
    intro g hg hgr
    apply le_of_not_gt
    intro heg
    by_cases hgf : g < f
    · have hgp : g ∈ view d I w p :=
        isIdeal_view d p (before_of_same_process hcompat r hgr hfr hgf.le) hfp
      have hge := hmax g (Finset.mem_inter.mpr ⟨hgp, hg⟩)
        (before_of_same_process hcompat r her hgr heg.le)
      exact (ne_of_lt heg) hge.symm
    · have hfg := before_of_same_process hcompat r hfr hgr (le_of_not_gt hgf)
      exact hfq (isIdeal_view d q hfg hg)

include hcompat in
/-- Lemma 1.19: maximal events in an intersection are primary to both processes. -/
theorem maximal_intersection_mem_primary (p q : Fin n) (e : Event w)
    (he : e ∈ view d I w p ∩ view d I w q)
    (hmax : ∀ f ∈ view d I w p ∩ view d I w q, Before I w e f → f = e) :
    e ∈ primaryEvents d I w p ∩ primaryEvents d I w q := by
  obtain ⟨hep, heq⟩ := Finset.mem_inter.mp he
  refine Finset.mem_inter.mpr ⟨?_, primary_of_maximal_intersection d hcompat p q e hep heq hmax⟩
  apply primary_of_maximal_intersection d hcompat q p e heq hep
  simpa [Finset.inter_comm] using hmax

/-- Every event of a finite ideal lies below one of its maximal events. -/
theorem exists_maximal_above (s : Finset (Event w)) {e : Event w} (he : e ∈ s) :
    ∃ f ∈ s, Before I w e f ∧ ∀ g ∈ s, Before I w f g → g = f := by
  let es := s.filter (fun f => Before I w e f)
  have hne : es.Nonempty := ⟨e, Finset.mem_filter.mpr ⟨he, before_refl e⟩⟩
  let f := es.max' hne
  have hf := Finset.mem_filter.mp (Finset.max'_mem es hne)
  refine ⟨f, hf.1, hf.2, ?_⟩
  intro g hg hfg
  apply le_antisymm
  · exact Finset.le_max' es g (Finset.mem_filter.mpr ⟨hg, hf.2.trans hfg⟩)
  · exact le_of_before hfg

include hcompat in
/-- Two-view intersections are generated by their common primary events. -/
theorem view_inter_eq_down_primary (p q : Fin n) :
    view d I w p ∩ view d I w q =
      down I (primaryEvents d I w p ∩ primaryEvents d I w q) := by
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨f, hf, hef, hmax⟩ := exists_maximal_above _ he
    exact (mem_down _ e).mpr ⟨f, maximal_intersection_mem_primary d hcompat p q f hf hmax, hef⟩
  · intro e he
    obtain ⟨f, hf, hef⟩ := (mem_down _ e).mp he
    obtain ⟨hfp, hfq⟩ := Finset.mem_inter.mp hf
    exact Finset.mem_inter.mpr
      ⟨isIdeal_view d p hef (primaryEvents_subset_view d p hfp),
        isIdeal_view d q hef (primaryEvents_subset_view d q hfq)⟩

include hcompat in
/-- Lemma 1.20: latest information can be compared using only common primary events. -/
theorem primary_before_iff (p q r : Fin n) {e f : Event w}
    (he : primary d I w p r = some e) (hf : primary d I w q r = some f) :
    Before I w e f ↔
      ∃ g ∈ primaryEvents d I w p ∩ primaryEvents d I w q, Before I w e g := by
  obtain ⟨hep, her, _⟩ := (latest_eq_some_iff d _ r e).mp he
  obtain ⟨hfq, _, _⟩ := (latest_eq_some_iff d _ r f).mp hf
  constructor
  · intro hef
    have heq := isIdeal_view d q hef hfq
    have hmem : e ∈ down I (primaryEvents d I w p ∩ primaryEvents d I w q) := by
      rw [← view_inter_eq_down_primary d hcompat p q]
      exact Finset.mem_inter.mpr ⟨hep, heq⟩
    exact (mem_down _ e).mp hmem
  · rintro ⟨g, hg, heg⟩
    have hgq := primaryEvents_subset_view d q (Finset.mem_inter.mp hg).2
    exact before_latest d hcompat _ r hf (isIdeal_view d q heg hgq) her

end

end TraceTheory.Zielonka
