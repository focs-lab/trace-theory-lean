import TraceTheory.Zielonka.PrimaryCuts

namespace TraceTheory.Zielonka

open Classical
noncomputable section

variable {α : Type} {n : ℕ} {I : Independence α} {w : List α}
variable (d : Distribution α n)

/-- A process view restricted to an ambient ideal. -/
def viewIn (I : Independence α) (w : List α) (J : Finset (Event w)) (p : Fin n) :
    Finset (Event w) := down I (J ∩ processEvents d w p)

@[simp] theorem mem_viewIn (J : Finset (Event w)) (p : Fin n) (e : Event w) :
    e ∈ viewIn d I w J p ↔ ∃ f ∈ J, p ∈ d.loc (label w f) ∧ Before I w e f := by
  simp [viewIn, mem_down, and_assoc]

theorem isIdeal_viewIn (J : Finset (Event w)) (p : Fin n) :
    IsIdeal I (viewIn d I w J p) := isIdeal_down _

theorem viewIn_subset (J : Finset (Event w)) (hJ : IsIdeal I J) (p : Fin n) :
    viewIn d I w J p ⊆ J := by
  intro e he
  obtain ⟨f, hf, _, hef⟩ := (mem_viewIn d J p e).mp he
  exact hJ hef hf

/-- Restricting the ambient ideal to an event past preserves that entire process view
when the process participates in the endpoint. -/
theorem viewIn_down_singleton (m : Event w) (p : Fin n)
    (hmp : p ∈ d.loc (label w m)) :
    viewIn d I w (down I {m}) p = down I {m} := by
  apply Finset.Subset.antisymm
  · exact viewIn_subset d _ (isIdeal_down _) p
  · intro e he
    have hem : Before I w e m := by simpa using (mem_down {m} e).mp he
    exact (mem_viewIn d _ p e).mpr
      ⟨m, subset_down {m} (Finset.mem_singleton_self m), hmp, hem⟩

@[simp] theorem viewIn_univ (p : Fin n) :
    viewIn d I w Finset.univ p = view d I w p := by simp [viewIn, view]

/-- Primary information relative to an ambient ideal. -/
def primaryIn (I : Independence α) (w : List α) (J : Finset (Event w))
    (p q : Fin n) : Option (Event w) := latest d (viewIn d I w J p) q

/-- Secondary information relative to an ambient ideal. -/
def secondaryIn (I : Independence α) (w : List α) (J : Finset (Event w))
    (p q r : Fin n) : Option (Event w) :=
  latest d (down I ((primaryIn d I w J p q).toFinset)) r

theorem viewIn_eq_down_latest (hcompat : d.Compatible I)
    (J : Finset (Event w)) (p : Fin n) {m : Event w}
    (hm : latest d J p = some m) : viewIn d I w J p = down I {m} := by
  obtain ⟨hmJ, hmp, _⟩ := (latest_eq_some_iff d J p m).mp hm
  ext e
  simp only [mem_viewIn, mem_down, Finset.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨f, hf, hfp, hef⟩
    exact hef.trans (before_latest d hcompat J p hm hf hfp)
  · intro hem
    exact ⟨m, hmJ, hmp, hem⟩

/-- Lemma 1.23 holds in every ambient ideal, including auxiliary ideals used in
safe primary/secondary label comparisons. -/
theorem primaryIn_secondaryIn_coverage (hcompat : d.Compatible I)
    (J : Finset (Event w)) (hJ : IsIdeal I J) (p q r : Fin n) {e : Event w}
    (he : primaryIn d I w J p r = some e) (hq : q ∈ d.loc (label w e)) :
    ∃ s, secondaryIn d I w J q s r = some e := by
  obtain ⟨hep, her, hmax⟩ := (latest_eq_some_iff d _ r e).mp he
  have heJ := viewIn_subset d J hJ p hep
  have heq : e ∈ viewIn d I w J q :=
    (mem_viewIn d J q e).mpr ⟨e, heJ, hq, before_refl e⟩
  obtain ⟨g, hgJ, hgp, heg⟩ := (mem_viewIn d J p e).mp hep
  obtain ⟨m, hm⟩ := exists_latest d J p hgJ hgp
  have hvm := viewIn_eq_down_latest d hcompat J p hm
  obtain ⟨f, hf, hef, hfmax⟩ := exists_maximal_above
    (viewIn d I w J p ∩ viewIn d I w J q) (Finset.mem_inter.mpr ⟨hep, heq⟩)
  obtain ⟨hfp, hfq⟩ := Finset.mem_inter.mp hf
  have hfm : Before I w f m := by
    rw [hvm] at hfp
    simpa using (mem_down {m} f).mp hfp
  obtain ⟨_, hmp, hbound⟩ := (latest_eq_some_iff d J p m).mp hm
  have hlatest := maximal_intersection_latest d hcompat
    (viewIn d I w J q) (isIdeal_viewIn d J q) m p hmp
    (fun g hg hgp => hbound g (viewIn_subset d J hJ q hg) hgp) f hfq hfm (by
      intro g hg hfg
      apply hfmax g
      · exact Finset.mem_inter.mpr ⟨hvm.symm ▸ (Finset.mem_inter.mp hg).2,
          (Finset.mem_inter.mp hg).1⟩
      · exact hfg)
  obtain ⟨s, hs⟩ := (mem_latestEvents d _ f).mp hlatest
  refine ⟨s, ?_⟩
  change latest d (down I ((latest d (viewIn d I w J q) s).toFinset)) r = some e
  rw [hs]
  simp only [Option.toFinset_some]
  apply (latest_eq_some_iff d _ r e).mpr
  refine ⟨(mem_down _ e).mpr ⟨f, Finset.mem_singleton_self f, hef⟩, her, ?_⟩
  intro g hg hgr
  obtain ⟨f', hf', hgf⟩ := (mem_down _ g).mp hg
  obtain rfl := Finset.mem_singleton.mp hf'
  exact hmax g (isIdeal_viewIn d J p hgf hfp) hgr

/-- A union changes a process view only through new events of that process. -/
theorem viewIn_union_eq_left (A B : Finset (Event w)) (p : Fin n)
    (hB : ∀ e ∈ B, p ∈ d.loc (label w e) → e ∈ viewIn d I w A p) :
    viewIn d I w (A ∪ B) p = viewIn d I w A p := by
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨f, hf, hfp, hef⟩ := (mem_viewIn d (A ∪ B) p e).mp he
    rcases Finset.mem_union.mp hf with hf | hf
    · exact (mem_viewIn d A p e).mpr ⟨f, hf, hfp, hef⟩
    · exact isIdeal_viewIn d A p hef (hB f hf hfp)
  · intro e he
    obtain ⟨f, hf, hfp, hef⟩ := (mem_viewIn d A p e).mp he
    exact (mem_viewIn d (A ∪ B) p e).mpr ⟨f, Finset.mem_union_left _ hf, hfp, hef⟩

theorem primaryIn_eq_of_viewIn_eq (A B : Finset (Event w)) (p : Fin n)
    (h : viewIn d I w A p = viewIn d I w B p) (q : Fin n) :
    primaryIn d I w A p q = primaryIn d I w B p q := by simp [primaryIn, h]

theorem secondaryIn_eq_of_viewIn_eq (A B : Finset (Event w)) (p : Fin n)
    (h : viewIn d I w A p = viewIn d I w B p) (q r : Fin n) :
    secondaryIn d I w A p q r = secondaryIn d I w B p q r := by
  simp [secondaryIn, primaryIn, h]

end
end TraceTheory.Zielonka
