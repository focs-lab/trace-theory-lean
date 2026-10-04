import TraceTheory.Zielonka.IdealGossip

namespace TraceTheory.Zielonka

open Classical
noncomputable section

variable {α L : Type} {n : ℕ} {I : Independence α} {w : List α}
variable (d : Distribution α n)

/-- Events present just before the indexed event is created. -/
def prefixBefore (e : Event w) : Finset (Event w) := Finset.univ.filter (fun f => f < e)

@[simp] theorem mem_prefixBefore (e f : Event w) : f ∈ prefixBefore e ↔ f < e := by
  simp [prefixBefore]

theorem isIdeal_prefixBefore (e : Event w) : IsIdeal I (prefixBefore e) := by
  intro f g hfg hg
  exact (mem_prefixBefore e f).mpr ((le_of_before hfg).trans_lt ((mem_prefixBefore e g).mp hg))

/-- Chronological freshness tests only actual prefix ideals. Events are represented
by their original indices, so no equality transport is hidden in the certificate. -/
def ChronologicalFresh (τ : Event w → L) : Prop :=
  ∀ e p, p ∈ d.loc (label w e) → ∀ q r f,
    secondaryIn d I w (prefixBefore e) p q r = some f → τ f ≠ τ e

/-- Equal encoded labels carry the same participant set. -/
def LabelLocations (τ : Event w → L) : Prop :=
  ∀ e f, τ e = τ f → d.loc (label w e) = d.loc (label w f)

private theorem viewIn_idem (A : Finset (Event w)) (p : Fin n) :
    viewIn d I w (viewIn d I w A p) p = viewIn d I w A p := by
  apply Finset.Subset.antisymm
  · exact viewIn_subset d _ (isIdeal_viewIn d A p) p
  · intro e he
    obtain ⟨f, hf, hfp, hef⟩ := (mem_viewIn d A p e).mp he
    have hfv : f ∈ viewIn d I w A p :=
      (mem_viewIn d A p f).mpr ⟨f, hf, hfp, before_refl f⟩
    exact (mem_viewIn d _ p e).mpr ⟨f, hfv, hfp, hef⟩

/-- A globally primary event cannot have its label reused by a later event.
The maximal frontier of the earlier prefix retains the event as primary somewhere. -/
theorem primary_label_ne_later (hcompat : d.Compatible I) (τ : Event w → L)
    (hfresh : ChronologicalFresh d (I := I) τ) (hloc : LabelLocations d τ)
    (p a : Fin n) {e f : Event w} (he : primary d I w p a = some e)
    (hef : e < f) : τ e ≠ τ f := by
  intro heq
  obtain ⟨hep, hea, hemax⟩ := (latest_eq_some_iff d _ a e).mp he
  have hfa : a ∈ d.loc (label w f) := (hloc e f heq) ▸ hea
  obtain ⟨m, hm, hem⟩ := exists_latest_view d hcompat p hep
  obtain ⟨_, hmp, hmbound⟩ := (latest_eq_some_iff d _ p m).mp hm
  have heH : e ∈ prefixBefore f := (mem_prefixBefore f e).mpr hef
  have hed : e ∈ down I {m} :=
    (mem_down {m} e).mpr ⟨m, Finset.mem_singleton_self m, hem⟩
  obtain ⟨g, hg, heg, hgmax⟩ := exists_maximal_above
    (prefixBefore f ∩ down I {m}) (Finset.mem_inter.mpr ⟨heH, hed⟩)
  obtain ⟨hgH, hgm⟩ := Finset.mem_inter.mp hg
  have hgmb : Before I w g m := by simpa using (mem_down {m} g).mp hgm
  have hgl := maximal_intersection_latest d hcompat (prefixBefore f)
    (isIdeal_prefixBefore f) m p hmp
    (fun x _ hxp => hmbound x (Finset.mem_univ x) hxp) g hgH hgmb hgmax
  obtain ⟨s, hs⟩ := (mem_latestEvents d _ g).mp hgl
  have hvs := viewIn_eq_down_latest d hcompat (prefixBefore f) s hs
  have heprim : primaryIn d I w (prefixBefore f) s a = some e := by
    unfold primaryIn
    rw [hvs]
    apply (latest_eq_some_iff d _ a e).mpr
    refine ⟨(mem_down _ e).mpr ⟨g, Finset.mem_singleton_self g, heg⟩, hea, ?_⟩
    intro x hx hxa
    obtain ⟨g', hg', hxg⟩ := (mem_down _ x).mp hx
    have hgg' : g' = g := Finset.mem_singleton.mp hg'
    subst g'
    have hgp : g ∈ view d I w p := by
      rw [view_eq_down_latest d hcompat p hm]
      exact hgm
    exact hemax x (isIdeal_view d p hxg hgp) hxa
  obtain ⟨s', hs'⟩ := primaryIn_secondaryIn_coverage d hcompat (prefixBefore f)
    (isIdeal_prefixBefore f) s a a heprim hea
  exact hfresh f a hfa s' a e hs' heq

/-- Chronological secondary freshness implies injectivity on current primary events. -/
theorem chronologicalFresh_primary_injective (hcompat : d.Compatible I)
    (τ : Event w → L) (hfresh : ChronologicalFresh d (I := I) τ)
    (hloc : LabelLocations d τ) {e f : Event w}
    (he : ∃ p r, primary d I w p r = some e)
    (hf : ∃ p r, primary d I w p r = some f) (heq : τ e = τ f) : e = f := by
  obtain ⟨p, r, he⟩ := he
  obtain ⟨q, s, hf⟩ := hf
  rcases lt_trichotomy e f with h | h | h
  · exact (primary_label_ne_later d hcompat τ hfresh hloc p r he h heq).elim
  · exact h
  · exact (primary_label_ne_later d hcompat τ hfresh hloc q s hf h heq.symm).elim

/-- Under the causal-cut guard, labels shared by primary and secondary entries
identify the same actual event. No injectivity of all secondary labels is assumed. -/
theorem guarded_primary_secondary_label_eq (hcompat : d.Compatible I)
    (τ : Event w → L) (hfresh : ChronologicalFresh d (I := I) τ)
    (hloc : LabelLocations d τ) (p q r a s : Fin n) {e g : Event w}
    (he : primary d I w p a = some e) (hg : secondary d I w q r s = some g)
    (hguard : primary d I w p r = none ∨
      ∃ h m, primary d I w p r = some h ∧ primary d I w q r = some m ∧ Before I w h m)
    (heq : τ e = τ g) : e = g := by
  rcases lt_trichotomy e g with heg | heg | hge
  · exact (primary_label_ne_later d hcompat τ hfresh hloc p a he heg heq).elim
  · exact heg
  · obtain ⟨hep, hea, _⟩ := (latest_eq_some_iff d _ a e).mp he
    have hlocations := hloc e g heq
    cases hm : primary d I w q r with
    | none => simp [secondary, hm, latest, down_empty] at hg
    | some m =>
      have hgm : latest d (down I {m}) s = some g := by
        simpa [secondary, hm] using hg
      obtain ⟨hgdown, hgs, hgmax⟩ := (latest_eq_some_iff d _ s g).mp hgm
      have hes : s ∈ d.loc (label w e) := hlocations.symm ▸ hgs
      have hnotem : ¬ Before I w e m := by
        intro hem
        have hed := (mem_down {m} e).mpr ⟨m, Finset.mem_singleton_self m, hem⟩
        exact (not_le_of_gt hge) (hgmax e hed hes)
      have hea' : a ∈ d.loc (label w g) := hlocations ▸ hea
      let H := prefixBefore e
      let A := viewIn d I w H a
      let J := A ∪ down I {m}
      have hA : IsIdeal I A := isIdeal_viewIn d H a
      have hJ : IsIdeal I J := hA.union (isIdeal_down {m})
      have hAp : A ⊆ view d I w p := by
        intro x hx
        obtain ⟨f, hf, hfa, hxf⟩ := (mem_viewIn d H a x).mp hx
        have hfe : Before I w f e := before_of_same_process hcompat a hfa hea
          ((mem_prefixBefore e f).mp hf).le
        exact isIdeal_view d p (hxf.trans hfe) hep
      have hview : viewIn d I w J a = viewIn d I w H a := by
        calc
          viewIn d I w J a = viewIn d I w A a := by
            apply viewIn_union_eq_left d A (down I {m}) a
            intro f hf hfa
            have hfm : Before I w f m := by simpa using (mem_down {m} f).mp hf
            have hfe : f < e := by
              apply lt_of_not_ge
              intro hef
              exact hnotem ((before_of_same_process hcompat a hea hfa hef).trans hfm)
            have hfA : f ∈ A :=
              (mem_viewIn d H a f).mpr
                ⟨f, (mem_prefixBefore e f).mpr hfe, hfa, before_refl f⟩
            exact (viewIn_idem d H a).symm ▸ hfA
          _ = viewIn d I w H a := viewIn_idem d H a
      have hbound : ∀ f ∈ view d I w p, r ∈ d.loc (label w f) → f ≤ m := by
        apply process_bound_of_primary d hcompat p r m
        rcases hguard with hnone | ⟨h, m', hh, hm', hhm⟩
        · exact Or.inl hnone
        · have hmm' : m' = m := Option.some.inj (hm'.symm.trans hm)
          subst m'
          exact Or.inr ⟨h, hh, hhm⟩
      have hmr := ((latest_eq_some_iff d _ r m).mp hm).2.1
      have hmJ : latest d J r = some m := by
        apply (latest_eq_some_iff d J r m).mpr
        refine ⟨Finset.mem_union_right _ (subset_down {m} (Finset.mem_singleton_self m)), hmr, ?_⟩
        intro f hf hfr
        rcases Finset.mem_union.mp hf with hf | hf
        · exact hbound f (hAp hf) hfr
        · have hfm : Before I w f m := by simpa using (mem_down {m} f).mp hf
          exact le_of_before hfm
      have hgprim : primaryIn d I w J r s = some g := by
        unfold primaryIn
        rw [viewIn_eq_down_latest d hcompat J r hmJ]
        exact hgm
      obtain ⟨b, hb⟩ := primaryIn_secondaryIn_coverage d hcompat J hJ r a s hgprim hea'
      have hbH : secondaryIn d I w H a b s = some g := by
        rw [← secondaryIn_eq_of_viewIn_eq d J H a hview b s]
        exact hb
      exact (hfresh e a hea b s g hbH heq.symm).elim

end
end TraceTheory.Zielonka
