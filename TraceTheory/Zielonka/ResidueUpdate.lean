import TraceTheory.Zielonka.PrimaryCuts
import TraceTheory.Zielonka.PrimaryAppend

namespace TraceTheory.Zielonka
open Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α M : Type} {n : ℕ} {I : Independence α} {w : List α} {a : α}
variable (d : Distribution α n)

/-- Old joint primary events selected by the requested table indices. -/
def jointCut (I : Independence α) (w : List α) (P R : Finset (Fin n)) :
    Finset (Event w) := R.biUnion (fun r => (latest d (jointView d I w P) r).toFinset)

/-- Indices in one source row matching the selected joint primary events. -/
def jointCutIndices (I : Independence α) (w : List α)
    (P : Finset (Fin n)) (hP : P.Nonempty) (p : Fin n) (R : Finset (Fin n)) :
    Finset (Fin n) := R.biUnion (fun r => primaryCutIndices d I w p
      (bestSource d (I := I) (w := w) P hP r) r)

theorem joint_primary_bound (hcompat : d.Compatible I) (P : Finset (Fin n))
    (p r : Fin n) (hp : p ∈ P) {e : Event w}
    (he : latest d (jointView d I w P) r = some e) :
    primary d I w p r = none ∨
      ∃ f, primary d I w p r = some f ∧ Before I w f e := by
  cases hf : primary d I w p r with
  | none => exact .inl rfl
  | some f =>
    obtain ⟨hfp, hfr, _⟩ := (latest_eq_some_iff d _ r f).mp hf
    exact .inr ⟨f, rfl, before_latest d hcompat _ r he
      (view_subset_jointView d P hp hfp) hfr⟩

/-- Selected joint cuts are reconstructible inside each participant view. -/
theorem view_inter_jointCut (hcompat : d.Compatible I) (P : Finset (Fin n))
    (hP : P.Nonempty) (p : Fin n) (hp : p ∈ P) (R : Finset (Fin n)) :
    view d I w p ∩ down I (jointCut d I w P R) =
      down I (primaryCut d I w p (jointCutIndices d I w P hP p R)) := by
  have hrow (r : Fin n) :
      view d I w p ∩ down I ((latest d (jointView d I w P) r).toFinset) =
      down I (primaryCut d I w p (primaryCutIndices d I w p
        (bestSource d (I := I) (w := w) P hP r) r)) := by
    cases he : latest d (jointView d I w P) r with
    | none =>
      have hb := primary_bestSource d (I := I) (w := w) P hP r
      rw [he] at hb
      have hi : primaryCutIndices d I w p
          (bestSource d (I := I) (w := w) P hP r) r = ∅ := by
        ext s
        simp [primaryCutIndices, secondary, hb, latest]
      simp [hi, primaryCut]
    | some e =>
      have hb := (primary_bestSource d (I := I) (w := w) P hP r).trans he
      simpa only [Option.toFinset_some, primaryCut] using
        view_inter_eq_down_cutIndices d hcompat p _ r e hb
          (joint_primary_bound d hcompat P p r hp he)
  unfold jointCut jointCutIndices
  rw [down_biUnion]
  have hcuts : primaryCut d I w p
      (R.biUnion (fun r => primaryCutIndices d I w p
        (bestSource d (I := I) (w := w) P hP r) r)) =
      R.biUnion (fun r => primaryCut d I w p (primaryCutIndices d I w p
        (bestSource d (I := I) (w := w) P hP r) r)) := by
    ext e
    simp only [mem_primaryCut, Finset.mem_biUnion]
    constructor
    · rintro ⟨s, ⟨r, hr, hs⟩, he⟩
      exact ⟨r, hr, s, hs, he⟩
    · rintro ⟨r, hr, s, hs, he⟩
      exact ⟨s, ⟨r, hr, hs⟩, he⟩
  rw [hcuts, down_biUnion]
  ext e
  simp only [Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hep, r, hr, her⟩
    exact ⟨r, hr, by rw [← hrow r]; exact Finset.mem_inter.mpr ⟨hep, her⟩⟩
  · rintro ⟨r, hr, he⟩
    rw [← hrow r] at he
    exact ⟨(Finset.mem_inter.mp he).1, r, hr, (Finset.mem_inter.mp he).2⟩

variable [Monoid M] [DecidableEq α] (φ : Trace I →* M)

/-- Multiply old table entries in participant order, excluding preceding views. -/
def updateProduct (w : List α) (P : Finset (Fin n)) (hP : P.Nonempty)
    (R : Finset (Fin n)) : List (Fin n) → Finset (Fin n) → M
  | [], _ => 1
  | p :: ps, B => primaryEffect d φ w p
      (jointCutIndices d I w P hP p R ∪ commonIndices d I w p B) *
      updateProduct w P hP R ps (insert p B)

omit [DecidableEq α] in
theorem residue_update_entry (hcompat : d.Compatible I) (P : Finset (Fin n))
    (hP : P.Nonempty) (R B : Finset (Fin n)) (p : Fin n) (hp : p ∈ P) :
    residueEffect d φ w p (down I (jointCut d I w P R) ∪ jointView d I w B) =
      primaryEffect d φ w p
        (jointCutIndices d I w P hP p R ∪ commonIndices d I w p B) := by
  rw [residueEffect_inter d φ p]
  have hi : view d I w p ∩
      (down I (jointCut d I w P R) ∪ jointView d I w B) =
      down I (primaryCut d I w p
        (jointCutIndices d I w P hP p R ∪ commonIndices d I w p B)) := by
    rw [Finset.inter_union_distrib_left, view_inter_jointCut d hcompat P hP p hp R,
      view_inter_jointView d hcompat, primaryCut_union, down_union]
  rw [hi]
  rfl

omit [DecidableEq α] in
theorem updateProduct_eq_residueProduct (hcompat : d.Compatible I)
    (P : Finset (Fin n)) (hP : P.Nonempty) (R : Finset (Fin n))
    (ps : List (Fin n)) (hps : ∀ p ∈ ps, p ∈ P) (B : Finset (Fin n)) :
    updateProduct d φ w P hP R ps B =
      residueProduct d φ w ps (down I (jointCut d I w P R) ∪ jointView d I w B) := by
  induction ps generalizing B with
  | nil => rfl
  | cons p ps ih =>
    rw [updateProduct, residueProduct, residue_update_entry d φ hcompat P hP R B p
      (hps p (List.mem_cons_self ..)), ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))]
    congr 1
    have hu : down I (jointCut d I w P R) ∪ jointView d I w (insert p B) =
        (down I (jointCut d I w P R) ∪ jointView d I w B) ∪ view d I w p := by
      ext e
      simp [jointView, or_comm]
    rw [hu]

omit [Monoid M] [DecidableEq α] in
theorem isIdeal_jointView (P : Finset (Fin n)) : IsIdeal I (jointView d I w P) := by
  intro e f hef hf
  obtain ⟨p, hp, hfp⟩ := (mem_jointView d P f).mp hf
  exact (mem_jointView d P e).mpr ⟨p, hp, isIdeal_view d p hef hfp⟩

omit [Monoid M] [DecidableEq α] in
theorem down_jointCut_subset (P R : Finset (Fin n)) :
    down I (jointCut d I w P R) ⊆ jointView d I w P := by
  intro e he
  obtain ⟨f, hf, hef⟩ := (mem_down _ e).mp he
  obtain ⟨r, _, hrf⟩ := Finset.mem_biUnion.mp hf
  have hlatest : latest d (jointView d I w P) r = some f := by simpa using hrf
  exact isIdeal_jointView d P hef ((latest_eq_some_iff d _ r f).mp hlatest).1

/-- Old participant tables reconstruct the effect above a selected joint cut. -/
theorem updateProduct_joint_residue (hcompat : d.Compatible I)
    (P : Finset (Fin n)) (hP : P.Nonempty) (R : Finset (Fin n))
    (ps : List (Fin n)) (hps : ps.toFinset = P) :
    φ ⟦project w (jointView d I w P \ down I (jointCut d I w P R))⟧ =
      updateProduct d φ w P hP R ps ∅ := by
  rw [updateProduct_eq_residueProduct d φ hcompat P hP R ps
    (fun p hp => by rw [← hps]; exact List.mem_toFinset.mpr hp)]
  simp only [jointView, Finset.biUnion_empty, Finset.union_empty]
  have hf := (residueProduct_residual d φ ps (down I (jointCut d I w P R))
    (isIdeal_down _) (by rw [hps]; exact down_jointCut_subset d P R)).symm
  simpa only [hps, jointView] using hf

omit [Monoid M] [DecidableEq α] in
theorem primaryCut_append_merged (hcompat : d.Compatible I) (p : Fin n)
    (hp : p ∈ d.loc a) (R : Finset (Fin n)) (hR : Disjoint R (d.loc a)) :
    primaryCut d I (w ++ [a]) p R = (jointCut d I w (d.loc a) R).map (oldEvent w a) := by
  have hentry (r : Fin n) (hr : r ∈ R) : primary d I (w ++ [a]) p r =
      (latest d (jointView d I w (d.loc a)) r).map (oldEvent w a) := by
    rw [primary_append_merged_index d hcompat p r hp
      (fun hra => Finset.disjoint_left.mp hR hr hra), primary_bestSource]
  ext e
  simp only [mem_primaryCut, Finset.mem_map, jointCut, Finset.mem_biUnion,
    Option.mem_toFinset]
  constructor
  · rintro ⟨r, hr, he⟩
    rw [hentry r hr] at he
    cases hf : latest d (jointView d I w (d.loc a)) r with
    | none => simp [hf] at he
    | some f =>
      simp only [hf, Option.map_some, Option.some.injEq] at he
      exact ⟨f, ⟨r, hr, hf⟩, he⟩
  · rintro ⟨f, ⟨r, hr, hf⟩, rfl⟩
    exact ⟨r, hr, by rw [hentry r hr, hf]; rfl⟩

omit [Monoid M] [DecidableEq α] in
theorem project_map_oldEvent_last (s : Finset (Event w)) :
    project (w ++ [a]) (s.map (oldEvent w a) ∪ {lastEvent w a}) = project w s ++ [a] := by
  unfold project
  rw [finRange_append_event, List.filter_append, List.map_append]
  have hpred : (fun e : Event w => decide (oldEvent w a e ∈
      s.map (oldEvent w a) ∪ {lastEvent w a})) = (fun e => decide (e ∈ s)) := by
    funext e
    have hne : oldEvent w a e ≠ lastEvent w a := by
      intro h
      have hv := congrArg Fin.val h
      have := e.isLt
      simp at hv
      omega
    simp [hne]
  rw [List.filter_map, List.map_map]
  simp only [Function.comp_def]
  rw [hpred]
  simp [label_oldEvent]

omit [Monoid M] [DecidableEq α] in
theorem participant_primary_residue (hcompat : d.Compatible I) (p : Fin n)
    (hp : p ∈ d.loc a) (R : Finset (Fin n)) (hR : Disjoint R (d.loc a)) :
    view d I (w ++ [a]) p \ down I (primaryCut d I (w ++ [a]) p R) =
      (jointView d I w (d.loc a) \ down I (jointCut d I w (d.loc a) R)).map
        (oldEvent w a) ∪ {lastEvent w a} := by
  rw [primaryCut_append_merged d hcompat p hp R hR, down_map_oldEvent,
    view_append_participant d hcompat p hp]
  have hv : (d.loc a).biUnion (fun q => (view d I w q).map (oldEvent w a)) =
      (jointView d I w (d.loc a)).map (oldEvent w a) := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_map, mem_jointView]
    constructor
    · rintro ⟨q, hq, f, hf, rfl⟩; exact ⟨f, ⟨q, hq, hf⟩, rfl⟩
    · rintro ⟨f, ⟨q, hq, hf⟩, rfl⟩; exact ⟨q, hq, f, hf, rfl⟩
  rw [hv, Finset.union_sdiff_distrib, Finset.map_sdiff]
  congr 1
  have hn : lastEvent w a ∉ (down I (jointCut d I w (d.loc a) R)).map (oldEvent w a) := by
    intro h
    obtain ⟨e, _, he⟩ := Finset.mem_map.mp h
    have hv := congrArg Fin.val he
    have := e.isLt
    simp at hv
    omega
  simp [hn]

/-- Lemma 1.35: a nontrivial participant entry is a product of old entries,
followed by the effect of the synchronizing action. -/
theorem primaryEffect_append_product (hcompat : d.Compatible I) (p : Fin n)
    (hp : p ∈ d.loc a) (R : Finset (Fin n)) (hR : Disjoint R (d.loc a))
    (ps : List (Fin n)) (hps : ps.toFinset = d.loc a) :
    primaryEffect d φ (w ++ [a]) p R =
      updateProduct d φ w (d.loc a) (d.loc_nonempty a) R ps ∅ * φ ⟦[a]⟧ := by
  unfold primaryEffect residueEffect
  rw [participant_primary_residue d hcompat p hp R hR, project_map_oldEvent_last]
  let t : Trace I := ⟦project w (jointView d I w (d.loc a) \ down I (jointCut d I w (d.loc a) R))⟧
  let u : Trace I := ⟦[a]⟧
  have hm := φ.map_mul t u
  have ht : φ t = updateProduct d φ w (d.loc a) (d.loc_nonempty a) R ps ∅ :=
    updateProduct_joint_residue d φ hcompat _ _ R ps hps
  exact hm.trans (congrArg (fun x => x * φ u) ht)

omit [DecidableEq α] in
/-- Selecting any newly participating index removes the whole updated view. -/
theorem primaryEffect_append_one (hcompat : d.Compatible I) (p : Fin n)
    (hp : p ∈ d.loc a) (R : Finset (Fin n)) (hR : ¬ Disjoint R (d.loc a)) :
    primaryEffect d φ (w ++ [a]) p R = 1 := by
  obtain ⟨r, hrR, hra⟩ := Finset.not_disjoint_iff.mp hR
  have hlast : lastEvent w a ∈ primaryCut d I (w ++ [a]) p R :=
    (mem_primaryCut d p R _).mpr ⟨r, hrR, primary_append_participating_index d p r hp hra⟩
  have hlp : latest d (Finset.univ : Finset (Event (w ++ [a]))) p = some (lastEvent w a) := by
    rw [← primary_self d (I := I) (w := w ++ [a]) p]
    exact primary_append_participating_index d (I := I) p p hp hp
  have hempty : view d I (w ++ [a]) p \ down I (primaryCut d I (w ++ [a]) p R) = ∅ := by
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    rw [view_eq_down_latest d hcompat p hlp]
    intro e he
    obtain ⟨f, hf, hef⟩ := (mem_down {lastEvent w a} e).mp he
    have hfe : f = lastEvent w a := Finset.mem_singleton.mp hf
    subst f
    exact (mem_down _ e).mpr ⟨lastEvent w a, hlast, hef⟩
  unfold primaryEffect residueEffect
  rw [hempty, project_empty]
  exact map_one φ

omit [Monoid M] [DecidableEq α] in
def participantOrder (a : α) : List (Fin n) :=
  (List.finRange n).filter (fun p => p ∈ d.loc a)

omit [Monoid M] [DecidableEq α] in
theorem participantOrder_toFinset (a : α) : (participantOrder d a).toFinset = d.loc a := by
  ext p
  simp [participantOrder]

/-- The semantic update uses only the old participant primary tables and gossip. -/
theorem primaryEffect_append_update (hcompat : d.Compatible I) (p : Fin n)
    (hp : p ∈ d.loc a) (R : Finset (Fin n)) :
    primaryEffect d φ (w ++ [a]) p R =
      if Disjoint R (d.loc a) then
        updateProduct d φ w (d.loc a) (d.loc_nonempty a) R (participantOrder d a) ∅ * φ ⟦[a]⟧
      else 1 := by
  split_ifs with hR
  · exact primaryEffect_append_product d φ hcompat p hp R hR _ (participantOrder_toFinset d a)
  · exact primaryEffect_append_one d φ hcompat p hp R hR

end
end TraceTheory.Zielonka
