import TraceTheory.Zielonka.Append
import TraceTheory.Zielonka.GossipSemantics

namespace TraceTheory.Zielonka

open Classical
noncomputable section

variable {α : Type} {n : ℕ} {I : Independence α} {w : List α}
variable (d : Distribution α n)

/-- The information collectively available to a set of processes. -/
def jointView (I : Independence α) (w : List α) (P : Finset (Fin n)) :
    Finset (Event w) := P.biUnion (view d I w)

@[simp] theorem mem_jointView (P : Finset (Fin n)) (e : Event w) :
    e ∈ jointView d I w P ↔ ∃ p ∈ P, e ∈ view d I w p := by
  simp [jointView]

theorem view_subset_jointView (P : Finset (Fin n)) {p : Fin n} (hp : p ∈ P) :
    view d I w p ⊆ jointView d I w P := by
  intro e he
  exact (mem_jointView d P e).mpr ⟨p, hp, he⟩

/-- A latest event in the union is already latest in a source containing it. -/
theorem primary_eq_joint_latest (P : Finset (Fin n)) (p r : Fin n)
    (hp : p ∈ P) {e : Event w} (he : latest d (jointView d I w P) r = some e)
    (hep : e ∈ view d I w p) : primary d I w p r = some e := by
  obtain ⟨_, her, hmax⟩ := (latest_eq_some_iff d _ r e).mp he
  exact (latest_eq_some_iff d _ r e).mpr
    ⟨hep, her, fun f hf hfr => hmax f (view_subset_jointView d P hp hf) hfr⟩

/-- Each joint primary entry can be selected from one participant's primary row. -/
theorem exists_primary_source (P : Finset (Fin n)) (hP : P.Nonempty) (r : Fin n) :
    ∃ p ∈ P, primary d I w p r = latest d (jointView d I w P) r := by
  cases he : latest d (jointView d I w P) r with
  | some e =>
    have hem := ((latest_eq_some_iff d _ r e).mp he).1
    obtain ⟨p, hp, hep⟩ := (mem_jointView d P e).mp hem
    exact ⟨p, hp, primary_eq_joint_latest d P p r hp he hep⟩
  | none =>
    obtain ⟨p, hp⟩ := hP
    refine ⟨p, hp, (latest_eq_none_iff d _ r).mpr ?_⟩
    have hempty := (latest_eq_none_iff d _ r).mp he
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨hep, her⟩ := Finset.mem_inter.mp he
    have : e ∈ jointView d I w P ∩ processEvents d w r :=
      Finset.mem_inter.mpr ⟨view_subset_jointView d P hp hep, her⟩
    simp [hempty] at this

/-- A semantic best source for each process index. -/
def bestSource (P : Finset (Fin n)) (hP : P.Nonempty) (r : Fin n) : Fin n :=
  (exists_primary_source d (I := I) (w := w) P hP r).choose

theorem bestSource_mem (P : Finset (Fin n)) (hP : P.Nonempty) (r : Fin n) :
    bestSource d (I := I) (w := w) P hP r ∈ P :=
  (exists_primary_source d (I := I) (w := w) P hP r).choose_spec.1

theorem primary_bestSource (P : Finset (Fin n)) (hP : P.Nonempty) (r : Fin n) :
    primary d I w (bestSource d (I := I) (w := w) P hP r) r =
      latest d (jointView d I w P) r :=
  (exists_primary_source d (I := I) (w := w) P hP r).choose_spec.2

/-- A causal comparison of merged events is visible in a source's primary graph. -/
theorem joint_primary_before_source (P : Finset (Fin n))
    (p r s : Fin n) (hp : p ∈ P) {e f : Event w}
    (he : latest d (jointView d I w P) r = some e)
    (hf : primary d I w p s = some f) (hef : Before I w e f) :
    primary d I w p r = some e := by
  apply primary_eq_joint_latest d P p r hp he
  exact isIdeal_view d p hef ((latest_eq_some_iff d _ s f).mp hf).1

/-- Comparable merged entries occur together in the selected source of the later one. -/
theorem primary_bestSource_of_before (P : Finset (Fin n)) (hP : P.Nonempty)
    (r s : Fin n) {e f : Event w}
    (he : latest d (jointView d I w P) r = some e)
    (hf : latest d (jointView d I w P) s = some f) (hef : Before I w e f) :
    primary d I w (bestSource d (I := I) (w := w) P hP s) r = some e := by
  apply joint_primary_before_source d P
    (bestSource d (I := I) (w := w) P hP s) r s
    (bestSource_mem d P hP s) he
  · rw [primary_bestSource]
    exact hf
  · exact hef

/-- The selected secondary row describes the past of the joint latest event. -/
theorem secondary_bestSource (P : Finset (Fin n)) (hP : P.Nonempty) (q r : Fin n) :
    secondary d I w (bestSource d (I := I) (w := w) P hP q) q r =
      latest d (down I ((latest d (jointView d I w P) q).toFinset)) r := by
  unfold secondary
  rw [primary_bestSource]

/-- An added event invisible to an index does not change its latest information. -/
theorem latest_insert_nonparticipant {a : α} (s : Finset (Event w)) (r : Fin n)
    (hr : r ∉ d.loc a) :
    latest d (s.map (oldEvent w a) ∪ {lastEvent w a}) r =
      (latest d s r).map (oldEvent w a) := by
  rw [← latest_map_oldEvent]
  have hset : (s.map (oldEvent w a) ∪ {lastEvent w a}) ∩
      processEvents d (w ++ [a]) r =
      s.map (oldEvent w a) ∩ processEvents d (w ++ [a]) r := by
    ext e
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton,
      mem_processEvents]
    constructor
    · rintro ⟨he | rfl, hep⟩
      · exact ⟨he, hep⟩
      · exact (hr (by simpa using hep)).elim
    · rintro ⟨he, hep⟩
      exact ⟨.inl he, hep⟩
  unfold latest
  rw [hset]

/-- A participating index has the new occurrence as its primary entry. -/
theorem primary_append_participating_index {a : α} (p r : Fin n)
    (hp : p ∈ d.loc a) (hr : r ∈ d.loc a) :
    primary d I (w ++ [a]) p r = some (lastEvent w a) := by
  apply (latest_eq_some_iff d _ r _).mpr
  refine ⟨mem_view_of_participates d p _ (by simpa using hp), by simpa using hr, ?_⟩
  intro e _ _
  change e.val ≤ w.length
  have := e.isLt
  simp at this
  omega

/-- Other primary indices are merged from the selected old participant rows. -/
theorem primary_append_merged_index {a : α} (hcompat : d.Compatible I)
    (p r : Fin n) (hp : p ∈ d.loc a) (hr : r ∉ d.loc a) :
    primary d I (w ++ [a]) p r =
      (primary d I w
        (bestSource d (I := I) (w := w) (d.loc a) (d.loc_nonempty a) r) r).map
          (oldEvent w a) := by
  rw [primary_bestSource]
  unfold primary
  rw [view_append_participant d hcompat p hp]
  have hunion : (d.loc a).biUnion (fun q => (view d I w q).map (oldEvent w a)) =
      (jointView d I w (d.loc a)).map (oldEvent w a) := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_map, mem_jointView]
    constructor
    · rintro ⟨q, hq, f, hf, rfl⟩
      exact ⟨f, ⟨q, hq, hf⟩, rfl⟩
    · rintro ⟨f, ⟨q, hq, hf⟩, rfl⟩
      exact ⟨q, hq, f, hf, rfl⟩
  rw [hunion]
  exact latest_insert_nonparticipant d _ r hr

end
end TraceTheory.Zielonka
