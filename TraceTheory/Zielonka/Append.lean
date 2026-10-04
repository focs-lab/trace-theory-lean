import TraceTheory.Zielonka.Views

namespace TraceTheory.Zielonka

open Classical
noncomputable section

variable {α : Type} {n : ℕ} {I : Independence α} {w : List α} {a : α}

/-- Existing occurrences retain their positions when an action is appended. -/
def oldEvent (w : List α) (a : α) : Event w ↪ Event (w ++ [a]) where
  toFun e := ⟨e.val, by simp; omega⟩
  inj' := by intro e f h; apply Fin.ext; exact congrArg (fun x : Event (w ++ [a]) => x.val) h

/-- The newly appended occurrence. -/
def lastEvent (w : List α) (a : α) : Event (w ++ [a]) :=
  ⟨w.length, by simp⟩

@[simp] theorem oldEvent_val (e : Event w) : (oldEvent w a e).val = e.val := rfl
@[simp] theorem lastEvent_val : (lastEvent w a).val = w.length := rfl

@[simp] theorem label_oldEvent (e : Event w) :
    label (w ++ [a]) (oldEvent w a e) = label w e := by
  change (w ++ [a])[e.val] = w[e.val]
  exact List.getElem_append_left e.isLt

@[simp] theorem label_lastEvent : label (w ++ [a]) (lastEvent w a) = a := by
  simp [label, lastEvent]

theorem event_append_cases (e : Event (w ++ [a])) :
    (∃ f, e = oldEvent w a f) ∨ e = lastEvent w a := by
  by_cases h : e.val < w.length
  · exact .inl ⟨⟨e.val, h⟩, by apply Fin.ext; rfl⟩
  · right; apply Fin.ext; have := e.isLt; simp at this; simp; omega

@[simp] theorem oldEvent_lt_oldEvent (e f : Event w) :
    oldEvent w a e < oldEvent w a f ↔ e < f := Iff.rfl

@[simp] theorem edge_oldEvent (e f : Event w) :
    Edge I (w ++ [a]) (oldEvent w a e) (oldEvent w a f) ↔ Edge I w e f := by
  simp [Edge]

theorem before_oldEvent {e f : Event w} (h : Before I w e f) :
    Before I (w ++ [a]) (oldEvent w a e) (oldEvent w a f) := by
  induction h with
  | refl => exact .refl
  | tail h hedge ih => exact ih.tail ((edge_oldEvent _ _).mpr hedge)

theorem before_restrict {e : Event w} {f : Event (w ++ [a])}
    (h : Before I (w ++ [a]) (oldEvent w a e) f) (hf : f.val < w.length) :
    Before I w e ⟨f.val, hf⟩ := by
  induction h with
  | refl => exact .refl
  | @tail f g h hedge ih =>
    have hfl : f.val < w.length := lt_trans hedge.1 hf
    exact (ih hfl).tail ⟨hedge.1, by
      simpa only [label, List.getElem_append_left hfl,
        List.getElem_append_left hf] using hedge.2⟩

@[simp] theorem before_oldEvent_iff (e f : Event w) :
    Before I (w ++ [a]) (oldEvent w a e) (oldEvent w a f) ↔ Before I w e f :=
  ⟨fun h => before_restrict h f.isLt, before_oldEvent⟩

theorem not_before_last_old (e : Event w) :
    ¬ Before I (w ++ [a]) (lastEvent w a) (oldEvent w a e) := by
  intro h
  have hle := le_of_before h
  have hlt := e.isLt
  change w.length ≤ e.val at hle
  omega

variable (d : Distribution α n)

/-- Appending an action does not change the causal view of an idle process. -/
theorem view_append_nonparticipant (p : Fin n) (hp : p ∉ d.loc a) :
    view d I (w ++ [a]) p = (view d I w p).map (oldEvent w a) := by
  ext e
  simp only [Finset.mem_map, mem_view]
  constructor
  · rintro ⟨f, hpf, hef⟩
    rcases event_append_cases f with ⟨f, rfl⟩ | rfl
    · rcases event_append_cases e with ⟨e, rfl⟩ | rfl
      · exact ⟨e, ⟨f, by simpa using hpf, (before_oldEvent_iff _ _).mp hef⟩, rfl⟩
      · exact (not_before_last_old f hef).elim
    · exact (hp (by simpa using hpf)).elim
  · rintro ⟨e, ⟨f, hpf, hef⟩, rfl⟩
    exact ⟨oldEvent w a f, by simpa using hpf, before_oldEvent hef⟩

/-- The causal past of the new event is precisely the union of participant views. -/
theorem before_last_iff (hcompat : d.Compatible I) (e : Event w) :
    Before I (w ++ [a]) (oldEvent w a e) (lastEvent w a) ↔
      ∃ p ∈ d.loc a, e ∈ view d I w p := by
  constructor
  · intro h
    rcases h.cases_tail with heq | ⟨f, hef, hfl⟩
    · have hv := congrArg Fin.val heq
      have := e.isLt
      simp only [lastEvent_val, oldEvent_val] at hv
      omega
    · have hf : f.val < w.length := hfl.1
      let f' : Event w := ⟨f.val, hf⟩
      have hlabel : label (w ++ [a]) f = label w f' := by
        exact List.getElem_append_left hf
      have hdep : ¬ Disjoint (d.loc (label w f')) (d.loc a) := by
        intro hd
        exact hfl.2 (by simpa [hlabel] using (hcompat _ _).mpr hd)
      obtain ⟨p, hpf, hpa⟩ := Finset.not_disjoint_iff.mp hdep
      exact ⟨p, hpa, (mem_view d p e).mpr ⟨f', hpf, before_restrict hef hf⟩⟩
  · rintro ⟨p, hpa, he⟩
    obtain ⟨f, hpf, hef⟩ := (mem_view d p e).mp he
    apply (before_oldEvent hef).trans
    apply before_of_lt_of_dependent
    · change f.val < w.length
      exact f.isLt
    · simp only [label_oldEvent, label_lastEvent]
      intro hind
      exact Finset.disjoint_left.mp ((hcompat _ _).mp hind) hpf hpa

/-- Participants merge their old causal views and add the new occurrence. -/
theorem view_append_participant (hcompat : d.Compatible I) (p : Fin n)
    (hp : p ∈ d.loc a) :
    view d I (w ++ [a]) p =
      ((d.loc a).biUnion (fun q => (view d I w q).map (oldEvent w a))) ∪
        {lastEvent w a} := by
  ext e
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_map,
    Finset.mem_singleton]
  constructor
  · intro he
    rcases event_append_cases e with ⟨e, rfl⟩ | rfl
    · left
      obtain ⟨f, hpf, hef⟩ := (mem_view d p (oldEvent w a e)).mp he
      have hlast : Before I (w ++ [a]) f (lastEvent w a) := by
        apply before_of_same_process hcompat p hpf
        · simpa using hp
        · change f.val ≤ w.length
          have := f.isLt
          simp at this
          omega
      obtain ⟨q, hqa, heq⟩ := (before_last_iff d hcompat e).mp (hef.trans hlast)
      exact ⟨q, hqa, e, heq, rfl⟩
    · exact .inr rfl
  · rintro (⟨q, hqa, f, hf, rfl⟩ | rfl)
    · exact (mem_view d p _).mpr ⟨lastEvent w a, by simpa using hp,
        (before_last_iff d hcompat f).mpr ⟨q, hqa, hf⟩⟩
    · exact mem_view_of_participates d p _ (by simpa using hp)

/-- Latest information commutes with the embedding of old occurrences. -/
theorem latest_map_oldEvent (s : Finset (Event w)) (q : Fin n) :
    latest d (s.map (oldEvent w a)) q = (latest d s q).map (oldEvent w a) := by
  cases he : latest d s q with
  | none =>
    simp only [Option.map_none]
    apply (latest_eq_none_iff d _ _).mpr
    have hempty := (latest_eq_none_iff d s q).mp he
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨hfs, hfp⟩ := Finset.mem_inter.mp hf
    obtain ⟨e, hes, rfl⟩ := Finset.mem_map.mp hfs
    have hep : e ∈ processEvents d w q := by
      simpa only [mem_processEvents, label_oldEvent] using hfp
    have : e ∈ s ∩ processEvents d w q := Finset.mem_inter.mpr ⟨hes, hep⟩
    simp [hempty] at this
  | some e =>
    simp only [Option.map_some]
    obtain ⟨hes, hep, hmax⟩ := (latest_eq_some_iff d s q e).mp he
    apply (latest_eq_some_iff d _ _ _).mpr
    refine ⟨Finset.mem_map.mpr ⟨e, hes, rfl⟩, by simpa using hep, ?_⟩
    intro f hfs hfp
    obtain ⟨g, hgs, rfl⟩ := Finset.mem_map.mp hfs
    exact hmax g hgs (by simpa using hfp)

/-- An idle process retains its indexed primary information. -/
theorem primary_append_nonparticipant (p q : Fin n) (hp : p ∉ d.loc a) :
    primary d I (w ++ [a]) p q = (primary d I w p q).map (oldEvent w a) := by
  unfold primary
  rw [view_append_nonparticipant d p hp, latest_map_oldEvent]

end
end TraceTheory.Zielonka
