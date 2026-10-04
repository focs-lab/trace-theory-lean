import TraceTheory.Zielonka.Gossip
import TraceTheory.Zielonka.GuardedLabels

namespace TraceTheory.Zielonka

open Classical
noncomputable section

variable {α : Type} {n : ℕ} {I : Independence α} {w : List α} {a : α}

/-- Earlier prefix ideals embed unchanged when a last event is appended. -/
theorem prefixBefore_oldEvent (e : Event w) :
    prefixBefore (oldEvent w a e) = (prefixBefore e).map (oldEvent w a) := by
  ext f
  rcases event_append_cases f with ⟨f, rfl⟩ | rfl
  · simp only [mem_prefixBefore, Finset.mem_map]
    constructor
    · intro h
      exact ⟨f, h, rfl⟩
    · rintro ⟨g, hg, hgf⟩
      have : g = f := (oldEvent w a).injective hgf
      subst g
      exact hg
  · simp only [mem_prefixBefore, Finset.mem_map]
    constructor
    · intro h
      have hv := e.isLt
      change w.length < e.val at h
      omega
    · rintro ⟨f, _, hf⟩
      have hh := congrArg Fin.val hf
      change f.val = w.length at hh
      omega

/-- The creation prefix of the last event consists of all old events. -/
theorem prefixBefore_lastEvent :
    prefixBefore (lastEvent w a) = Finset.univ.map (oldEvent w a) := by
  ext f
  rcases event_append_cases f with ⟨f, rfl⟩ | rfl
  · simp [mem_prefixBefore, Fin.lt_def, f.isLt]
  · simp only [mem_prefixBefore, lt_self_iff_false, Finset.mem_map]
    constructor
    · exact False.elim
    · rintro ⟨f, _, hf⟩
      have hh := congrArg Fin.val hf
      change f.val = w.length at hh
      omega

variable (d : Distribution α n)

/-- Ideal-relative views commute with embedding old occurrences. -/
theorem viewIn_map_oldEvent (J : Finset (Event w)) (p : Fin n) :
    viewIn d I (w ++ [a]) (J.map (oldEvent w a)) p =
      (viewIn d I w J p).map (oldEvent w a) := by
  unfold viewIn
  have hgen : J.map (oldEvent w a) ∩ processEvents d (w ++ [a]) p =
      (J ∩ processEvents d w p).map (oldEvent w a) := by
    ext e
    simp only [Finset.mem_inter, Finset.mem_map, mem_processEvents]
    constructor
    · rintro ⟨⟨f, hf, rfl⟩, hp⟩
      exact ⟨f, ⟨hf, by simpa using hp⟩, rfl⟩
    · rintro ⟨f, ⟨hf, hp⟩, rfl⟩
      exact ⟨⟨f, hf, rfl⟩, by simpa using hp⟩
  rw [hgen, gossip_down_map_oldEvent]

theorem primaryIn_map_oldEvent (J : Finset (Event w)) (p q : Fin n) :
    primaryIn d I (w ++ [a]) (J.map (oldEvent w a)) p q =
      (primaryIn d I w J p q).map (oldEvent w a) := by
  unfold primaryIn
  rw [viewIn_map_oldEvent, latest_map_oldEvent]

theorem secondaryIn_map_oldEvent (J : Finset (Event w)) (p q r : Fin n) :
    secondaryIn d I (w ++ [a]) (J.map (oldEvent w a)) p q r =
      (secondaryIn d I w J p q r).map (oldEvent w a) := by
  unfold secondaryIn
  rw [primaryIn_map_oldEvent]
  cases he : primaryIn d I w J p q with
  | none => simp [down, latest]
  | some e =>
    simp only [Option.map_some, Option.toFinset_some]
    rw [← Finset.map_singleton, gossip_down_map_oldEvent, latest_map_oldEvent]

@[simp] theorem secondaryIn_univ (p q r : Fin n) :
    secondaryIn d I w Finset.univ p q r = secondary d I w p q r := by
  simp [secondaryIn, primaryIn, secondary, primary]

/-- The deterministic recycling allocator satisfies chronological freshness at
all creation prefixes; it does not require freshness on arbitrary ideals. -/
theorem gossipLabelling_chronologicalFresh (hcompat : d.Compatible I) (w : List α) :
    ChronologicalFresh d (I := I) (gossipLabelling d w) := by
  induction w using List.reverseRecOn with
  | nil => intro e; exact Fin.elim0 e
  | append_singleton w a ih =>
    intro e p hp q r f hf
    rcases event_append_cases e with ⟨e, rfl⟩ | rfl
    · rw [prefixBefore_oldEvent, secondaryIn_map_oldEvent] at hf
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp hf
      simp only [gossipLabelling_old]
      apply ih e p (by simpa using hp) q r f' hf'
    · rw [prefixBefore_lastEvent, secondaryIn_map_oldEvent, secondaryIn_univ] at hf
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp hf
      rw [gossipLabelling_old, gossipLabelling_last]
      have hp' : p ∈ d.loc a := by simpa using hp
      have hstate := (gossipInvariant_eval d I hcompat w).secondary_eq p q r
      rw [hf'] at hstate
      simp only [Option.map_some] at hstate
      intro heq
      have hreserved := secondary_id_reserved (d.loc a)
        (fun q => (gossipAutomaton d).eval w q.val) ⟨p, hp'⟩ q r hstate
      rw [heq] at hreserved
      exact freshGossipId_not_reserved (d.loc a)
        (fun q => (gossipAutomaton d).eval w q.val) hreserved

/-- Canonical finite gossip labels retain their full participant component. -/
theorem gossipLabelling_locations (hcompat : d.Compatible I) (w : List α) :
    LabelLocations d (gossipLabelling d w) := by
  intro e f hef
  have he := (gossipInvariant_eval d I hcompat w).label_processes e
  have hf := (gossipInvariant_eval d I hcompat w).label_processes f
  exact he.symm.trans ((congrArg Prod.fst hef).trans hf)

/-- Encoded primary/secondary equality is safe exactly under the residue cut guard. -/
theorem gossipLabelling_guarded_eq (hcompat : d.Compatible I)
    (p q r a s : Fin n) {e g : Event w}
    (he : primary d I w p a = some e) (hg : secondary d I w q r s = some g)
    (hguard : primary d I w p r = none ∨
      ∃ h m, primary d I w p r = some h ∧ primary d I w q r = some m ∧ Before I w h m)
    (heq : gossipLabelling d w e = gossipLabelling d w g) : e = g :=
  guarded_primary_secondary_label_eq d hcompat (gossipLabelling d w)
    (gossipLabelling_chronologicalFresh d hcompat w)
    (gossipLabelling_locations d hcompat w) p q r a s he hg hguard heq

end
end TraceTheory.Zielonka
