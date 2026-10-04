import Mathlib.Data.List.Induction
import Mathlib.Data.Fintype.Sigma

import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

import TraceTheory.Zielonka.Secondary
import TraceTheory.Zielonka.Merge

namespace TraceTheory.Zielonka

open Classical
noncomputable section

/-- The process set distinguishes concurrently chosen tags; the bounded numeric
part is recycled only after all participating secondary arrays have released it. -/
abbrev GossipLabel (n : ℕ) := Finset (Fin n) × Fin (n ^ 3 + 1)

/-- A finite local representation of primary and secondary information. -/
structure GossipState (n : ℕ) where
  primary : Fin n → Option (GossipLabel n)
  order : Fin n → Fin n → Bool
  secondary : Fin n → Fin n → Option (GossipLabel n)
  deriving DecidableEq

instance : Fintype (GossipState n) :=
  Fintype.ofInjective
    (fun x : GossipState n => (x.primary, x.order, x.secondary))
    (by intro a b hab; cases a; cases b; simpa using hab)

namespace GossipState

def empty (n : ℕ) : GossipState n := ⟨fun _ => none, fun _ _ => false, fun _ _ => none⟩

/-- Lemma 1.20 implemented using only two finite local states. -/
def compares {n : ℕ} (x y : GossipState n) (r : Fin n) : Prop :=
  match x.primary r, y.primary r with
  | none, _ => True
  | some _, none => False
  | some _, some _ => ∃ i j l, x.primary i = some l ∧ y.primary j = some l ∧
      x.order r i = true

end GossipState

variable {α : Type} {n : ℕ} {I : Independence α} {w : List α}

/-- `τ` is injective only on currently primary events. Old secondary entries may
share recycled tags. This is the distinction needed for bounded safe reuse. -/
structure GossipInvariant (d : Distribution α n) (I : Independence α) (w : List α)
    (x : Fin n → GossipState n) (τ : Event w → GossipLabel n) : Prop where
  primary_eq : ∀ p r, (x p).primary r = (primary d I w p r).map τ
  secondary_eq : ∀ p q r, (x p).secondary q r = (secondary d I w p q r).map τ
  label_processes : ∀ e, (τ e).1 = d.loc (label w e)
  primary_injective : ∀ e f, (∃ p r, primary d I w p r = some e) →
    (∃ p r, primary d I w p r = some f) → τ e = τ f → e = f
  order_eq : ∀ p r s e f, primary d I w p r = some e →
    primary d I w p s = some f → ((x p).order r s = true ↔ Before I w e f)

/-- Absence is below all information; present events are compared causally. -/
def PrimaryLE (I : Independence α) (w : List α)
    (e f : Option (Event w)) : Prop :=
  match e, f with
  | none, _ => True
  | some _, none => False
  | some e, some f => Before I w e f

/-- Old-event embedding preserves downward closures. -/
theorem gossip_down_map_oldEvent {a : α} (s : Finset (Event w)) :
    down I (s.map (oldEvent w a)) = (down I s).map (oldEvent w a) := by
  ext e
  simp only [mem_down, Finset.mem_map]
  constructor
  · rintro ⟨f, ⟨g, hg, rfl⟩, hef⟩
    rcases event_append_cases e with ⟨e, rfl⟩ | rfl
    · exact ⟨e, ⟨g, hg, (before_oldEvent_iff _ _).mp hef⟩, rfl⟩
    · exact (not_before_last_old g hef).elim
  · rintro ⟨e, ⟨f, hf, hef⟩, rfl⟩
    exact ⟨oldEvent w a f, ⟨f, hf, rfl⟩, before_oldEvent hef⟩

variable {d : Distribution α n} {x : Fin n → GossipState n} {τ : Event w → GossipLabel n}

theorem gossip_comparison_correct (hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (p q r : Fin n) :
    GossipState.compares (x p) (x q) r ↔
      PrimaryLE I w (primary d I w p r) (primary d I w q r) := by
  unfold GossipState.compares
  rw [h.primary_eq, h.primary_eq]
  cases he : primary d I w p r with
  | none => simp [PrimaryLE]
  | some e =>
    cases hf : primary d I w q r with
    | none => simp [PrimaryLE]
    | some f =>
      simp only [Option.map_some, PrimaryLE]
      rw [primary_before_iff d hcompat p q r he hf]
      constructor
      · rintro ⟨i, j, l, hi, hj, hoi⟩
        rw [h.primary_eq] at hi hj
        obtain ⟨g, hg, hgl⟩ := Option.map_eq_some_iff.mp hi
        obtain ⟨g', hg', hg'l⟩ := Option.map_eq_some_iff.mp hj
        have hgg' : g = g' := h.primary_injective g g' ⟨p, i, hg⟩ ⟨q, j, hg'⟩
          (hgl.trans hg'l.symm)
        subst g'
        exact ⟨g, Finset.mem_inter.mpr
          ⟨(mem_primaryEvents d p g).mpr ⟨i, hg⟩,
           (mem_primaryEvents d q g).mpr ⟨j, hg'⟩⟩,
          (h.order_eq p r i e g he hg).mp hoi⟩
      · rintro ⟨g, hg, heg⟩
        obtain ⟨hgp, hgq⟩ := Finset.mem_inter.mp hg
        obtain ⟨i, hi⟩ := (mem_primaryEvents d p g).mp hgp
        obtain ⟨j, hj⟩ := (mem_primaryEvents d q g).mp hgq
        exact ⟨i, j, τ g, by rw [h.primary_eq, hi]; rfl,
          by rw [h.primary_eq, hj]; rfl, (h.order_eq p r i e g he hi).mpr heg⟩

/-- All tags that could matter for recycling, padded by zero for nonparticipants
and absent entries. There are at most `n³` positions, hence one tag remains free. -/
def reservedGossipIds (P : Finset (Fin n))
    (x : (p : {p // p ∈ P}) → GossipState n) : Finset (Fin (n ^ 3 + 1)) :=
  Finset.univ.image (fun t : Fin n × Fin n × Fin n =>
    if hp : t.1 ∈ P then ((x ⟨t.1, hp⟩).secondary t.2.1 t.2.2).map Prod.snd |>.getD 0
    else 0)

theorem reservedGossipIds_card_le (P : Finset (Fin n))
    (x : (p : {p // p ∈ P}) → GossipState n) :
    (reservedGossipIds P x).card ≤ n ^ 3 := by
  unfold reservedGossipIds
  calc
    _ ≤ (Finset.univ : Finset (Fin n × Fin n × Fin n)).card := Finset.card_image_le
    _ = n ^ 3 := by simp [pow_succ, Nat.mul_assoc]

theorem exists_freshGossipId (P : Finset (Fin n))
    (x : (p : {p // p ∈ P}) → GossipState n) :
    ∃ k : Fin (n ^ 3 + 1), k ∉ reservedGossipIds P x := by
  have hc : (reservedGossipIds P x).card <
      (Finset.univ : Finset (Fin (n ^ 3 + 1))).card := by
    simpa using Nat.lt_succ_of_le (reservedGossipIds_card_le P x)
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨k, hk⟩

def freshGossipId (P : Finset (Fin n))
    (x : (p : {p // p ∈ P}) → GossipState n) : Fin (n ^ 3 + 1) :=
  (exists_freshGossipId P x).choose

theorem freshGossipId_not_reserved (P : Finset (Fin n))
    (x : (p : {p // p ∈ P}) → GossipState n) :
    freshGossipId P x ∉ reservedGossipIds P x :=
  (exists_freshGossipId P x).choose_spec

theorem secondary_id_reserved (P : Finset (Fin n))
    (x : (p : {p // p ∈ P}) → GossipState n) (p : {p // p ∈ P})
    (q r : Fin n) {l : GossipLabel n} (hl : (x p).secondary q r = some l) :
    l.2 ∈ reservedGossipIds P x := by
  unfold reservedGossipIds
  apply Finset.mem_image.mpr
  refine ⟨(p.val, q, r), Finset.mem_univ _, ?_⟩
  simp [p.property, hl]

/-- Freshness against participant secondary arrays implies freshness against
*every* process's primary entries with that process set. -/
theorem freshGossipLabel_not_primary (hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (P : Finset (Fin n)) (hP : P.Nonempty)
    (p r : Fin n) {e : Event w} (he : primary d I w p r = some e) :
    τ e ≠ (P, freshGossipId P (fun q => x q.val)) := by
  intro hlabel
  obtain ⟨q, hq⟩ := hP
  have hqe : q ∈ d.loc (label w e) := by
    rw [← h.label_processes e, hlabel]
    exact hq
  obtain ⟨s, hs⟩ := primary_secondary_coverage d hcompat p q r he hqe
  have hsecondary : (x q).secondary s r = some (τ e) := by
    rw [h.secondary_eq, hs]; rfl
  have hr := secondary_id_reserved P (fun q => x q.val) ⟨q, hq⟩ s r hsecondary
  rw [hlabel] at hr
  exact freshGossipId_not_reserved P (fun q => x q.val) hr

/-- Candidates dominate every participant's information at the selected index. -/
def gossipCandidates (P : Finset (Fin n))
    (x : (p : {p // p ∈ P}) → GossipState n) (r : Fin n) : Finset {p // p ∈ P} :=
  Finset.univ.filter (fun p => ∀ q, GossipState.compares (x q) (x p) r)

/-- The least dominating source is deterministic. The fallback makes transitions
 total even on unreachable, malformed gossip states. -/
def gossipSource (P : Finset (Fin n)) (hP : P.Nonempty)
    (x : (p : {p // p ∈ P}) → GossipState n) (r : Fin n) : {p // p ∈ P} :=
  if hc : (gossipCandidates P x r).Nonempty then (gossipCandidates P x r).min' hc
  else ⟨P.min' hP, Finset.min'_mem P hP⟩

theorem gossipSource_dominates (P : Finset (Fin n)) (hP : P.Nonempty)
    (x : (p : {p // p ∈ P}) → GossipState n) (r : Fin n)
    (hc : (gossipCandidates P x r).Nonempty) (q : {p // p ∈ P}) :
    GossipState.compares (x q) (x (gossipSource P hP x r)) r := by
  have hm : gossipSource P hP x r ∈ gossipCandidates P x r := by
    simp only [gossipSource, dif_pos hc]
    exact Finset.min'_mem _ hc
  exact (Finset.mem_filter.mp hm).2 q

/-- The participant-only update of all three gossip arrays. Every participant
receives the same merged state. Its secondary rows describe each selected
primary event's past, not the previous local primary row. -/
def gossipUpdate (P : Finset (Fin n)) (hP : P.Nonempty)
    (x : (p : {p // p ∈ P}) → GossipState n) : GossipState n :=
  let fresh : GossipLabel n := (P, freshGossipId P x)
  let prim : Fin n → Option (GossipLabel n) := fun r =>
    if r ∈ P then some fresh else (x (gossipSource P hP x r)).primary r
  { primary := prim
    order := fun r s => decide (∃ l m, prim r = some l ∧ prim s = some m ∧
      (s ∈ P ∨ (r ∉ P ∧ ∃ p i j,
        (x p).primary i = some l ∧ (x p).primary j = some m ∧ (x p).order i j = true)))
    secondary := fun q r => if q ∈ P then prim r
      else (x (gossipSource P hP x q)).secondary q r }

/-- The underlying finite asynchronous automaton. Acceptance is immaterial:
this automaton supplies gossip to the later residue product construction. -/
def gossipAutomaton (d : Distribution α n) : AsyncDFA d (fun _ => GossipState n) where
  step := fun a x _ => gossipUpdate (d.loc a) (d.loc_nonempty a) x
  start := fun _ => GossipState.empty n
  accept := Set.univ

@[simp] theorem gossipUpdate_primary_participant (P : Finset (Fin n)) (hP : P.Nonempty)
    (x : (p : {p // p ∈ P}) → GossipState n) (r : Fin n) (hr : r ∈ P) :
    (gossipUpdate P hP x).primary r = some (P, freshGossipId P x) := by
  simp [gossipUpdate, hr]

@[simp] theorem gossipUpdate_secondary_participant (P : Finset (Fin n)) (hP : P.Nonempty)
    (x : (p : {p // p ∈ P}) → GossipState n) (q r : Fin n) (hq : q ∈ P) :
    (gossipUpdate P hP x).secondary q r = (gossipUpdate P hP x).primary r := by
  simp [gossipUpdate, hq]

/-- Each participant's old primary information lies below the joint latest
information. This proves the finite source selector has a candidate on valid states. -/
theorem primaryLE_joint_latest (hcompat : d.Compatible I)
    (P : Finset (Fin n)) (p r : Fin n) (hp : p ∈ P) :
    PrimaryLE I w (primary d I w p r) (latest d (jointView d I w P) r) := by
  cases he : primary d I w p r with
  | none => simp [PrimaryLE]
  | some e =>
    obtain ⟨hep, her, _⟩ := (latest_eq_some_iff d _ r e).mp he
    have hejoint := view_subset_jointView d P hp hep
    obtain ⟨f, hf⟩ := exists_latest d (jointView d I w P) r hejoint her
    simp only [hf, PrimaryLE]
    exact before_latest d hcompat _ r hf hejoint her

theorem gossipCandidates_nonempty (hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (P : Finset (Fin n)) (hP : P.Nonempty) (r : Fin n) :
    (gossipCandidates P (fun p => x p.val) r).Nonempty := by
  let p : {p // p ∈ P} := ⟨bestSource d (I := I) (w := w) P hP r,
    bestSource_mem d P hP r⟩
  refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro q
  apply (gossip_comparison_correct hcompat h q.val p.val r).mpr
  change PrimaryLE I w (primary d I w q.val r)
    (primary d I w (bestSource d (I := I) (w := w) P hP r) r)
  rw [primary_bestSource]
  exact primaryLE_joint_latest hcompat P q.val r q.property

/-- Antisymmetry also covers the absence case. -/
theorem primaryLE_antisymm {e f : Option (Event w)}
    (hef : PrimaryLE I w e f) (hfe : PrimaryLE I w f e) : e = f := by
  cases e with
  | none => cases f <;> simp_all [PrimaryLE]
  | some e =>
    cases f with
    | none => simp [PrimaryLE] at hef
    | some f =>
      exact congrArg some (le_antisymm (le_of_before hef) (le_of_before hfe))

/-- The deterministic finite source selects exactly the semantic joint latest event. -/
theorem gossipSource_primary (hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (P : Finset (Fin n)) (hP : P.Nonempty) (r : Fin n) :
    primary d I w (gossipSource P hP (fun p => x p.val) r).val r =
      latest d (jointView d I w P) r := by
  apply primaryLE_antisymm
  · exact primaryLE_joint_latest hcompat P _ r
      (gossipSource P hP (fun p => x p.val) r).property
  · rw [← primary_bestSource d (I := I) (w := w) P hP r]
    apply (gossip_comparison_correct hcompat h _ _ r).mp
    exact gossipSource_dominates P hP (fun p => x p.val) r
      (gossipCandidates_nonempty hcompat h P hP r)
      ⟨bestSource d (I := I) (w := w) P hP r, bestSource_mem d P hP r⟩

/-- Extending the semantic labelling preserves every old event's tag, including
recycled secondary tags; only the newly appended occurrence gets the fresh tag. -/
def appendGossipLabel (τ : Event w → GossipLabel n) (a : α) (l : GossipLabel n) :
    Event (w ++ [a]) → GossipLabel n := fun e =>
  if he : e.val < w.length then τ ⟨e.val, he⟩ else l

@[simp] theorem appendGossipLabel_old (τ : Event w → GossipLabel n)
    (a : α) (l : GossipLabel n) (e : Event w) :
    appendGossipLabel τ a l (oldEvent w a e) = τ e := by
  simp [appendGossipLabel, e.isLt]

@[simp] theorem appendGossipLabel_last (τ : Event w → GossipLabel n)
    (a : α) (l : GossipLabel n) :
    appendGossipLabel τ a l (lastEvent w a) = l := by
  simp [appendGossipLabel]

/-- The primary component of the finite transition implements the semantic
append operation, with the chosen fresh tag for the new occurrence. -/
theorem gossipUpdate_primary_correct (hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (a : α) (p r : Fin n) (hp : p ∈ d.loc a) :
    (gossipUpdate (d.loc a) (d.loc_nonempty a) (fun q => x q.val)).primary r =
      (primary d I (w ++ [a]) p r).map
        (appendGossipLabel τ a (d.loc a,
          freshGossipId (d.loc a) (fun q => x q.val))) := by
  by_cases hr : r ∈ d.loc a
  · rw [primary_append_participating_index d p r hp hr]
    simp [gossipUpdate, hr]
  · rw [primary_append_merged_index d hcompat p r hp hr]
    simp only [Option.map_map]
    have hfun : (appendGossipLabel τ a (d.loc a,
        freshGossipId (d.loc a) (fun q => x q.val))) ∘ oldEvent w a = τ := by
      funext e
      exact appendGossipLabel_old τ a _ e
    rw [hfun]
    simp only [gossipUpdate, hr, ↓reduceIte]
    rw [h.primary_eq, gossipSource_primary hcompat h,
      primary_bestSource]

/-- Secondary rows for participating indices are the newly merged primary row;
other rows are inherited from a source with the same selected primary event. -/
theorem gossipUpdate_secondary_correct (hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (a : α) (p q r : Fin n) (hp : p ∈ d.loc a) :
    (gossipUpdate (d.loc a) (d.loc_nonempty a) (fun q => x q.val)).secondary q r =
      (secondary d I (w ++ [a]) p q r).map
        (appendGossipLabel τ a (d.loc a,
          freshGossipId (d.loc a) (fun q => x q.val))) := by
  by_cases hq : q ∈ d.loc a
  · rw [gossipUpdate_secondary_participant _ _ _ q r hq]
    rw [gossipUpdate_primary_correct hcompat h a p r hp]
    congr 1
    unfold secondary
    rw [primary_append_participating_index d p q hp hq]
    simp only [Option.toFinset_some]
    have hlast : latest d Finset.univ p = some (lastEvent w a) := by
      rw [← primary_self d (I := I)]
      exact primary_append_participating_index d p p hp hp
    rw [← view_eq_down_latest d hcompat p hlast]
    rfl
  · simp only [gossipUpdate, hq, ↓reduceIte]
    rw [h.secondary_eq]
    unfold secondary
    rw [primary_append_merged_index d hcompat p q hp hq]
    have hsource := gossipSource_primary hcompat h (d.loc a) (d.loc_nonempty a) q
    rw [primary_bestSource] 
    rw [hsource]
    cases he : latest d (jointView d I w (d.loc a)) q with
    | none => simp [down, latest]
    | some e =>
      simp only [Option.map_some, Option.toFinset_some]
      rw [← Finset.map_singleton, gossip_down_map_oldEvent, latest_map_oldEvent]
      rw [Option.map_map]
      congr 1
      funext f
      exact (appendGossipLabel_old τ a _ f).symm

/-- Any old occurrence that remains globally primary was already globally
primary before the append; merging cannot revive a forgotten occurrence. -/
theorem primary_append_old_provenance (hcompat : d.Compatible I)
    (a : α) (p r : Fin n) (e : Event w)
    (he : primary d I (w ++ [a]) p r = some (oldEvent w a e)) :
    ∃ q, primary d I w q r = some e := by
  by_cases hp : p ∈ d.loc a
  · by_cases hr : r ∈ d.loc a
    · rw [primary_append_participating_index d p r hp hr] at he
      have hv := congrArg (fun o : Option (Event (w ++ [a])) => o.map Fin.val) he
      simp at hv
      have := e.isLt
      omega
    · rw [primary_append_merged_index d hcompat p r hp hr] at he
      obtain ⟨f, hf, hfe⟩ := Option.map_eq_some_iff.mp he
      exact ⟨_, (oldEvent w a).injective hfe ▸ hf⟩
  · rw [primary_append_nonparticipant d p r hp] at he
    obtain ⟨f, hf, hfe⟩ := Option.map_eq_some_iff.mp he
    exact ⟨p, (oldEvent w a).injective hfe ▸ hf⟩

/-- The old global-primary injection remains valid after assigning the freshly
recycled tag to the new occurrence. Secondary arrays need no injection assumption. -/
theorem appendGossipLabel_primary_injective (hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (a : α) (e f : Event (w ++ [a]))
    (he : ∃ p r, primary d I (w ++ [a]) p r = some e)
    (hf : ∃ p r, primary d I (w ++ [a]) p r = some f)
    (hef : appendGossipLabel τ a (d.loc a,
        freshGossipId (d.loc a) (fun q => x q.val)) e =
      appendGossipLabel τ a (d.loc a,
        freshGossipId (d.loc a) (fun q => x q.val)) f) : e = f := by
  obtain ⟨p, r, hpe⟩ := he
  obtain ⟨q, s, hqf⟩ := hf
  rcases event_append_cases e with ⟨e', rfl⟩ | rfl <;>
    rcases event_append_cases f with ⟨f', rfl⟩ | rfl
  · simp only [appendGossipLabel_old] at hef
    obtain ⟨p', he'⟩ := primary_append_old_provenance hcompat a p r e' hpe
    obtain ⟨q', hf'⟩ := primary_append_old_provenance hcompat a q s f' hqf
    exact congrArg (oldEvent w a) (h.primary_injective e' f' ⟨p', r, he'⟩ ⟨q', s, hf'⟩ hef)
  · simp only [appendGossipLabel_old, appendGossipLabel_last] at hef
    obtain ⟨p', he'⟩ := primary_append_old_provenance hcompat a p r e' hpe
    exact (freshGossipLabel_not_primary hcompat h (d.loc a) (d.loc_nonempty a) p' r he' hef).elim
  · simp only [appendGossipLabel_old, appendGossipLabel_last] at hef
    obtain ⟨q', hf'⟩ := primary_append_old_provenance hcompat a q s f' hqf
    exact (freshGossipLabel_not_primary hcompat h (d.loc a) (d.loc_nonempty a) q' s hf' hef.symm).elim
  · rfl

/-- Causality between the jointly selected old primary events is visible in
one participant's primary graph. Only globally-primary label injection is used. -/
theorem gossip_joint_order_correct (_hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (P : Finset (Fin n)) (hP : P.Nonempty)
    (r s : Fin n) (e f : Event w)
    (he : latest d (jointView d I w P) r = some e)
    (hf : latest d (jointView d I w P) s = some f) :
    (∃ p : {p // p ∈ P}, ∃ i j, (x p.val).primary i = some (τ e) ∧
      (x p.val).primary j = some (τ f) ∧ (x p.val).order i j = true) ↔ Before I w e f := by
  obtain ⟨pe, hpe, hpec⟩ := exists_primary_source d P hP r
  obtain ⟨pf, hpf, hpfc⟩ := exists_primary_source d P hP s
  rw [he] at hpec
  rw [hf] at hpfc
  constructor
  · rintro ⟨p, i, j, hi, hj, hij⟩
    rw [h.primary_eq] at hi hj
    obtain ⟨g, hg, hge⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨g', hg', hgf⟩ := Option.map_eq_some_iff.mp hj
    have hge' : g = e := h.primary_injective g e ⟨p.val, i, hg⟩ ⟨pe, r, hpec⟩ hge
    have hgf' : g' = f := h.primary_injective g' f ⟨p.val, j, hg'⟩ ⟨pf, s, hpfc⟩ hgf
    subst g; subst g'
    exact (h.order_eq p.val i j e f hg hg').mp hij
  · intro hef
    have hper : primary d I w pf r = some e :=
      joint_primary_before_source d P pf r s hpf he hpfc hef
    refine ⟨⟨pf, hpf⟩, r, s, ?_, ?_, (h.order_eq pf r s e f hper hpfc).mpr hef⟩
    · rw [h.primary_eq, hper]; rfl
    · rw [h.primary_eq, hpfc]; rfl

theorem gossipUpdate_order_rule (P : Finset (Fin n)) (hP : P.Nonempty)
    (x : (p : {p // p ∈ P}) → GossipState n) (r s : Fin n) (l m : GossipLabel n)
    (hr : (gossipUpdate P hP x).primary r = some l)
    (hs : (gossipUpdate P hP x).primary s = some m) :
    (gossipUpdate P hP x).order r s = true ↔
      s ∈ P ∨ (r ∉ P ∧ ∃ p i j,
        (x p).primary i = some l ∧ (x p).primary j = some m ∧ (x p).order i j = true) := by
  change decide (∃ l' m', (gossipUpdate P hP x).primary r = some l' ∧
    (gossipUpdate P hP x).primary s = some m' ∧ _) = true ↔ _
  simp [hr, hs]

/-- The finite primary graph has exactly the causal order after a participant
update, including the new occurrence and all selected old occurrences. -/
theorem gossipUpdate_order_correct (hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (a : α) (p r s : Fin n) (hp : p ∈ d.loc a)
    (e f : Event (w ++ [a]))
    (he : primary d I (w ++ [a]) p r = some e)
    (hf : primary d I (w ++ [a]) p s = some f) :
    (gossipUpdate (d.loc a) (d.loc_nonempty a) (fun q => x q.val)).order r s = true ↔
      Before I (w ++ [a]) e f := by
  let T := appendGossipLabel τ a (d.loc a,
      freshGossipId (d.loc a) (fun q => x q.val))
  have her : (gossipUpdate (d.loc a) (d.loc_nonempty a) (fun q => x q.val)).primary r =
      some (T e) := by rw [gossipUpdate_primary_correct hcompat h a p r hp, he]; rfl
  have hfs : (gossipUpdate (d.loc a) (d.loc_nonempty a) (fun q => x q.val)).primary s =
      some (T f) := by rw [gossipUpdate_primary_correct hcompat h a p s hp, hf]; rfl
  rw [gossipUpdate_order_rule _ _ _ r s (T e) (T f) her hfs]
  by_cases hs : s ∈ d.loc a
  · have hfe : f = lastEvent w a := by
      rw [primary_append_participating_index d p s hp hs] at hf
      exact (Option.some.inj hf).symm
    subst f
    simp only [hs, true_or, true_iff]
    have hev := ((latest_eq_some_iff d _ r e).mp he).1
    have hlast : latest d Finset.univ p = some (lastEvent w a) := by
      rw [← primary_self d (I := I)]
      exact primary_append_participating_index d p p hp hp
    rw [view_eq_down_latest d hcompat p hlast] at hev
    simpa [mem_down] using hev
  · rw [primary_append_merged_index d hcompat p s hp hs, primary_bestSource] at hf
    obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp hf
    by_cases hr : r ∈ d.loc a
    · have hee : e = lastEvent w a := by
        rw [primary_append_participating_index d p r hp hr] at he
        exact (Option.some.inj he).symm
      subst e
      simp [hs, hr, not_before_last_old]
    · rw [primary_append_merged_index d hcompat p r hp hr, primary_bestSource] at he
      obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.mp he
      simp only [hs, false_or, hr, not_false_eq_true, true_and]
      simp only [T, appendGossipLabel_old]
      change (∃ q : {q // q ∈ d.loc a}, ∃ i j,
        (x q.val).primary i = some (τ e') ∧ (x q.val).primary j = some (τ f') ∧
        (x q.val).order i j = true) ↔ _
      rw [gossip_joint_order_correct hcompat h (d.loc a) (d.loc_nonempty a) r s e' f' he' hf']
      exact (before_oldEvent_iff e' f').symm

/-- The complete invariant is preserved by the finite asynchronous transition. -/
theorem gossipInvariant_step (hcompat : d.Compatible I)
    (h : GossipInvariant d I w x τ) (a : α) :
    GossipInvariant d I (w ++ [a]) ((gossipAutomaton d).globalStep x a)
      (appendGossipLabel τ a (d.loc a,
        freshGossipId (d.loc a) (fun q => x q.val))) := by
  let T := appendGossipLabel τ a (d.loc a,
      freshGossipId (d.loc a) (fun q => x q.val))
  have hcomp : T ∘ oldEvent w a = τ := by
    funext e; exact appendGossipLabel_old τ a _ e
  refine ⟨?_, ?_, ?_, appendGossipLabel_primary_injective hcompat h a, ?_⟩
  · intro p r
    by_cases hp : p ∈ d.loc a
    · rw [AsyncDFA.globalStep_of_mem _ _ a p hp]
      exact gossipUpdate_primary_correct hcompat h a p r hp
    · rw [AsyncDFA.globalStep_of_not_mem _ _ a p hp,
        primary_append_nonparticipant d p r hp, Option.map_map, hcomp]
      exact h.primary_eq p r
  · intro p q r
    by_cases hp : p ∈ d.loc a
    · rw [AsyncDFA.globalStep_of_mem _ _ a p hp]
      exact gossipUpdate_secondary_correct hcompat h a p q r hp
    · rw [AsyncDFA.globalStep_of_not_mem _ _ a p hp, h.secondary_eq]
      unfold secondary
      rw [primary_append_nonparticipant d p q hp]
      cases he : primary d I w p q with
      | none => simp [down, latest]
      | some e =>
        simp only [Option.map_some, Option.toFinset_some]
        rw [← Finset.map_singleton, gossip_down_map_oldEvent, latest_map_oldEvent,
          Option.map_map, hcomp]
  · intro e
    rcases event_append_cases e with ⟨e', rfl⟩ | rfl
    · simp only [appendGossipLabel_old, label_oldEvent]
      exact h.label_processes e'
    · simp
  · intro p r s e f he hf
    by_cases hp : p ∈ d.loc a
    · rw [AsyncDFA.globalStep_of_mem _ _ a p hp]
      exact gossipUpdate_order_correct hcompat h a p r s hp e f he hf
    · rw [AsyncDFA.globalStep_of_not_mem _ _ a p hp]
      rw [primary_append_nonparticipant d p r hp] at he
      rw [primary_append_nonparticipant d p s hp] at hf
      obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp hf
      rw [before_oldEvent_iff]
      exact h.order_eq p r s e' f' he' hf'

/-- The empty input has no events and all local information is absent. -/
theorem gossipInvariant_empty (d : Distribution α n) (I : Independence α) :
    GossipInvariant d I [] (fun _ => GossipState.empty n) (fun e => Fin.elim0 e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p r
    have he : primary d I [] p r = none := by
      apply (latest_eq_none_iff d _ r).mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e; exact Fin.elim0 e
    simp [GossipState.empty, he]
  · intro p q r
    have he : secondary d I [] p q r = none := by
      apply (latest_eq_none_iff d _ r).mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e; exact Fin.elim0 e
    simp [GossipState.empty, he]
  · intro e; exact Fin.elim0 e
  · intro e; exact Fin.elim0 e
  · intro p r s e; exact Fin.elim0 e

/-- Chronological labelling associated with the deterministic finite run. Old
occurrence labels persist, while the new occurrence gets the participant-fresh tag. -/
def gossipLabelling (d : Distribution α n) (w : List α) : Event w → GossipLabel n :=
  List.reverseRecOn (motive := fun w => Event w → GossipLabel n) w
    (fun e => Fin.elim0 e)
    (fun v a τ => appendGossipLabel τ a
      (d.loc a, freshGossipId (d.loc a) (fun q => (gossipAutomaton d).eval v q.val)))

@[simp] theorem gossipLabelling_append (d : Distribution α n) (w : List α) (a : α) :
    gossipLabelling d (w ++ [a]) = appendGossipLabel (gossipLabelling d w) a
      (d.loc a, freshGossipId (d.loc a) (fun q => (gossipAutomaton d).eval w q.val)) := by
  unfold gossipLabelling
  exact List.reverseRecOn_concat _ _ _ _

@[simp] theorem gossipLabelling_old (d : Distribution α n) (w : List α) (a : α) (e : Event w) :
    gossipLabelling d (w ++ [a]) (oldEvent w a e) = gossipLabelling d w e := by
  rw [gossipLabelling_append, appendGossipLabel_old]

@[simp] theorem gossipLabelling_last (d : Distribution α n) (w : List α) (a : α) :
    gossipLabelling d (w ++ [a]) (lastEvent w a) =
      (d.loc a, freshGossipId (d.loc a) (fun q => (gossipAutomaton d).eval w q.val)) := by
  rw [gossipLabelling_append, appendGossipLabel_last]

/-- The finite gossip automaton correctly maintains primary events, their causal
order, and secondary events for every input word. -/
theorem gossipInvariant_eval (d : Distribution α n) (I : Independence α)
    (hcompat : d.Compatible I) (w : List α) :
    GossipInvariant d I w ((gossipAutomaton d).eval w) (gossipLabelling d w) := by
  induction w using List.reverseRecOn with
  | nil =>
    simpa only [gossipLabelling, List.reverseRecOn, List.reverseRec_nil, AsyncDFA.eval,
      DFA.eval_nil, AsyncDFA.toDFA, gossipAutomaton] using
      gossipInvariant_empty d I
  | append_singleton w a ih =>
    rw [gossipLabelling_append]
    change GossipInvariant d I (w ++ [a])
      ((gossipAutomaton d).toDFA.eval (w ++ [a])) _
    rw [DFA.eval_append_singleton]
    exact gossipInvariant_step hcompat ih a

end
end TraceTheory.Zielonka
