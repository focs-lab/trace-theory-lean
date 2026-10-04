import TraceTheory.Zielonka.Gossip
import TraceTheory.Zielonka.Residues
import TraceTheory.Zielonka.ResidueUpdate
import TraceTheory.Zielonka.GuardedLabels

namespace TraceTheory.Zielonka

open Classical
noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α M : Type} {n : ℕ} {I : Independence α} {w : List α}

/-- Recover process-residue indices by comparing finite primary tags. -/
def encodedCommonIndices (x : Fin n → GossipState n) (p : Fin n)
    (P : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun r => ∃ q ∈ P, ∃ s l,
    (x p).primary r = some l ∧ (x q).primary s = some l)

theorem encodedCommonIndices_correct {d : Distribution α n}
    {x : Fin n → GossipState n} {τ : Event w → GossipLabel n}
    (h : GossipInvariant d I w x τ) (p : Fin n) (P : Finset (Fin n)) :
    encodedCommonIndices x p P = commonIndices d I w p P := by
  ext r
  simp only [encodedCommonIndices, commonIndices, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_primaryEvents]
  constructor
  · rintro ⟨q, hq, s, l, hr, hs⟩
    rw [h.primary_eq] at hr hs
    obtain ⟨e, he, hel⟩ := Option.map_eq_some_iff.mp hr
    obtain ⟨f, hf, hfl⟩ := Option.map_eq_some_iff.mp hs
    have hef := h.primary_injective e f ⟨p, r, he⟩ ⟨q, s, hf⟩ (hel.trans hfl.symm)
    subst f
    exact ⟨q, hq, e, he, s, hf⟩
  · rintro ⟨q, hq, e, he, s, hs⟩
    refine ⟨q, hq, s, τ e, ?_, ?_⟩
    · rw [h.primary_eq, he]; rfl
    · rw [h.primary_eq, hs]; rfl

/-- Match a primary index against a secondary row. The causal guard is needed
for correctness because old secondary entries can contain recycled tags. -/
def encodedPrimaryCutIndices (x : Fin n → GossipState n) (p q r : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun s => ∃ t l,
    (x p).primary s = some l ∧ (x q).secondary r t = some l)

theorem encodedPrimaryCutIndices_correct (d : Distribution α n) (hcompat : d.Compatible I)
    (x : Fin n → GossipState n) (τ : Event w → GossipLabel n)
    (hg : GossipInvariant d I w x τ) (hfresh : ChronologicalFresh d (I := I) τ)
    (p q r : Fin n)
    (hguard : PrimaryLE I w (primary d I w p r) (primary d I w q r)) :
    encodedPrimaryCutIndices x p q r = primaryCutIndices d I w p q r := by
  have hloc : LabelLocations d τ := by
    intro e f h
    rw [← hg.label_processes e, ← hg.label_processes f, h]
  have hguard' : primary d I w p r = none ∨
      ∃ h m, primary d I w p r = some h ∧ primary d I w q r = some m ∧ Before I w h m := by
    cases he : primary d I w p r with
    | none => exact .inl rfl
    | some e =>
      cases hm : primary d I w q r with
      | none => simp [he, hm, PrimaryLE] at hguard
      | some m =>
        exact .inr ⟨e, m, rfl, rfl, by simpa only [PrimaryLE, he, hm] using hguard⟩
  ext s
  simp only [encodedPrimaryCutIndices, primaryCutIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, l, he, hf⟩
    rw [hg.primary_eq] at he
    rw [hg.secondary_eq] at hf
    obtain ⟨e, he, hel⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨f, hf, hfl⟩ := Option.map_eq_some_iff.mp hf
    have hef := guarded_primary_secondary_label_eq d hcompat τ hfresh hloc
      p q r s t he hf hguard' (hel.trans hfl.symm)
    subst f
    exact ⟨t, e, he, hf⟩
  · rintro ⟨t, e, he, hf⟩
    refine ⟨t, τ e, ?_, ?_⟩
    · rw [hg.primary_eq, he]; rfl
    · rw [hg.secondary_eq, hf]; rfl

/-- The finite participant-only generator used in Lemma 1.35. -/
def encodedJointCutIndices (x : Fin n → GossipState n) (P : Finset (Fin n))
    (hP : P.Nonempty) (p : Fin n) (R : Finset (Fin n)) : Finset (Fin n) :=
  R.biUnion (fun r => encodedPrimaryCutIndices x p
    (gossipSource P hP (fun q => x q.val) r).val r)

theorem encodedJointCutIndices_correct (d : Distribution α n) (hcompat : d.Compatible I)
    (x : Fin n → GossipState n) (τ : Event w → GossipLabel n)
    (hg : GossipInvariant d I w x τ) (hfresh : ChronologicalFresh d (I := I) τ)
    (P : Finset (Fin n)) (hP : P.Nonempty) (p : Fin n) (hp : p ∈ P)
    (R : Finset (Fin n)) :
    encodedJointCutIndices x P hP p R = jointCutIndices d I w P hP p R := by
  unfold encodedJointCutIndices jointCutIndices
  congr 1
  funext r
  have hsource := gossipSource_primary hcompat hg P hP r
  have hguard : PrimaryLE I w (primary d I w p r)
      (primary d I w (gossipSource P hP (fun q => x q.val) r).val r) := by
    rw [hsource]
    exact primaryLE_joint_latest hcompat P p r hp
  rw [encodedPrimaryCutIndices_correct d hcompat x τ hg hfresh p _ r hguard]
  have hrow : secondary d I w (gossipSource P hP (fun q => x q.val) r).val r =
      secondary d I w (bestSource d (I := I) (w := w) P hP r) r := by
    funext s
    unfold secondary
    rw [hsource, primary_bestSource]
  simp only [primaryCutIndices, hrow]

theorem encodedCommonIndices_local (x y : Fin n → GossipState n)
    (P B : Finset (Fin n)) (hxy : ∀ q ∈ P, x q = y q) (p : Fin n)
    (hp : p ∈ P) (hB : B ⊆ P) :
    encodedCommonIndices x p B = encodedCommonIndices y p B := by
  ext r
  simp only [encodedCommonIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨q, hq, s, l, hr, hs⟩
  · exact ⟨q, hq, s, l, by simpa [hxy p hp] using hr,
      by simpa [hxy q (hB hq)] using hs⟩
  · exact ⟨q, hq, s, l, by simpa [hxy p hp] using hr,
      by simpa [hxy q (hB hq)] using hs⟩

theorem encodedJointCutIndices_local (x y : Fin n → GossipState n)
    (P : Finset (Fin n)) (hP : P.Nonempty) (hxy : ∀ q ∈ P, x q = y q)
    (p : Fin n) (hp : p ∈ P) (R : Finset (Fin n)) :
    encodedJointCutIndices x P hP p R = encodedJointCutIndices y P hP p R := by
  have hrestrict : (fun q : {q // q ∈ P} => x q.val) = (fun q => y q.val) :=
    funext fun q => hxy q.val q.property
  unfold encodedJointCutIndices
  congr 1
  funext r
  rw [hrestrict]
  unfold encodedPrimaryCutIndices
  rw [hxy p hp, hxy _ (gossipSource P hP (fun q => y q.val) r).property]

/-- A local state contains finite gossip and a finite table of residue effects. -/
abbrev ResidueState (n : ℕ) (M : Type) := GossipState n × (Finset (Fin n) → M)

/-- Compose residues while recording the processes whose views have already been consumed. -/
def decodeResidues [Monoid M] (x : Fin n → ResidueState n M) :
    List (Fin n) → Finset (Fin n) → M
  | [], _ => 1
  | p :: ps, P => (x p).2 (encodedCommonIndices (fun q => (x q).1) p P) *
      decodeResidues x ps (insert p P)

theorem jointView_insert (d : Distribution α n) (p : Fin n) (P : Finset (Fin n)) :
    jointView d I w (insert p P) = jointView d I w P ∪ view d I w p := by
  ext e
  simp [jointView, or_comm]

/-- Decode a valid finite residue table using the PDF's process-residue factorization. -/
theorem decodeResidues_correct [Monoid M] [DecidableEq α]
    (d : Distribution α n) (hcompat : d.Compatible I) (φ : Trace I →* M)
    (x : Fin n → ResidueState n M) (τ : Event w → GossipLabel n)
    (hg : GossipInvariant d I w (fun p => (x p).1) τ)
    (ht : ∀ p R, (x p).2 R = primaryEffect d φ w p R)
    (ps : List (Fin n)) (P : Finset (Fin n)) :
    decodeResidues x ps P = residueProduct d φ w ps (jointView d I w P) := by
  induction ps generalizing P with
  | nil => rfl
  | cons p ps ih =>
    simp only [decodeResidues, residueProduct]
    rw [encodedCommonIndices_correct hg, ht,
      ← process_residue_primary d φ hcompat, ih, jointView_insert]

/-- On reached states satisfying the invariant, global decoding is the recognizing morphism. -/
theorem decodeResidues_finRange [Monoid M] [DecidableEq α]
    (d : Distribution α n) (hcompat : d.Compatible I) (φ : Trace I →* M)
    (x : Fin n → ResidueState n M) (τ : Event w → GossipLabel n)
    (hg : GossipInvariant d I w (fun p => (x p).1) τ)
    (ht : ∀ p R, (x p).2 R = primaryEffect d φ w p R) :
    decodeResidues x (List.finRange n) ∅ = φ ⟦w⟧ := by
  rw [decodeResidues_correct d hcompat φ x τ hg ht]
  simpa [jointView] using residueProduct_finRange d φ (w := w)

end
end TraceTheory.Zielonka
