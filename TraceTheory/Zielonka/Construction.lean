import TraceTheory.Zielonka.Decoding
import TraceTheory.Zielonka.ResidueUpdate
import TraceTheory.Zielonka.GossipFresh

namespace TraceTheory.Zielonka

open Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α M : Type} {n : ℕ} {I : Independence α} {w : List α}
variable [Monoid M]

/-- Complete a participant tuple by harmless defaults. Every query made by the
transition is restricted to participants, so these defaults are never observed. -/
def extendParticipantResidue (P : Finset (Fin n))
    (x : (p : {p // p ∈ P}) → ResidueState n M) : Fin n → ResidueState n M :=
  fun p => if hp : p ∈ P then x ⟨p, hp⟩ else (GossipState.empty n, fun _ => 1)

@[simp] theorem extendParticipantResidue_mem (P : Finset (Fin n))
    (x : (p : {p // p ∈ P}) → ResidueState n M) (p : Fin n) (hp : p ∈ P) :
    extendParticipantResidue P x p = x ⟨p, hp⟩ := by
  simp [extendParticipantResidue, hp]

/-- Finite residue multiplication, parameterized by the selected joint cut.
The accumulator lists processes whose views have already been consumed. -/
def finiteUpdateProductWith (x : Fin n → ResidueState n M)
    (cuts : Fin n → Finset (Fin n)) : List (Fin n) → Finset (Fin n) → M
  | [], _ => 1
  | p :: ps, B => (x p).2 (cuts p ∪ encodedCommonIndices (fun q => (x q).1) p B) *
      finiteUpdateProductWith x cuts ps (insert p B)

/-- The finite product implements the semantic multiplication whenever its cut
indices decode correctly. -/
theorem finiteUpdateProductWith_correct [DecidableEq α]
    (d : Distribution α n) (φ : Trace I →* M)
    (x : Fin n → ResidueState n M) (τ : Event w → GossipLabel n)
    (hg : GossipInvariant d I w (fun p => (x p).1) τ)
    (ht : ∀ p R, (x p).2 R = primaryEffect d φ w p R)
    (P : Finset (Fin n)) (hP : P.Nonempty) (R : Finset (Fin n))
    (cuts : Fin n → Finset (Fin n))
    (hcuts : ∀ p ∈ P, cuts p = jointCutIndices d I w P hP p R)
    (ps : List (Fin n)) (hps : ∀ p ∈ ps, p ∈ P) (B : Finset (Fin n)) :
    finiteUpdateProductWith x cuts ps B = updateProduct d φ w P hP R ps B := by
  induction ps generalizing B with
  | nil => rfl
  | cons p ps ih =>
    simp only [finiteUpdateProductWith, updateProduct]
    rw [encodedCommonIndices_correct hg, hcuts p (hps p (List.mem_cons_self ..)), ht,
      ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))]

/-- No outsider's local state contributes to a participant residue product. -/
theorem finiteUpdateProductWith_local (x y : Fin n → ResidueState n M)
    (P : Finset (Fin n)) (cuts cuts' : Fin n → Finset (Fin n))
    (hxy : ∀ p ∈ P, x p = y p) (hcuts : ∀ p ∈ P, cuts p = cuts' p)
    (ps : List (Fin n)) (hps : ∀ p ∈ ps, p ∈ P)
    (B : Finset (Fin n)) (hB : B ⊆ P) :
    finiteUpdateProductWith x cuts ps B = finiteUpdateProductWith y cuts' ps B := by
  induction ps generalizing B with
  | nil => rfl
  | cons p ps ih =>
    have hp := hps p (List.mem_cons_self ..)
    simp only [finiteUpdateProductWith]
    rw [encodedCommonIndices_local (fun q => (x q).1) (fun q => (y q).1) P B
      (fun q hq => congrArg Prod.fst (hxy q hq)) p hp hB, hxy p hp, hcuts p hp,
      ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _]
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hB hq

/-- Finite cut decoding followed by the ordered multiplication of old tables. -/
def finiteUpdateProduct (x : Fin n → ResidueState n M)
    (P : Finset (Fin n)) (hP : P.Nonempty) (R : Finset (Fin n)) :
    List (Fin n) → Finset (Fin n) → M :=
  finiteUpdateProductWith x
    (fun p => encodedJointCutIndices (fun q => (x q).1) P hP p R)

def residueAutomaton (d : Distribution α n) (φ : Trace I →* M) (F : Set M) :
    AsyncDFA d (fun _ => ResidueState n M) where
  step := fun a x _ =>
    (gossipUpdate (d.loc a) (d.loc_nonempty a) (fun q => (x q).1),
      fun R => if Disjoint R (d.loc a) then
        finiteUpdateProduct (extendParticipantResidue (d.loc a) x)
          (d.loc a) (d.loc_nonempty a) R (participantOrder d a) ∅ * φ ⟦[a]⟧
      else 1)
  start := fun _ => (GossipState.empty n, fun _ => 1)
  accept := {x | decodeResidues x (List.finRange n) ∅ ∈ F}

theorem finiteUpdateProduct_local (x y : Fin n → ResidueState n M)
    (P : Finset (Fin n)) (hP : P.Nonempty) (R : Finset (Fin n))
    (hxy : ∀ p ∈ P, x p = y p) (ps : List (Fin n))
    (hps : ∀ p ∈ ps, p ∈ P) (B : Finset (Fin n)) (hB : B ⊆ P) :
    finiteUpdateProduct x P hP R ps B = finiteUpdateProduct y P hP R ps B := by
  apply finiteUpdateProductWith_local x y P _ _ hxy _ ps hps B hB
  intro p hp
  exact encodedJointCutIndices_local _ _ P hP
    (fun q hq => congrArg Prod.fst (hxy q hq)) p hp R

theorem finiteUpdateProduct_correct [DecidableEq α]
    (d : Distribution α n) (hcompat : d.Compatible I) (φ : Trace I →* M)
    (x : Fin n → ResidueState n M) (τ : Event w → GossipLabel n)
    (hg : GossipInvariant d I w (fun p => (x p).1) τ)
    (hfresh : ChronologicalFresh d (I := I) τ)
    (ht : ∀ p R, (x p).2 R = primaryEffect d φ w p R)
    (P : Finset (Fin n)) (hP : P.Nonempty) (R : Finset (Fin n))
    (ps : List (Fin n)) (hps : ∀ p ∈ ps, p ∈ P) (B : Finset (Fin n)) :
    finiteUpdateProduct x P hP R ps B = updateProduct d φ w P hP R ps B := by
  apply finiteUpdateProductWith_correct d φ x τ hg ht P hP R _ _ ps hps B
  intro p hp
  exact encodedJointCutIndices_correct d hcompat _ τ hg hfresh P hP p hp R

/-- The first component of the product transition is exactly finite gossip. -/
theorem residueAutomaton_step_gossip (d : Distribution α n) (φ : Trace I →* M) (F : Set M)
    (x : Fin n → ResidueState n M) (a : α) :
    (fun p => ((residueAutomaton d φ F).globalStep x a p).1) =
      (gossipAutomaton d).globalStep (fun p => (x p).1) a := by
  funext p
  by_cases hp : p ∈ d.loc a
  · simp [AsyncDFA.globalStep, hp, residueAutomaton, gossipAutomaton]
  · simp [AsyncDFA.globalStep, hp]

/-- Every product run projects to the canonical gossip run. -/
theorem residueAutomaton_eval_gossip (d : Distribution α n) (φ : Trace I →* M) (F : Set M)
    (w : List α) :
    (fun p => ((residueAutomaton d φ F).eval w p).1) = (gossipAutomaton d).eval w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    change (fun p => ((residueAutomaton d φ F).toDFA.eval (w ++ [a]) p).1) =
      (gossipAutomaton d).toDFA.eval (w ++ [a])
    rw [DFA.eval_append_singleton, DFA.eval_append_singleton]
    change (fun p => ((residueAutomaton d φ F).globalStep
      ((residueAutomaton d φ F).eval w) a p).1) =
      (gossipAutomaton d).globalStep ((gossipAutomaton d).eval w) a
    rw [residueAutomaton_step_gossip, ih]

/-- All participant table entries are updated by the semantic append law. -/
theorem residueAutomaton_step_tables [DecidableEq α]
    (d : Distribution α n) (hcompat : d.Compatible I) (φ : Trace I →* M) (F : Set M)
    (x : Fin n → ResidueState n M) (τ : Event w → GossipLabel n)
    (hg : GossipInvariant d I w (fun p => (x p).1) τ)
    (hfresh : ChronologicalFresh d (I := I) τ)
    (ht : ∀ p R, (x p).2 R = primaryEffect d φ w p R) (a : α) (p : Fin n)
    (R : Finset (Fin n)) :
    ((residueAutomaton d φ F).globalStep x a p).2 R = primaryEffect d φ (w ++ [a]) p R := by
  by_cases hp : p ∈ d.loc a
  · rw [AsyncDFA.globalStep_of_mem _ _ a p hp]
    change (if Disjoint R (d.loc a) then
      finiteUpdateProduct (extendParticipantResidue (d.loc a) (fun q => x q.val))
        (d.loc a) (d.loc_nonempty a) R (participantOrder d a) ∅ * φ ⟦[a]⟧ else 1) = _
    rw [primaryEffect_append_update d φ hcompat p hp R]
    split_ifs with hR
    · congr 1
      rw [finiteUpdateProduct_local _ x (d.loc a) (d.loc_nonempty a) R
        (fun q hq => extendParticipantResidue_mem _ _ q hq) (participantOrder d a)
        (fun q hq => by rw [← participantOrder_toFinset d a]; exact List.mem_toFinset.mpr hq)
        ∅ (Finset.empty_subset _)]
      exact finiteUpdateProduct_correct d hcompat φ x τ hg hfresh ht _ _ R _
        (fun q hq => by rw [← participantOrder_toFinset d a]; exact List.mem_toFinset.mpr hq) ∅
    · rfl
  · rw [AsyncDFA.globalStep_of_not_mem _ _ a p hp,
      primaryEffect_append_nonparticipant d φ p R hp]
    exact ht p R

/-- Every local table in a reached finite state contains the intended primary
residue effects. Freshness is supplied by the canonical gossip labelling theorem. -/
theorem residueAutomaton_eval_tables [DecidableEq α]
    (d : Distribution α n) (hcompat : d.Compatible I) (φ : Trace I →* M) (F : Set M)
    (w : List α) :
    ∀ p R, ((residueAutomaton d φ F).eval w p).2 R = primaryEffect d φ w p R := by
  induction w using List.reverseRecOn with
  | nil =>
    intro p R
    change 1 = primaryEffect d φ [] p R
    unfold primaryEffect residueEffect
    have hv : view d I [] p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e; exact Fin.elim0 e
    simp [hv, project_empty]
  | append_singleton w a ih =>
    intro p R
    change ((residueAutomaton d φ F).toDFA.eval (w ++ [a]) p).2 R = _
    rw [DFA.eval_append_singleton]
    apply residueAutomaton_step_tables d hcompat φ F _ (gossipLabelling d w) _
      (gossipLabelling_chronologicalFresh d hcompat w) ih a p R
    rw [residueAutomaton_eval_gossip]
    exact gossipInvariant_eval d I hcompat w

/-- Global decoding of the finite asynchronous automaton is the recognizing morphism. -/
theorem residueAutomaton_decode [DecidableEq α]
    (d : Distribution α n) (hcompat : d.Compatible I) (φ : Trace I →* M) (F : Set M)
    (w : List α) :
    decodeResidues ((residueAutomaton d φ F).eval w) (List.finRange n) ∅ = φ ⟦w⟧ := by
  apply decodeResidues_finRange d hcompat φ _ (gossipLabelling d w) _
    (residueAutomaton_eval_tables d hcompat φ F w)
  rw [residueAutomaton_eval_gossip]
  exact gossipInvariant_eval d I hcompat w

/-- The finite asynchronous construction recognizes precisely the morphism's
inverse image of the chosen accepting set. -/
theorem residueAutomaton_accepts [DecidableEq α]
    (d : Distribution α n) (hcompat : d.Compatible I) (φ : Trace I →* M) (F : Set M)
    (w : List α) : (residueAutomaton d φ F).accepts w ↔ φ ⟦w⟧ ∈ F := by
  change decodeResidues ((residueAutomaton d φ F).eval w) (List.finRange n) ∅ ∈ F ↔ _
  rw [residueAutomaton_decode d hcompat φ F w]

omit [Monoid M] in
/-- A finite target monoid gives finite local states for the construction. -/
theorem residueState_finite [Finite M] : Finite (ResidueState n M) := by
  let : Fintype M := Fintype.ofFinite M
  let : Fintype (ResidueState n M) := inferInstance
  infer_instance

end
end TraceTheory.Zielonka
