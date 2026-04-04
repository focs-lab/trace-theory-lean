import TraceTheory.Language
import TraceTheory.MyhillNerode

namespace TraceTheory

section Recognizability

variable {α : Type} {I : Independence α}

lemma isRegular_of_recognizable {L : Language α} (h : IsRecognizable L) :
    L.IsRegular := by
  rcases recognizable_is_recognizableDFMA L h with ⟨σ, h_fin, h_decide, M, hM⟩
  rw [Language.isRegular_iff]
  let M_DFA : DFA α σ := {
    step := fun q a => M.step q [a]
    start := M.start
    accept := M.accept
  }
  use σ, h_fin, M_DFA
  rw [hM]
  ext w
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  unfold DFMA.accepts DFMA.eval
  rw [Set.mem_setOf, Set.mem_setOf]
  have h_eval : ∀ q, List.foldl M_DFA.step q w = M.step q w := by
    induction w with
    | nil =>
      intro q
      simp only [List.foldl_nil]
      exact (M.idempotent q).symm
    | cons a ws ih =>
      intro q
      simp only [List.foldl_cons]
      rw [ih (M.step q [a])]
      exact (M.composition q [a] ws)
  rw [h_eval M_DFA.start]

lemma recognizable_of_isRegular {L : Language α} (h : L.IsRegular) :
    IsRecognizable L := by
  rcases Language.isRegular_iff.mp h with ⟨σ, h_fin, M, hM⟩
  apply recognizableDFMA_is_recognizable L
  use σ, h_fin, Classical.decEq σ
  let M_DFMA : DFMA (List α) σ := {
    step := fun q w => List.foldl M.step q w
    start := M.start
    accept := M.accept
    idempotent := fun _ => rfl
    composition := by
      intro q u v
      symm
      apply List.foldl_append
  }
  use M_DFMA
  rw [← hM]
  ext w
  simp [DFMA.accepts, DFMA.eval, DFA.accepts, DFA.acceptsFrom, DFA.evalFrom, M_DFMA]

lemma recognizable_iff_regular_preimage (T : Set (Trace I)) :
    IsRecognizable T ↔ Language.IsRegular (Trace.mk' I ⁻¹' T) := by
  constructor
  · intro h
    have h_pre_rec := recognizable_has_recognizablePreImage (Trace.mk' I) h
    exact isRegular_of_recognizable h_pre_rec
  · intro h
    have h_pre_rec := recognizable_of_isRegular h
    exact recognizablePreImage_is_recognizable (Trace.mk' I) Quotient.mk_surjective h_pre_rec

lemma preimage_mk_image_eq_traceClosure (X : Language α) :
    Trace.mk' I ⁻¹' (Trace.mk' I '' X) = traceClosure I X := by
  ext w
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨x, hx, heq⟩
    exact ⟨x, hx, Quotient.exact heq⟩
  · rintro ⟨x, hx, heqv⟩
    exact ⟨x, hx, Quotient.sound heqv⟩

end Recognizability

open Classical

variable {α σ : Type} {I : Independence α} [DecidableEq α] [DecidableEq σ] [Fintype α] [Fintype σ]

/-- Represents the state of a single `xs` chunk in the factorization. -/
structure ChunkProfile (α σ : Type) where
  /-- State before processing `alph`. -/
  q_start : σ
  /-- State after processing `alph`. -/
  q_end : σ
  /-- Processed symbols. -/
  alph : Finset α
  deriving DecidableEq

/-- We manually define an equivalence to a tuple so Lean can easily infer the Fintype. -/
def ChunkProfile.equiv : ChunkProfile α σ ≃ (σ × σ × Finset α) where
  toFun c := (c.q_start, c.q_end, c.alph)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype α] [Fintype σ] : Fintype (ChunkProfile α σ) :=
  Fintype.ofEquiv _ ChunkProfile.equiv.symm

/-- A configuration is a list of chunks (length ≤ k + 1).
  Because the Hashiguchi automaton is a DFA, its state is a Set of these configurations
  to track all non-deterministic guesses simultaneously. -/
def HashiguchiState (α σ : Type) (k : ℕ) :=
  Finset (Fin (k + 1) → ChunkProfile α σ)

instance {k : ℕ} : Membership (Fin (k + 1) → (ChunkProfile α σ)) (HashiguchiState α σ k) :=
  Finset.instMembership

/-- To read a character `a`, we guess which chunk `m` it belongs to.
  We can legally append `a` to chunk `m` if it is independent of all chunks `j > m`. -/
noncomputable def stepConfiguration {k : ℕ}
    (I : Independence α) (M : DFA α σ)
    (config : Fin (k + 1) → ChunkProfile α σ) (a : α) :
    Finset (Fin (k + 1) → ChunkProfile α σ) :=
  Finset.univ.filter (fun config' =>
    ∃ m : Fin (k + 1),
      (∀ j, m < j → ∀ c ∈ (config j).alph, I.rel a c) ∧
      config' =
        Function.update config m {
          config m with
          q_end := M.step (config m).q_end a,
          alph := insert a (config m).alph
        })

/-- The step function unions the results of all configurations in the current subset. -/
noncomputable def hashiguchiStep {k : ℕ}
    (I : Independence α) (M : DFA α σ) (q : HashiguchiState α σ k) (a : α) :
    HashiguchiState α σ k :=
  q.biUnion (fun c => stepConfiguration I M c a)

/-- The start configuration assumes all chunks are empty. -/
noncomputable def hashiguchiStart (k : ℕ) : HashiguchiState α σ k:=
  Finset.univ.filter (fun config =>
    ∀ j, (config j).q_start = (config j).q_end ∧ (config j).alph = ∅)

/-- A configuration is accepting if the chunks stitch together perfectly. -/
def IsAcceptingConfig (M : DFA α σ) : List (ChunkProfile α σ) → σ → Prop
  | [], q => q ∈ M.accept
  | c :: cs, q =>
    c.q_start = q ∧
    IsAcceptingConfig M cs c.q_end

/-- A configuration is accepting if we can find a valid run stitching together chunks
  that connects `config[i].q_end` to `config[i+1].q_start`, ending in an accept state of M. -/
def hashiguchiAccept {k : ℕ} (M : DFA α σ) : Set (HashiguchiState α σ k) :=
  { S | ∃ config ∈ S, IsAcceptingConfig M (List.ofFn config) M.start }

/-- The automaton which accepts the trace closure of L(`M`) if it has finite rank `k`. -/
noncomputable def hashiguchiDFA (I : Independence α) (M : DFA α σ) (k : ℕ) :
    DFA α (HashiguchiState α σ k) where
  step := hashiguchiStep I M
  start := hashiguchiStart k
  accept := hashiguchiAccept M

/-- The core invariant maintained by the Hashiguchi DFA execution. -/
def ConfigInvariant {k : ℕ}
    (I : Independence α) (M : DFA α σ) (C : Fin (k + 1) → ChunkProfile α σ) (w : List α) : Prop :=
  ∃ xs : Fin (k + 1) → List α,
    TraceEqv I w (List.flatten (List.ofFn xs)) ∧
    (∀ i, (C i).alph = (xs i).toFinset) ∧
    (∀ i, List.foldl M.step (C i).q_start (xs i) = (C i).q_end)

lemma hashiguchiStart_invariant {k : ℕ} (M : DFA α σ) (C : Fin (k + 1) → ChunkProfile α σ) :
    C ∈ hashiguchiStart k → ConfigInvariant I M C [] := by
  intro hC
  use fun _ => []
  simp only [List.ofFn_succ, List.ofFn_const, List.flatten_cons, List.flatten_replicate_nil,
    List.append_nil, List.toFinset_nil, List.foldl_nil]
  rw [hashiguchiStart, Finset.mem_filter] at hC
  simp only [Finset.mem_univ, true_and] at hC
  and_intros
  · exact TraceEqv.refl _
  · intro i
    exact (hC i).right
  · intro i
    exact (hC i).left

omit [DecidableEq α] [Fintype α] in
lemma traceEqv_flatten_update (n : ℕ) (xs : Fin n → List α) (m : Fin n) (a : α)
    (hindep : ∀ j, m < j → ∀ c ∈ xs j, I.rel a c) :
    TraceEqv I
      ((List.ofFn xs).flatten ++ [a])
      ((List.ofFn (Function.update xs m (xs m ++ [a]))).flatten) := by
  induction n with
  | zero => exact m.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    by_cases hm0 : m.val = 0
    · have hm : m = 0 := Fin.ext hm0
      subst hm
      have h_ne : ∀ i : Fin n, Fin.succ i ≠ 0 := by
        intro i h
        have hv := congrArg Fin.val h
        simp at hv
      rw [Function.update_self]
      have h_upd_succ :
          (fun i => Function.update xs 0 (xs 0 ++ [a]) (Fin.succ i)) =
          fun i => xs (Fin.succ i) := by
        ext i
        rw [Function.update_of_ne (h_ne i)]
      rw [h_upd_succ]
      simp only [List.flatten_cons, List.append_assoc]
      apply TraceEqv.compat (TraceEqv.refl (xs 0))
      have h_indep_tl : I.Independent [a] (List.ofFn (fun i => xs (Fin.succ i))).flatten := by
        intro x hx y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx
        rw [List.mem_flatten] at hy
        rcases hy with ⟨l, hl, hyl⟩
        rw [List.mem_ofFn] at hl
        rcases hl with ⟨i, rfl⟩
        have h_gt : (0 : Fin (n + 1)) < Fin.succ i := by
          have h0 : (0 : Fin (n + 1)).val = 0 := rfl
          have hi : (Fin.succ i).val = i.val + 1 := rfl
          omega
        exact hindep (Fin.succ i) h_gt y hyl
      exact comm_singleton_of_indep h_indep_tl
    · have ⟨m', hm'⟩ : ∃ m' : Fin n, m = Fin.succ m' := by
        use ⟨m.val - 1, by omega⟩
        ext
        simp only [Fin.succ_mk]
        omega
      subst hm'
      have h_ne : (0 : Fin (n + 1)) ≠ Fin.succ m' := by
        intro h
        simpa using congrArg Fin.val h
      rw [Function.update_of_ne h_ne]
      simp only [List.flatten_cons, List.append_assoc]
      apply TraceEqv.compat (TraceEqv.refl (xs 0))
      have h_fun_eq :
          (fun i => Function.update xs (Fin.succ m') (xs (Fin.succ m') ++ [a]) (Fin.succ i)) =
          Function.update (fun i => xs (Fin.succ i)) m' (xs (Fin.succ m') ++ [a]) := by
        ext i
        by_cases hi : i = m'
        · subst hi
          simp
        · have h_ne' : Fin.succ i ≠ Fin.succ m' := by
            intro h
            have hv := congrArg Fin.val h
            simp at hv
            exact hi (Fin.ext hv)
          simp only [Function.update_of_ne hi, Function.update_of_ne h_ne']
      rw [h_fun_eq]
      apply ih (fun i => xs (Fin.succ i)) m'
      intro j hj c hc
      have hj_succ : Fin.succ m' < Fin.succ j := by
        have hm : (Fin.succ m').val = m'.val + 1 := rfl
        have hj_val : (Fin.succ j).val = j.val + 1 := rfl
        omega
      exact hindep (Fin.succ j) hj_succ c hc

lemma stepConfiguration_invariant {k : ℕ} (I : Independence α) (M : DFA α σ)
    (C C' : Fin (k + 1) → ChunkProfile α σ) (w : List α) (a : α) :
    ConfigInvariant I M C w →
    C' ∈ stepConfiguration I M C a →
    ConfigInvariant I M C' (w ++ [a]) := by
  rintro ⟨xs, heqv, halph, hstate⟩ hC'
  simp only [stepConfiguration, Finset.mem_filter, Finset.mem_univ, true_and] at hC'
  rcases hC' with ⟨m, h_indep, hC'_eq⟩
  use Function.update xs m (xs m ++ [a])
  and_intros
  · apply TraceEqv.trans (TraceEqv.compat heqv (TraceEqv.refl [a]))
    have hindep_xs : ∀ j, m < j → ∀ c ∈ xs j, I.rel a c := by
      intro j hj c hc
      have hc_finset : c ∈ (xs j).toFinset := by simpa using hc
      rw [← halph j] at hc_finset
      exact h_indep j hj c hc_finset
    exact traceEqv_flatten_update (k + 1) xs m a hindep_xs
  · intro i
    subst hC'_eq
    by_cases hi : i = m
    · subst hi
      simp [halph i]
    · push_neg at hi
      rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact halph i
  · intro i
    subst hC'_eq
    by_cases hi : i = m
    · subst hi
      simp only [Function.update_self, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hstate i]
    · push_neg at hi
      rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact hstate i

lemma eval_invariant {k : ℕ} (I : Independence α) (M : DFA α σ)
    (w : List α) (C : Fin (k + 1) → ChunkProfile α σ) :
    C ∈ (hashiguchiDFA I M k).eval w → ConfigInvariant I M C w := by
  change C ∈ List.foldl (hashiguchiStep I M) (hashiguchiStart k) w → ConfigInvariant I M C w
  induction w using List.reverseRecOn generalizing C with
  | nil =>
    simp only [List.foldl_nil]
    intro hC
    exact hashiguchiStart_invariant M C hC
  | append_singleton w' a ih =>
    intro hC
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hC
    rw [hashiguchiStep, Finset.mem_biUnion] at hC
    rcases hC with ⟨C', hC'_eval, hC'_step⟩
    have h_inv' := ih C' hC'_eval
    exact stepConfiguration_invariant I M C' C w' a h_inv' hC'_step

omit [DecidableEq α] [DecidableEq σ] [Fintype α] [Fintype σ] in
lemma accepts_stitched_chunks_list (M : DFA α σ)
    (pairs : List (ChunkProfile α σ × List α)) (q : σ) :
    IsAcceptingConfig M (pairs.map Prod.fst) q →
    (∀ p ∈ pairs, List.foldl M.step p.1.q_start p.2 = p.1.q_end) →
    List.foldl M.step q (pairs.map Prod.snd).flatten ∈ M.accept := by
  induction pairs generalizing q with
  | nil =>
    intro h_acc _
    exact h_acc
  | cons p pairs' ih =>
    intro h_acc h_fold
    simp only [List.map_cons, List.flatten_cons, List.foldl_append]
    have h_fold_p := h_fold p List.mem_cons_self
    have h_q : p.1.q_start = q := h_acc.left
    have h_acc' : IsAcceptingConfig M (pairs'.map Prod.fst) p.1.q_end := h_acc.right
    rw [← h_q, h_fold_p]
    apply ih p.1.q_end h_acc'
    intro p' hp'
    exact h_fold p' (List.mem_cons_of_mem p hp')

omit [DecidableEq α] [DecidableEq σ] [Fintype α] [Fintype σ] in
lemma accepts_stitched_chunks {k : ℕ} (M : DFA α σ) (C : Fin (k + 1) → ChunkProfile α σ)
    (xs : Fin (k + 1) → List α) :
    IsAcceptingConfig M (List.ofFn C) M.start →
    (∀ i, List.foldl M.step (C i).q_start (xs i) = (C i).q_end) →
    List.flatten (List.ofFn xs) ∈ M.accepts := by
  intro h_acc h_fold
  let pairs : List (ChunkProfile α σ × List α) := List.ofFn (fun i => (C i, xs i))
  have h_fst : pairs.map Prod.fst = List.ofFn C := by
    simp only [List.ofFn_succ, List.map_cons, List.map_ofFn, List.cons.injEq, List.ofFn_inj,
      true_and, pairs]
    rfl
  have h_snd : pairs.map Prod.snd = List.ofFn xs := by
    simp only [List.ofFn_succ, List.map_cons, List.map_ofFn, List.cons.injEq, List.ofFn_inj,
      true_and, pairs]
    rfl
  have h_fold' : ∀ p ∈ pairs, List.foldl M.step p.1.q_start p.2 = p.1.q_end := by
    intro p hp
    rw [List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩
    exact h_fold i
  have h_acc' : IsAcceptingConfig M (pairs.map Prod.fst) M.start := by
    rw [h_fst]
    exact h_acc
  have h_res := accepts_stitched_chunks_list M pairs M.start h_acc' h_fold'
  change List.foldl M.step M.start (List.flatten (List.ofFn xs)) ∈ M.accept
  rw [← h_snd]
  exact h_res

lemma hashiguchi_soundness (I : Independence α) (M : DFA α σ) {X : Language α} (k : ℕ)
    (h_acc : M.accepts = X) (w : List α) :
    (hashiguchiDFA I M k).eval w ∈ hashiguchiAccept M → w ∈ traceClosure I X := by
  intro h_acc_config
  rcases h_acc_config with ⟨C, hC_eval, hC_acc⟩
  have ⟨xs, h_eqv, _, h_state⟩ := eval_invariant I M w C hC_eval
  use List.flatten (List.ofFn xs)
  constructor
  · rw [← h_acc]
    exact accepts_stitched_chunks M C xs hC_acc h_state
  · exact h_eqv.symm

lemma hashiguchi_completeness (I : Independence α) (M : DFA α σ) {X : Language α} (k : ℕ)
    (h_acc : M.accepts = X) (h_rank : HasRankAtMost I X k) (w : List α) :
    w ∈ traceClosure I X → (hashiguchiDFA I M k).eval w ∈ hashiguchiAccept M := by
  sorry

theorem accepts_traceClosure (M : DFA α σ) {X : Language α} (k : ℕ)
    (h_acc : M.accepts = X)
    (h_rank : HasRankAtMost I X k) :
    (hashiguchiDFA I M k).accepts = traceClosure I X := by
  ext w
  simp only [DFA.accepts]
  constructor
  · exact hashiguchi_soundness I M k h_acc w
  · exact hashiguchi_completeness I M k h_acc h_rank w

theorem recognizable_image_of_regular_finite_rank {X : Language α}
    (hX_reg : X.IsRegular)
    (hX_rank : HasFiniteRank I X) :
    IsRecognizable (Trace.mk' I '' X) := by
  rw [recognizable_iff_regular_preimage, preimage_mk_image_eq_traceClosure]
  rcases Language.isRegular_iff.mp hX_reg with ⟨σ, h_fin, M, hM_acc⟩
  have ⟨k, hk_bound⟩ := hX_rank
  let H := hashiguchiDFA I M k
  have h_H_accepts : H.accepts = traceClosure I X :=
    accepts_traceClosure M k hM_acc hk_bound
  apply Language.isRegular_iff.mpr
  use (HashiguchiState α σ k)
  have h_fin' : Fintype (HashiguchiState α σ k) := by
    unfold HashiguchiState
    infer_instance
  use h_fin', H

end TraceTheory
