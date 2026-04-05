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

structure HashiguchiBucket (α σ : Type) where
  trans : σ → σ
  alph : Finset α

def HashiguchiBucket.equiv : HashiguchiBucket α σ ≃ (σ → σ) × Finset α where
  toFun b := (b.trans, b.alph)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype α] [Fintype σ] : Fintype (HashiguchiBucket α σ) :=
  Fintype.ofEquiv _ HashiguchiBucket.equiv.symm

def HashiguchiState (α σ : Type) (k : ℕ) := Finset (Fin (k + 1) → HashiguchiBucket α σ)

instance {k : ℕ} : Membership (Fin (k + 1) → HashiguchiBucket α σ) (HashiguchiState α σ k) :=
  Finset.instMembership

noncomputable def hashiguchiStart (k : ℕ) : HashiguchiState α σ k :=
  Finset.univ.filter (fun β => ∀ i, (β i).trans = id ∧ (β i).alph = ∅)

noncomputable def stepBucket {k : ℕ}
    (I : Independence α) (M : DFA α σ) (β : Fin (k + 1) → HashiguchiBucket α σ) (a : α) :
    Finset (Fin (k + 1) → HashiguchiBucket α σ) :=
  Finset.univ.filter (fun β' =>
    ∃ m : Fin (k + 1),
      (∀ j, m < j → ∀ c ∈ (β j).alph, I.rel a c) ∧
      β' =
        Function.update β m {
          trans := fun q => M.step ((β m).trans q) a,
          alph  := insert a (β m).alph
        })

noncomputable def hashiguchiStep {k : ℕ}
    (I : Independence α) (M : DFA α σ) (S : HashiguchiState α σ k) (a : α) :
    HashiguchiState α σ k :=
  S.biUnion (fun β => stepBucket I M β a)

def hashiguchiAccept {k : ℕ} (M : DFA α σ) :
    Set (HashiguchiState α σ k) :=
  { S | ∃ β ∈ S, (List.ofFn β).foldl (fun q bucket => bucket.trans q) M.start ∈ M.accept }

noncomputable def hashiguchiDFA (I : Independence α) (M : DFA α σ) (k : ℕ) :
    DFA α (HashiguchiState α σ k) where
  step := hashiguchiStep I M
  start := hashiguchiStart k
  accept := hashiguchiAccept M

omit [DecidableEq α] [DecidableEq σ] [Fintype α] [Fintype σ] in
lemma foldl_flatten_trans_eq
    (M : DFA α σ) (lxs : List (List α)) (lβ : List (HashiguchiBucket α σ))
    (h_len : lxs.length = lβ.length)
    (h_trans : ∀ i (hi : i < lxs.length), (lβ[i]).trans = fun q => (lxs[i]).foldl M.step q)
    (q₀ : σ) :
    lxs.flatten.foldl M.step q₀ = lβ.foldl (fun q bucket => bucket.trans q) q₀ := by
  induction lxs generalizing lβ q₀ with
  | nil =>
    cases lβ
    · rfl
    · contradiction
  | cons x xs ih =>
    cases lβ with
    | nil => simp at h_len
    | cons b β_tail =>
      simp only [List.length_cons, Nat.succ_inj] at h_len
      simp only [List.flatten_cons, List.foldl_append, List.foldl_cons]
      have hb : b.trans = fun q => x.foldl M.step q := h_trans 0 (by simp)
      rw [hb]
      apply ih β_tail
      · intro i hi
        simpa [List.getElem_cons_succ] using h_trans (i + 1) (by simpa)
      · exact h_len

omit [DecidableEq α] [DecidableEq σ] [Fintype α] [Fintype σ] in
lemma foldl_join_eq_foldl_bucket {k : ℕ} (M : DFA α σ)
    (xs : Fin (k + 1) → List α) (β : Fin (k + 1) → HashiguchiBucket α σ)
    (h_trans : ∀ i, (β i).trans = fun q => (xs i).foldl M.step q) (q₀ : σ) :
    (List.ofFn xs).flatten.foldl M.step q₀ =
    (List.ofFn β).foldl (fun q bucket => bucket.trans q) q₀ := by
  apply foldl_flatten_trans_eq
  · intro i hi
    simp only [List.getElem_ofFn]
    exact h_trans ⟨i, by simp_all⟩
  · simp

omit [DecidableEq α] [Fintype α] in
lemma traceEqv_join_set_abstract (I : Independence α) (L : List (List α)) (m : ℕ) (a : α)
    (hm : m < L.length)
    (h_indep : ∀ j (hj : j < L.length), m < j → ∀ c ∈ L[j], I.rel a c) :
    TraceEqv I (L.flatten ++ [a]) ((L.set m (L[m] ++ [a])).flatten) := by
  induction L generalizing m with
  | nil => contradiction
  | cons x xs ih =>
    cases m with
    | zero =>
      simp only [List.set, List.flatten_cons, List.getElem_cons_zero, List.length_cons] at *
      have h_comm : TraceEqv I (xs.flatten ++ [a]) ([a] ++ xs.flatten) := by
        apply comm_append_of_indep
        intro a' ha' c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        simp only [List.mem_flatten] at ha'
        rcases ha' with ⟨l, hl_in_xs, ha'_in_l⟩
        rcases List.mem_iff_getElem.mp hl_in_xs with ⟨j, hj_lt, hj_eq⟩
        have h_rel := h_indep (j + 1) (by omega) (by omega) a' (by simp_all)
        subst hc
        exact I.symm c a' h_rel
      have h_compat := TraceEqv.compat (TraceEqv.refl x) h_comm
      simp only [List.append_assoc] at h_compat ⊢
      exact h_compat
    | succ m' =>
      simp only [List.set, List.flatten_cons, List.getElem_cons_succ, List.length_cons] at *
      have hm' : m' < xs.length := by simpa using hm
      have h_indep' : ∀ j (hj : j < xs.length), m' < j → ∀ c ∈ xs[j], I.rel a c := by
        intro j hj1 hj2 c hc
        exact h_indep (j + 1) (by omega) (by omega) c hc
      have h_ih := ih m' hm' h_indep'
      have h_compat := TraceEqv.compat (TraceEqv.refl x) h_ih
      simp only [List.append_assoc] at h_compat ⊢
      exact h_compat

omit [DecidableEq α] [Fintype α] in
lemma traceEqv_join_update {k : ℕ} (I : Independence α)
    (xs' : Fin (k + 1) → List α) (m : Fin (k + 1)) (a : α)
    (h_indep : ∀ j, m < j → ∀ c ∈ xs' j, I.rel a c) :
    TraceEqv I ((List.ofFn xs').flatten ++ [a])
               ((List.ofFn (Function.update xs' m (xs' m ++ [a]))).flatten) := by
  have h_update : List.ofFn (Function.update xs' m (xs' m ++ [a])) = (List.ofFn xs').set m (xs' m ++ [a]) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_set]
      split_ifs with h_eq
      · subst h_eq
        simp
      · have hne : (⟨i, by simpa using h1⟩ : Fin (k + 1)) ≠ m := by
          intro hc
          apply h_eq
          rw [← hc]
        simp [Function.update_of_ne hne]
  rw [h_update]
  have h_xm : xs' m = (List.ofFn xs')[ (m : ℕ) ] := by rw [List.getElem_ofFn]
  rw [h_xm]
  apply traceEqv_join_set_abstract
  intro j hj1 hj2 c hc
  rw [List.getElem_ofFn] at hc
  simp only [List.ofFn_succ, List.length_cons, List.length_ofFn] at hj1
  exact h_indep ⟨j, hj1⟩ hj2 c hc

lemma hashiguchi_soundness_invariant (I : Independence α) (M : DFA α σ) (k : ℕ) (w : List α)
    (β : Fin (k + 1) → HashiguchiBucket α σ)
    (hβ : β ∈ w.foldl (hashiguchiStep I M) (hashiguchiStart k)) :
    ∃ (xs : Fin (k + 1) → List α),
      TraceEqv I w (List.ofFn xs).flatten ∧
      (∀ i, (β i).trans = fun q => (xs i).foldl M.step q) ∧
      (∀ i, (β i).alph = (xs i).toFinset) := by
  induction w using List.reverseRecOn generalizing β with
  | nil =>
    simp only [List.foldl_nil] at hβ
    rw [hashiguchiStart, Finset.mem_filter] at hβ
    rcases hβ with ⟨_, hβ_prop⟩
    use fun _ => []
    and_intros
    · simp [TraceEqv.refl]
    · intro i
      simpa using (hβ_prop i).left
    · intro i
      simpa using (hβ_prop i).right
  | append_singleton w' a ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hβ
    rw [hashiguchiStep, Finset.mem_biUnion] at hβ
    rcases hβ with ⟨β', hβ'_in, hβ_step⟩
    rcases ih β' hβ'_in with ⟨xs', hw', htrans', halph'⟩
    rw [stepBucket, Finset.mem_filter] at hβ_step
    rcases hβ_step with ⟨-, m, h_indep_cond, rfl⟩
    use Function.update xs' m (xs' m ++ [a])
    and_intros
    · have h_indep : ∀ (j : Fin (k + 1)), m < j → ∀ c ∈ xs' j, I.rel a c := by
        intro j hj c hc
        have hc_in : c ∈ (β' j).alph := by
          rw [halph' j]
          exact List.mem_toFinset.mpr hc
        exact h_indep_cond j hj c hc_in
      have heqv := traceEqv_join_update I xs' m a h_indep
      exact TraceEqv.trans (TraceEqv.compat hw' (TraceEqv.refl [a])) heqv
    · intro i
      by_cases h : i = m
      · subst h
        simp [Function.update_self, htrans']
      · simp [Function.update_of_ne h, htrans' i]
    · intro i
      by_cases h : i = m
      · subst h
        simp [Function.update_self, halph']
      · simp [Function.update_of_ne h, halph' i]

lemma hashiguchi_soundness (I : Independence α) (M : DFA α σ) {X : Language α} (k : ℕ)
    (h_acc : M.accepts = X) (w : List α) :
    (hashiguchiDFA I M k).eval w ∈ hashiguchiAccept M → w ∈ traceClosure I X := by
  intro h_eval
  rw [hashiguchiAccept, Set.mem_setOf] at h_eval
  rcases h_eval with ⟨β, hβ_in, hβ_acc⟩
  have ⟨xs, h_equiv, h_trans, _⟩ := hashiguchi_soundness_invariant I M k w β hβ_in
  let u := (List.ofFn xs).flatten
  have hu_eqv : TraceEqv I u w := TraceEqv.symm h_equiv
  have hu_acc : M.eval u ∈ M.accept := by
    have h_fold := foldl_join_eq_foldl_bucket M xs β h_trans M.start
    rwa [← h_fold] at hβ_acc
  have hu_in_X : u ∈ X := by
    rw [← h_acc]
    exact hu_acc
  unfold traceClosure
  rw [Set.mem_setOf]
  exact ⟨u, hu_in_X, hu_eqv⟩

lemma zipWith_append_flatten_eq_of_flatten_empty {α : Type*} (xs ys : List (List α))
    (hlen : xs.length = ys.length) (hys : ys.flatten = []) :
    (List.zipWith (· ++ ·) xs ys).flatten = xs.flatten := by
  induction xs generalizing ys with
  | nil =>
    cases ys
    · rfl
    · contradiction
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys =>
      simp only [List.length_cons, Nat.succ_inj] at hlen
      simp only [List.flatten_cons, List.append_eq_nil_iff] at hys
      rcases hys with ⟨hy_nil, hys_nil⟩
      simp only [List.zipWith_cons_cons, List.flatten_cons]
      rw [hy_nil, List.append_nil, ih ys hlen hys_nil]

omit [DecidableEq α] [Fintype α] in
lemma rank_provides_factorization (I : Independence α) {X : Language α} (k : ℕ)
    (h_rank : HasRankAtMost I X k) (w : List α) (hw : w ∈ traceClosure I X) :
    ∃ xs : Fin (k + 1) → List α,
      TraceEqv I w (List.ofFn xs).flatten ∧
      (List.ofFn xs).flatten ∈ X := by
  have hw_append : w ++ [] ∈ traceClosure I X := by
    simp only [List.append_nil]
    exact hw
  rcases h_rank w [] hw_append with ⟨xs_list, ys_list, h_len_bound, h_valid⟩
  unfold IsValidFactorization at h_valid
  rcases h_valid with ⟨h_len_eq, h_zip_in_X, h_w_eqv, h_nil_eqv, -⟩
  have h_ys_empty : ys_list.flatten = [] := by
    have h_len_zero := length_eq_of_eqv h_nil_eqv
    simp only [List.length_nil] at h_len_zero
    exact List.length_eq_zero_iff.mp h_len_zero.symm
  have h_zip_eq : (List.zipWith (· ++ ·) xs_list ys_list).flatten = xs_list.flatten :=
    zipWith_append_flatten_eq_of_flatten_empty xs_list ys_list h_len_eq h_ys_empty
  rw [h_zip_eq] at h_zip_in_X
  let pad_len := k + 1 - xs_list.length
  let xs_padded := xs_list ++ List.replicate pad_len []
  have h_padded_len : xs_padded.length = k + 1 := by
    simp only [xs_padded, pad_len, List.length_append, List.length_replicate]
    omega
  have h_padded_flatten : xs_padded.flatten = xs_list.flatten := by
    rw [List.flatten_append, List.flatten_replicate_nil, List.append_nil]
  let f : Fin (k + 1) → List α := fun i => xs_padded[ (i : ℕ) ]'(by omega)
  use f
  have h_ofFn : List.ofFn f = xs_padded := by
    apply List.ext_getElem
    · simp [h_padded_len]
    · intro i _ _
      rw [List.getElem_ofFn]
  rw [h_ofFn, h_padded_flatten]
  exact ⟨h_w_eqv, h_zip_in_X⟩

-- Helper 1: An empty trace equivalence implies all chunks are empty
lemma traceEqv_nil_implies {k : ℕ} (I : Independence α) (xs : Fin (k + 1) → List α)
    (h_eqv : TraceEqv I [] (List.ofFn xs).flatten) :
    ∀ i, xs i = [] := by
  sorry

-- Helper 2: The structural trace extraction
-- If w' ++ [a] is equivalent to the flattened chunks, `a` must have originated from
-- the end of some chunk `m`, and been commuted past all subsequent chunks (hence independent).
lemma traceEqv_append_singleton_implies (I : Independence α) {k : ℕ} (w' : List α) (a : α)
    (xs : Fin (k + 1) → List α) (h_eqv : TraceEqv I (w' ++ [a]) (List.ofFn xs).flatten) :
    ∃ (xs' : Fin (k + 1) → List α) (m : Fin (k + 1)),
      xs m = xs' m ++ [a] ∧
      (∀ i, i ≠ m → xs i = xs' i) ∧
      TraceEqv I w' (List.ofFn xs').flatten ∧
      (∀ j, m < j → ∀ c ∈ xs' j, I.rel a c) := by
  sorry

lemma hashiguchi_completeness_invariant (I : Independence α) (M : DFA α σ) (k : ℕ) (w : List α)
    (xs : Fin (k + 1) → List α) (h_eqv : TraceEqv I w (List.ofFn xs).flatten) :
    ∃ β ∈ w.foldl (hashiguchiStep I M) (hashiguchiStart k),
      (∀ i, (β i).trans = fun q => (xs i).foldl M.step q) ∧
      (∀ i, (β i).alph = (xs i).toFinset) := by
  induction w using List.reverseRecOn generalizing xs with
  | nil =>
    have h_nil := traceEqv_nil_implies I xs h_eqv
    simp only [List.foldl_nil]
    let β : Fin (k + 1) → HashiguchiBucket α σ := fun _ => { trans := id, alph := ∅ }
    use β
    rw [hashiguchiStart, Finset.mem_filter]
    and_intros
    · exact Finset.mem_univ β
    · intro i
      trivial
    · intro i
      rw [h_nil i]
      trivial
    · intro i
      rw [h_nil i]
      trivial
  | append_singleton w' a ih =>
    have ⟨xs', m, h_xm, h_xi, h_eqv', h_indep⟩ := traceEqv_append_singleton_implies I w' a xs h_eqv
    rcases ih xs' h_eqv' with ⟨β', hβ'_in, htrans', halph'⟩
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hashiguchiStep]
    let β_new := Function.update β' m {
      trans := fun q => M.step ((β' m).trans q) a,
      alph  := insert a (β' m).alph
    }
    sorry

lemma hashiguchi_completeness (I : Independence α) (M : DFA α σ) {X : Language α} (k : ℕ)
    (h_acc : M.accepts = X) (h_rank : HasRankAtMost I X k) (w : List α) :
    w ∈ traceClosure I X → (hashiguchiDFA I M k).eval w ∈ hashiguchiAccept M := by
  intro hw_in
  have ⟨xs, hw_eqv, hxs_in_X⟩ := rank_provides_factorization I k h_rank w hw_in
  have h_eval_w : (hashiguchiDFA I M k).eval w = w.foldl (hashiguchiStep I M) (hashiguchiStart k) :=
    rfl
  have ⟨β, hβ_in, h_trans, _⟩ := hashiguchi_completeness_invariant I M k w xs hw_eqv
  rw [hashiguchiAccept, Set.mem_setOf]
  use β
  and_intros
  · rw [h_eval_w]
    exact hβ_in
  · have h_fold := foldl_join_eq_foldl_bucket M xs β h_trans M.start
    rw [← h_fold]
    have hxs_acc : M.eval ((List.ofFn xs).flatten) ∈ M.accept := by
      rw [← DFA.mem_accepts, h_acc]
      exact hxs_in_X
    exact hxs_acc

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
