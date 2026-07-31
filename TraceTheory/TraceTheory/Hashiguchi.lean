import TraceTheory.Language
import TraceTheory.MyhillNerode

namespace Language

/-- The left quotient of a language `L` by `u` is the set of all strings `v` such that
  `u ++ v` is in `L`. -/
def leftQuotient {α : Type} (L : Language α) (u : List α) : Language α :=
  { v | u ++ v ∈ L }

@[simp]
lemma leftQuotient_nil {α : Type} {L : Language α} : leftQuotient L [] = L := rfl

lemma leftQuotient_append {α : Type} (L : Language α) (u v : List α) :
    leftQuotient L (u ++ v) = leftQuotient (leftQuotient L u) v := by
  simp [leftQuotient, Language]

end Language

namespace TraceTheory

open Classical Language

variable {α σ : Type} [DecidableEq α] [DecidableEq σ] [Fintype α] [Fintype σ]
variable (I : Independence α)

/-- A possible factor of a prefix being read. -/
structure HashiguchiBucket (α σ : Type) where
  /-- The effect of the factor on the states of an automaton. -/
  trans : σ → σ
  /-- The alphabet of this factor. -/
  alph : Finset α

/-- An explicit equivalence to allow inference of finiteness. -/
def HashiguchiBucket.equiv : HashiguchiBucket α σ ≃ (σ → σ) × Finset α where
  toFun b := (b.trans, b.alph)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype α] [Fintype σ] : Fintype (HashiguchiBucket α σ) :=
  Fintype.ofEquiv _ HashiguchiBucket.equiv.symm

/-- A sequence of buckets bounded by length k + 1. -/
abbrev BucketSeq (α σ : Type) (k : ℕ) :=
  { β : List (HashiguchiBucket α σ) // β.length ≤ k + 1 }

namespace BucketSeq

variable {α σ : Type} {k : ℕ}

/-- Embed a bounded bucket sequence into a fixed-domain Pi type of Options.
  Indices out of bounds naturally map to `none`. -/
def toPi (β : BucketSeq α σ k) : Fin (k + 1) → Option (HashiguchiBucket α σ) :=
  fun i => β.val[i.val]?

/-- The embedding into the Pi type is strictly injective. -/
lemma toPi_injective : Function.Injective (toPi (α := α) (σ := σ) (k := k)) := by
  intro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ heq
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k + 1
  · exact congr_fun heq ⟨i, hi⟩
  · push_neg at hi
    have h_out₁ : l₁[i]? = none := List.getElem?_eq_none (by omega)
    have h_out₂ : l₂[i]? = none := List.getElem?_eq_none (by omega)
    rw [h_out₁, h_out₂]

end BucketSeq

/-- Derive the Fintype instance for bounded bucket sequences via injection. -/
noncomputable instance {k : ℕ} : Fintype (BucketSeq α σ k) :=
  Fintype.ofInjective BucketSeq.toPi BucketSeq.toPi_injective

/-- A possible factorization of a prefix being read. -/
def HashiguchiState (α σ : Type) (k : ℕ) := Finset (BucketSeq α σ k)

/-- Returns the possible factorizations of a prefix being read. -/
noncomputable def hashiguchiProfile (I : Independence α) (M : DFA α σ) (k : ℕ) (u : List α) :
    HashiguchiState α σ k :=
  Finset.univ.filter (fun ⟨β, _⟩ => (
    ∃ xs : List (List α),
      TraceEqv I u xs.flatten ∧
      β = xs.map (fun x => { trans := fun q => x.foldl M.step q, alph := x.toFinset })))

instance {k : ℕ} : Membership (BucketSeq α σ k) (HashiguchiState α σ k) :=
  Finset.instMembership

instance {k : ℕ} : HasSubset (HashiguchiState α σ k) := Finset.instHasSubset

instance : HasSubset (Language α) := Set.instHasSubset

noncomputable instance : Fintype (HashiguchiState α σ k) := by
  unfold HashiguchiState
  infer_instance

lemma eval_interleaved_eq {α σ : Type*}
    (M : DFA α σ) (xs xs' ys : List (List α))
    (h1 : xs.length = ys.length) (h2 : xs'.length = ys.length)
    (h_trans : ∀ i (hx : i < xs.length) (hx' : i < xs'.length),
      xs[i].foldl M.step = xs'[i].foldl M.step)
    (q : σ) :
    (List.zipWith (· ++ ·) xs ys).flatten.foldl M.step q =
    (List.zipWith (· ++ ·) xs' ys).flatten.foldl M.step q := by
  induction xs generalizing xs' ys q with
  | nil =>
    cases ys
    · cases xs'
      · rfl
      · simp at h2
    · simp at h1
  | cons x xs ih =>
    cases ys with
    | nil => simp at h1
    | cons y ys =>
      cases xs' with
      | nil => simp at h2
      | cons x' xs' =>
        simp only [List.zipWith_cons_cons, List.flatten_cons, List.append_assoc, List.foldl_append]
        have h_eq_x : x.foldl M.step q = x'.foldl M.step q := by
          have h0 := h_trans 0 (by simp) (by simp)
          exact congrFun h0 q
        rw [h_eq_x]
        apply ih xs' ys (by simpa using h1) (by simpa using h2)
        intro i hi hi'
        exact h_trans (i + 1) (by simpa) (by simpa)

lemma traceEqv_flatten_append_interleaved_list {α : Type*}
    (I : Independence α)
    (xs ys : List (List α)) (hlen : xs.length = ys.length)
    (hindep : ∀ i j (hi : i < ys.length) (hj : j < xs.length), i < j → I.Independent ys[i] xs[j]) :
    TraceEqv I (xs.flatten ++ ys.flatten) (List.zipWith (· ++ ·) xs ys).flatten := by
  induction xs generalizing ys with
  | nil =>
    cases ys
    · exact TraceEqv.refl []
    · simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil, Nat.succ_ne_zero] at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ_inj] at hlen
      simp only [List.flatten, List.zipWith]
      have hindep_y_xs : ∀ a ∈ xs.flatten, ∀ b ∈ y, I.rel a b := by
        intro a ha b hb
        simp only [List.mem_flatten] at ha
        rcases ha with ⟨x', hx'_in, ha_in⟩
        rcases List.mem_iff_getElem.mp hx'_in with ⟨j, hj, hj_eq⟩
        subst hj_eq
        have hindep_0 := hindep 0 (j + 1) (by simp) (by simpa) (by omega)
        have rel_ba := hindep_0 b hb a ha_in
        exact I.symm b a rel_ba
      have h_comm : TraceEqv I (xs.flatten ++ y) (y ++ xs.flatten) := by
        apply comm_append_of_indep
        exact hindep_y_xs
      have ih_app := ih ys hlen (by
        intro i j hi hj hij
        exact hindep (i + 1) (j + 1) (by simpa) (by simpa) (by omega)
      )
      have h_swap :
          TraceEqv I (x ++ xs.flatten ++ y ++ ys.flatten) (x ++ y ++ xs.flatten ++ ys.flatten) := by
        simpa using append_left_right x ys.flatten h_comm
      have h_ih_compat := TraceEqv.compat (TraceEqv.refl (x ++ y)) ih_app
      simp only [← List.append_assoc] at h_ih_compat
      simp only [List.append_eq, ← List.append_assoc]
      exact TraceEqv.trans h_swap h_ih_compat

lemma leftQuotient_subset_of_profile_subset {X : Language α}
    (I : Independence α) (M : DFA α σ) (k : ℕ)
    (h_acc : M.accepts = X) (h_rank : HasRankAtMost I X k) (u u' : List α)
    (h_sub : hashiguchiProfile I M k u ⊆ hashiguchiProfile I M k u') :
    (traceClosure I X).leftQuotient u ⊆ (traceClosure I X).leftQuotient u' := by
  intro v hv
  rw [leftQuotient, Set.mem_setOf] at hv ⊢

  have ⟨xs, ys, h_len_le, h_valid⟩ := h_rank u v hv
  rcases h_valid with ⟨h_len_eq, h_in_X, h_u_eqv, h_v_eqv, h_indep⟩

  let β_list : List (HashiguchiBucket α σ) :=
    xs.map (fun x => { trans := fun q => x.foldl M.step q, alph := x.toFinset })
  have hβ_len : β_list.length ≤ k + 1 := by simpa [β_list] using h_len_le
  let β : BucketSeq α σ k := ⟨β_list, hβ_len⟩

  have hβ_in_u : β ∈ hashiguchiProfile I M k u := by
    rw [hashiguchiProfile, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, xs, h_u_eqv, rfl⟩
  have hβ_in_u' : β ∈ hashiguchiProfile I M k u' := h_sub hβ_in_u
  rw [hashiguchiProfile, Finset.mem_filter] at hβ_in_u'
  rcases hβ_in_u'.right with ⟨xs', h_xs'_eqv, h_map_eq⟩

  have h_map_eq_list : xs.map (fun x => { trans := fun q => x.foldl M.step q, alph := x.toFinset : HashiguchiBucket α σ }) =
      xs'.map (fun x => { trans := fun q => x.foldl M.step q, alph := x.toFinset }) := by
    exact h_map_eq

  have h_len_xs' : xs'.length = ys.length := by
    have h1 : xs.length = β_list.length := by simp only [β_list, List.length_map]
    have h2 : β_list.length = xs'.length := by simp_all
    omega

  have h_bucket_eq : ∀ i (hx : i < xs.length) (hx' : i < xs'.length),
      { trans := fun q => xs[i].foldl M.step q, alph := xs[i].toFinset : HashiguchiBucket α σ } =
      { trans := fun q => xs'[i].foldl M.step q, alph := xs'[i].toFinset } := by
    intro i hx hx'
    have h_get := congr_arg (fun l : List (HashiguchiBucket α σ) => l[i]?) h_map_eq_list
    simpa [List.getElem?_map, hx, hx'] using h_get

  have h_trans_match : ∀ i (hx : i < xs.length) (hx' : i < xs'.length),
      xs[i].foldl M.step = xs'[i].foldl M.step := by
    intro i hx hx'
    exact congr_arg HashiguchiBucket.trans (h_bucket_eq i hx hx')

  have h_indep' : ∀ i j (hi : i < ys.length) (hj : j < xs'.length), i < j → I.Independent ys[i] xs'[j] := by
    intro i j hi hj hij a ha b hb
    have hj_xs : j < xs.length := by omega
    have h_rel := h_indep i j hi hj_xs hij a ha
    have h_alph := by simpa using congr_arg HashiguchiBucket.alph (h_bucket_eq j hj_xs hj)
    have hb_in_xs : b ∈ xs[j] := by rwa [← List.mem_toFinset, h_alph, List.mem_toFinset]
    exact h_rel b hb_in_xs

  let interleaved' := (List.zipWith (· ++ ·) xs' ys).flatten
  use interleaved'
  constructor
  · rw [← h_acc, DFA.accepts, DFA.acceptsFrom, Set.mem_setOf] at h_in_X ⊢
    have h_eval_eq := eval_interleaved_eq M xs xs' ys h_len_eq h_len_xs' h_trans_match M.start
    unfold interleaved'
    rwa [DFA.evalFrom, ← h_eval_eq]
  · have h_u'_ys := TraceEqv.compat h_xs'_eqv (TraceEqv.refl ys.flatten)
    have h_trace_swap := TraceEqv.trans h_u'_ys (traceEqv_flatten_append_interleaved_list I xs' ys h_len_xs' h_indep')
    exact (TraceEqv.trans (TraceEqv.compat (TraceEqv.refl u') h_v_eqv) h_trace_swap).symm

lemma leftQuotient_eq_of_profile_eq (I : Independence α) (M : DFA α σ) {X : Language α} (k : ℕ)
    (h_acc : M.accepts = X) (h_rank : HasRankAtMost I X k) (u u' : List α)
    (h_eq : hashiguchiProfile I M k u = hashiguchiProfile I M k u') :
    (traceClosure I X).leftQuotient  u = (traceClosure I X).leftQuotient  u' := by
  apply le_antisymm
  · apply leftQuotient_subset_of_profile_subset I M k h_acc h_rank u u'
    exact subset_of_subset_of_eq (fun _ a => a) h_eq
  · apply leftQuotient_subset_of_profile_subset I M k h_acc h_rank u' u
    exact subset_of_subset_of_eq (fun _ a => a) h_eq.symm

/-- The Myhill-Nerode construction of the state space of an automaton recongizing
  the trace closure of `X`. -/
def QuotientState (I : Independence α) (X : Language α) :=
  { L : Language α // ∃ u : List α, L = (traceClosure I X).leftQuotient u }

/-- The finiteness of `QuotientState` via a surjection from `HashiguchiState`. -/
noncomputable def quotientStateFintype (M : DFA α σ) {X : Language α} (k : ℕ)
    (h_acc : M.accepts = X) (h_rank : HasRankAtMost I X k) :
    Fintype (QuotientState I X) :=
  Fintype.ofSurjective
    (fun profile =>
      if h : ∃ u' : List α, hashiguchiProfile I M k u' = profile then
        ⟨(traceClosure I X).leftQuotient (choose h), ⟨choose h, rfl⟩⟩
      else
        ⟨(traceClosure I X).leftQuotient [], ⟨[], rfl⟩⟩)
    (by
      intro ⟨L, h_exists⟩
      rcases h_exists with ⟨u, rfl⟩
      simp only [leftQuotient_nil]
      use hashiguchiProfile I M k u
      have h_exists' : ∃ u', hashiguchiProfile I M k u' = hashiguchiProfile I M k u := ⟨u, rfl⟩
      rw [dif_pos h_exists']
      apply Subtype.ext
      apply leftQuotient_eq_of_profile_eq I M k h_acc h_rank
      exact choose_spec h_exists'
    )

/-- The M-automaton that recognizes the trace closure of `X`. -/
noncomputable def quotientDFMA (I : Independence α) (X : Language α) :
    DFMA (List α) (QuotientState I X) where
  step := fun ⟨L, h_exists⟩ w => ⟨L.leftQuotient w, by
    rcases h_exists with ⟨u, rfl⟩
    use u ++ w
    exact (leftQuotient_append (traceClosure I X) u w).symm
  ⟩
  start := ⟨(traceClosure I X).leftQuotient [], ⟨[], rfl⟩⟩
  accept := { ⟨L, _⟩ | [] ∈ L }
  idempotent := by
    rintro ⟨L, hL⟩
    congr
  composition := by
    rintro ⟨L, hL⟩ u v
    simp_rw [← leftQuotient_append]
    rfl

omit [DecidableEq α] [Fintype α] in
lemma quotientDFMA_accepts (I : Independence α) (X : Language α) :
    (quotientDFMA I X).accepts = traceClosure I X := by
  ext w
  simp only [DFMA.accepts, DFMA.eval, quotientDFMA, leftQuotient, List.nil_append, Set.mem_setOf_eq]
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, List.append_nil]

omit [DecidableEq α] in
theorem recognizable_image_of_regular_finite_rank {I : Independence α} {X : Language α}
    (hX_reg : X.IsRegular)
    (hX_rank : HasFiniteRank I X) :
    IsRecognizable (Trace.mk' I '' X) := by
  rcases Language.isRegular_iff.mp hX_reg with ⟨σ, h_fin, M, hM_acc⟩
  rcases hX_rank with ⟨k, hk_bound⟩
  apply recognizablePreImage_is_recognizable (Trace.mk' I) Quotient.mk_surjective
  rw [preimage_mk_image_eq_traceClosure]
  apply recognizableDFMA_is_recognizable (traceClosure I X)
  use QuotientState I X
  use quotientStateFintype I M k hM_acc hk_bound
  use decEq _
  use quotientDFMA I X
  exact (quotientDFMA_accepts I X).symm

end TraceTheory
