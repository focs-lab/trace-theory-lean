import TraceTheory.Language
import TraceTheory.MyhillNerode

namespace Language

def leftQuotient (L : Language α) (u : List α) : Language α :=
  { v | u ++ v ∈ L }

@[simp]
lemma leftQuotient_nil : leftQuotient L [] = L := rfl

lemma leftQuotient_append (L : Language α) (u v : List α) :
    leftQuotient L (u ++ v) = leftQuotient (leftQuotient L u) v := by
  simp [leftQuotient, Language]

end Language

namespace TraceTheory

open Classical Language

variable {α σ : Type} [DecidableEq α] [DecidableEq σ] [Fintype α] [Fintype σ]
variable (I : Independence α)

/-- A possible factor of a prefix being read. -/
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

/-- A possible factorization of a prefix being read. -/
def HashiguchiState (α σ : Type) (k : ℕ) := Finset (Fin (k + 1) → HashiguchiBucket α σ)

instance {k : ℕ} : Membership (Fin (k + 1) → HashiguchiBucket α σ) (HashiguchiState α σ k) :=
  Finset.instMembership

instance {k : ℕ} : HasSubset (HashiguchiState α σ k) := Finset.instHasSubset

instance : HasSubset (Language α) := Set.instHasSubset

instance : Fintype (HashiguchiState α σ k) := by
  unfold HashiguchiState
  infer_instance

/-- Returns the possible factorizations of a prefix being read. -/
noncomputable def hashiguchiProfile (I : Independence α) (M : DFA α σ) (k : ℕ) (u : List α) :
    HashiguchiState α σ k :=
  Finset.univ.filter (fun β => (
    ∃ xs : Fin (k + 1) → List α,
      TraceEqv I u (List.ofFn xs).flatten ∧
      (∀ i, (β i).trans = fun q => (xs i).foldl M.step q) ∧
      (∀ i, (β i).alph = (xs i).toFinset)))

lemma zipWith_append_append_of_length_eq {α β γ : Type*} (f : α → β → γ)
    (xs1 : List α) (ys1 : List β) (xs2 : List α) (ys2 : List β)
    (h : xs1.length = ys1.length) :
    List.zipWith f (xs1 ++ xs2) (ys1 ++ ys2) =
    List.zipWith f xs1 ys1 ++ List.zipWith f xs2 ys2 := by
  induction xs1 generalizing ys1 with
  | nil =>
    cases ys1
    · rfl
    · contradiction
  | cons x xs ih =>
    cases ys1 with
    | nil => contradiction
    | cons y ys =>
      simp only [List.length_cons, Nat.succ_inj] at h
      simp [ih ys h]

lemma ofFn_getElem_pad {α : Type*} {k : ℕ} (L : List α) (h : L.length = k + 1) :
    List.ofFn (fun (i : Fin (k + 1)) => L[ (i : ℕ) ]) = L := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_ofFn]

lemma getElem_pad_right {α : Type*} (L : List (List α)) (pad : ℕ) (i : ℕ)
    (hi : i < (L ++ List.replicate pad []).length) (h_out : L.length ≤ i) :
    (L ++ List.replicate pad [])[i] = [] := by
  have h1 : (L ++ List.replicate pad [])[i] =
            (List.replicate pad [])[i - L.length]'(by simp_all; omega) :=
    List.getElem_append_right h_out
  rw [h1]
  exact List.getElem_replicate _

lemma pad_factorization {α : Type*} {k : ℕ}
    (I : Independence α) (X : Language α) (u v : List α)
    (xs_list ys_list : List (List α)) (h_len : xs_list.length ≤ k + 1)
    (h_valid : IsValidFactorization I X u v xs_list ys_list) :
    ∃ xs ys : Fin (k + 1) → List α,
      TraceEqv I u (List.ofFn xs).flatten ∧
      TraceEqv I v (List.ofFn ys).flatten ∧
      (List.ofFn (fun i => xs i ++ ys i)).flatten ∈ X ∧
      ∀ i j, i < j → I.Independent (ys i) (xs j) := by
  rcases h_valid with ⟨h_eq_len, h_in_X, h_u_eqv, h_v_eqv, h_indep⟩
  let pad_len := k + 1 - xs_list.length
  let xs_pad := xs_list ++ List.replicate pad_len []
  let ys_pad := ys_list ++ List.replicate pad_len []
  have h_xs_pad_len : xs_pad.length = k + 1 := by
    simp only [List.length_append, List.length_replicate, xs_pad, pad_len]
    omega
  have h_ys_pad_len : ys_pad.length = k + 1 := by
    simp only [List.length_append, List.length_replicate, ys_pad, pad_len]
    omega
  let xs : Fin (k + 1) → List α := fun i => xs_pad[ (i : ℕ) ]
  let ys : Fin (k + 1) → List α := fun i => ys_pad[ (i : ℕ) ]
  use xs, ys
  have h_ofFn_xs : List.ofFn xs = xs_pad := ofFn_getElem_pad xs_pad h_xs_pad_len
  have h_ofFn_ys : List.ofFn ys = ys_pad := ofFn_getElem_pad ys_pad h_ys_pad_len
  have h_ofFn_zip : List.ofFn (fun i => xs i ++ ys i) = List.zipWith (· ++ ·) xs_pad ys_pad := by
    apply List.ext_getElem
    · simp [h_xs_pad_len, h_ys_pad_len]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_zipWith]
      rw [List.append_cancel_left_eq]
  and_intros
  · rw [h_ofFn_xs, List.flatten_append, List.flatten_replicate_nil, List.append_nil]
    exact h_u_eqv
  · rw [h_ofFn_ys, List.flatten_append, List.flatten_replicate_nil, List.append_nil]
    exact h_v_eqv
  · rw [h_ofFn_zip, zipWith_append_append_of_length_eq _ _ _ _ _ h_eq_len]
    simp [h_in_X]
  · intro i j hij
    by_cases hy : i < ys_list.length
    · by_cases hx : j < xs_list.length
      · have hy_val : ys i = ys_list[i] := by exact List.getElem_append_left hy
        have hx_val : xs j = xs_list[j] := by exact List.getElem_append_left hx
        rw [hy_val, hx_val]
        exact h_indep i j hy hx hij
      · have hx_val : xs j = [] := by
          apply getElem_pad_right
          omega
        rw [hx_val]
        intro a ha b hb
        cases hb
    · have hy_val : ys i = [] := by
        apply getElem_pad_right
        omega
      rw [hy_val]
      intro a ha b hb
      cases ha

lemma eval_interleaved_eq_list {α σ : Type*}
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

lemma eval_interleaved_eq {α σ: Type*} {k : ℕ}
    (M : DFA α σ) (xs xs' ys : Fin (k + 1) → List α)
    (h_trans : ∀ i, (xs i).foldl M.step = (xs' i).foldl M.step) (q : σ) :
    (List.ofFn (fun i => xs i ++ ys i)).flatten.foldl M.step q =
    (List.ofFn (fun i => xs' i ++ ys i)).flatten.foldl M.step q := by
  have h_zip : ∀ f g : Fin (k + 1) → List α,
      List.ofFn (fun i => f i ++ g i) = List.zipWith (· ++ ·) (List.ofFn f) (List.ofFn g) := by
    intro f g
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_ofFn, List.getElem_zipWith]
  rw [h_zip xs ys, h_zip xs' ys]
  apply eval_interleaved_eq_list
  · simp
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    exact h_trans ⟨i, by simpa using h1⟩

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

omit [Fintype α] in
lemma traceEqv_interleaved_swap {k : ℕ} (I : Independence α) (u' : List α)
    (xs xs' ys : Fin (k + 1) → List α)
    (hu' : TraceEqv I u' (List.ofFn xs').flatten)
    (h_alph : ∀ i, (xs i).toFinset = (xs' i).toFinset)
    (h_indep : ∀ i j, i < j → I.Independent (ys i) (xs j)) :
    TraceEqv I (u' ++ (List.ofFn ys).flatten)
               (List.ofFn (fun i => xs' i ++ ys i)).flatten := by
  let L_xs' := List.ofFn xs'
  let L_ys := List.ofFn ys
  have hlen : L_xs'.length = L_ys.length := by simp [L_xs', L_ys]
  have hindep_list : ∀ i j (hi : i < L_ys.length) (hj : j < L_xs'.length),
      i < j → I.Independent L_ys[i] L_xs'[j] := by
    intro i j hi hj hij a ha b hb
    have hi_fin : i < k + 1 := by rwa [List.length_ofFn] at hi
    have hj_fin : j < k + 1 := by rwa [List.length_ofFn] at hj
    have h_orig := h_indep ⟨i, hi_fin⟩ ⟨j, hj_fin⟩ hij
    have hy_eq : L_ys[i] = ys ⟨i, hi_fin⟩ := by rw [List.getElem_ofFn]
    have hx'_eq : L_xs'[j] = xs' ⟨j, hj_fin⟩ := by rw [List.getElem_ofFn]
    rw [hy_eq] at ha
    rw [hx'_eq] at hb
    have h_alph_j := h_alph ⟨j, hj_fin⟩
    have hb_in_xs : b ∈ xs ⟨j, hj_fin⟩ := by
      rw [← List.mem_toFinset, h_alph_j, List.mem_toFinset]
      exact hb
    exact h_orig a ha b hb_in_xs
  have h_list_eqv := traceEqv_flatten_append_interleaved_list I L_xs' L_ys hlen hindep_list
  have h_zip_eq : (List.zipWith (· ++ ·) L_xs' L_ys) = List.ofFn (fun i => xs' i ++ ys i) := by
    apply List.ext_getElem
    · simp [L_xs', L_ys]
    · intro i hi1 hi2
      simp only [L_xs', L_ys, List.getElem_ofFn, List.getElem_zipWith]
  rw [h_zip_eq] at h_list_eqv
  have h_step1 : TraceEqv I (u' ++ L_ys.flatten) (L_xs'.flatten ++ L_ys.flatten) :=
    TraceEqv.compat hu' (TraceEqv.refl _)
  exact TraceEqv.trans h_step1 h_list_eqv

lemma leftQuotient_subset_of_profile_subset {X : Language α}
    (I : Independence α) (M : DFA α σ) (k : ℕ)
    (h_acc : M.accepts = X) (h_rank : HasRankAtMost I X k) (u u' : List α)
    (h_sub : hashiguchiProfile I M k u ⊆ hashiguchiProfile I M k u') :
    (traceClosure I X).leftQuotient u ⊆ (traceClosure I X).leftQuotient u' := by
  intro v hv
  rw [leftQuotient, Set.mem_setOf] at hv ⊢

  have ⟨xs_list, ys_list, h_len, h_valid⟩ := h_rank u v hv
  have ⟨xs, ys, h_xs_eqv, h_ys_eqv, h_interleaved_in_X, h_indep⟩ :=
    pad_factorization I X u v xs_list ys_list h_len h_valid

  let β : Fin (k + 1) → HashiguchiBucket α σ := fun i =>
    { trans := fun q => (xs i).foldl M.step q, alph := (xs i).toFinset }
  have hβ_in_u : β ∈ hashiguchiProfile I M k u := by
    rw [hashiguchiProfile, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, xs, h_xs_eqv, fun _ => rfl, fun _ => rfl⟩
  have hβ_in_u' : β ∈ hashiguchiProfile I M k u' := h_sub hβ_in_u
  rw [hashiguchiProfile, Finset.mem_filter] at hβ_in_u'
  rcases hβ_in_u'.right with ⟨xs', h_xs'_eqv, h_trans_eq, h_alph_eq⟩

  have h_trans_match (i : Fin (k + 1)) : (xs i).foldl M.step = (xs' i).foldl M.step :=
    List.map_inj.mp (congrArg List.map (h_trans_eq i))
  have h_alph_match (i : Fin (k + 1)) : (xs i).toFinset = (xs' i).toFinset :=
    Finset.val_inj.mp (congrArg Finset.val (h_alph_eq i))
  let interleaved' := (List.ofFn (fun i => xs' i ++ ys i)).flatten
  use interleaved'
  constructor
  · rw [← h_acc, DFA.accepts, DFA.acceptsFrom, Set.mem_setOf] at h_interleaved_in_X ⊢
    have h_eval_eq := eval_interleaved_eq M xs xs' ys h_trans_match M.start
    unfold interleaved'
    rwa [DFA.evalFrom, ← h_eval_eq]
  · have h_trace_swap := traceEqv_interleaved_swap I u' xs xs' ys h_xs'_eqv h_alph_match h_indep
    exact (TraceEqv.trans (TraceEqv.compat (TraceEqv.refl u') h_ys_eqv) h_trace_swap).symm

lemma leftQuotient_eq_of_profile_eq (I : Independence α) (M : DFA α σ) {X : Language α} (k : ℕ)
    (h_acc : M.accepts = X) (h_rank : HasRankAtMost I X k) (u u' : List α)
    (h_eq : hashiguchiProfile I M k u = hashiguchiProfile I M k u') :
    (traceClosure I X).leftQuotient  u = (traceClosure I X).leftQuotient  u' := by
  apply le_antisymm
  · apply leftQuotient_subset_of_profile_subset I M k h_acc h_rank u u'
    exact subset_of_subset_of_eq (fun _ a => a) h_eq
  · apply leftQuotient_subset_of_profile_subset I M k h_acc h_rank u' u
    exact subset_of_subset_of_eq (fun _ a => a) h_eq.symm

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
