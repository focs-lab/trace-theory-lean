import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

open Classical Computability

variable {α : Type}

namespace εNFA

section concat

variable {σ₁ σ₂ : Type*}

def concat (εM₁ : εNFA α σ₁) (εM₂ : εNFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step q oa := match q, oa with
    | Sum.inl q₁, some _ =>
      (εM₁.step q₁ oa).image Sum.inl
    | Sum.inl q₁, none =>
      let internal := (εM₁.step q₁ none).image Sum.inl
      if q₁ ∈ εM₁.accept then
        internal ∪ (εM₂.start.image Sum.inr)
      else
        internal
    | Sum.inr q₂, _ =>
      (εM₂.step q₂ oa).image Sum.inr
  start := εM₁.start.image Sum.inl
  accept := εM₂.accept.image Sum.inr

lemma IsPath.concat_lift_inl {εM₁ : εNFA α σ₁} {εM₂ : εNFA α σ₂} {s t : σ₁} {x : List (Option α)}
    (h : εM₁.IsPath s t x) : (concat εM₁ εM₂).IsPath (Sum.inl s) (Sum.inl t) x := by
  induction h with
  | nil _ =>
    exact (εNFA.isPath_nil (concat εM₁ εM₂)).mpr rfl
  | cons t' s' u oa x' h_step h_path ih =>
    apply εNFA.IsPath.cons (Sum.inl t') (Sum.inl s') (Sum.inl u)
    · simp [concat]
      cases oa with
      | some a =>
        simpa
      | none =>
        by_cases h_mem : s' ∈ εM₁.accept <;> simp [h_mem, h_step]
    · exact ih

lemma IsPath.concat_lift_inr {εM₁ : εNFA α σ₁} {εM₂ : εNFA α σ₂} {s t : σ₂} {x : List (Option α)}
    (h : εM₂.IsPath s t x) : (concat εM₁ εM₂).IsPath (Sum.inr s) (Sum.inr t) x := by
  induction h with
  | nil _ =>
    exact (εNFA.isPath_nil (concat εM₁ εM₂)).mpr rfl
  | cons t' s' u _ _ h_step _ ih =>
    apply εNFA.IsPath.cons (Sum.inr t') (Sum.inr s') (Sum.inr u)
    · simp [concat]
      exact h_step
    · exact ih

lemma IsPath.concat_proj_inr {εM₁ : εNFA α σ₁} {εM₂ : εNFA α σ₂}  {s t : σ₂} {x : List (Option α)}
    (h : (concat εM₁ εM₂).IsPath (Sum.inr s) (Sum.inr t) x) : εM₂.IsPath s t x := by
  generalize hs' : Sum.inr s = s' at h
  generalize ht' : Sum.inr t = t' at h
  induction h generalizing s with
  | nil u =>
    simp
    subst hs'
    cases ht'
    rfl
  | cons _ s'' t'' _ _ h_step _ ih =>
    subst hs' ht'
    simp [concat] at h_step
    rcases h_step with ⟨q, hq, rfl⟩
    apply εNFA.IsPath.cons q s t
    · exact hq
    · simp [ih]

lemma IsPath.concat_split_inl_inr
    {εM₁ : εNFA α σ₁} {εM₂ : εNFA α σ₂} {s : σ₁} {t : σ₂} {x : List (Option α)}
    (h : (concat εM₁ εM₂).IsPath (Sum.inl s) (Sum.inr t) x) :
    ∃ u v s_acc s_start, x = u ++ [none] ++ v ∧
    εM₁.IsPath s s_acc u ∧ s_acc ∈ εM₁.accept ∧
    s_start ∈ εM₂.start ∧ εM₂.IsPath s_start t v := by
  generalize hs' : Sum.inl s = s' at h
  generalize ht' : Sum.inr t = t' at h
  induction h generalizing s with
  | nil u =>
    subst ht'
    cases hs'
  | cons r s'' t'' oa x' h_step h_path ih =>
    subst hs' ht'
    cases oa with
    | some a =>
      simp [concat] at h_step
      rcases h_step with ⟨q, hq, rfl⟩
      have ⟨u, v, s_acc, s_start, hx', h_path_rest, h_acc, h_bridge, h_path_M₂⟩ :=
        ih (Eq.refl _) (Eq.refl _)
      use some a :: u, v, s_acc, s_start
      and_intros
      · simp [hx']
      · exact εNFA.IsPath.cons q s s_acc (some a) u hq h_path_rest
      · exact h_acc
      · exact h_bridge
      · exact h_path_M₂
    | none =>
      by_cases h_mem : s ∈ εM₁.accept
      · simp [concat, h_mem] at h_step
        rcases h_step with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · have ⟨u, v, s_acc, s_start, hx', h_path_rest, h_acc, h_bridge, h_path_M₂⟩ :=
            ih (Eq.refl _) (Eq.refl _)
          use none :: u, v, s_acc, s_start
          and_intros
          · simp [hx']
          · exact εNFA.IsPath.cons q s s_acc none u hq h_path_rest
          · exact h_acc
          · exact h_bridge
          · exact h_path_M₂
        · use [], x', s, q
          and_intros
          · simp
          · exact (εNFA.isPath_nil εM₁).mpr rfl
          · exact h_mem
          · exact hq
          · exact IsPath.concat_proj_inr h_path
      · simp [concat, h_mem] at h_step
        rcases h_step with ⟨q, hq, rfl⟩
        have ⟨u, v, s_acc, s_start, hx', h_path_rest, h_acc, h_bridge, h_path_M₂⟩ :=
          ih (Eq.refl _) (Eq.refl _)
        use none :: u, v, s_acc, s_start
        and_intros
        · simp [hx']
        · exact εNFA.IsPath.cons q s s_acc none u hq h_path_rest
        · exact h_acc
        · exact h_bridge
        · exact h_path_M₂

theorem accepts_concat {εM₁ : εNFA α σ₁} {εM₂ : εNFA α σ₂} :
    (concat εM₁ εM₂).accepts = εM₁.accepts * εM₂.accepts := by
  ext x
  constructor
  · intro h
    have ⟨q₁, q₂, x', hq₁, hq₂, hx', hεM⟩ :=
      (εNFA.mem_accepts_iff_exists_path (concat εM₁ εM₂)).mp h
    simp [concat] at hq₁ hq₂
    rcases hq₁ with ⟨s, hs, rfl⟩
    rcases hq₂ with ⟨t, ht, rfl⟩
    have ⟨u', v', s_acc, s_start, hx, h_path_M₁, h_acc_M₁, h_start_M₂, h_path_M₂⟩ :=
      IsPath.concat_split_inl_inr hεM
    apply Language.mem_mul.mpr
    use u'.reduceOption
    constructor
    · apply (εNFA.mem_accepts_iff_exists_path εM₁).mpr
      use s, s_acc, u'
    · use v'.reduceOption
      constructor
      · apply (εNFA.mem_accepts_iff_exists_path εM₂).mpr
        use s_start, t, v'
      · rw [← hx', ← List.reduceOption_append, hx]
        simp [List.reduceOption_append, List.reduceOption_cons_of_none]
  · simp [Language.mul_def, Set.image2]
    rw [Set.mem_setOf_eq]
    intro ⟨u, hu, v, hv, hx⟩
    have ⟨uq₁, uq₂, u', huq₁, huq₂, hu', hεM₁⟩ := (εNFA.mem_accepts_iff_exists_path εM₁).mp hu
    have ⟨vq₁, vq₂, v', hvq₁, hvq₂, hv', hεM₂⟩ := (εNFA.mem_accepts_iff_exists_path εM₂).mp hv
    apply (εNFA.mem_accepts_iff_exists_path (concat εM₁ εM₂)).mpr
    use Sum.inl uq₁, Sum.inr vq₂, u' ++ [none] ++ v'
    and_intros
    · simp [concat]
      exact huq₁
    · simp [concat]
      exact hvq₂
    · simp [List.reduceOption_append, hx, hu', hv']
    · simp only [εNFA.isPath_append]
      use (Sum.inr vq₁)
      constructor
      · use (Sum.inl uq₂)
        constructor
        · exact IsPath.concat_lift_inl hεM₁
        · simp [concat, huq₂, hvq₁]
      · exact IsPath.concat_lift_inr hεM₂

end concat

section kstar

variable {σ : Type*}

def kstar (εM : εNFA α σ) : εNFA α (Unit ⊕ σ) where
  step q oa := match q, oa with
    | Sum.inl _, some _ =>
      {}
    | Sum.inl _, none =>
      εM.start.image Sum.inr
    | Sum.inr s, some a =>
      (εM.step s (some a)).image Sum.inr
    | Sum.inr s, none =>
      let internal := (εM.step s none).image Sum.inr
      if s ∈ εM.accept then
        internal ∪ (εM.start.image Sum.inr)
      else
        internal
  start := { Sum.inl () }
  accept := { Sum.inl () } ∪ (εM.accept.image Sum.inr)

lemma IsPath.kstar_lift_inr {εM : εNFA α σ} {s t : σ} {x : List (Option α)}
    (h : εM.IsPath s t x) :
    εM.kstar.IsPath (Sum.inr s) (Sum.inr t) x := by
  induction h with
  | nil _ =>
    exact (isPath_nil εM.kstar).mpr rfl
  | cons t' s' u oa x' h_step h_path ih =>
    apply εNFA.IsPath.cons (Sum.inr t') (Sum.inr s') (Sum.inr u)
    · simp [kstar]
      cases oa with
      | some a =>
        simp [h_step]
      | none =>
        by_cases h_mem : s' ∈ εM.accept <;> simp [h_mem, h_step]
    · exact ih

lemma exists_path_inr_of_flatten {εM : εNFA α σ}
    (L : List (List α)) (h_nonempty : L ≠ []) (h_all : ∀ y ∈ L, y ∈ εM.accepts) :
    ∃ (s : σ) (q : Unit ⊕ σ) (x : List (Option α)),
      s ∈ εM.start ∧
      q ∈ εM.kstar.accept ∧
      x.reduceOption = L.flatten ∧
      εM.kstar.IsPath (Sum.inr s) q x := by
  induction L with
  | nil =>
    contradiction
  | cons y L' ih =>
    have hy := h_all y List.mem_cons_self
    have ⟨s, t, x, hs, ht, hy', hx⟩ := (εNFA.mem_accepts_iff_exists_path εM).mp hy
    subst hy'
    cases L' with
    | nil =>
      use s, Sum.inr t, x
      and_intros
      · exact hs
      · simp [kstar]
        exact ht
      · simp
      · exact IsPath.kstar_lift_inr hx
    | cons z L'' =>
      have h_nonempty' : z :: L'' ≠ [] := by simp
      have h_all' : ∀ y ∈ z :: L'', y ∈ εM.accepts := by
        intro y hy
        exact h_all y (by simp [hy])
      have ⟨s', q, x', hs', hq, hL'', hx'⟩:= ih h_nonempty' h_all'
      use s, q, x ++ [none] ++ x'
      and_intros
      · exact hs
      · exact hq
      · simp [hL'', List.reduceOption_append]
      · rw [List.append_assoc, isPath_append]
        use Sum.inr t
        constructor
        · exact IsPath.kstar_lift_inr hx
        · apply IsPath.cons (Sum.inr s')
          · simp [kstar, ht, hs']
          · simp [hx']

theorem accepts_kstar {εM : εNFA α σ} : (kstar εM).accepts = (εM.accepts)∗ := by
  ext x
  constructor
  · sorry
  · intro h
    rw [Language.kstar_def, Set.mem_setOf_eq] at h
    rcases h with ⟨L, hx, hL⟩
    apply (mem_accepts_iff_exists_path εM.kstar).mpr
    cases L with
    | nil =>
      use Sum.inl (), Sum.inl (), []
      simp [kstar, hx]
    | cons l L' =>
      expose_names
      have h_nonempty : l :: L' ≠ [] := by simp
      have ⟨s, q, x', hs, hq, hL', hx'⟩ := exists_path_inr_of_flatten (l :: L') h_nonempty hL
      use Sum.inl (), q, none :: x'
      and_intros
      · simp [kstar]
      · exact hq
      · simp [hx, hL']
      · apply IsPath.cons (Sum.inr s)
        · simp [kstar]
          exact hs
        · exact hx'

end kstar

end εNFA

namespace DFA

section singleton

def char (a : α) [DecidableEq α] : DFA α (Fin 3) where
  step (n : Fin 3) (x : α) :=
    match n.val with
    | Nat.zero =>
      if x = a then 1 else 2
    | Nat.succ _ =>
      2
  start := 0
  accept := {1}

theorem accepts_char {a : α} : (char a).accepts = { [a] } := by
  ext x
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  constructor
  · intro h
    rw [Set.mem_setOf_eq] at h
    cases x with
    | nil =>
      simp [char] at h
    | cons b x' =>
      have h_dead_state : ∀ w, List.foldl (char a).step 2 w = 2 := by
        intro w
        induction w with
        | nil =>
          simp
        | cons b w' ih =>
          simp [char] at *
          simp [ih]
      by_cases heq : b = a
      · subst heq
        simp [char] at h h_dead_state
        cases x' with
        | nil =>
          rfl
        | cons c x'' =>
          by_cases heq' : c = b
          all_goals(
            simp [heq'] at h
            rw [h_dead_state] at h
            contradiction
          )
      · simp [char, heq] at h h_dead_state
        rw [h_dead_state] at h
        contradiction
  · rintro rfl
    rw [Set.mem_setOf_eq]
    simp [char]

end singleton

end DFA

namespace Language

theorem IsRegular.zero : IsRegular (0 : Language α) := by
  apply isRegular_iff.mpr
  use Unit, inferInstance, ⟨fun _ _ => (), (), {}⟩
  rfl

theorem IsRegular.top : IsRegular (⊤ : Language α) := by
  rw [← compl_bot, bot_eq_zero]
  apply IsRegular.compl
  exact IsRegular.zero

theorem IsRegular.one : IsRegular (1 : Language α) := by
  apply isRegular_iff.mpr
  use Fin 2, inferInstance, ⟨fun _ _ => 1, 0, { 0 }⟩
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  ext x
  rw [Set.mem_setOf_eq]
  cases x with
  | nil =>
    simp
  | cons _ x' =>
    simp
    intro h
    have h_dead_state : ∀ w : List α, List.foldl (fun (_ : Fin 2) _ => 1) 1 w = 1 := by
      intro w
      induction w with
      | nil =>
        simp
      | cons b w' ih =>
        simp [ih]
    have h_absurd := h_dead_state x'
    rw [h] at h_absurd
    contradiction

theorem IsRegular.mul {L₁ L₂ : Language α} [DecidableEq α]
    (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) :
    IsRegular (L₁ * L₂) := by
  have ⟨σ₁, _, M₁, hM₁⟩ := h₁
  have ⟨σ₂, _, M₂, hM₂⟩ := h₂
  let εM₁ := M₁.toNFA.toεNFA
  let εM₂ := M₂.toNFA.toεNFA
  let εM := εNFA.concat εM₁ εM₂
  apply isRegular_iff.mpr
  use Set (σ₁ ⊕ σ₂), inferInstance, εM.toNFA.toDFA
  subst hM₁ hM₂
  rw [NFA.toDFA_correct, εNFA.toNFA_correct]
  rw [← DFA.toNFA_correct, ← NFA.toεNFA_correct]
  rw [← DFA.toNFA_correct, ← NFA.toεNFA_correct]
  exact εNFA.accepts_concat

theorem IsRegular.kstar {L : Language α} (h : IsRegular L) : IsRegular (L∗) := by
  have ⟨σ, _, M, hM⟩ := h
  let εM := M.toNFA.toεNFA
  let εM_kstar := εNFA.kstar εM
  apply isRegular_iff.mpr
  use Set (Unit ⊕ σ), inferInstance, εM_kstar.toNFA.toDFA
  subst hM
  rw [NFA.toDFA_correct, εNFA.toNFA_correct]
  rw [← DFA.toNFA_correct, ← NFA.toεNFA_correct]
  exact εNFA.accepts_kstar

theorem IsRegular.singleton {a : α} : IsRegular ({ [a] }) := by
  apply isRegular_iff.mpr
  let M := DFA.char a
  use Fin 3, inferInstance, M
  exact DFA.accepts_char

end Language
