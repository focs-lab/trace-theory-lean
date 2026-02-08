import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Fintype.Option

open Classical Computability

variable {α : Type}

namespace DFA

section epsilon

def epsilon : DFA α (Option Unit) where
  step := fun _ _ => none
  start := some ()
  accept := { some () }

theorem accepts_epsilon : epsilon.accepts = (1 : Language α) := by
  ext x
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  rw [Set.mem_setOf_eq]
  cases x with
  | nil =>
    simp [epsilon]
  | cons a x' =>
    simp [epsilon]
    have h_dead : ∀ w : List α, List.foldl (fun _ _ => none) (none : Option Unit) w = none := by
      intro w; induction w <;> simp [*]
    intro h_absurd
    rw [h_dead] at h_absurd
    contradiction

end epsilon

section singleton

def char (a : α) [DecidableEq α] : DFA α (Option Bool) where
  step (ob : Option Bool) (x : α) := match ob with
    | some true  => none
    | some false => if x = a then some true else none
    | none       => none
  start := some false
  accept := { some true }

@[simp]
theorem char_step_start (a : α) [DecidableEq α] (x : α) :
    (char a).step (some false) x = if x = a then some true else none := rfl

@[simp]
theorem char_step_accept (a : α) [DecidableEq α] (x : α) :
    (char a).step (some true) x = none := rfl

@[simp]
theorem char_step_dead (a : α) [DecidableEq α] (x : α) :
    (char a).step none x = none := rfl

theorem accepts_char {a : α} : (char a).accepts = { [a] } := by
  ext x
  simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]
  rw [Set.mem_setOf_eq, Set.mem_singleton_iff]
  cases x with
  | nil =>
    simp [char]
  | cons b x' =>
    cases x' with
    | nil =>
      simp [char]
    | cons c x'' =>
      have h_dead : ∀ w, List.foldl (char a).step none w = none := by
        intro w; induction w <;> simp [*]
      simp [char] at *
      split_ifs
      all_goals(
        intro h_absurd
        rw [h_dead] at h_absurd
        contradiction
      )

end singleton

end DFA

namespace εNFA

section concat

variable {σ₁ σ₂ : Type*}
variable {M₁ : εNFA α σ₁} {M₂ : εNFA α σ₂}

def concat (M₁ : εNFA α σ₁) (M₂ : εNFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step q oa := match q, oa with
    | Sum.inl q₁, some _ => (M₁.step q₁ oa).image Sum.inl
    | Sum.inl q₁, none   =>
      (M₁.step q₁ none).image Sum.inl ∪
      (if q₁ ∈ M₁.accept then (M₂.start.image Sum.inr) else ∅)
    | Sum.inr q₂, _      => (M₂.step q₂ oa).image Sum.inr
  start := M₁.start.image Sum.inl
  accept := M₂.accept.image Sum.inr

@[simp]
theorem concat_step_inl_none :
    (concat M₁ M₂).step (Sum.inl q) none =
    (M₁.step q none).image Sum.inl ∪
    (if q ∈ M₁.accept then M₂.start.image Sum.inr else ∅) :=
  rfl

@[simp]
theorem concat_step_inl_some :
    (concat M₁ M₂).step (Sum.inl q) (some a) =
    (M₁.step q (some a)).image Sum.inl :=
  rfl

@[simp]
theorem concat_step_inr_none :
    (concat M₁ M₂).step (Sum.inr q) none =
    (M₂.step q none).image Sum.inr :=
  rfl

@[simp]
theorem concat_step_inr_some :
    (concat M₁ M₂).step (Sum.inr q) (some a) =
    (M₂.step q (some a)).image Sum.inr :=
  rfl

lemma IsPath.concat_lift_inl
    (h : M₁.IsPath s t x) : (concat M₁ M₂).IsPath (Sum.inl s) (Sum.inl t) x := by
  induction h with
  | nil _ =>
    exact (isPath_nil (concat M₁ M₂)).mpr rfl
  | cons t' s' u oa x' h_step h_path ih =>
    apply IsPath.cons (Sum.inl t') (Sum.inl s') (Sum.inl u)
    · cases oa <;> simpa
    · exact ih

lemma IsPath.concat_lift_inr
    (h : M₂.IsPath s t x) : (concat M₁ M₂).IsPath (Sum.inr s) (Sum.inr t) x := by
  induction h with
  | nil _ =>
    exact (isPath_nil (concat M₁ M₂)).mpr rfl
  | cons t' s' u _ _ h_step _ ih =>
    apply IsPath.cons (Sum.inr t') (Sum.inr s') (Sum.inr u)
    · simpa [concat]
    · exact ih

lemma IsPath.concat_proj_inr
    (h : (concat M₁ M₂).IsPath (Sum.inr s) (Sum.inr t) x) : M₂.IsPath s t x := by
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
    apply IsPath.cons q s t
    · exact hq
    · simp [ih]

lemma IsPath.concat_split_inl_inr
    (h : (concat M₁ M₂).IsPath (Sum.inl s) (Sum.inr t) x) :
    ∃ u v s_acc s_start,
      x = u ++ [none] ++ v ∧
      M₁.IsPath s s_acc u ∧
      s_acc ∈ M₁.accept ∧
      s_start ∈ M₂.start ∧
      M₂.IsPath s_start t v := by
  generalize hs' : Sum.inl s = s' at h
  generalize ht' : Sum.inr t = t' at h
  induction h generalizing s with
  | nil u =>
    cases ht'
    cases hs'
  | cons _ _ _ oa x' h_step h_path ih =>
    subst hs' ht'
    cases oa with
    | some a =>
      simp at h_step
      rcases h_step with ⟨q, hq, rfl⟩
      have ⟨u, v, s_acc, s_start, hx', h_path_rest, h_acc, h_bridge, h_path_M₂⟩ := ih rfl rfl
      use some a :: u, v, s_acc, s_start
      and_intros
      · simp [hx']
      · exact cons q s s_acc (some a) u hq h_path_rest
      · exact h_acc
      · exact h_bridge
      · exact h_path_M₂
    | none =>
      simp at h_step
      rcases h_step with ⟨q, hq, rfl⟩ | ⟨hs, q, hq, rfl⟩
      · have ⟨u, v, s_acc, s_start, hx', h_path_rest, h_acc, h_bridge, h_path_M₂⟩ := ih rfl rfl
        use none :: u, v, s_acc, s_start
        and_intros
        · simp [hx']
        · exact cons q s s_acc none u hq h_path_rest
        · exact h_acc
        · exact h_bridge
        · exact h_path_M₂
      · use [], x', s, q
        and_intros
        · simp
        · exact (isPath_nil M₁).mpr rfl
        · exact hs
        · exact hq
        · exact concat_proj_inr h_path

theorem accepts_concat : (concat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  simp only [Language.mem_mul]
  constructor
  · intro h
    have ⟨q₁, q₂, x', hq₁, hq₂, hx', hM⟩ := (mem_accepts_iff_exists_path (concat M₁ M₂)).mp h
    simp [concat] at hq₁ hq₂
    rcases hq₁ with ⟨s, hs, rfl⟩
    rcases hq₂ with ⟨t, ht, rfl⟩
    have ⟨u', v', s_acc, s_start, hx, h_path_M₁, h_acc_M₁, h_start_M₂, h_path_M₂⟩ :=
      IsPath.concat_split_inl_inr hM
    apply Language.mem_mul.mpr
    refine ⟨u'.reduceOption, ?_, v'.reduceOption, ?_, ?_⟩
    · apply (mem_accepts_iff_exists_path M₁).mpr
      use s, s_acc, u'
    · apply (mem_accepts_iff_exists_path M₂).mpr
      use s_start, t, v'
    · subst hx' hx
      simp [List.reduceOption_append, List.reduceOption_cons_of_none]
  · intro ⟨u, hu, v, hv, hx⟩
    have ⟨uq₁, uq₂, u', huq₁, huq₂, hu', hM₁⟩ := (mem_accepts_iff_exists_path M₁).mp hu
    have ⟨vq₁, vq₂, v', hvq₁, hvq₂, hv', hM₂⟩ := (mem_accepts_iff_exists_path M₂).mp hv
    apply (mem_accepts_iff_exists_path (concat M₁ M₂)).mpr
    use Sum.inl uq₁, Sum.inr vq₂, u' ++ [none] ++ v'
    and_intros
    · simpa [concat]
    · simpa [concat]
    · simp [List.reduceOption_append, hx, hu', hv']
    · simp only [isPath_append]
      use Sum.inr vq₁
      constructor
      · use Sum.inl uq₂
        constructor
        · exact IsPath.concat_lift_inl hM₁
        · simp [huq₂, hvq₁]
      · exact IsPath.concat_lift_inr hM₂

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
    apply IsPath.cons (Sum.inr t') (Sum.inr s') (Sum.inr u)
    · simp [kstar]
      cases oa with
      | some a =>
        simp [h_step]
      | none =>
        by_cases h_mem : s' ∈ εM.accept <;> simp [h_mem, h_step]
    · exact ih

lemma kstar_exists_path_inr {εM : εNFA α σ}
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
    have ⟨s, t, x, hs, ht, hy', hx⟩ := (mem_accepts_iff_exists_path εM).mp hy
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

lemma kstar_no_return {εM : εNFA α σ} {s : σ} {t : Unit ⊕ σ} {x : List (Option α)}
    (h : (kstar εM).IsPath (Sum.inr s) t x) : t ≠ Sum.inl () := by
  generalize hs' : Sum.inr s = s' at h
  induction h generalizing s with
  | nil u =>
    subst hs'
    simp
  | cons t' s'' u oa x' h_step h_path ih =>
    subst hs'
    have h_next_is_inr : ∃ y, Sum.inr y = t' := by
      simp [kstar] at h_step
      cases oa with
      | some a =>
        simp at h_step
        rcases h_step with ⟨y, _, rfl⟩
        use y
      | none =>
        simp at h_step
        split_ifs at h_step with h_mem
        · rcases h_step with ⟨y, _, rfl⟩ | ⟨y, _, rfl⟩
          · use y
          · use y
        · rcases h_step with ⟨y, _, rfl⟩
          use y
    rcases h_next_is_inr with ⟨y, rfl⟩
    exact ih rfl

lemma IsPath.kstar_split_inr {s t : σ} {x : List (Option α)}
    (h : (kstar εM).IsPath (Sum.inr s) (Sum.inr t) x) :
    (∃ x', x'.reduceOption = x.reduceOption ∧ εM.IsPath s t x') ∨
    (∃ (u v : List (Option α)) (q_acc : σ) (s_next : σ),
      x.reduceOption = u.reduceOption ++ v.reduceOption ∧
      εM.IsPath s q_acc u ∧
      q_acc ∈ εM.accept ∧
      s_next ∈ εM.start ∧
      (kstar εM).IsPath (Sum.inr s_next) (Sum.inr t) v ∧
      v.length < x.length) := by
  generalize hs' : Sum.inr s = s' at h
  generalize ht' : Sum.inr t = t' at h
  induction h generalizing s with
  | nil q =>
    left
    use []
    simp
    cases hs'
    cases ht'
    rfl
  | cons u' s'' t'' oa x'' h_step h_path ih =>
    subst hs' ht'
    cases oa with
    | some a =>
      simp [kstar] at h_step
      have ⟨s_next, hs_next, hu'⟩ := h_step
      rcases ih hu' rfl with
        ⟨y, hx'', hy⟩ |
        ⟨u, v, q_acc, s_next', huv, hu, hq_acc, hs_next', hv, hlt⟩
      · left
        use some a :: y
        constructor
        · simp [hx'']
        · exact IsPath.cons s_next s t (some a) y hs_next hy
      · right
        use some a :: u, v, q_acc, s_next'
        and_intros
        · simp [huv]
        · exact IsPath.cons s_next s q_acc (some a) u hs_next hu
        · exact hq_acc
        · exact hs_next'
        · exact hv
        · simp
          exact Nat.lt_add_right 1 hlt
    | none =>
      simp [kstar] at h_step
      split_ifs at h_step with h_mem
      · simp at h_step
        rcases h_step with ⟨s_next, hs_next, hu'⟩ | ⟨s_start, hs_start, hu'⟩
        · rcases ih hu' rfl with
            ⟨y, hx'', hy⟩ |
            ⟨u, v, q_acc, s_next', huv, hu, hq_acc, hs_next', hv, hlt⟩
          · left
            use none :: y
            constructor
            · simp [hx'']
            · exact cons s_next s t none y hs_next hy
          · right
            use none :: u, v, q_acc, s_next'
            and_intros
            · simp [huv]
            · exact IsPath.cons s_next s q_acc none u hs_next hu
            · exact hq_acc
            · exact hs_next'
            · exact hv
            · simp
              exact Nat.lt_add_right 1 hlt
        · right
          use [], x'', s, s_start
          and_intros
          · simp
          · exact (isPath_nil εM).mpr rfl
          · exact h_mem
          · exact hs_start
          · simp [hu', h_path]
          · simp
      · simp at h_step
        rcases h_step with ⟨s_next, hs_next, hu'⟩
        rcases ih hu' rfl with
          ⟨y, hx'', hy⟩ |
          ⟨u, v, q_acc, s_next', huv, hu, hq_acc, hs_next', hv, hlt⟩
        · left
          use none :: y
          constructor
          · simp [hx'']
          · exact IsPath.cons s_next s t none y hs_next hy
        · right
          use none :: u, v, q_acc, s_next'
          and_intros
          · simp [huv]
          · exact IsPath.cons s_next s q_acc none u hs_next hu
          · exact hq_acc
          · exact hs_next'
          · exact hv
          · simp
            exact Nat.lt_add_right 1 hlt

lemma IsPath.kstar_exists_decomp {εM : εNFA α σ} {s t : σ} {x : List (Option α)}
    (h : (kstar εM).IsPath (Sum.inr s) (Sum.inr t) x)
    (hs : s ∈ εM.start) (ht : t ∈ εM.accept) :
    ∃ (L : List (List α)), L.flatten = x.reduceOption ∧ ∀ y ∈ L, y ∈ εM.accepts := by
  generalize h_len : x.length = n
  induction n using Nat.strong_induction_on generalizing s x with
  | h n ih =>
    rcases IsPath.kstar_split_inr h with
      ⟨x', hx, hx'⟩ |
      ⟨u, v, q_acc, s_next, hx, hu, h_acc, h_next, hv, hlt⟩
    · use [x'.reduceOption]
      constructor
      · simp [hx]
      · intro y hy
        simp at hy
        subst hy
        apply (mem_accepts_iff_exists_path εM).mpr
        use s, t, x'
    · have hu_acc : u.reduceOption ∈ εM.accepts := by
        apply (mem_accepts_iff_exists_path εM).mpr
        use s, q_acc, u
      subst h_len
      have ⟨L', hv', hL'⟩ := ih v.length hlt hv h_next rfl
      use u.reduceOption :: L'
      constructor
      · simp [hv', hx]
      · intro y hy
        simp at hy
        rcases hy with hy | hy
        · simp [hu_acc, hy]
        · exact hL' y hy

theorem accepts_kstar {εM : εNFA α σ} : (kstar εM).accepts = (εM.accepts)∗ := by
  ext x
  constructor
  · intro h
    rw [Language.kstar_def, Set.mem_setOf_eq]
    have ⟨s, t, x', hs, ht, hx, h_path⟩ := (mem_accepts_iff_exists_path εM.kstar).mp h
    match t with
    | Sum.inl _ =>
      use []
      simp [kstar] at hs
      simp [hs] at h_path
      cases h_path with
      | nil _ =>
        simpa using hx
      | cons t' s' u oa x'' h_step h_path =>
        simp [kstar] at h_step
        cases oa with
        | some a =>
          simp at h_step
        | none =>
          simp at h_step
          rcases h_step with ⟨y, _, rfl⟩
          have h_absurd := kstar_no_return h_path
          contradiction
    | Sum.inr t' =>
      cases x' with
      | nil =>
        simp [kstar] at hs h_path
        subst hs
        contradiction
      | cons oa x'' =>
        rw [← List.singleton_append, isPath_append] at h_path
        have ⟨u, hsu, hut⟩ := h_path
        simp [kstar] at hs
        subst hs
        cases oa with
        | some a =>
          simp [kstar] at hsu
        | none =>
          simp [kstar] at hsu ht
          rcases hsu with ⟨u', hu', hu⟩
          subst hu
          have ⟨L, hx', hL⟩ := IsPath.kstar_exists_decomp hut hu' ht
          use L
          constructor
          · simp at hx
            simp [hx, hx']
          · exact hL
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
      have ⟨s, q, x', hs, hq, hL', hx'⟩ := kstar_exists_path_inr (l :: L') h_nonempty hL
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

namespace Language

theorem IsRegular.zero : IsRegular (0 : Language α) := by
  apply isRegular_iff.mpr
  use Unit, inferInstance, ⟨fun _ _ => (), (), {}⟩
  rfl

theorem IsRegular.one : IsRegular (1 : Language α) := by
  apply isRegular_iff.mpr
  use Option Unit, inferInstance, DFA.epsilon
  exact DFA.accepts_epsilon

theorem IsRegular.top : IsRegular (⊤ : Language α) := by
  rw [← compl_bot, bot_eq_zero]
  apply IsRegular.compl
  exact IsRegular.zero

theorem IsRegular.singleton {a : α} : IsRegular ({ [a] }) := by
  apply isRegular_iff.mpr
  use Option Bool, inferInstance, DFA.char a
  exact DFA.accepts_char

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

end Language

namespace RegularExpressions

theorem IsRegular.matches (P : RegularExpression α) : Language.IsRegular (P.matches') := by
  induction P with
  | zero =>
    simp
    exact Language.IsRegular.zero
  | epsilon =>
    simp
    exact Language.IsRegular.one
  | char =>
    simp
    exact Language.IsRegular.singleton
  | plus _ _ ih₁ ih₂ =>
    simp
    exact Language.IsRegular.add ih₁ ih₂
  | comp _ _ ih₁ ih₂ =>
    simp
    exact Language.IsRegular.mul ih₁ ih₂
  | star _ ih =>
    simp
    exact Language.IsRegular.kstar ih

end RegularExpressions
