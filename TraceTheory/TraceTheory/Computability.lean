import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Option

open Classical Computability

variable {α : Type}

namespace DFA

section epsilon

/-- DFA which accepts the empty language. -/
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

/-- DFA which accepts the singleton language of `a`. -/
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

theorem accepts_char {a : α} [DecidableEq α] : (char a).accepts = { [a] } := by
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
variable [DecidablePred (· ∈ M₁.accept)]

/-- DFA which accepts the concatenation of the languages of `M₁` and `M₂`. -/
def concat (M₁ : εNFA α σ₁) (M₂ : εNFA α σ₂) [DecidablePred (· ∈ M₁.accept)]: εNFA α (σ₁ ⊕ σ₂) where
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
variable {M : εNFA α σ}
variable [DecidablePred (· ∈ M.accept)]

/-- DFA which accepts the Kleene star of the language of `M`. -/
def kstar (M : εNFA α σ) [DecidablePred (· ∈ M.accept)] : εNFA α (Option σ) where
  step oq oa := match oq, oa with
    | none,   some _ => ∅
    | none,   none   => M.start.image some
    | some q, some a => (M.step q (some a)).image some
    | some q, none   =>
      (M.step q none).image some ∪
      (if q ∈ M.accept then M.start.image some else ∅)
  start := { none }
  accept := { none } ∪ M.accept.image some

@[simp]
theorem kstar_step_none_none : (kstar M).step none none = M.start.image some :=
  rfl

@[simp]
theorem kstar_step_none_some (a : α) : (kstar M).step none (some a) = ∅ := rfl

@[simp]
lemma kstar_step_some (q : σ) (a : Option α) :
    (kstar M).step (some q) a =
    (M.step q a).image some ∪
    (if a = none ∧ q ∈ M.accept then M.start.image some else ∅) := by
  cases a <;> simp [kstar]

lemma IsPath.kstar_lift_some
    (h : M.IsPath s t x) :
    M.kstar.IsPath (some s) (some t) x := by
  induction h with
  | nil _ =>
    exact (isPath_nil M.kstar).mpr rfl
  | cons t' s' u oa x' h_step h_path ih =>
    apply cons (some t') (some s') (some u)
    · cases oa <;> simp [h_step]
    · exact ih

lemma kstar_exists_path_some
    (L : List (List α)) (h_nonempty : L ≠ []) (h_all : ∀ y ∈ L, y ∈ M.accepts) :
    ∃ (s : σ) (q : Option σ) (x : List (Option α)),
      s ∈ M.start ∧
      q ∈ M.kstar.accept ∧
      x.reduceOption = L.flatten ∧
      M.kstar.IsPath (some s) q x := by
  induction L with
  | nil =>
    contradiction
  | cons y L' ih =>
    have hy := h_all y List.mem_cons_self
    have ⟨s, t, x, hs, ht, hy', hx⟩ := (mem_accepts_iff_exists_path M).mp hy
    subst hy'
    cases L' with
    | nil =>
      use s, some t, x
      and_intros
      · exact hs
      · simpa [kstar]
      · simp
      · exact IsPath.kstar_lift_some hx
    | cons z L'' =>
      have h_nonempty' : z :: L'' ≠ [] := by simp
      have h_all' : ∀ y ∈ z :: L'', y ∈ M.accepts := by aesop
      have ⟨s', q, x', hs', hq, hL'', hx'⟩:= ih h_nonempty' h_all'
      use s, q, x ++ [none] ++ x'
      and_intros
      · exact hs
      · exact hq
      · simp [hL'', List.reduceOption_append]
      · rw [List.append_assoc, isPath_append]
        use some t
        constructor
        · exact IsPath.kstar_lift_some hx
        · apply IsPath.cons (some s')
          · simp [ht, hs']
          · simpa

lemma IsPath.kstar_path_from_none
    (h : (kstar M).IsPath none t x) :
    t = none ∧ x = [] ∨
    ∃ s_start x',
      x = none :: x' ∧
      s_start ∈ M.start ∧
      (kstar M).IsPath (some s_start) t x' := by
  cases h with
  | nil _ =>
    simp
  | cons t' s u oa x' h_step h_path =>
    simp
    cases oa with
    | some a =>
      simp at h_step
    | none =>
      simp at h_step ⊢
      rcases h_step with ⟨s_start, hs_start, rfl⟩
      exact ⟨s_start, hs_start, h_path⟩

lemma IsPath.kstar_split_some
    (h : (kstar M).IsPath (some s) (some t) x) :
    (∃ x', x'.reduceOption = x.reduceOption ∧ M.IsPath s t x') ∨
    (∃ (u v : List (Option α)) (s_acc s_next : σ),
      x = u ++ [none] ++ v ∧
      M.IsPath s s_acc u ∧
      s_acc ∈ M.accept ∧
      s_next ∈ M.start ∧
      (kstar M).IsPath (some s_next) (some t) v ∧
      v.length < x.length) := by
    generalize hs : some s = os at h
    generalize ht : some t = ot at h
    induction h generalizing s with
    | nil _ =>
      cases hs
      cases ht
      simp
      use []
      simp
    | cons t' s' u' oa x' h_step h_path ih =>
      subst hs ht
      simp at h_step
      rcases h_step with
        ⟨s_next, h_step_M, rfl⟩ |
        ⟨⟨rfl, hs_acc⟩, s_next, h_start, rfl⟩
      · rcases ih rfl rfl with
          ⟨y, hx'', hy⟩ |
          ⟨u, v, q_acc, q_next, rfl, hu, hq_acc, hq_next, hv, hlt⟩
        · left
          use oa :: y
          constructor
          · rw [← List.singleton_append]
            nth_rw 2 [← List.singleton_append]
            simp only [List.reduceOption_append]
            simpa
          · exact cons s_next s t oa y h_step_M hy
        · right
          use oa :: u, v, q_acc, q_next
          and_intros
          · simp
          · exact cons s_next s q_acc oa u h_step_M hu
          · exact hq_acc
          · exact hq_next
          · exact hv
          · simp at hlt ⊢
            exact Nat.lt_add_right 1 hlt
      · right
        use [], x', s, s_next
        and_intros
        · simp
        · exact (isPath_nil M).mpr rfl
        · exact hs_acc
        · exact h_start
        · exact h_path
        · simp

lemma IsPath.kstar_no_return {q : σ} {y : List (Option α)} :
    ¬ (kstar M).IsPath (some q) none y := by
  intro h
  generalize hq : some q = oq at h
  generalize hn : none = n at h
  induction h generalizing q with
  | nil =>
    cases hq
    cases hn
  | cons t s u oa x h_step h_path ih =>
    subst hq hn
    simp at h_step
    rcases h_step with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ih rfl rfl

lemma IsPath.kstar_exists_decomp
    (h : (kstar M).IsPath (some s) (some t) x)
    (hs : s ∈ M.start) (ht : t ∈ M.accept) :
    ∃ (L : List (List α)), L.flatten = x.reduceOption ∧ ∀ y ∈ L, y ∈ M.accepts := by
  generalize h_len : x.length = n
  induction n using Nat.strong_induction_on generalizing s x with
  | h n ih =>
    rcases IsPath.kstar_split_some h with
      ⟨x', hx, hx'⟩ |
      ⟨u, v, q_acc, s_next, hx, hu, h_acc, h_next, hv, hlt⟩
    · use [x'.reduceOption]
      simp
      constructor
      · exact hx
      · apply (mem_accepts_iff_exists_path M).mpr
        use s, t, x'
    · have hu_acc : u.reduceOption ∈ M.accepts := by
        apply (mem_accepts_iff_exists_path M).mpr
        use s, q_acc, u
      subst h_len
      have ⟨L', hv', hL'⟩ := ih v.length hlt hv h_next rfl
      use u.reduceOption :: L'
      constructor
      · subst hx
        simp [hv', List.reduceOption_append]
      · intro y hy
        simp at hy
        rcases hy with hy | hy
        · simp [hu_acc, hy]
        · exact hL' y hy

theorem accepts_kstar : (kstar M).accepts = (M.accepts)∗ := by
  ext x
  constructor
  · intro h
    have ⟨s_start, s_end, x', h_start, h_end, hx', h_path⟩ :=
      (mem_accepts_iff_exists_path (kstar M)).mp h
    simp [kstar] at h_start h_end
    subst h_start
    simp [Language.mem_kstar]
    rcases h_end with rfl | ⟨q_start, hq_start, rfl⟩
    · use []
      cases h_path with
      | nil _ =>
        simpa using hx'
      | cons t' s' u oa x'' h_step h_rest =>
        cases oa with
        | some a =>
          simp at h_step
        | none =>
          exfalso
          simp at h_step
          rcases h_step with ⟨y, _, rfl⟩
          exact IsPath.kstar_no_return h_rest
    · cases h_path with
      | cons t' s' u oa x'' h_step h_rest =>
        cases oa with
        | some a =>
          simp [kstar] at h_step
        | none =>
          simp [kstar] at h_step
          rcases h_step with ⟨u', hu', rfl⟩
          have ⟨L, hx'', hL⟩ := IsPath.kstar_exists_decomp h_rest hu' hq_start
          use L
          constructor
          · simp at hx'
            simp [hx', hx'']
          · exact hL
  · intro h
    simp [Language.mem_kstar] at h
    rcases h with ⟨L, hx, hL⟩
    apply (mem_accepts_iff_exists_path (kstar M)).mpr
    induction L generalizing x with
    | nil =>
      use none, none, []
      simp [kstar, hx]
    | cons w L' ih =>
      expose_names
      have h_nonempty : w :: L' ≠ [] := by simp
      have ⟨s, q, x', hs, hq, hL', hx'⟩ := kstar_exists_path_some (w :: L') h_nonempty hL
      use none, q, none :: x'
      and_intros
      · simp [kstar]
      · exact hq
      · simp [hx, hL']
      · apply IsPath.cons (some s)
        · simpa [kstar]
        · exact hx'

end kstar

section toSingleεNFA

variable {σ : Type*}
variable {M : εNFA α σ}

/-- The extended state space with a new start state and accept state. -/
inductive ExtendedState (σ : Type*)
  | start : ExtendedState σ
  | accept : ExtendedState σ
  | state (s : σ) : ExtendedState σ
  deriving DecidableEq, Fintype

/-- Transform any `εNFA` into an `εNFA` with a single start state and accept state. -/
def toSingleεNFA (M : εNFA α σ) : εNFA α (ExtendedState σ) where
  step q oa := match q, oa with
    | .start, some _   => ∅
    | .start, none     => (M.start).image .state
    | .accept, _       => ∅
    | .state s, some a => (M.step s (some a)).image .state
    | .state s, none   =>
      (M.step s none).image .state ∪
      if s ∈ M.accept then { ExtendedState.accept } else ∅
  start := { .start }
  accept := { .accept }

@[simp]
theorem toSingleεNFA_step_start_some : M.toSingleεNFA.step .start (some a) = ∅ :=
  rfl

@[simp]
theorem toSingleεNFA_step_start_none : M.toSingleεNFA.step .start none = (M.start).image .state :=
  rfl

@[simp]
theorem toSingleεNFA_step_accept : M.toSingleεNFA.step .accept oa = ∅ :=
  rfl

@[simp]
theorem toSingleεNFA_step_state_some :
    M.toSingleεNFA.step (.state s) (some a) = (M.step s (some a)).image .state :=
  rfl

@[simp]
theorem toSingleεNFA_step_state_none :
    M.toSingleεNFA.step (.state s) none =
      (M.step s none).image .state ∪
      if s ∈ M.accept then { ExtendedState.accept } else ∅ :=
  rfl

lemma IsPath.toSingleεNFA_lift_extendedState (h : M.IsPath s t x) :
    M.toSingleεNFA.IsPath (.state s) (.state t) x := by
  induction h with
  | nil _ =>
    simp
  | cons t' s' u oa x' h_step h_path ih =>
    apply cons (ExtendedState.state t') (.state s') (.state u)
    · cases oa <;> simpa
    · exact ih

lemma IsPath.from_accept (h : M.toSingleεNFA.IsPath .accept u x) :
    u = .accept ∧ x = [] := by
  cases h with
  | nil =>
    simp
  | cons _ _ _ _ _ h_step _ =>
    simp at h_step

lemma IsPath.state_accept (h : M.toSingleεNFA.IsPath (.state s) .accept x):
    ∃ t x', t ∈ M.accept ∧ x = x' ++ [none] ∧ M.IsPath s t x' := by
  generalize hs : (ExtendedState.state s) = ss at h
  generalize ha : ExtendedState.accept = a' at h
  induction h generalizing s with
  | nil _ =>
    cases hs
    cases ha
  | cons t' s' u oa x' h_step h_path ih =>
    subst hs ha
    cases oa with
    | some a =>
      simp at h_step
      rcases h_step with ⟨t, ht, ht'⟩
      subst ht'
      have ⟨t', x'', ht', hx'', h_before⟩ := ih rfl rfl
      use t', some a :: x''
      and_intros
      · exact ht'
      · simpa
      · exact cons t s t' (some a) x'' ht h_before
    | none =>
      simp at h_step
      rcases h_step with ⟨t, ht, ht'⟩ | ⟨hs, ht'⟩
      · subst ht'
        have ⟨t', x'', ht', hx'', h_before⟩ := ih rfl rfl
        use t', none :: x''
        and_intros
        · exact ht'
        · simpa
        · exact cons t s t' none x'' ht h_before
      · subst ht'
        rcases IsPath.from_accept h_path with ⟨_, rfl⟩
        use s, []
        simpa

theorem accepts_toSingleεNFA : M.toSingleεNFA.accepts = M.accepts := by
  ext x
  constructor
  · intro h
    apply (mem_accepts_iff_exists_path M).mpr
    have ⟨s₁, s₂, x', hs₁, hs₂, hx, h_path⟩ := (mem_accepts_iff_exists_path (M.toSingleεNFA)).mp h
    simp [toSingleεNFA] at hs₁ hs₂
    subst hx hs₁ hs₂
    cases h_path with
    | cons t' s' u oa x'' h_step h_rest =>
      cases oa with
      | some a =>
        simp at h_step
      | none =>
        simp at h_step
        rcases h_step with ⟨s, hs, rfl⟩
        have ⟨t, y, ht, hy, h_before⟩ := IsPath.state_accept h_rest
        subst hy
        use s, t, y
        and_intros
        · exact hs
        · exact ht
        · simp [List.reduceOption_append]
        · exact h_before
  · intro h
    apply (mem_accepts_iff_exists_path (M.toSingleεNFA)).mpr
    have ⟨s₁, s₂, x', hs₁, hs₂, hx, hx'⟩ := (mem_accepts_iff_exists_path M).mp h
    subst hx
    use .start, .accept, [none] ++ x' ++ [none]
    and_intros
    · simp [toSingleεNFA]
    · simp [toSingleεNFA]
    · simp [List.reduceOption_append]
    · simp only [isPath_append]
      use .state s₂
      constructor
      · use .state s₁
        constructor
        · simpa
        · exact IsPath.toSingleεNFA_lift_extendedState hx'
      · simpa

end toSingleεNFA

section Kleene

open RegularExpression

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
variable {M : εNFA α (ExtendedState σ)}

local notation "n" => Fintype.card (ExtendedState σ)

/-- The equivalence between the extended states and a finite set of states. -/
noncomputable def e : ExtendedState σ ≃ Fin n := Fintype.equivFin _

variable (M) in
/-- The regex for a direct edge between indices i and j. -/
noncomputable def directRegex (i j : Fin n) : RegularExpression α :=
  let s_i := e.symm i
  let s_j := e.symm j
  let char_transitions : RegularExpression α :=
    Finset.univ.sort.foldl (fun acc a =>
      acc + (if s_j ∈ M.step s_i (some a) then char a else 0)
    ) 0
  let epsilon_transitions : RegularExpression α :=
    if s_j ∈ M.step s_i none ∨ i = j then 1 else 0
  char_transitions + epsilon_transitions

variable (M) in
/-- The path regex using intermediate states < k. -/
noncomputable def pathRegex : ℕ → Fin n → Fin n → RegularExpression α
  | 0, i, j     => directRegex M i j
  | k + 1, i, j =>
    if hk : k < n then
      let k' : Fin n := ⟨k, hk⟩
      let R_to_k := pathRegex k i k'
      let R_loop := pathRegex k k' k'
      let R_from := pathRegex k k' j
      let R_old  := pathRegex k i j
      R_to_k * R_loop.star * R_from + R_old
    else
      pathRegex k i j

omit [Fintype α] [DecidableEq α] [LinearOrder α] in
theorem matches'_foldl_sum (L : List α) (f : α → RegularExpression α) :
    (L.foldl (fun acc a => acc + f a) 0).matches' =
    ((⋃ x ∈ L, (f x).matches') : Language α) := by
  let g := fun (acc : RegularExpression α) (a : α) => acc + f a
  let u : Language α := (⋃ x ∈ L, (f x).matches')
  have h : ∀ acc, (L.foldl g acc).matches' = acc.matches' + u := by
    dsimp [u]
    induction L with
    | nil =>
      intro acc
      simp
      apply Set.empty_subset
    | cons a L' ih =>
      intro acc
      dsimp [g]
      rw [ih, matches'_add, add_assoc]
      apply congr_arg
      simp
      rfl
  specialize h 0
  simp [g, u] at h
  exact h

variable (M) in
/-- A path in the NFA restricted to intermediate states < k. -/
inductive IsRestrictedPath (k : ℕ) : Fin n → Fin n → List α → Prop
  | direct (i j : Fin n) (x : List α) :
      x ∈ (directRegex M i j).matches' →
      IsRestrictedPath k i j x
  | trans (i j m : Fin (n)) (x₁ x₂ : List α) :
      IsRestrictedPath k i m x₁ →
      m.val < k →
      IsRestrictedPath k m j x₂ →
      IsRestrictedPath k i j (x₁ ++ x₂)

theorem mem_pathRegex_iff_isRestrictedPath (k : ℕ) (i j : Fin n) (w : List α) :
    w ∈ (pathRegex M k i j).matches' ↔ IsRestrictedPath M k i j w := by
  sorry

noncomputable def toRegex (M : εNFA a σ) : RegularExpression α :=
  sorry

theorem isRestrictedPath_iff_isPath {i j : Fin n} {x : List α} :
    IsRestrictedPath M n i j x ↔ M.IsPath (e.symm i) (e.symm j) x := by
  constructor
  · intro h
    induction h with
    | direct i' j' x' h_match =>
      dsimp [directRegex] at h_match
      simp only [matches'_foldl_sum] at h_match
      simp only [Language.mem_add] at h_match
      sorry
    | trans i' j' m x₁ x₂ h₁ hlt h₂ ih₁ ih₂ =>
      sorry
  · sorry

theorem accepts_toRegex (M : εNFA a σ) : (toRegex M).matches' = M.accepts := by
  sorry

end Kleene

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

theorem IsRegular.singleton {a : α} [DecidableEq α] : IsRegular ({ [a] }) := by
  apply isRegular_iff.mpr
  use Option Bool, inferInstance, DFA.char a
  exact DFA.accepts_char

theorem IsRegular.mul {L₁ L₂ : Language α}
    (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) :
    IsRegular (L₁ * L₂) := by
  have ⟨σ₁, _, M₁, hM₁⟩ := h₁
  have ⟨σ₂, _, M₂, hM₂⟩ := h₂
  let N₁ := M₁.toNFA.toεNFA
  let N₂ := M₂.toNFA.toεNFA
  let N := εNFA.concat N₁ N₂
  apply isRegular_iff.mpr
  use Set (σ₁ ⊕ σ₂), inferInstance, N.toNFA.toDFA
  subst hM₁ hM₂
  rw [NFA.toDFA_correct, εNFA.toNFA_correct]
  rw [← DFA.toNFA_correct, ← NFA.toεNFA_correct]
  rw [← DFA.toNFA_correct, ← NFA.toεNFA_correct]
  exact εNFA.accepts_concat

theorem IsRegular.kstar {L : Language α} (h : IsRegular L) : IsRegular (L∗) := by
  have ⟨σ, _, M, hM⟩ := h
  let N₁ := M.toNFA.toεNFA
  let N := εNFA.kstar N₁
  apply isRegular_iff.mpr
  use Set (Option σ), inferInstance, N.toNFA.toDFA
  subst hM
  rw [NFA.toDFA_correct, εNFA.toNFA_correct]
  rw [← DFA.toNFA_correct, ← NFA.toεNFA_correct]
  exact εNFA.accepts_kstar

end Language

namespace RegularExpression

/-- The language matched by a regular expression is a regular language. -/
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

end RegularExpression
