import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Option

open Computability Set

variable {α : Type*}

namespace DFA

section epsilon

/-- DFA which accepts the language of only the empty string. -/
@[simps]
def epsilon : DFA α (Option Unit) where
  step := fun _ _ => none
  start := some ()
  accept := { some () }

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem accepts_epsilon : epsilon.accepts = (1 : Language α) := by
  ext x
  simp only [accepts, acceptsFrom, evalFrom]
  rw [Set.mem_ofPred]
  cases x with
  | nil => simp
  | cons a x' =>
    have h_dead : ∀ w : List α, List.foldl epsilon.step (none : Option Unit) w = none := by
      intro w
      induction w <;> simp_all
    simp_all

end epsilon

section singleton

/-- DFA which accepts the singleton language of `a`. -/
@[simps]
def char (a : α) [DecidableEq α] : DFA α (Option Bool) where
  step (ob : Option Bool) (x : α) := match ob with
    | some true  => none
    | some false => if x = a then some true else none
    | none       => none
  start := some false
  accept := { some true }

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem accepts_char {a : α} [DecidableEq α] : (char a).accepts = { [a] } := by
  ext x
  simp only [accepts, acceptsFrom, evalFrom]
  rw [Set.mem_ofPred, Set.mem_singleton_iff]
  cases x with
  | nil => simp
  | cons b x' =>
    cases x' with
    | nil => simp
    | cons c x'' =>
      have h_dead : ∀ w, List.foldl (char a).step none w = none := by
        intro w
        induction w <;> simp_all
      aesop

end singleton

end DFA

namespace εNFA

section concat

variable {σ₁ σ₂ : Type*}
variable {M₁ : εNFA α σ₁} {M₂ : εNFA α σ₂}
variable [DecidablePred (· ∈ M₁.accept)]

/-- εNFA which accepts the concatenation of the languages of `M₁` and `M₂`. -/
@[simps]
def concat (M₁ : εNFA α σ₁) (M₂ : εNFA α σ₂) [DecidablePred (· ∈ M₁.accept)] :
    εNFA α (σ₁ ⊕ σ₂) where
  step
    | Sum.inl q₁, some a => (M₁.step q₁ (some a)).image Sum.inl
    | Sum.inl q₁, none   =>
      (M₁.step q₁ none).image Sum.inl ∪
      (if q₁ ∈ M₁.accept then (M₂.start.image Sum.inr) else ∅)
    | Sum.inr q₂, oa      => (M₂.step q₂ oa).image Sum.inr
  start := M₁.start.image Sum.inl
  accept := M₂.accept.image Sum.inr

lemma IsPath.concat_lift_inl {s t : σ₁} {x : List (Option α)} (h : M₁.IsPath s t x) :
    (concat M₁ M₂).IsPath (Sum.inl s) (Sum.inl t) x := by
  induction h with
  | nil _ => exact (isPath_nil (concat M₁ M₂)).mpr rfl
  | cons t' s' u oa x' h_step h_path ih =>
    apply IsPath.cons (Sum.inl t') (Sum.inl s') (Sum.inl u)
    · cases oa <;> simpa
    · exact ih

lemma IsPath.concat_lift_inr {s t : σ₂} {x : List (Option α)} (h : M₂.IsPath s t x) :
    (concat M₁ M₂).IsPath (Sum.inr s) (Sum.inr t) x := by
  induction h with
  | nil _ => exact (isPath_nil (concat M₁ M₂)).mpr rfl
  | cons t' s' u _ _ h_step _ ih =>
    apply IsPath.cons (Sum.inr t') (Sum.inr s') (Sum.inr u)
    · simpa
    · exact ih

lemma IsPath.concat_proj_inr {s t : σ₂} {x : List (Option α)}
    (h : (concat M₁ M₂).IsPath (Sum.inr s) (Sum.inr t) x) : M₂.IsPath s t x := by
  generalize hs' : Sum.inr s = s' at h
  generalize ht' : Sum.inr t = t' at h
  induction h generalizing s with
  | nil u =>
    subst hs'
    simp_all
  | cons _ s'' t'' _ _ h_step _ ih =>
    subst hs' ht'
    simp only [concat, mem_image] at h_step
    rcases h_step with ⟨q, hq, rfl⟩
    apply IsPath.cons q s t
    · exact hq
    · simp [ih]

lemma IsPath.concat_split_inl_inr {s : σ₁} {t : σ₂} {x : List (Option α)}
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
      simp only [concat_step, mem_image] at h_step
      rcases h_step with ⟨q, hq, rfl⟩
      rcases ih rfl rfl with ⟨u, v, s_acc, s_start, hx', h_path_rest, h_acc, h_bridge, h_path_M₂⟩
      use some a :: u, v, s_acc, s_start
      and_intros
      · simp [hx']
      · exact cons q s s_acc (some a) u hq h_path_rest
      · exact h_acc
      · exact h_bridge
      · exact h_path_M₂
    | none =>
      simp only [concat_step, mem_union, mem_image, mem_ite_empty_right] at h_step
      rcases h_step with ⟨q, hq, rfl⟩ | ⟨hs, q, hq, rfl⟩
      · rcases ih rfl rfl with ⟨u, v, s_acc, s_start, hx', h_path_rest, h_acc, h_bridge, h_path_M₂⟩
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

@[simp]
theorem accepts_concat : (concat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  simp only [Language.mem_mul]
  constructor
  · intro h
    rcases (mem_accepts_iff_exists_path (concat M₁ M₂)).mp h with ⟨q₁, q₂, x', hq₁, hq₂, hx', hM⟩
    simp only [concat, mem_image] at hq₁ hq₂
    rcases hq₁ with ⟨s, hs, rfl⟩
    rcases hq₂ with ⟨t, ht, rfl⟩
    rcases IsPath.concat_split_inl_inr hM with
      ⟨u', v', s_acc, s_start, hx, h_path_M₁, h_acc_M₁, h_start_M₂, h_path_M₂⟩
    apply Language.mem_mul.mpr
    refine ⟨u'.reduceOption, ?_, v'.reduceOption, ?_, ?_⟩
    · apply (mem_accepts_iff_exists_path M₁).mpr
      use s, s_acc, u'
    · apply (mem_accepts_iff_exists_path M₂).mpr
      use s_start, t, v'
    · subst hx' hx
      simp [List.reduceOption_append, List.reduceOption_cons_of_none]
  · intro ⟨u, hu, v, hv, hx⟩
    rcases (mem_accepts_iff_exists_path M₁).mp hu with ⟨uq₁, uq₂, u', huq₁, huq₂, hu', hM₁⟩
    rcases (mem_accepts_iff_exists_path M₂).mp hv with ⟨vq₁, vq₂, v', hvq₁, hvq₂, hv', hM₂⟩
    apply (mem_accepts_iff_exists_path (concat M₁ M₂)).mpr
    use Sum.inl uq₁, Sum.inr vq₂, u' ++ [none] ++ v'
    and_intros
    · simpa
    · simpa
    · simp [List.reduceOption_append, hx, hu', hv']
    · simp only [isPath_append]
      use Sum.inr vq₁
      constructor
      · exact ⟨Sum.inl uq₂, IsPath.concat_lift_inl hM₁, by simp [huq₂, hvq₁]⟩
      · exact IsPath.concat_lift_inr hM₂

end concat

section kstar

variable {M : εNFA α σ}
variable [DecidablePred (· ∈ M.accept)]

/-- DFA which accepts the Kleene star of the language of `M`. -/
@[simps]
def kstar (M : εNFA α σ) [DecidablePred (· ∈ M.accept)] : εNFA α (Option σ) where
  step
    | none,   some _ => ∅
    | none,   none   => M.start.image some
    | some q, some a => (M.step q (some a)).image some
    | some q, none   =>
      (M.step q none).image some ∪
      (if q ∈ M.accept then M.start.image some else ∅)
  start := { none }
  accept := { none } ∪ M.accept.image some

lemma kstar_step_some (q : σ) (a : Option α) :
    (kstar M).step (some q) a =
    (M.step q a).image some ∪
    (if a = none ∧ q ∈ M.accept then M.start.image some else ∅) := by
  cases a <;> simp

lemma IsPath.kstar_lift_some {s t : σ} {x : List (Option α)} (h : M.IsPath s t x) :
    M.kstar.IsPath (some s) (some t) x := by
  induction h with
  | nil _ => exact (isPath_nil M.kstar).mpr rfl
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
  | nil => contradiction
  | cons y L' ih =>
    have hy := h_all y List.mem_cons_self
    have ⟨s, t, x, hs, ht, hy', hx⟩ := (mem_accepts_iff_exists_path M).mp hy
    subst hy'
    cases L' with
    | nil => exact ⟨s, some t, x, hs, by simpa, by simp, IsPath.kstar_lift_some hx⟩
    | cons z L'' =>
      have h_nonempty' : z :: L'' ≠ [] := by simp
      have h_all' : ∀ y ∈ z :: L'', y ∈ M.accepts := by aesop
      rcases ih h_nonempty' h_all' with ⟨s', q, x', hs', hq, hL'', hx'⟩
      refine ⟨s, q, x ++ [none] ++ x', hs, hq, ?_, ?_⟩
      · simp [hL'', List.reduceOption_append]
      · rw [List.append_assoc, isPath_append]
        use some t
        constructor
        · exact IsPath.kstar_lift_some hx
        · apply IsPath.cons (some s')
          · simp [ht, hs']
          · simpa

lemma IsPath.kstar_path_from_none {t : Option σ} {x : List (Option α)}
    (h : (kstar M).IsPath none t x) :
    t = none ∧ x = [] ∨
    ∃ s_start x',
      x = none :: x' ∧
      s_start ∈ M.start ∧
      (kstar M).IsPath (some s_start) t x' := by
  cases h with
  | nil _ => simp
  | cons _ _ _ oa _ h_step h_path =>
    cases oa with
    | some a => simpa
    | none =>
      simp only [kstar_step, mem_image] at h_step
      rcases h_step with ⟨s_start, hs_start, rfl⟩
      aesop

lemma IsPath.kstar_split_some {s t : σ} {x : List (Option α)}
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
      left
      subst hs
      exact ⟨[], by simp_all⟩
    | cons _ _ _ oa x' h_step h_path ih =>
      subst hs ht
      simp only [kstar_step_some, mem_union, mem_image, mem_ite_empty_right] at h_step
      rcases h_step with
        ⟨s_next, h_step_M, rfl⟩ |
        ⟨⟨rfl, hs_acc⟩, s_next, h_start, rfl⟩
      · rcases ih rfl rfl with
          ⟨y, hx'', hy⟩ |
          ⟨u, v, q_acc, q_next, rfl, hu, hq_acc, hq_next, hv, hlt⟩
        · left
          use oa :: y
          constructor
          · change ([oa] ++ y).reduceOption = ([oa] ++ x').reduceOption
            rw [List.reduceOption_append, hx'', ← List.reduceOption_append]
          · exact cons s_next s t oa y h_step_M hy
        · right
          use oa :: u, v, q_acc, q_next
          and_intros
          · simp
          · exact cons s_next s q_acc oa u h_step_M hu
          · exact hq_acc
          · exact hq_next
          · exact hv
          · simpa using Nat.lt_add_right 1 hlt
      · right
        use [], x', s, s_next
        and_intros
        · simp
        · exact (isPath_nil M).mpr rfl
        · exact hs_acc
        · exact h_start
        · exact h_path
        · simp

lemma IsPath.kstar_no_return {q : σ} {x : List (Option α)} :
    ¬ (kstar M).IsPath (some q) none x := by
  intro h
  generalize hq : some q = oq at h
  generalize hn : none = n at h
  induction h generalizing q with
  | nil =>
    cases hq
    cases hn
  | cons _ _ _ _ _ h_step _ ih =>
    subst hq hn
    simp only [kstar_step_some, mem_union, mem_image, mem_ite_empty_right] at h_step
    rcases h_step with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ih rfl rfl

lemma IsPath.kstar_exists_decomp {s t : σ} {x : List (Option α)}
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
      constructor
      · simpa
      · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        apply (mem_accepts_iff_exists_path M).mpr
        use s, t, x'
    · have hu_acc : u.reduceOption ∈ M.accepts := by
        apply (mem_accepts_iff_exists_path M).mpr
        use s, q_acc, u
      subst h_len
      rcases ih v.length hlt hv h_next rfl with ⟨L', hv', hL'⟩
      use u.reduceOption :: L'
      constructor
      · subst hx
        simp [hv', List.reduceOption_append]
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · simp [hu_acc, hy]
        · exact hL' y hy

@[simp]
theorem accepts_kstar : (kstar M).accepts = (M.accepts)∗ := by
  ext x
  constructor
  · intro h
    rcases (mem_accepts_iff_exists_path (kstar M)).mp h with
      ⟨s_start, s_end, x', h_start, h_end, hx', h_path⟩
    simp only [kstar, singleton_union, mem_singleton_iff] at h_start
    subst h_start
    simp only [Language.mem_kstar]
    simp only [kstar, singleton_union, mem_insert_iff, mem_image] at h_end
    rcases h_end with rfl | ⟨q_start, hq_start, rfl⟩
    · cases h_path with
      | nil _ =>
        use []
        simpa using hx'
      | cons t' s' u oa x'' h_step h_rest =>
        cases oa with
        | some a => simp at h_step
        | none =>
          exfalso
          simp only [kstar_step, mem_image] at h_step
          rcases h_step with ⟨y, _, rfl⟩
          exact IsPath.kstar_no_return h_rest
    · cases h_path with
      | cons t' s' u oa x'' h_step h_rest =>
        cases oa with
        | some a => simp at h_step
        | none =>
          simp only [kstar, singleton_union, mem_image] at h_step
          rcases h_step with ⟨u', hu', rfl⟩
          rcases IsPath.kstar_exists_decomp h_rest hu' hq_start with ⟨L, hx'', hL⟩
          exact ⟨L, by simp_all, hL⟩
  · intro h
    simp only [Language.mem_kstar] at h
    rcases h with ⟨L, hx, hL⟩
    apply (mem_accepts_iff_exists_path (kstar M)).mpr
    induction L generalizing x with
    | nil => exact ⟨none, none, [], by simp [hx]⟩
    | cons w L' ih =>
      expose_names
      have h_nonempty : w :: L' ≠ [] := by simp
      rcases kstar_exists_path_some (w :: L') h_nonempty hL with ⟨s, q, x', hs, hq, hL', hx'⟩
      use none, q, none :: x'
      and_intros
      · simp
      · exact hq
      · simp [hx, hL']
      · apply IsPath.cons (some s)
        · simpa
        · exact hx'

end kstar

end εNFA

namespace Language

/-- The empty language is regular. -/
theorem IsRegular.zero : IsRegular (0 : Language α) :=
  ⟨Unit, inferInstance, ⟨fun _ _ => (), (), {}⟩, rfl⟩

/-- The language of only the empty string is regular. -/
theorem IsRegular.one : IsRegular (1 : Language α) :=
  ⟨Option Unit, inferInstance, DFA.epsilon, DFA.accepts_epsilon⟩

/-- The language of all strings over an alpabet is regular. -/
theorem IsRegular.top : IsRegular (⊤ : Language α) := by
  rw [← compl_bot, bot_eq_zero]
  apply IsRegular.compl
  exact IsRegular.zero

/-- The language of only a single symbol is regular. -/
theorem IsRegular.singleton {a : α} : IsRegular ({ [a] }) := by
  classical
  exact ⟨Option Bool, inferInstance, DFA.char a, DFA.accepts_char⟩

/-- Regular languages are closed under concatenation. -/
theorem IsRegular.mul {L₁ L₂ : Language α} (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) :
    IsRegular (L₁ * L₂) := by
  classical
  have ⟨σ₁, _, M₁, hM₁⟩ := h₁
  have ⟨σ₂, _, M₂, hM₂⟩ := h₂
  let M := εNFA.concat M₁.toNFA.toεNFA M₂.toNFA.toεNFA
  exact ⟨Set (σ₁ ⊕ σ₂), inferInstance, M.toNFA.toDFA, by aesop⟩

/-- Regular languages are closed under Kleene star. -/
theorem IsRegular.kstar {L : Language α} (h : IsRegular L) : IsRegular L∗ := by
  classical
  have ⟨σ, _, M, hM⟩ := h
  let M := εNFA.kstar M.toNFA.toεNFA
  exact ⟨Set (Option σ), inferInstance, M.toNFA.toDFA, by aesop⟩

end Language

namespace RegularExpression

/-- The language matched by a regular expression is a regular language. -/
theorem IsRegular.matches' (P : RegularExpression α) : Language.IsRegular (P.matches') := by
  induction P with
  | zero             => simp [Language.IsRegular.zero]
  | epsilon          => simp [Language.IsRegular.one]
  | char             => simp [Language.IsRegular.singleton]
  | plus _ _ ih₁ ih₂ => simp only [RegularExpression.matches', Language.IsRegular.add ih₁ ih₂]
  | comp _ _ ih₁ ih₂ => simp [Language.IsRegular.mul ih₁ ih₂]
  | star _ ih        => simp [Language.IsRegular.kstar ih]

set_option backward.isDefEq.respectTransparency false in
theorem matches'_sum_map {α : Type*} (L : List α) (f : α → RegularExpression α) :
    (L.map f).sum.matches' = ⋃ x ∈ L, (f x).matches' := by
  induction L with
  | nil => simp [Language.zero_def]
  | cons b L' ih =>
    simp only [List.map_cons, List.sum_cons, matches', add_eq_sup, List.mem_cons,
      iUnion_iUnion_eq_or_left, ih]
    rfl

theorem mem_matches'_mul_star_mul {R_to R_loop R_from : RegularExpression α} {w : List α} :
    w ∈ (R_to * R_loop.star * R_from).matches' ↔
    ∃ w₁ w₂ w₃, w = w₁ ++ w₂ ++ w₃ ∧
                w₁ ∈ R_to.matches' ∧
                w₂ ∈ R_loop.star.matches' ∧
                w₃ ∈ R_from.matches' := by
  simp only [matches'_mul, Language.mem_mul]
  constructor
  · rintro ⟨u, ⟨w₁, hw₁, w₂, hw₂, rfl⟩, w₃, hw₃, rfl⟩
    use w₁, w₂, w₃
  · rintro ⟨w₁, w₂, w₃, rfl, hw₁, hw₂, hw₃⟩
    exact ⟨w₁ ++ w₂, ⟨w₁, hw₁, w₂, hw₂, rfl⟩, w₃, hw₃, rfl⟩

theorem mem_matches'_star_concat {R : RegularExpression α} {w₁ w₂ : List α}
    (h₁ : w₁ ∈ R.star.matches') (h₂ : w₂ ∈ R.star.matches') :
    w₁ ++ w₂ ∈ R.star.matches' := by
  rw [matches'_star, Language.mem_kstar] at *
  rcases h₁ with ⟨L₁, rfl, hL₁⟩
  rcases h₂ with ⟨L₂, rfl, hL₂⟩
  exact ⟨L₁ ++ L₂, by simp, List.forall_mem_append.mpr ⟨hL₁, hL₂⟩⟩

theorem mem_matches'_star {R : RegularExpression α} {w : List α}
    (h : w ∈ R.matches') : w ∈ R.star.matches' := by
  rw [matches'_star, Language.mem_kstar]
  exact ⟨[w], by simpa⟩

end RegularExpression

namespace εNFA

section toSingleεNFA

variable {σ : Type*}
variable {α : Type*}
variable {M : εNFA α σ}
variable [DecidablePred (· ∈ M.accept)]

/-- The extended state space with a new start state and accept state. -/
inductive ExtendedState (σ : Type*)
  | start : ExtendedState σ
  | accept : ExtendedState σ
  | state (s : σ) : ExtendedState σ
  deriving DecidableEq, Fintype

variable (M) in
/-- Transform any `εNFA` into an `εNFA` with a single start state and accept state. -/
@[simps]
def toSingleεNFA : εNFA α (ExtendedState σ) where
  step
    | .start, some _   => ∅
    | .start, none     => (M.start).image .state
    | .accept, _       => ∅
    | .state s, some a => (M.step s (some a)).image .state
    | .state s, none   =>
      (M.step s none).image .state ∪
      if s ∈ M.accept then { ExtendedState.accept } else ∅
  start := { .start }
  accept := { .accept }

theorem IsPath.toSingleεNFA_lift_extendedState {s t : σ} {x : List (Option α)}
    (h : M.IsPath s t x) :
    M.toSingleεNFA.IsPath (.state s) (.state t) x := by
  induction h with
  | nil _ => simp
  | cons t' s' u oa x' h_step h_path ih =>
    apply cons (ExtendedState.state t') (.state s') (.state u)
    · cases oa <;> simpa
    · exact ih

theorem IsPath.from_accept {u : ExtendedState σ} {x : List (Option α)}
    (h : M.toSingleεNFA.IsPath .accept u x) :
    u = .accept ∧ x = [] := by
  cases h with
  | nil => simp
  | cons _ _ _ _ _ h_step _ => simp at h_step

theorem IsPath.state_accept {s : σ} {x : List (Option α)}
    (h : M.toSingleεNFA.IsPath (.state s) .accept x) :
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
      simp only [toSingleεNFA_step, mem_image] at h_step
      rcases h_step with ⟨t, ht, rfl⟩
      rcases ih rfl rfl with ⟨t', x'', ht', rfl, h_before⟩
      exact ⟨t', some a :: x'', ht', by simp, cons t s t' (some a) x'' ht h_before⟩
    | none =>
      simp only [toSingleεNFA_step, mem_union, mem_image, mem_ite_empty_right,
        mem_singleton_iff] at h_step
      rcases h_step with ⟨t, ht, rfl⟩ | ⟨hs, rfl⟩
      · rcases ih rfl rfl with ⟨t', x'', ht', hx'', h_before⟩
        exact ⟨t', none :: x'', ht', by simpa, cons t s t' none x'' ht h_before⟩
      · rcases IsPath.from_accept h_path with ⟨_, rfl⟩
        exact ⟨s, [], by simpa⟩

theorem accepts_toSingleεNFA : M.toSingleεNFA.accepts = M.accepts := by
  ext x
  constructor
  · intro h
    apply (mem_accepts_iff_exists_path M).mpr
    rcases (mem_accepts_iff_exists_path (M.toSingleεNFA)).mp h with
      ⟨s₁, s₂, x', hs₁, hs₂, rfl, h_path⟩
    simp only [toSingleεNFA_start, mem_singleton_iff, toSingleεNFA_accept] at hs₁ hs₂
    subst hs₁ hs₂
    cases h_path with
    | cons t' s' u oa x'' h_step h_rest =>
      cases oa with
      | some a => simp at h_step
      | none =>
        simp only [toSingleεNFA_step, mem_image] at h_step
        rcases h_step with ⟨s, hs, rfl⟩
        rcases IsPath.state_accept h_rest with ⟨t, y, ht, rfl, h_before⟩
        exact ⟨s, t, y, hs, ht, by simp [List.reduceOption_append], h_before⟩
  · intro h
    apply (mem_accepts_iff_exists_path (M.toSingleεNFA)).mpr
    rcases (mem_accepts_iff_exists_path M).mp h with ⟨s₁, s₂, x', hs₁, hs₂, rfl, hx'⟩
    use .start, .accept, [none] ++ x' ++ [none]
    and_intros
    · simp
    · simp
    · simp [List.reduceOption_append]
    · simp only [isPath_append]
      exact ⟨.state s₂, ⟨.state s₁, by simpa, IsPath.toSingleεNFA_lift_extendedState hx'⟩, by simpa⟩

end toSingleεNFA

section Kleene

open RegularExpression

variable {σ : Type*} [FinEnum σ]
variable {α : Type*} [Fintype α] [LinearOrder α]
variable {M : εNFA α (ExtendedState σ)}
variable [∀ q oa q', Decidable (q' ∈ M.step q oa)]

local notation "n" => FinEnum.card (ExtendedState σ)

/-- An equivalence mapping the extended state space `ExtendedState σ` to the disjoint union
`Sum (Fin 2) σ`. This is a helper used to derive the `FinEnum` instance for `ExtendedState σ`. -/
def ExtendedState.equivSum (σ : Type*) : ExtendedState σ ≃ Sum (Fin 2) σ where
  toFun := fun
    | .start   => .inl 0
    | .accept  => .inl 1
    | .state s => .inr s
  invFun := fun
    | .inl ⟨0, _⟩ => .start
    | .inl ⟨1, _⟩ => .accept
    | .inl _      => .start
    | .inr s      => .state s
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with ⟨_ | _ | _⟩ | s
    all_goals first | rfl | contradiction

set_option linter.overlappingInstances false in
instance [FinEnum σ] : FinEnum (ExtendedState σ) :=
  FinEnum.ofEquiv (Sum (Fin 2) σ) (ExtendedState.equivSum σ)

/-- The bijection indexing every state in the extended NFA with a unique integer in `Fin n`.
This allows `pathRegex` to implement Kleene's algorithm. -/
def e : ExtendedState σ ≃ Fin n := FinEnum.equiv

variable (M) in
/-- The regex matching the union of all single symbols that results in a single transition from a
state indexed `i` to a state indexed `j` and the empty string if there also exists an epsilon
transition. -/
def directRegex (i j : Fin n) : RegularExpression α :=
  let char_transitions : RegularExpression α :=
    (Finset.univ.sort.map (fun a =>
      if (e.symm j) ∈ M.step (e.symm i) (some a) then char a else 0
    )).sum
  let epsilon_transitions : RegularExpression α :=
    if (e.symm j) ∈ M.step (e.symm i) none ∨ i = j then 1 else 0
  char_transitions + epsilon_transitions

set_option backward.isDefEq.respectTransparency false in
theorem mem_matches'_directRegex {i j : Fin n} {x : List α} :
    x ∈ (M.directRegex i j).matches' ↔
    (∃ a, x = [a] ∧ e.symm j ∈ M.step (e.symm i) (some a)) ∨
    (x = [] ∧ ((e.symm j ∈ M.step (e.symm i) none) ∨ i = j)) := by
  simp only [directRegex, matches'_add, Language.mem_add, matches'_sum_map, Finset.mem_sort,
    Finset.mem_univ, iUnion_true]
  constructor
  · rintro (⟨s, ⟨a, ha⟩, hx⟩ | hε)
    · left
      simp only at ha
      subst ha
      split_ifs at hx with h_step
      · simp only [matches'] at hx
        exact ⟨a, mem_singleton_iff.mp hx, h_step⟩
      · simp [Language.zero_def] at hx
    · right
      split_ifs at hε with h_step
      · simp only [matches', Language.mem_one] at hε
        rcases h_step with h_step | rfl
        · exact ⟨hε, Or.inl h_step⟩
        · simp [hε]
      · simp [Language.zero_def] at hε
        contradiction
  · rintro (⟨a, rfl, h_step⟩ | ⟨rfl, h_step⟩)
    · left
      apply Set.mem_iUnion.mpr
      use a
      simp [h_step]
      rfl
    · right
      simp [h_step]


variable (M) in
/-- The regex matching all words that result in a path from a state indexed `i` to a state indexed
`j` using no intermediate state with index greater than or equal to `k`.

Implements Kleene's algorithm for computing the regex. -/
@[simp]
def pathRegex (k : ℕ) (i j : Fin n) : RegularExpression α :=
  match k, i, j with
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

theorem pathRegex_mono {k k' : ℕ} {i j : Fin n} {x : List α}
    (hle : k ≤ k') (h : x ∈ (pathRegex M k i j).matches') :
    x ∈ (pathRegex M k' i j).matches' := by
  induction hle with
  | refl => exact h
  | step hn ih =>
    simp only [pathRegex]
    split_ifs
    · exact Or.inr ih
    · exact ih

theorem pathRegex_trans {k : ℕ} {i j m : Fin n} (hm : m.val < k)
    {x₁ x₂ : List α}
    (h₁ : x₁ ∈ (pathRegex M k i m).matches')
    (h₂ : x₂ ∈ (pathRegex M k m j).matches') :
    x₁ ++ x₂ ∈ (pathRegex M k i j).matches' := by
  induction k generalizing i j m x₁ x₂ with
  | zero => contradiction
  | succ k' ih =>
    simp only [pathRegex] at *
    split_ifs at * with hk'
    · rw [matches'_add, Language.mem_add, mem_matches'_mul_star_mul] at *
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm | rfl
      <;> rcases h₁ with ⟨y₁, y₂, y₃, rfl, hy₁, hy₂, hy₃⟩ | h_old₁
      <;> rcases h₂ with ⟨z₁, z₂, z₃, rfl, hz₁, hz₂, hz₃⟩ | h_old₂
      · left
        refine ⟨y₁, y₂ ++ y₃ ++ z₁ ++ z₂, z₃, by simp, hy₁, ?_, hz₃⟩
        have h₁ := ih hm hy₃ hz₁
        have h₂ := mem_matches'_star_concat hy₂ (mem_matches'_star h₁)
        rw [← List.append_assoc] at h₂
        exact mem_matches'_star_concat h₂ hz₂
      · left
        exact ⟨y₁, y₂, y₃ ++ x₂, by simp, hy₁, hy₂, ih hm hy₃ h_old₂⟩
      · left
        exact ⟨x₁ ++ z₁, z₂, z₃, by simp, ih hm h_old₁ hz₁, hz₂, hz₃⟩
      · right
        exact ih hm h_old₁ h_old₂
      · left
        refine ⟨y₁, y₂ ++ y₃ ++ z₁ ++ z₂, z₃, by simp, hy₁, ?_, hz₃⟩
        have h₁ := mem_matches'_star_concat hy₂ (mem_matches'_star hy₃)
        have h₂ := mem_matches'_star_concat h₁ (mem_matches'_star hz₁)
        exact mem_matches'_star_concat h₂ hz₂
      · left
        refine ⟨y₁, y₂ ++ y₃, x₂, by simp, hy₁, ?_, h_old₂⟩
        exact mem_matches'_star_concat hy₂ (mem_matches'_star hy₃)
      · left
        refine ⟨x₁, z₁ ++ z₂, z₃, by simp, h_old₁, ?_, hz₃⟩
        exact mem_matches'_star_concat (mem_matches'_star hz₁) hz₂
      · left
        exact ⟨x₁, [], x₂, by simp, h_old₁, ⟨[], rfl, by simp⟩, h_old₂⟩
    · rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm | rfl
      · exact ih hm h₁ h₂
      · simp at hk'

variable (M) in
/-- A path in the NFA restricted to intermediate states < k. -/
inductive IsRestrictedPath (k : ℕ) : Fin n → Fin n → List (Option α) → Prop
  | nil (i: Fin n) : IsRestrictedPath k i i []
  | step (i j : Fin n) (oa : Option α) :
      e.symm j ∈ M.step (e.symm i) oa →
      IsRestrictedPath k i j [oa]
  | trans (i j m : Fin n) (x₁ x₂ : List (Option α)) :
      IsRestrictedPath k i m x₁ →
      m.val < k →
      IsRestrictedPath k m j x₂ →
      IsRestrictedPath k i j (x₁ ++ x₂)

omit [Fintype α] [LinearOrder α] [∀ q oa q', Decidable (q' ∈ M.step q oa)] in
theorem isRestrictedPath_iff_isPath {i j : Fin n} {x : List (Option α)} :
    M.IsRestrictedPath n i j x ↔ M.IsPath (e.symm i) (e.symm j) x := by
  constructor
  · intro h
    induction h with
    | nil _ => exact (isPath_nil M).mpr rfl
    | step _ _ _ ih => exact IsPath.singleton M ih
    | trans _ _ m _ _ _ _ _ ih₁ ih₂ =>
      rw [isPath_append]
      use e.symm m
  · intro h
    generalize hs : e.symm i = s at h
    generalize hu : e.symm j = u at h
    induction h generalizing i with
    | nil _ =>
      subst hs
      rw [Equiv.apply_eq_iff_eq] at hu
      subst hu
      exact IsRestrictedPath.nil j
    | cons t s' u' oa x' h_step h_path ih =>
      subst hs hu
      rw [← List.singleton_append]
      apply IsRestrictedPath.trans (m := e t)
      · apply IsRestrictedPath.step
        simp [h_step]
      · exact (e t).isLt
      · exact ih (Equiv.symm_apply_apply _ _) rfl

variable (M) in
/-- A match by a path regex in the NFA restricted to intermediate states < k. -/
inductive IsRestrictedMatch (k : ℕ) : Fin n → Fin n → List α → Prop
  | direct (i j : Fin n) (x : List α) :
      x ∈ (directRegex M i j).matches' →
      IsRestrictedMatch k i j x
  | trans (i j m : Fin (n)) (x₁ x₂ : List α) :
      IsRestrictedMatch k i m x₁ →
      m.val < k →
      IsRestrictedMatch k m j x₂ →
      IsRestrictedMatch k i j (x₁ ++ x₂)

theorem isRestrictedMatch_nil {k : ℕ} {i : Fin n} : M.IsRestrictedMatch k i i [] := by
  apply IsRestrictedMatch.direct
  rw [mem_matches'_directRegex]
  right
  simp

theorem isRestrictedMatch_iff_exists_isRestrictedPath
    {k : ℕ} {i j : Fin n} {x : List α} :
    M.IsRestrictedMatch k i j x ↔
    ∃ y, y.reduceOption = x ∧ M.IsRestrictedPath k i j y := by
  constructor
  · intro h
    induction h with
    | direct i' j' x' h_match =>
      rw [mem_matches'_directRegex] at h_match
      rcases h_match with ⟨a, rfl, h_step⟩ | ⟨rfl, h_step | rfl⟩
      · exact ⟨[a], by simpa using IsRestrictedPath.step i' j' (some a) h_step⟩
      · exact ⟨[none], by simpa using IsRestrictedPath.step i' j' none h_step⟩
      · exact ⟨[], by simpa using IsRestrictedPath.nil i'⟩
    | trans i' j' m y₁ y₂ h₁ hlt h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨x₁, rfl, hx₁⟩
      rcases ih₂ with ⟨x₂, rfl, hx₂⟩
      exact ⟨x₁ ++ x₂, by rw [List.reduceOption_append],
        IsRestrictedPath.trans i' j' m x₁ x₂ hx₁ hlt hx₂⟩
  · rintro ⟨y, rfl, h⟩
    induction h with
    | nil i' => exact isRestrictedMatch_nil
    | step i' j' oa h_step =>
      apply IsRestrictedMatch.direct
      rw [mem_matches'_directRegex]
      cases oa with
      | some a => exact Or.inl ⟨a, rfl, h_step⟩
      | none   => exact Or.inr ⟨rfl, Or.inl h_step⟩
    | trans i' j' m x₁ x₂ hx₁ hlt hx₂ ih₁ ih₂ =>
      rw [List.reduceOption_append]
      exact IsRestrictedMatch.trans i' j' m x₁.reduceOption x₂.reduceOption ih₁ hlt ih₂

theorem isRestrictedMatch_iff_exists_isPath {i j : Fin n} {x : (List α)} :
    IsRestrictedMatch M n i j x ↔
    ∃ y : List (Option α),
      y.reduceOption = x ∧
      M.IsPath (e.symm i) (e.symm j) y := by
  rw [isRestrictedMatch_iff_exists_isRestrictedPath]
  simp_rw [isRestrictedPath_iff_isPath]

theorem IsRestrictedMatch.mono {k k' : ℕ} {i j : Fin n} {w : List α}
    (h : IsRestrictedMatch M k i j w) (hle : k ≤ k') : IsRestrictedMatch M k' i j w := by
  induction h with
  | direct i' j' x hx => exact direct i' j' x hx
  | trans i' j' m x₁ x₂ _ hlt _ ih₁ ih₂ =>
    exact trans i' j' m x₁ x₂ ih₁ (lt_of_lt_of_le hlt hle) ih₂

lemma isRestrictedMatch_star {k : ℕ} {m : Fin n} {w : List α}
    (h : w ∈ (pathRegex M k m m).star.matches')
    (ih : ∀ {x}, x ∈ (pathRegex M k m m).matches' → IsRestrictedMatch M k m m x)
    (hm : m.val < k + 1) :
    IsRestrictedMatch M (k + 1) m m w := by
  rw [matches'_star, Language.mem_kstar] at h
  rcases h with ⟨L, rfl, hL⟩
  induction L with
  | nil => exact isRestrictedMatch_nil
  | cons z L' ih' =>
    simp only [List.forall_mem_cons] at hL
    apply IsRestrictedMatch.trans m m m
    · exact IsRestrictedMatch.mono (ih hL.left) (Nat.le_succ k)
    · exact hm
    · exact ih' hL.right

lemma isRestrictedMatch_of_mem_pathRegex {k : ℕ} {i j : Fin n} {w : List α}
    (h : w ∈ (pathRegex M k i j).matches') :
    IsRestrictedMatch M k i j w := by
  induction k generalizing i j w with
  | zero =>
    apply IsRestrictedMatch.direct
    simp_all
  | succ k' ih =>
    simp only [pathRegex] at h
    split_ifs at h with hlt
    · rw [matches'_add, Language.mem_add, mem_matches'_mul_star_mul] at h
      rcases h with ⟨w₁, w₂, w₃, rfl, hw₁, hw₂, hw₃⟩ | h_old
      · apply IsRestrictedMatch.trans (m := ⟨k', hlt⟩)
        · apply IsRestrictedMatch.trans (m := ⟨k', hlt⟩)
          · exact IsRestrictedMatch.mono (ih hw₁) (Nat.le_succ k')
          · simp
          · exact isRestrictedMatch_star hw₂ ih (lt_add_one _)
        · simp
        · exact IsRestrictedMatch.mono (ih hw₃) (Nat.le_succ k')
      · exact IsRestrictedMatch.mono (ih h_old) (Nat.le_succ k')
    · exact IsRestrictedMatch.mono (ih h) (Nat.le_succ k')

lemma mem_pathRegex_of_isRestrictedMatch {k : ℕ} {i j : Fin n} {w : List α}
    (h : IsRestrictedMatch M k i j w) :
    w ∈ (pathRegex M k i j).matches' := by
  induction h with
  | direct i' j' x hx => exact pathRegex_mono (Nat.zero_le k) hx
  | trans i' j' m x₁ x₂ hx₁ hlt hx₂ ih₁ ih₂ => exact pathRegex_trans hlt ih₁ ih₂

theorem mem_pathRegex_iff_isRestrictedMatch {k : ℕ} {i j : Fin n} {w : List α} :
    w ∈ (pathRegex M k i j).matches' ↔ IsRestrictedMatch M k i j w :=
  ⟨isRestrictedMatch_of_mem_pathRegex, mem_pathRegex_of_isRestrictedMatch⟩

instance {M : εNFA α σ}
    [DecidablePred (· ∈ M.start)]
    [DecidablePred (· ∈ M.accept)]
    [∀ q oa q', Decidable (q' ∈ M.step q oa)]
    (q : ExtendedState σ) (oa : Option α) (q' : ExtendedState σ) :
    Decidable (q' ∈ M.toSingleεNFA.step q oa) := by
  cases q <;> cases oa
  <;> simp only [toSingleεNFA_step, mem_union, mem_image, mem_ite_empty_right, mem_singleton_iff]
  <;> infer_instance

/-- The regular expression that matches the language of `M`. -/
def toRegex (M : εNFA α σ)
    [∀ q oa q', Decidable (q' ∈ M.step q oa)]
    [DecidablePred (· ∈ M.start)]
    [DecidablePred (· ∈ M.accept)] :
    RegularExpression α :=
  pathRegex M.toSingleεNFA n (e .start) (e .accept)

theorem accepts_toRegex (M : εNFA α σ)
    [∀ q oa q', Decidable (q' ∈ M.step q oa)]
    [DecidablePred (· ∈ M.start)]
    [DecidablePred (· ∈ M.accept)] :
    (toRegex M).matches' = M.accepts := by
  ext x
  unfold toRegex
  rw [mem_pathRegex_iff_isRestrictedMatch, isRestrictedMatch_iff_exists_isPath,
    ← accepts_toSingleεNFA, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    mem_accepts_iff_exists_path]
  simp

end Kleene

end εNFA
