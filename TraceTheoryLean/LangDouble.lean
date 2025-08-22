import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import Mathlib.Computability.NFA

universe u v
variable {α : Type u} {σ : Type v} {M : NFA α σ}

def str_double (w : List α) : List α :=
  match w with
  | [] => []
  | a :: u => a :: a :: str_double u

namespace Language

def double (L : Language α) : Language α := {str_double w | w ∈ L}

end Language

namespace NFA

variable (M) in
/-- If [M] recognizes a language [L], [M.double] is an NFA constructed
 such that it should recognize exactly [double L]. -/
def double : (NFA α (σ ⊕ (σ × α))) where
  step := fun st a =>
    match st with
    | Sum.inl s => {Sum.inr (s, a)}
    | Sum.inr (s, a') => { x | a = a' ∧ ∃ t, t ∈ M.step s a' ∧ x = Sum.inl t }
  start := M.start.image Sum.inl
  accept := M.accept.image Sum.inl

/-- Taking two steps [a, a] in [M.double] should lead to the same set of states
 as taking one step [a] in [M] (starting from any set of states) (with Sum.inl
 to correct the fact that the sets have different types). -/
lemma double_step_equal (a : α) (S : Set σ) :
  (M.stepSet S a).image Sum.inl = M.double.stepSet (M.double.stepSet (S.image Sum.inl) a) a := by
  simp [stepSet]
  simp [double]
  --- vvv  by LLM recommendation  vvv ---
  -- probably useful to get familiar with the kind of syntax below
  ext x
  simp
  constructor
  · -- Forward direction: x ∈ image of union → x ∈ union of images
    rintro ⟨t, ⟨s, hs, ht⟩, rfl⟩
    exact ⟨s, hs, t, ht, rfl⟩
  · -- Reverse direction: x ∈ union of images → x ∈ image of union
    rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨t, ⟨s, hs, ht⟩, rfl⟩

/-- Following [double w] in [M.double] should lead to the same set of states
 as following [w] in [M] (starting from any set of states). -/
lemma double_steps_equal {w : List α} :
  ∀ S : Set σ,
    Sum.inl '' M.evalFrom S w
    = M.double.evalFrom (Sum.inl '' S) (str_double w) := by
  induction w with
  | nil =>
    simp [str_double]
  | cons a u IH =>
    simp [str_double]
    intro s
    rw [<- M.double_step_equal a s]
    rw [IH]

/-- Evaluating [double w] in [M.double] should lead to the same set of states
 as evaluating [w] in [M]. -/
lemma double_eval_equal {w : List α} :
  (M.eval w).image Sum.inl = M.double.eval (str_double w) := by
  simp [eval]
  nth_rw 2 [double]
  simp
  rw [double_steps_equal]

/-- [M.double] accepts [double w] iff [M] accepts [w]. -/
lemma mem_iff_double_in_double_lang {w : List α} :
  (w ∈ M.accepts) <-> (str_double w ∈ M.double.accepts) := by
  simp [accepts]
  repeat rw [Set.mem_setOf]
  rw [<- double_eval_equal]
  simp [double]

/-- A generic induction principle for two-element induction on lists.
 Allows a List to be decomposed into cases
  | hnil
  | hsingle a
  | hcons a b u IH -/
theorem list_induction_two {α} {P : List α → Prop} (l : List α)
    (hnil : P [])
    (hsingle : ∀ a, P [a])
    (hcons : ∀ a b tail, P tail → P (a :: b :: tail)) : P l := by
  --- vvv  per LLM generation  vvv ---
  -- inducts on length of list
  have Q : ∀ (n : Nat) (l' : List α), l'.length = n → P l' := by
    intro n
    induction' n using Nat.strong_induction_on with n IH
    intro l' hlen
    match n with
    | 0 =>
        cases l' with
        | nil => exact hnil
        | cons a as => simp at hlen
    | 1 =>
        cases l' with
        | nil => simp at hlen
        | cons a as =>
          cases as with
          | nil => exact hsingle a
          | cons b bs => simp at hlen
    | n+2 =>
        cases l' with
        | nil => simp at hlen
        | cons a as =>
          cases as with
          | nil => simp at hlen
          | cons b tail =>
            apply hcons a b tail
            have : tail.length < (a :: b :: tail).length := by
              simp
              exact Nat.lt.step (Nat.lt_succ_self tail.length)
            rw [hlen] at this
            exact IH tail.length this tail rfl
  exact Q l.length l rfl

variable (M) in
@[simp]
theorem stepSets_empty (x : List α) :
  List.foldl M.stepSet ∅ x = ∅ := by
  induction x with
  | nil =>
    simp
  | cons a y IH =>
    simp [stepSet]
    exact IH

variable (M) in
/-- If [S] consists only of states in [M], taking two steps [a, a] in [M.double]
 leads only to states also in [M]. -/
lemma even_two_steps_to_even {S : Set σ} (a : α) :
  ∃ T : Set σ, Sum.inl '' T = M.double.stepSet (M.double.stepSet (Sum.inl '' S) a) a := by
  rw [<- double_step_equal]
  use M.stepSet S a

/-- If [w] leads from some set [S] (of only states in [M])
 to an accepted state in [M.double], [w] must be the double of a string. -/
lemma even_to_accepted_is_double {w : List α} :
  (∃ (S : Set σ), ∃ x ∈ M.accept, Sum.inl x ∈ M.double.evalFrom (Sum.inl '' S) w)
  -> ∃ j : List α, w = str_double j := by
  induction w using list_induction_two with
  | hnil => -- empty list, is double of []
    intro h
    use []
    simp [str_double]
  | hsingle a => -- singleton list, cannot lead to accepted states
    simp [double]
    simp [stepSet]
  | hcons a b u IH => -- list of 2+ elements a :: b :: u
    by_cases h_ab : a = b
    · rw [<- h_ab] -- case a = b, use IH
      /- if [a :: a :: u] leads from some set [S] to an accepted state,
       [u] leads from [M.double.step (M.double.step S a) a] to an accepted state
       so we can use [M.double.step (M.double.step S a) a] to satisfy IH condition. -/
      intro h
      simp at h
      obtain ⟨h_ex1, ⟨h_ex2, h⟩⟩ := h
      have ex : (∃ T : Set σ, Sum.inl '' T
      = (M.double.stepSet (M.double.stepSet (Sum.inl '' h_ex1) a) a)) := by
        simp [even_two_steps_to_even]
      obtain ⟨T, ex⟩ := ex
      rw [<- ex] at h
      have rh := by exact IH ⟨T, h_ex2, h⟩
      obtain ⟨j, h_double⟩ := rh
      use a :: j
      simp [str_double]
      exact h_double
    · simp [double, evalFrom, stepSet] -- case a ≠ b, cannot lead to accepted states
      simp [Ne.symm h_ab]

/-- If [w] is accepted by [M.double], [w] must be the double of a string. -/
lemma mem_of_double_lang_is_double {w : List α} :
  w ∈ M.double.accepts → ∃ j : List α, w = str_double j := by
  simp [accepts, eval]
  intro h
  rw [Set.mem_setOf] at h
  rcases h with h | h
  · have h_st : M.double.start = Sum.inl '' M.start := by simp [double]
    rw [h_st] at h
    apply M.even_to_accepted_is_double
    use M.start
    obtain ⟨a, h⟩ := h
    nth_rw 1 [double] at h
    simp at h
    use a
  · simp [double] at h -- impossible case

/-- The language accepted by [M.double] is the double of the language
 accepted by [M]. -/
theorem lang_of_double_is_double_of_lang {L : Language α} : -- Theorem-1
  L = M.accepts -> L.double = M.double.accepts := by
  intro h
  ext x
  constructor
  · -- x ∈ L.double → x ∈ M.double.accepts
    -- essentially proven by [mem_iff_double_in_double_lang]
    simp [Language.double]
    rw [Set.mem_setOf, h]
    intro h
    obtain ⟨w, ⟨h_w, h_d⟩⟩ := h
    rw [mem_iff_double_in_double_lang, h_d] at h_w
    exact h_w
  · -- x ∈ M.double.accepts → x ∈ L.double
    /- use [mem_of_double_lang_is_double] to prove
     that [M.double.accepts] contains only doubled-strings -/
    intro h_x
    have h_xd : ∃ j, x = str_double j := by
      apply mem_of_double_lang_is_double at h_x
      exact h_x
    obtain ⟨j, h_xd⟩ := h_xd
    /- then use [mem_iff_double_in_double_lang] to prove those
     strings have halves accepted by [M] -/
    rw [h_xd, <- mem_iff_double_in_double_lang] at h_x
    rw [h]
    simp [Language.double]
    rw [Set.mem_setOf]
    use j
    simp [h_x, h_xd]

-- Todo: Theorem 2

variable (M) in
def lang_half : (NFA α σ) where
  step := fun (s : σ) (a : α) => ⋃ x ∈ (M.step s a), M.step x a
  start := M.accept
  accept := M.start

end NFA

namespace Language

-- Theorem-1
-- If language [L] is regular, the language [double L] is regular.
protected theorem IsRegular.double {α : Type} [hf_α : Fintype α]
{L : Language α} (h : L.IsRegular) : L.double.IsRegular := by
  simp [IsRegular] at h
  simp [IsRegular]
  obtain ⟨σ, hNe, M, hAcc⟩ := h
  use Set (σ ⊕ (σ × α))
  -- prove (Set (σ ⊕ σ × α)) is nonempty & finite, so that it can
  -- be used as the state set of a DFA/NFA
  have h_dirsum : Nonempty (Fintype (Set (σ ⊕ σ × α))) := by
    have h_mem_σ : Fintype σ := Classical.choice hNe
    exact ⟨Fintype.ofFinite (Set (σ ⊕ σ × α))⟩
  use h_dirsum, M.toNFA.double.toDFA
  simp
  rw [NFA.lang_of_double_is_double_of_lang]
  simp
  rw [hAcc]

end Language
