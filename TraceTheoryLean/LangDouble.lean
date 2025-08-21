import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import Mathlib.Computability.NFA
import Mathlib.Logic.Relation

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
def double : (NFA α (σ ⊕ (σ × α))) where
  step := fun st a =>
    match st with
    | Sum.inl s => {Sum.inr (s, a)}
    | Sum.inr (s, a') => { x | a = a' ∧ ∃ t, t ∈ M.step s a' ∧ x = Sum.inl t }
  start := M.start.image Sum.inl
  accept := M.accept.image Sum.inl

lemma double_step_equal (a : α) (S : Set σ) :
  (M.stepSet S a).image Sum.inl = M.double.stepSet (M.double.stepSet (S.image Sum.inl) a) a := by
  simp [stepSet]
  simp [double]
  --- vvv  by LLM recommendation  vvv ---
  ext x
  simp
  constructor
  · -- Forward direction: x ∈ image of union → x ∈ union of images
    rintro ⟨t, ⟨s, hs, ht⟩, rfl⟩
    exact ⟨s, hs, t, ht, rfl⟩ -- probably useful to get used to this syntax
  · -- Reverse direction: x ∈ union of images → x ∈ image of union
    rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨t, ⟨s, hs, ht⟩, rfl⟩

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

lemma double_eval_equal {w : List α} :
  (M.eval w).image Sum.inl = M.double.eval (str_double w) := by
  simp [eval]
  nth_rw 2 [double]
  simp
  rw [double_steps_equal]

lemma mem_iff_double_in_double_lang {w : List α} :
  (w ∈ M.accepts) <-> (str_double w ∈ M.double.accepts) := by
  simp [accepts]
  repeat rw [Set.mem_setOf]
  rw [<- double_eval_equal]
  simp [double]

--- vvv  per LLM generation  vvv ---
theorem list_induction_two {α} {P : List α → Prop} (l : List α)
    (hnil : P [])
    (hsingle : ∀ a, P [a])
    (hcons : ∀ a b tail, P tail → P (a :: b :: tail)) : P l := by
  -- Generic induction principle for two-element induction on lists
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
theorem stepSets_empty (x : List α) : List.foldl M.stepSet ∅ x = ∅ := by
  induction x with
  | nil =>
    simp
  | cons a y IH =>
    simp [stepSet]
    exact IH

/-variable (M) in
lemma no_even_two_steps_to_no_even {S : Set (σ ⊕ (σ × α))} (a : α) :
  (∃ x : σ, Sum.inl x ∈ M.double.stepSet (M.double.stepSet S a) a)
  -> (∃ x : σ, Sum.inl x ∈ S) := by
    simp [double, stepSet]
    by_cases h_empt : ∃ p, Sum.inl p ∈ S
    · simp [h_empt]
    · intro _ p h
      exfalso
      apply h_empt
      use p
-/

variable (M) in
lemma even_two_steps_to_even {S : Set σ} (a : α) :
  ∃ T : Set σ, Sum.inl '' T = M.double.stepSet (M.double.stepSet (Sum.inl '' S) a) a := by
  rw [<- double_step_equal]
  use M.stepSet S a

lemma mem_of_double_lang_is_double {w : List α} :
  (∃ (S : Set σ), ∃ x ∈ M.accept, Sum.inl x ∈ M.double.evalFrom (Sum.inl '' S) w)
  -> ∃ j : List α, w = str_double j := by
  induction w using list_induction_two with
  | hnil =>
    intro h
    use []
    simp [str_double]
  | hsingle a =>
    simp [double]
    simp [stepSet]
  | hcons a b u IH =>
    by_cases h_ab : a = b
    · rw [<- h_ab]
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
    · simp [double, evalFrom, stepSet]
      simp [Ne.symm h_ab]

theorem lang_of_double_is_double_of_lang {L : Language α} : -- Theorem-1
  L = M.accepts -> L.double = M.double.accepts := by
  intro h
  simp [Language.double]
  sorry

-- Todo

variable (M) in
def lang_half : (NFA α σ) where
  step := fun (s : σ) (a : α) => ⋃ x ∈ (M.step s a), M.step x a
  start := M.accept
  accept := M.start

end NFA

namespace Language

protected theorem IsRegular.double {L : Language α} (h : L.IsRegular) : L.double.IsRegular :=
  sorry

end Language
