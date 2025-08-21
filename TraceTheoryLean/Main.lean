import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Computability.Language
import Mathlib.Logic.Relation

variable {U : Type} [DecidableEq U]

def Alphabet U := Finset U

def proj (S : Finset U) (w : List U) : List U :=
  match w with
  | [] => []
  | b :: u => if b ∈ S then b :: proj S u else proj S u

def cancel (w : List U) (a : U) :=
  match w with
  | [] => []
  | b :: u => if a = b then u else b :: (cancel u a)

lemma cancelling_proj_mem_is_id (S : Finset U) (w : List U) (a : U) :
  (a ∉ S) -> (cancel (proj S w) a = proj S w) := by
  intro h
  induction w with
  | nil => rfl
  | cons b u IH =>
    by_cases h_ab : a = b
    · rw [h_ab] at h
      simp [proj, h]
      exact IH
    · by_cases h_bs : b ∈ S
      · simp [proj, h_bs]
        simp [cancel, h_ab]
        exact IH
      · simp [proj, h_bs]
        exact IH

lemma proj_cancel_comm (S : Finset U) (w : List U) (a : U) : -- (1.3)
  proj S (cancel w a) = cancel (proj S w) a := by
  induction w with
  | nil => rfl
  | cons b u IH =>
    by_cases h_bs : b ∈ S
    · simp [proj, h_bs]
      by_cases h_ab : a = b
      · simp [cancel, h_ab]
      · simp [cancel, h_ab]
        simp [proj, h_bs]
        exact IH
    · by_cases h_ab : a = b
      · simp [cancel, h_ab]
        simp [proj, h_bs]
        symm
        apply (cancelling_proj_mem_is_id S u b)
        exact h_bs
      · simp [cancel, h_ab]
        simp [proj, h_bs]
        exact IH

def proj_lang (S : Finset U) (A : Language U) : Language U :=
  Set.image (proj S) A

def pref (w : List U) : Language U := {u : List U | ∃v, u ++ v = w}

structure Dependency (α) [Fintype α] where
  r : α → α → Prop
  refl : ∀ x, r x x
  symm : ∀ {x y}, r x y → r y x
