import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Computability.Language
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic

variable {α : Type*} [DecidableEq α]
-- An alphabet is a finite set of symbols / letters
def Alphabet α := Finset α
instance : Membership α (Alphabet α) := Finset.instMembership

-- Implement string structure w/ lists as underlying

-- e.g. w/ length, etc.
-- notation : "|" s : string "|"
-- def concat :
-- w/ ∘ notation
-- notation : ε = []

-- def occurs w a : Bool
-- <-> a ∈ w

-- def Alph w : Alphabet α := {x | x ∈ w}

-- [DecidablePred (· ∈ S)] just once?
def proj (S : Alphabet α) [DecidablePred (· ∈ S)] (w : List α) : List α :=
  match w with
  | [] => []
  | b :: u => if b ∈ S then b :: proj S u else proj S u

def cancel (w : List α) (a : α) :=
  match w with
  | [] => []
  | b :: u => if a = b then u else b :: (cancel u a)

-- cons list -> induction w with | cons u b IH

-- Lemma for [proj_cancel_comm]:
-- Cancelling with an element not in the set S does not change the projection
lemma cancelling_proj_mem_is_id (S : Finset α) (w : List α) (a : α) :
  (a ∉ S) -> (cancel (proj S w) a = proj S w) := by
  intro h
  -- Structural induction on strings as lists
  induction w with
  | nil => rfl
  | cons b u IH =>
    by_cases h_ab : a = b
    -- Case where a = b
    · rw [h_ab] at h
      simp [proj, h]
      exact IH
    -- Case where a ≠ b
    · by_cases h_bs : b ∈ S
      · simp [proj, h_bs]
        simp [cancel, h_ab]
        exact IH
      · simp [proj, h_bs]
        exact IH

lemma proj_cancel_comm (S : Finset α) (w : List α) (a : α) : -- (1.3)
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

def proj_lang (S : Finset α) (A : Language α) : Language α :=
  Set.image (proj S) A

def pref (w : List α) : Language α := {u : List α | ∃v, u ++ v = w}

-- see [Preorder] class

structure Dependency (α) [Fintype α] where
  r : α → α → Prop
  refl : ∀ x, r x x
  symm : ∀ {x y}, r x y → r y x


-- def trace_equivalence (D) :
-- such that
  -- {([x], [y]) | (x, y) ∈ I_D}
  -- follows monoid structure (axioms)
  -- transitively closed
  --
  -- -> (optional? prove is least congruence)
