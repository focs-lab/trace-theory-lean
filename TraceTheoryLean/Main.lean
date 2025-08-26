import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Computability.Language
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic

variable {α : Type*} [DecidableEq α]
-- An alphabet is a finite set of symbols / letters

abbrev Alphabet α := Finset α

/-
def Alphabet α := Finset α
instance : Membership α (Alphabet α) := Finset.instMembership
instance (a : α) (S : Alphabet α) : Decidable (a ∈ S) := Finset.decidableMem a S
-/

namespace RString

-- Implement string structure w/ lists as underlying

-- e.g.
-- length notation : "|" s : string "|"
-- occurs notation "∈"

-- def Alph w : Alphabet α := {x | x ∈ w}

inductive String (α : Type*) where
  | nil : String α
  | snoc (s : String α) (a : α) : String α

notation "ε" => String.nil
infixl:67 " :: " => String.snoc

def proj (S : Alphabet α) (w : String α) : String α :=
  match w with
  | ε => ε
  | u :: b => if b ∈ S then proj S u :: b else proj S u

def cancel (w : String α) (a : α) :=
  match w with
  | ε => ε
  | u :: b => if a = b then u else (cancel u a) :: b

-- Lemma for [proj_cancel_comm]:
-- Cancelling with an element not in the set S does not change the projection
lemma cancelling_proj_mem_is_id (S : Finset α) (w : String α) (a : α) :
  (a ∉ S) -> (cancel (proj S w) a = proj S w) := by
  intro h
  -- Structural induction on strings as lists
  induction w with
  | nil => rfl
  | snoc u b IH =>
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

lemma proj_cancel_comm (S : Finset α) (w : String α) (a : α) : -- (1.3)
  proj S (cancel w a) = cancel (proj S w) a := by
  induction w with
  | nil => rfl
  | snoc u b IH =>
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

/-- Auxiliary for `List.reverse`. `List.reverseAux l r = l.reverse ++ r`,
but it is defined directly. -/
def reverseAux : String α → String α → String α
  | ε, r      => r
  | u :: a, r => reverseAux u (r :: a)

def reverse (w : String α) : String α := reverseAux w ε

-- protected def concat
def concat : (xs ys : String α) → String α
  | as, ε       => as
  | as, bs :: b => (RString.concat as bs) :: b

/- consider tail-recursive concatenation

def appendTR (as bs : List α) : List α :=
  reverseAux as.reverse bs -/

infixl:100 " ∘ " => concat

def length : String α → Nat
  | ε => 0
  | u :: _ => Nat.succ (length u)

def occurs (w : String α) (a : α) : Bool :=
  match w with
  | ε => False
  | u :: b => if a = b then True else occurs u a

instance : Membership α (String α) := ⟨fun w a => occurs w a⟩

def Alph (w : String α) : Alphabet α :=
  match w with
  | ε => Finset.empty
  | u :: b => (Alph u) ∪ {b}


end RString

open RString

def Lang (α) :=
  Set (String α)

namespace Lang

instance : Membership (String α) (Lang α) := ⟨Set.Mem⟩

def proj_lang (S : Alphabet α) (A : Lang α) : Lang α :=
  Set.image (proj S) A

def prefixes (w : String α) : Lang α := {u : String α | ∃v, u ∘ v = w}

def concat (A B : Lang α) := {w | ∃u ∈ A, ∃v ∈ B, u ∘ v = w}

infixl:100 " * " => concat

--instance : KStar (Lang α) := ⟨fun l ↦ {x | ∃ L : List (String α),
--  x = L.foldl RString.concat ε ∧ ∀ y ∈ L, y ∈ l}⟩

end Lang

-- see [Preorder] class

abbrev _temp α := Preorder α

-- [Fintype α] is sufficient to ensure finiteness since dependencies are reflexive.
structure Dependency (α) [Fintype α] where
  r : α → α → Prop
  refl : ∀ x, r x x
  symm : ∀ {x y}, r x y → r y x

/-
structure Dependency (α) where
  elems : List α
  complete : ∀ x : α, x ∈ elems
  r : α → α → Prop
  refl : ∀ x, r x x
  symm : ∀ {x y}, r x y → r y x
-/

structure Independency (α) [Fintype α] where
  r : α → α → Prop
  irrefl : ∀ x, ¬r x x
  symm : ∀ {x y}, r x y → r y x

structure TraceEquivalence (α) [Fintype α] where
  r : String α → String α → Prop
  refl : ∀ x, r x x
  symm : ∀ {x y}, r x y → r y x
  trans : ∀ {x y z}, r x y ∧ r y z → r x z
  monoid : ∀ {x x' y y'}, r x x' ∧ r y y' → r (x ∘ y) (x' ∘ y')

namespace Dependency

variable {α : Type} [Fintype α] {D : Dependency α}

-- instance (a b : σ) (D : Dependency σ) : Decidable (D.r a b) :=-

-- variable (D) in
-- def alphabet : Finset σ := {x | D.r x x}

def alphabet : Type _ := α

variable (D) in
def independency : Independency α where
  r x y := ¬ D.r x y
  irrefl x := by
    intro h
    exact h (D.refl x)
  symm {x y} h := by
    intro h'
    exact h (D.symm h')

end Dependency

namespace Independency

variable {α : Type} [Fintype α] {I : Independency α}

variable (I) in
inductive gen_tr : String α → String α → Prop
| refl (s : String α) : gen_tr s s
| symm {l₁ l₂} (h : gen_tr l₁ l₂) : gen_tr l₂ l₁
| trans {l₁ l₂ l₃} (h₁ : gen_tr l₁ l₂) (h₂ : gen_tr l₂ l₃) : gen_tr l₁ l₃
| cong {l₁ l₂ l₃ l₄} (h₁ : gen_tr l₁ l₂) (h₂ : gen_tr l₃ l₄) : gen_tr (l₁ ∘ l₃) (l₂ ∘ l₄)
| swap (a b : α) (h : I.r a b) : gen_tr ((ε :: a) :: b) ((ε :: b) :: a)

variable (I) in
def tr_eq : TraceEquivalence α where
  r := gen_tr I
  refl := gen_tr.refl
  symm := gen_tr.symm
  trans := fun ⟨h1, h2⟩ => gen_tr.trans h1 h2
  monoid := fun ⟨h1, h2⟩ => gen_tr.cong h1 h2

end Independency

-- def trace_equivalence (D) :
-- such that
  -- {([x], [y]) | (x, y) ∈ I_D}
  -- follows monoid structure (axioms)
  -- transitively closed
  --
  -- -> (optional? prove is least congruence)
