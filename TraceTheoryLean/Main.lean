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

-- Largely the same as List
inductive String (α : Type*) where
  | nil : String α
  | snoc (s : String α) (a : α) : String α
-- snoc: reverse cons

notation "ε" => String.nil
infixl:67 " :: " => String.snoc
-- " ∘ " in particular does not work?

variable {w : String α}

def proj (S : Alphabet α) (w : String α) : String α :=
  match w with
  | ε => ε
  | u :: b => if b ∈ S then proj S u :: b else proj S u

def cancel (w : String α) (a : α) :=
  match w with
  | ε => ε
  | u :: b => if a = b then u else (cancel u a) :: b

-- Extra lemma for [proj_cancel_comm]:
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

/-- Todo:
Auxiliary for `List.reverse`. `List.reverseAux l r = l.reverse ++ r`,
but it is defined directly. -/
@[simp]
def reverseAux : String α → String α → String α
  | r, ε      => r
  | r, u :: a => reverseAux (r :: a) u

variable (w) in
def reverse : String α := reverseAux ε w

-- protected def concat
def concat : (xs ys : String α) → String α
  | as, ε       => as
  | as, bs :: b => (RString.concat as bs) :: b

/- consider tail-recursive concatenation

def appendTR (as bs : List α) : List α :=
  reverseAux as.reverse bs -/

infixl:100 " ∘ " => concat

omit [DecidableEq α] in
@[simp]
lemma concat_left_id (w : String α) : ε ∘ w = w := by
  induction w with
  | nil => rw [concat]
  | snoc u a IH => simp [concat]; exact IH

omit [DecidableEq α] in
@[simp]
lemma concat_assoc (u v w : String α) : (u ∘ v) ∘ w = u ∘ (v ∘ w) := by
  induction w with
  | nil => rfl
  | snoc w a IH => simp [concat]; exact IH

omit [DecidableEq α] in
lemma reverseAux_eq_concat (u v : String α) : reverseAux u v = u ∘ (reverseAux ε v) := by
  induction v generalizing u with
  | nil => simp [reverseAux, concat]
  | snoc v a IH =>
    simp [reverseAux]
    rw [IH (u := u :: a), IH (u := (ε :: a)), <- concat_assoc]
    rfl

omit [DecidableEq α] in
@[simp]
lemma reverse_snoc (w : String α) (a : α) : reverse (w :: a) = (ε :: a) ∘ reverse w := by
  simp [reverse, reverseAux]
  rw [← reverseAux_eq_concat]

omit [DecidableEq α] in
@[simp]
lemma reverse_concat_commutation (u v : String α) :
    reverse (u ∘ v) = reverse v ∘ reverse u := by
  induction v with
  | nil => simp [reverse, concat]
  | snoc v a IH =>
    rw [reverse_snoc]
    simp [<- IH, concat]

-- Todo: Make [w.length] syntax work
def length : String α → Nat
  | ε => 0
  | u :: _ => Nat.succ (length u)

omit [DecidableEq α] in
@[simp]
lemma length_concat {u v : String α} : length (u ∘ v) = length u + length v := by
  induction v with
  | nil => simp [length, concat]
  | snoc v _ IH => simp [concat, length, <- Nat.add_assoc]; exact IH

/-
@[simp]
def occurs (a : α) (w : String α) : Bool :=
  match w with
  | ε => False
  | u :: b => if a = b then True else occurs a u
-/

@[simp]
def occurs (w : String α) (a : α) : Bool :=
  match w with
  | ε => False
  | u :: b => if a = b then True else occurs u a

-- infixl:50 " ∈ " => occurs

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

-- Todo: dependency morphism φ : Σ* -> [trace monoid]

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

/- Todo-?: Might want to define a structure capturing a trace equivalence
 instead of relying on Independency.trace_equiv

structure TraceEquivalence (α) [Fintype α] where
  r : String α → String α → Prop
  refl : ∀ x, r x x
  symm : ∀ {x y}, r x y → r y x
  trans : ∀ {x y z}, r x y ∧ r y z → r x z
  monoid : ∀ {x x' y y'}, r x x' ∧ r y y' → r (x ∘ y) (x' ∘ y')

variable (I) in
def tr_eq : TraceEquivalence α where
  r := I.gen_tr
  refl := gen_tr.refl
  symm := gen_tr.symm
  trans := fun ⟨h1, h2⟩ => gen_tr.trans h1 h2
  monoid := fun ⟨h1, h2⟩ => gen_tr.cong h1 h2
-/

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

variable {α : Type} [Fintype α] [DecidableEq α] {I : Independency α}

variable (I) in
inductive trace_equiv : String α → String α → Prop
| refl (s : String α) : trace_equiv s s
| symm {l₁ l₂} (h : trace_equiv l₁ l₂) : trace_equiv l₂ l₁
| trans {l₁ l₂ l₃} (h₁ : trace_equiv l₁ l₂) (h₂ : trace_equiv l₂ l₃) : trace_equiv l₁ l₃
| cong {l₁ l₂ l₃ l₄} (h₁ : trace_equiv l₁ l₂) (h₂ : trace_equiv l₃ l₄) :
  trace_equiv (l₁ ∘ l₃) (l₂ ∘ l₄)
| swap (a b : α) (h : I.r a b) : trace_equiv ((ε :: a) :: b) ((ε :: b) :: a)
-- Todo-?: "(ε :: a) :: b" is a bit clunky, consider better notation

-- infixl:100 " ≡ " => trace_equiv
-- Todo: Figure out how to make this notation work

-- Todo-?: Define Permutation congruence & prove properties

-- Todo: Define traces as equivalence classes
-- Todo-?: Define the [monoid of strings] and the [trace monoid]
-- Todo-?: Define the natural homomorphism (of strings to their traces)

/-
We have that l₁ ≡ l₂.
The ≡ has to be derived from one of the 5 constructors above,
1. refl
2. symm
3. trans
4. cong
5. swap

(+ other cases, same as below)

Supposing it was [trans], this means that ∃s₁, s₂, s₃ such that
l₁ = s₁, l₂ = s₃,
s₁ ≡ s₂, s₂ ≡ s₃,
and by induction; IH : length s₁ = length s₂, length s₂ = length s₃

and WTS length l₁ = length l₂ to close the induction.
-/
omit [DecidableEq α] in
variable (I) in
lemma trace_equiv_length :
    ∀ {l₁ l₂ : String α}, I.trace_equiv l₁ l₂ → length l₁ = length l₂ := by
  intro l1 l2 h
  induction h with
  | refl _ => rfl
  | symm h IH => rw [IH]
  | trans h1 h2 ih1 ih2 => exact Eq.trans ih1 ih2
  | cong h1 h2 ih1 ih2 => simp [ih1, ih2]
  | swap _ _ _ => rfl

variable (I) in
lemma swap_exact (a b : α) (hne : a ≠ b)
    (h : I.trace_equiv ((ε :: a) :: b) ((ε :: b) :: a)) : I.r a b := by sorry

/- Todo?: Prove that ab ≡ ba -> (a, b) ∈ I.
 Might be related with proving that I.trace_equiv is the least congruence.
 LLM brute-force proof suggestion below: -/

/-
variable (I) in
lemma reverse_imply (a b : α) (hne : a ≠ b)
    (h : I.trace_equiv ((ε :: a) :: b) ((ε :: b) :: a)) : I.r a b := by
  induction h with
  | refl l =>
      have : [a, b] = [b, a] := by assumption
      have : a = b ∧ b = a := by
        injection this with h1 h2
        injection h2 with h3
        exact ⟨h1, h3⟩
      exfalso
      exact hne this.1
  | symm h' ih =>
      exact I.symm (ih hne)
  | trans h1 h2 ih1 ih2 =>
      have len1 := gen_tr_length I h1
      have len2 := gen_tr_length I h2
      simp at len1 len2
      -- Intermediate list must be [a,b] or [b,a]
      cases' Classical.em (I.gen_tr [a, b] [b, a]) with h3 h3
      · exact ih2 hne
      · have : I.gen_tr [a, b] [a, b] := gen_tr.refl I [a, b]
        have := gen_tr.trans this h1
        contradiction
  | cong h1 h2 =>
      have : [a, b] = [a] ++ [b] := by rfl
      have : [b, a] = [b] ++ [a] := by rfl
      -- Length preservation forces component lists to match
      have len1 := gen_tr_length I h1
      have len2 := gen_tr_length I h2
      simp at len1 len2
      -- The only possible splits are trivial due to length constraints
      exfalso
      exact hne rfl
  | swap a' b' h' =>
      have h1 : a = a' ∧ b = b' := by
        injection ‹[a, b] = [a', b']› with h1 h2
        injection h2 with h3
        exact ⟨h1, h3⟩
      have h2 : b = b' ∧ a = a' := by
        injection ‹[b, a] = [b', a']› with h1 h2
        injection h2 with h3
        exact ⟨h1, h3⟩
      rcases h1 with ⟨rfl, rfl⟩
      exact h'
-/

variable (I) in
omit [DecidableEq α] in
lemma reverse_preserves_congruence :
    ∀ {u v : String α}, I.trace_equiv u v → I.trace_equiv (reverse u) (reverse v) := by
  intro u v h
  induction h with
  | refl l => exact trace_equiv.refl (reverse l)
  | symm _ ih => exact trace_equiv.symm ih
  | trans h1 h2 ih1 ih2 => exact trace_equiv.trans ih1 ih2
  | cong h1 h2 ih1 ih2 =>
    repeat rw [reverse_concat_commutation]
    exact trace_equiv.cong ih2 ih1
  | swap a b h =>
    simp [reverse]
    exact trace_equiv.swap b a (I.symm h)

@[simp]
lemma cancels_on_concat_suffix_iff_occurs {α} [DecidableEq α] (u v : String α) (a : α) :
    cancel (u ∘ v) a = if occurs v a then u ∘ (cancel v a) else cancel u a ∘ v := by
  by_cases h : occurs v a
  · simp [h]
    induction v with
    | nil => simp [occurs] at h
    | snoc v b IH =>
      by_cases h_ab : a = b
      -- Case where a = b
      · simp [h_ab, concat, cancel]
      -- Case where a ≠ b
      · simp [h_ab, concat, cancel]
        simp [occurs, h_ab] at h
        simp [h] at IH
        exact IH
  · simp [h]
    induction v with
    | nil => simp [concat]
    | snoc v b IH =>
      simp [occurs] at h
      obtain ⟨h1, h2⟩ := h
      simp [h2] at IH
      simp [concat, cancel, h1]
      exact IH

@[simp]
lemma concat_adds_occurs {α} [DecidableEq α] (u v : String α) (a : α) :
    occurs (u ∘ v) a = (occurs u a ∨ occurs v a) := by
  induction v with
  | nil => simp [occurs, concat]
  | snoc v b IH =>
    by_cases h_ab : a = b
    · simp [h_ab, occurs, concat]
    · simp [h_ab, occurs, concat]
      rw [IH]


variable (I) in
@[simp]
lemma equivalence_preserves_occurs (u v : String α) (a : α) :
    I.trace_equiv u v → occurs u a = occurs v a := by
  intro h
  induction h with
  | refl l => rfl
  | symm _ ih => symm; exact ih
  | trans h1 h2 ih1 ih2 => rw [ih1, ih2]
  | cong h1 h2 ih1 ih2 =>
    rw [Bool.eq_iff_iff]
    simp [concat_adds_occurs]
    rw [ih1, ih2]
  | swap b c h =>
    simp [occurs]
    apply Bool.or_comm

variable (I) in
lemma cancel_preserves_congruence (a : α) :
    ∀ {u v : String α}, I.trace_equiv u v → I.trace_equiv (cancel u a) (cancel v a) := by
  intro u v h
  induction h with
  | refl l => exact trace_equiv.refl (cancel l a)
  | symm _ ih => exact trace_equiv.symm ih
  | trans h1 h2 ih1 ih2 => exact trace_equiv.trans ih1 ih2
  | cong h1 h2 ih1 ih2 =>
    rename_i l1 l2 l3 l4
    by_cases h_occ : occurs l3 a
    · apply equivalence_preserves_occurs at h2
      rw [h_occ] at h2
      simp [h_occ, h2]
      exact trace_equiv.cong h1 ih2
    · have h_occ_l3 : occurs l4 a = false := by
        apply equivalence_preserves_occurs at h2
        simp at h_occ
        rw [h_occ] at h2
        rw [h2]
      simp [h_occ, h_occ_l3]
      exact trace_equiv.cong ih1 h2
  | swap b c h =>
    by_cases h_ab : a = b
    · by_cases h_ac : a = c
      · simp [<- h_ab, <- h_ac, cancel]
        exact trace_equiv.refl (ε :: a)
      · simp [<- h_ab, cancel, h_ac]
        exact trace_equiv.refl (ε :: c)
    · by_cases h_ac : a = c
      · simp [h_ab, <- h_ac, cancel]
        exact trace_equiv.refl (ε :: b)
      · simp [h_ab, cancel, h_ac]
        exact trace_equiv.swap b c h

omit [Fintype α] in
@[simp]
lemma proj_concat_comm (S : Finset α) (u v : String α) :
    proj S (u ∘ v) = proj S u ∘ proj S v := by
  induction v with
  | nil => simp [proj, concat]
  | snoc v a IH =>
    by_cases h_a : a ∈ S
    · simp [proj, concat, h_a]
      exact IH
    · simp [proj, concat, h_a]
      exact IH

--Todo: Use [Sigma] in place of [S] (everywhere)
variable (I) in
lemma proj_preserves_congruence (S : Alphabet α) :
    ∀ {u v : String α}, I.trace_equiv u v → I.trace_equiv (proj S u) (proj S v) := by
  intro u v h
  induction h with
  | refl l => exact trace_equiv.refl (proj S l)
  | symm _ ih => exact trace_equiv.symm ih
  | trans h1 h2 ih1 ih2 => exact trace_equiv.trans ih1 ih2
  | cong h1 h2 ih1 ih2 =>
    simp
    exact trace_equiv.cong ih1 ih2
  | swap b c h =>
    by_cases h_b : b ∈ S
    · by_cases h_c : c ∈ S
      · simp [h_b, h_c, proj]
        exact trace_equiv.swap b c h
      · simp [h_b, h_c, proj]
        exact trace_equiv.refl (ε :: b)
    · by_cases h_c : c ∈ S
      · simp [h_b, h_c, proj]
        exact trace_equiv.refl (ε :: c)
      · simp [h_b, h_c, proj]
        exact trace_equiv.refl ε

variable (I) in
lemma tail_swap_rev {w : String α} {a b : α} :
    (I.trace_equiv (((ε :: a) :: b) ∘ w) (((ε :: b) :: a) ∘ w)) →
    (I.trace_equiv ((ε :: a) :: b) ((ε :: b) :: a)) := by
  induction w with
  | nil => simp [concat]
  | snoc u c IH =>
    intro h
    apply cancel_preserves_congruence I c at h
    simp [cancel] at h
    exact IH h

variable (I) in
@[simp]
lemma tail_swap_lemma (w : String α) (a b : α) :
    (I.trace_equiv ((w :: a) :: b) ((w :: b) :: a)) →
    (I.trace_equiv ((ε :: a) :: b) ((ε :: b) :: a)) := by
  intro h
  apply reverse_preserves_congruence at h
  repeat rw [reverse_snoc] at h
  repeat rw [<- concat_assoc] at h
  simp [concat] at h
  exact (I.tail_swap_rev (trace_equiv.symm h))

variable (I) in
theorem tail_lemma (u v : String α) (a b : α) :
    (I.trace_equiv (u :: a) (v :: b) ∧ a ≠ b) →
    (I.r a b ∧ ∃ w, I.trace_equiv u (w :: b) ∧ I.trace_equiv v (w :: a)) := by
  intro ⟨h_eq, h_ab⟩
  have h_u_wb : I.trace_equiv u (cancel v a :: b) := by
    apply (cancel_preserves_congruence I a) at h_eq
    simp [cancel, h_ab] at h_eq
    exact h_eq
  have h_v_wa : I.trace_equiv v (cancel u b :: a) := by
    apply (cancel_preserves_congruence I b) at h_eq
    symm at h_ab
    simp [cancel, h_ab] at h_eq
    exact trace_equiv.symm h_eq
  have h_w : I.trace_equiv (cancel v a) (cancel u b) := by
    apply (cancel_preserves_congruence I a) at h_eq
    apply (cancel_preserves_congruence I b) at h_eq
    simp [cancel, h_ab] at h_eq
    exact trace_equiv.symm h_eq




end Independency

-- def trace_equivalence (D) :
-- such that
  -- {([x], [y]) | (x, y) ∈ I_D}
  -- follows monoid structure (axioms)
  -- transitively closed
  --
  -- -> (optional? prove is least congruence)
