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

omit [DecidableEq α] in
@[simp]
lemma reverse_reverse (u : String α) :
    reverse (reverse u) = u := by
  induction u with
  | nil => simp [reverse]
  | snoc v a IH =>
    rw [reverse_snoc, reverse_concat_commutation]
    rw [IH]
    simp [reverse, concat]

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

-- Todo: infixl:50 " ∈ " => occurs

instance : Membership α (String α) := ⟨fun w a => occurs w a⟩

@[simp]
def Alph (w : String α) : Alphabet α :=
  match w with
  | ε => Finset.empty
  | u :: b => (Alph u) ∪ {b}

lemma mem_alph_occurs {w : String α} {a : α} : a ∈ Alph w ↔ occurs w a := by
  induction w with
  | nil =>
    simp
    exact Finset.notMem_empty a
  | snoc w b IH =>
    simp
    by_cases h_ab : a = b
    · simp [h_ab]
    · simp [h_ab]
      exact IH

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
@[simp]
lemma snoc_preserves_congruence {u v : String α} (a : α) :
    I.trace_equiv u v → I.trace_equiv (u :: a) (v :: a) := by
  intro h
  induction h with
  | refl l => exact trace_equiv.refl (l :: a)
  | symm _ ih => exact trace_equiv.symm ih
  | trans h1 h2 ih1 ih2 => exact trace_equiv.trans ih1 ih2
  | cong h1 h2 ih1 ih2 =>
    exact trace_equiv.cong h1 ih2
  | swap b c h =>
    have h_bc := trace_equiv.swap b c h
    have h_bca := trace_equiv.cong h_bc (trace_equiv.refl (ε :: a))
    simp [concat] at h_bca
    exact h_bca

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

@[simp]
lemma concat_adds_alph {α} [DecidableEq α] (u v : String α) :
    Alph (u ∘ v) = Alph u ∪ Alph v := by
  induction v with
  | nil =>
    simp [Alph, concat]
    apply Finset.empty_subset
  | snoc v b IH => simp [Alph, concat, IH]

variable (I) in
@[simp]
lemma equivalence_preserves_occurs {u v : String α} {a : α} :
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
@[simp]
lemma equivalence_preserves_alph {u v : String α} :
    I.trace_equiv u v → Alph u = Alph v := by
  intro h
  rw [Finset.ext_iff]
  intro a
  simp [mem_alph_occurs]
  apply I.equivalence_preserves_occurs
  exact h

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
lemma str_cancel_preserves_cong {u v w : String α} (h : I.trace_equiv (u ∘ w) (v ∘ w)) :
    I.trace_equiv u v := by
  induction w with
  | nil =>
    simp [concat] at h
    exact h
  | snoc w c IH =>
    apply cancel_preserves_congruence I c at h
    simp [cancel] at h
    exact IH h

variable (I) in
lemma left_cancel_preserves_cong {u v w : String α} (h : I.trace_equiv (w ∘ u) (w ∘ v)) :
    I.trace_equiv u v := by
  apply I.reverse_preserves_congruence at h
  simp [reverse_concat_commutation] at h
  apply str_cancel_preserves_cong at h
  apply I.reverse_preserves_congruence at h
  simp [reverse_reverse] at h
  exact h

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
  apply (I.snoc_preserves_congruence b) at h_w
  have h_u_wb := trace_equiv.trans h_u_wb h_w
  have h_w : I.trace_equiv u (cancel u b :: b) ∧ I.trace_equiv v (cancel u b :: a)
    := ⟨h_u_wb, h_v_wa⟩
  apply (I.snoc_preserves_congruence a) at h_u_wb
  apply (I.snoc_preserves_congruence b) at h_v_wa
  have h_eq := trace_equiv.trans h_eq h_v_wa
  have h_eq := trace_equiv.trans (trace_equiv.symm h_eq) h_u_wb
  apply I.tail_swap_lemma (cancel u b) a b at h_eq
  use (I.swap_exact a b h_ab h_eq)
  use cancel u b

variable (I) in
@[simp]
def indep (u v : String α) := ∀ a ∈ Alph u, ∀ b ∈ Alph v, I.r a b

variable (I) in
@[simp]
lemma indep_occurs {u v : String α} :
    I.indep u v = (∀ a b, occurs u a ∧ occurs v b → I.r a b):= by
  simp [indep, mem_alph_occurs]
  constructor
  · intro h a b ha hb
    exact h a ha b hb
  · intro h a ha b hb
    exact h a b ha hb

variable (I) in
@[simp]
lemma indep_commutative {u v : String α} : I.indep u v = I.indep v u := by
  simp
  constructor
  · intro h a ha b hb
    have hI := h b hb a ha
    exact I.symm hI
  · intro h a ha b hb
    have hI := h b hb a ha
    exact I.symm hI

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma relation_empty {a : α} : ∀ b ∈ Finset.empty, I.r a b := by
  intro b hb
  exfalso
  exact Finset.notMem_empty b hb

variable (I) in
@[simp]
lemma indep_empty {u : String α} : I.indep u ε := by
  simp [Alph]
  intro a ha b
  exact I.relation_empty b

variable (I) in
@[simp]
lemma indep_snoc {u v : String α} (a : α) :
    I.indep u (v :: a) ↔ I.indep u v ∧ I.indep u (ε :: a) := by
  constructor
  · intro h
    simp
    simp at h
    have h1 : (∀ a ∈ Alph u, ∀ b ∈ Alph v, I.r a b) := by
      intro a ha b hb
      have ⟨_, h⟩ := h a ha
      exact h b hb
    use h1
    intro a' ha'
    have ⟨h, _⟩ := h a' ha'
    use h
    intro a ha
    exfalso
    exact Finset.notMem_empty a ha
  · intro h
    simp
    simp at h
    intro a' ha'
    have ⟨h1, h2⟩ := h
    have ⟨h2, _⟩ := h2 a' ha'
    use h2
    exact h1 a' ha'

variable (I) in
@[simp]
lemma equivalence_preserves_indep {u v w : String α} (h : I.trace_equiv u v) :
    I.indep w u = I.indep w v := by
  induction w with
  | nil => simp only [indep_commutative, indep_empty]
  | snoc w a IH =>
    nth_rw 1 [indep_commutative]
    nth_rw 2 [indep_commutative]
    nth_rw 1 [indep_snoc]
    nth_rw 2 [indep_snoc]
    nth_rw 1 [indep_commutative] at IH
    nth_rw 2 [indep_commutative] at IH
    rw [IH]
    congr 1
    repeat rw [indep_occurs]
    simp [I.equivalence_preserves_occurs h]

variable (I) in
@[simp]
lemma concat_adds_indep (u v w : String α) :
    I.indep w (u ∘ v) ↔ (I.indep w u ∧ I.indep w v) := by
  simp [indep]
  constructor
  · intro h
    constructor
    · intro a ha b hb
      exact h a ha b (Or.inl hb)
    · intro a ha b hb
      exact h a ha b (Or.inr hb)
  · intro ⟨h1, h2⟩ a ha b hb
    cases hb with
    | inl hb => exact h1 a ha b hb
    | inr hb => exact h2 a ha b hb

variable (I) in
lemma commute_indep_symbol_preserves_cong {u : String α} {a : α} (h : I.indep u (ε :: a)) :
    I.trace_equiv (u :: a) ((ε :: a) ∘ u) := by
  induction u with
  | nil => simp [concat, trace_equiv.refl]
  | snoc u b IH =>
    rw [I.indep_commutative, I.indep_snoc b] at h
    have ⟨ih, h⟩ := h
    rw [I.indep_commutative] at ih
    apply IH at ih
    apply I.snoc_preserves_congruence b at ih
    simp [concat]
    apply trace_equiv.symm
    apply trace_equiv.trans (trace_equiv.symm ih)
    have h_ab : I.trace_equiv (u ∘ ((ε :: a) :: b)) (u ∘ ((ε :: b) :: a)) := by
      simp at h
      have ⟨⟨h_ab, _⟩, _⟩ := h
      exact trace_equiv.cong (trace_equiv.refl u) (trace_equiv.swap a b h_ab)
    simp [concat] at h_ab
    exact h_ab

variable (I) in
lemma commute_indep_concat_preserves_cong {u v : String α} (h : I.indep u v) :
    I.trace_equiv (u ∘ v) (v ∘ u) := by
  induction v with
  | nil => simp [concat, trace_equiv.refl]
  | snoc v a IH =>
    rw [I.indep_snoc a] at h
    have ⟨ih, h⟩ := h
    apply IH at ih
    apply I.snoc_preserves_congruence a at ih
    simp [concat]
    apply trace_equiv.trans ih
    have h := I.commute_indep_symbol_preserves_cong h
    have h := trace_equiv.cong (trace_equiv.refl v) h
    simp [concat, <- concat_assoc] at h
    exact h

variable (I) in
theorem commutation_lemma (u v w : String α) (a : α) (h_av : a ∉ Alph v) :
    I.trace_equiv ((u :: a) ∘ v) (w :: a) → I.indep (ε :: a) v := by
  intro h
  induction v generalizing w with
  | nil =>
    simp [Alph]
    constructor
    · intro b hb
      exfalso
      exact Finset.notMem_empty b hb
    · intro a ha
      exfalso
      exact Finset.notMem_empty a ha
  | snoc x b IH =>
    have hs : (u :: a) ∘ (x :: b) = ((u ∘ (ε :: a)) ∘ x) :: b := by simp [concat]
    rw [hs] at h
    simp at h_av
    obtain ⟨h_ab, h_av⟩ := h_av
    have h_tail := I.tail_lemma ((u ∘ (ε :: a)) ∘ x) w b a
    have h_tcond : (I.trace_equiv ((u ∘ (ε :: a)) ∘ x :: b) (w :: a) ∧ b ≠ a) := by
      use h
      exact mt Eq.symm h_ab
    apply h_tail at h_tcond
    have h_eq := I.cancel_preserves_congruence b h
    simp [cancel, mt Eq.symm h_ab, concat] at h_eq
    have h_ax := IH (cancel w b) h_av h_eq
    rw [indep_snoc]
    use IH (cancel w b) h_av h_eq
    simp [indep]
    have ⟨h_abr, _⟩ := h_tcond
    use ⟨I.symm h_abr, I.relation_empty⟩
    intro ea h_ea
    exfalso
    exact Finset.notMem_empty ea h_ea

omit [Fintype α] in
lemma occur_lemma {w : String α} {a : α} (h : occurs w a) :
    ∃ w' w'', w = (w' ∘ (ε :: a)) ∘ w'' ∧ ¬ occurs w'' a := by
  induction w with
  | nil => simp at h
  | snoc w b IH =>
    by_cases h_ab : a = b
    · use w; use ε
      simp [concat, h_ab]
    · simp [occurs, h_ab] at h
      apply IH at h
      have ⟨w', w'', h⟩ := h
      use w'; use (w'' :: b)
      have ⟨h_w, h_wa⟩ := h
      rw [h_w]
      simp [concat, h_ab, h_wa]

/- The book's proof of Levi Lemma seems to have a mistake stemming from the
 choices of z1', ..., z4'. It can be salvaged by using the following choices
 instead:

 For case (1),
 u ≡ z1' ∘ z2', v' ∘ v'' ≡ z3' ∘ z4', x ≡ z1' ∘ z3', y ≡ z2' ∘ z4'
 and
 z1 = z1', z2 = z2', z3 = z3', z4 = z4' :: e

 For case (2),
 u' ∘ u'' ≡ z1' ∘ z2', v ≡ z3' ∘ z4', x ≡ z1' ∘ z3', y ≡ z2' ∘ z4'
 and
 z1 = z1', z2 = z2' :: e, z3 = z3', z4 = z4'
-/
variable (I) in
theorem levi_lemma {u v x y : String α} (h : I.trace_equiv (u ∘ v) (x ∘ y)) :
    ∃ z1 z2 z3 z4, I.indep z2 z3
    ∧ I.trace_equiv u (z1 ∘ z2) ∧ I.trace_equiv v (z3 ∘ z4)
    ∧ I.trace_equiv x (z1 ∘ z3) ∧ I.trace_equiv y (z2 ∘ z4) := by
  induction y generalizing u v with
  | nil =>
    use u; use ε; use v; use ε
    simp [trace_equiv.refl, concat]
    have h1 : (∀ a ∈ Finset.empty, ∀ b ∈ Alph v, I.r a b) := by
      intro a ha
      exfalso
      exact Finset.notMem_empty a ha
    use h1
    simp [concat] at h
    apply trace_equiv.symm at h
    exact h
  | snoc w e IH =>
    by_cases h_ve : occurs v e
    · have ⟨v', v'', h_v, h_ve⟩ := occur_lemma h_ve
      have h' := h
      have h : I.trace_equiv (u ∘ (v' ∘ v'')) (x ∘ w) := by
        rw [h_v] at h
        have h := I.cancel_preserves_congruence e h
        simp [concat, h_ve, cancel] at h
        exact h
      apply IH at h
      have ⟨z1', z2', z3', z4', h_ind, h⟩ := h
      use z1'; use z2'; use z3'; use z4' :: e; use h_ind
      simp [h, concat]
      rw [h_v]
      simp [concat]
      have ⟨h_iu, h_iv, h_ix, h_iy⟩ := h
      have h_iuv : I.trace_equiv ((z1' ∘ z2') ∘ ((v' ∘ (ε :: e)) ∘ v'')) (u ∘ v) := by
        have h : I.trace_equiv ((v' ∘ (ε :: e)) ∘ v'') v := by simp [h_v, trace_equiv.refl]
        exact trace_equiv.cong (trace_equiv.symm h_iu) h
      have h_ixw : I.trace_equiv ((z1' ∘ z3') ∘ ((z2' ∘ z4') :: e)) (x ∘ (w :: e)) := by
        exact trace_equiv.symm (trace_equiv.cong h_ix (I.snoc_preserves_congruence e h_iy))
      have h := trace_equiv.trans (trace_equiv.trans h_iuv h') (trace_equiv.symm h_ixw)
      have h_z2_z3 : I.trace_equiv
          ((z1' ∘ z3') ∘ (z2' ∘ z4' :: e))
          ((z1' ∘ z2') ∘ (z3' ∘ z4' :: e)) := by
        simp [concat_assoc, concat]
        nth_rw 2 [<- concat_assoc]
        nth_rw 3 [<- concat_assoc]
        apply I.commute_indep_concat_preserves_cong at h_ind
        apply snoc_preserves_congruence
        apply trace_equiv.cong (trace_equiv.refl z1')
        exact trace_equiv.cong (trace_equiv.symm h_ind) (trace_equiv.refl z4')
      apply trace_equiv.trans h at h_z2_z3
      apply left_cancel_preserves_cong at h_z2_z3
      exact h_z2_z3
    · have h_ue : occurs u e := by
        have h_xwe : occurs (x ∘ (w :: e)) e := by simp
        apply equivalence_preserves_occurs at h
        rw [h_xwe] at h
        simp [concat_adds_occurs, h_ve] at h
        exact h
      have ⟨u', u'', h_u, h_ue⟩ := occur_lemma h_ue
      have h' := h
      have h : I.trace_equiv ((u' ∘ u'') ∘ v) (x ∘ w) := by
        rw [h_u] at h
        have h := I.cancel_preserves_congruence e h
        simp [concat, h_ue, h_ve, cancel] at h
        simp [concat_assoc]
        exact h
      apply IH at h
      have ⟨z1', z2', z3', z4', h_ind, h⟩ := h
      have ⟨h_iu, h_iv, h_ix, h_iy⟩ := h
      have h_ind : I.indep (z2' :: e) z3' := by
        rw [I.indep_commutative, I.indep_snoc e, I.indep_commutative]
        use h_ind
        have h_uve : e ∉ Alph (u'' ∘ v) := by
          simp [mem_alph_occurs, h_ve, h_ue]
        have h_ind := I.commutation_lemma u' (u'' ∘ v) (x ∘ w) e h_uve
        simp [h_u, concat] at h'
        apply h_ind at h'
        rw [concat_adds_indep] at h'
        have ⟨_, h'⟩ := h'
        rw [I.equivalence_preserves_indep h_iv] at h'
        rw [concat_adds_indep] at h'
        rw [I.indep_commutative]
        exact h'.left
      use z1'; use z2' :: e; use z3'; use z4'; use h_ind
      simp [h, concat]
      rw [h_u]
      constructor
      · have h_iue : I.indep u'' (ε :: e) := by
          have h_uve : e ∉ Alph (u'' ∘ v) := by
            simp [mem_alph_occurs, h_ve, h_ue]
          have h_iue := I.commutation_lemma u' (u'' ∘ v) (x ∘ w) e h_uve
          simp [h_u, concat] at h'
          apply h_iue at h'
          rw [concat_adds_indep, indep_commutative] at h'
          exact h'.left
        apply trace_equiv.symm
        apply trace_equiv.trans (trace_equiv.symm (I.snoc_preserves_congruence e h_iu))
        have h := trace_equiv.cong
          (trace_equiv.refl u')
          (I.commute_indep_symbol_preserves_cong h_iue)
        simp [concat, <- concat_assoc] at h
        exact h
      · have h_iz4e : I.indep z4' (ε :: e) := by
          have h_uve : e ∉ Alph (u'' ∘ v) := by
            simp [mem_alph_occurs, h_ve, h_ue]
          have h_iue := I.commutation_lemma u' (u'' ∘ v) (x ∘ w) e h_uve
          simp [h_u, concat] at h'
          apply h_iue at h'
          rw [concat_adds_indep, indep_commutative] at h'
          have h' := h'.right
          rw [I.equivalence_preserves_indep h_iv, concat_adds_indep] at h'
          rw [indep_commutative]
          exact h'.right
        apply trace_equiv.trans (I.snoc_preserves_congruence e h_iy)
        have h := trace_equiv.cong
          (trace_equiv.refl z2')
          (I.commute_indep_symbol_preserves_cong h_iz4e)
        simp [concat, <- concat_assoc] at h
        exact h


end Independency

-- def trace_equivalence (D) :
-- such that
  -- {([x], [y]) | (x, y) ∈ I_D}
  -- follows monoid structure (axioms)
  -- transitively closed
  --
  -- -> (optional? prove is least congruence)
