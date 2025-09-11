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

/-

Right-end inductive [String]s, in accordance with the book's tendency
to induct on strings on their rightmost symbols.
Compare and contrast with left-end inductive [List]s.

Existing language & computability libraries are written for [List]s.
We should establish an equivalence between [String]s and [List]s so that
we can utilize these libraries, and in turn so that future projects
using [List]s can interface with our results.

-/

namespace List

theorem right_induction {α} {motive : List α → Prop} (nil : motive [])
    (cons : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : ∀ l, motive l := by
  intro l
  let motive' := fun (l : List α) => ∀ k, motive k → motive (k ++ l)
  have h_base : motive' [] := by
    intro k hk
    rw [append_nil]
    exact hk
  have h_step : ∀ (a : α) (l' : List α), motive' l' → motive' (a :: l') := by
    intro a l' IH k hk
    have h1 : motive (k ++ [a]) := cons k a hk
    have : k ++ a :: l' = (k ++ [a]) ++ l' := by
      simp
    rw [this]
    exact IH (k ++ [a]) h1
  have : ∀ l, motive' l := by
    intro l
    induction l with
    | nil => exact h_base
    | cons a l' IH => exact h_step a l' IH
  exact this l [] nil

example (l : List Nat) : l.length = l.length := by
  induction l using right_induction with
  | nil => rfl
  | cons l a IH => rfl

-- ∈ notation already exists
example (a : α) : a ∈ [a] := by
  simp

/- Left-recursive, as opposed to right-recursive in the book. May need to prove
the two are equal. -/
def proj (w : List α) (S : Alphabet α) : List α :=
  match w with
  | [] => []
  | b :: u => if b ∈ S then b :: (proj u S) else proj u S

/-
protected def projRight (w : List α) (S : Alphabet α) : List α := reverse (proj w.reverse S)
-/

def cancelLeft (w : List α) (a : α) :=
  match w with
  | [] => []
  | b :: u => if a = b then u else b :: (cancelLeft u a)

def cancelRight (w : List α) (a : α) := reverse (cancelLeft w.reverse a)

@[simp]
lemma cancelRight_prop (w : List α) (a b : α) :
    cancelRight (w ++ [b]) a = (if a = b then w else cancelRight w a ++ [b]) := by
  by_cases h_ab : a = b
  · simp [h_ab]
    simp [cancelRight, cancelLeft]
  · simp [h_ab]
    simp [cancelRight, cancelLeft]
    simp [h_ab]

@[simp]
lemma cancelRight_singleton (a : α) : [a].cancelRight a = [] := by
  simp [cancelRight, cancelLeft]

@[simp]
lemma proj_concat_dist (u v : List α) (S : Finset α) :
    proj (u ++ v) S = proj u S ++ proj v S := by
  induction u with
  | nil => simp [proj]
  | cons a u IH =>
    by_cases h_a : a ∈ S
    · simp [proj, h_a]
      exact IH
    · simp [proj, h_a]
      exact IH

@[simp]
lemma proj_reverse_comm (w : List α) (S : Alphabet α) :
    proj (reverse w) S = reverse (proj w S) := by
  induction w with
  | nil => simp [proj]
  | cons b u IH =>
    by_cases h_bs : b ∈ S
    · simp [proj, h_bs]
      exact IH
    · simp [proj, h_bs]
      exact IH

/- Extra lemma for [proj_cancel_comm]:
 (Left)-cancelling with an element not in the set S does not change the projection -/
lemma cancelling_proj_mem_is_id (w : List α) (S : Alphabet α) (a : α) :
    (a ∉ S) -> (cancelLeft (w.proj S) a = w.proj S) := by
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
        simp [cancelLeft, h_ab]
        exact IH
      · simp [proj, h_bs]
        exact IH

@[simp]
lemma proj_cancelLeft_comm (w : List α) (S : Finset α) (a : α) : -- (1.3)
  proj (cancelLeft w a) S = cancelLeft (proj w S) a := by
  induction w with
  | nil => rfl
  | cons b u IH =>
    by_cases h_bs : b ∈ S
    · simp [proj, h_bs]
      by_cases h_ab : a = b
      · simp [cancelLeft, h_ab]
      · simp [cancelLeft, h_ab]
        simp [proj, h_bs]
        exact IH
    · by_cases h_ab : a = b
      · simp [cancelLeft, h_ab]
        simp [proj, h_bs]
        symm
        apply cancelling_proj_mem_is_id
        exact h_bs
      · simp [cancelLeft, h_ab]
        simp [proj, h_bs]
        exact IH

@[simp]
lemma proj_cancelRight_comm (w : List α) (S : Finset α) (a : α) : -- (1.3)
    proj (cancelRight w a) S = cancelRight (proj w S) a := by
  simp [cancelRight, proj_reverse_comm]

@[simp]
def Alph (w : List α) : Alphabet α := w.toFinset

@[simp]
lemma toFinset_mem_iff_mem (w : List α) (a : α) :
    (a ∈ w.toFinset) = (a ∈ w) := by simp

end List

namespace Language
-- ...
end Language

-- see [Preorder] class on how to write & handle algebraic objects in Lean
-- abbrev _temp α := Preorder α

/-

Dependencies and Independencies.

-/

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

/-

We define the [trace_equiv]alence of an independency as its closure under the
following properties. Foundational lemmas about trace equivalence are then
proven using this inductive structure.

This differs from the book's main definition of a trace equivalence
(least congruence), but the book later states offhand that this is an
equivalent formulation.

We should prove the two definitions are equivalent (in any case,
one lemma in this section essentially depends on it (and is currently
left unproven)).

-/

namespace Independency

variable {α : Type} [Fintype α] [DecidableEq α] {I : Independency α}

variable (I) in
inductive trace_equiv : List α → List α → Prop
| refl (s : List α) : trace_equiv s s
| symm {l₁ l₂} (h : trace_equiv l₁ l₂) : trace_equiv l₂ l₁
| trans {l₁ l₂ l₃} (h₁ : trace_equiv l₁ l₂) (h₂ : trace_equiv l₂ l₃) : trace_equiv l₁ l₃
| cong {l₁ l₂ l₃ l₄} (h₁ : trace_equiv l₁ l₂) (h₂ : trace_equiv l₃ l₄) :
  trace_equiv (l₁ ++ l₃) (l₂ ++ l₄)
| swap (a b : α) (h : I.r a b) : trace_equiv [a, b] [b, a]

-- infixl:100 " ≡ " => trace_equiv
-- Todo: Figure out how to make this notation work

-- Todo-?: Define Permutation congruence & prove properties

-- Todo: Define traces as equivalence classes
-- Todo-?: Define the [monoid of strings] and the [trace monoid]
-- Todo-?: Define the natural homomorphism (of strings to their traces)

/-
Lemmas using the inductive structure of [trace_equiv] follow a certain
style which is logically straightforward but has a slightly tricky syntax.

We will explain it in this lemma as an example.

Suppose that we have l₁ ≡ l₂.
Then the ≡ has to be derived from one of the definition's 5 constructors,
1. refl
2. symm
3. trans
4. cong
5. swap

Supposing it was [trans], this means that ∃s₁, s₂, s₃ such that
l₁ = s₁, l₂ = s₃,
s₁ ≡ s₂, s₂ ≡ s₃,
and by induction; IH : length s₁ = length s₂, length s₂ = length s₃

and WTS length l₁ = length l₂ to close the induction.
-/
omit [DecidableEq α] in
variable (I) in
lemma trace_equiv_length {l₁ l₂ : List α} :
    I.trace_equiv l₁ l₂ → l₁.length = l₂.length := by
  intro h
  induction h with
  -- The first possibility is that l₁ ≡ l₂ because of [refl].
  -- That is, l₁ = l₂. In this case it is clear that l₁.length = l₂.length.
  | refl _ => rfl
  /- The second possibility is that l₁ ≡ l₂ because of [symm];
     that is, because l₂ ≡ l₁.

     Because the definition of [trace_equiv] was inductive, we can extract
     an inductive hypothesis (that length l₂ = length l₁).
  -/
  | symm h IH => rw [IH]
  /- The third possiblity is that l₁ ≡ l₂ because of [trans];
     that is, because ∃s₁, s₂, s₃ such that
     l₁ = s₁, l₂ = s₃,
     s₁ ≡ s₂, s₂ ≡ s₃.

     Again we can extract an IH
     (that length s₁ = length s₂ ∧ length s₂ = length s₃).
  -/
  | trans h1 h2 ih1 ih2 => exact Eq.trans ih1 ih2
  -- etc. for [cong]
  | cong h1 h2 ih1 ih2 => simp [ih1, ih2]
  -- and etc. for [swap]
  | swap _ _ _ => rfl
  -- and by definition one of these 5 cases must hold for l₁ ≡ l₂,
  -- so proving the goal given each of the 5 closes the proof.

/-
We also introduce the following @[simp] lemmas to make it easier to
perform the above approach.
-/

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma trace_equiv_refl_prop {w : List α} :
    I.trace_equiv w w := by exact trace_equiv.refl w

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma trq_symm {u v : List α} :
    I.trace_equiv u v → I.trace_equiv v u := by exact trace_equiv.symm

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma trace_equiv_trans_prop {u v w : List α} (h1 : I.trace_equiv u w) (h2 : I.trace_equiv w v) :
    I.trace_equiv u v := by exact trace_equiv.trans h1 h2

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma trq_left_trans {u v w : List α} (h : I.trace_equiv u v) :
    I.trace_equiv u w ↔ I.trace_equiv v w := by
  constructor
  · intro hw
    exact trace_equiv.trans (trace_equiv.symm h) hw
  · intro hw
    exact trace_equiv.trans h hw

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma trq_right_trans {u v w : List α} (h : I.trace_equiv u v) :
    I.trace_equiv w u ↔ I.trace_equiv w v := by
  constructor
  · intro hw
    exact trace_equiv.trans hw h
  · intro hw
    exact trace_equiv.trans hw (trace_equiv.symm h)

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma trace_equiv_cong_prop {l₁ l₂ l₃ l₄ : List α}
    (h₁ : I.trace_equiv l₁ l₂) (h₂ : I.trace_equiv l₃ l₄) :
    I.trace_equiv (l₁ ++ l₃) (l₂ ++ l₄) := by exact trace_equiv.cong h₁ h₂

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma trq_left_concat {u v : List α} (w : List α) (h : I.trace_equiv u v) :
    I.trace_equiv (w ++ u) (w ++ v) := by simp [h]

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma trq_right_concat {u v : List α} (w : List α) (h : I.trace_equiv u v) :
    I.trace_equiv (u ++ w) (v ++ w) := by simp [h]

variable (I) in
omit [DecidableEq α] in
@[simp]
lemma trace_equiv_swap_prop {a b : α} (h : I.r a b) :
    I.trace_equiv [a, b] [b, a] := by exact trace_equiv.swap a b h


variable (I) in
omit [DecidableEq α] in
@[simp]
lemma equivalence_preserves_occurs {u v : List α} {a : α} :
    I.trace_equiv u v → (a ∈ u) = (a ∈ v) := by
  intro h
  induction h with
  | refl l => rfl
  | symm _ ih => symm; exact ih
  | trans h1 h2 ih1 ih2 => rw [ih1, ih2]
  | cong h1 h2 ih1 ih2 => simp [ih1, ih2]
  | swap b c h => simp [Or.comm]

variable (I) in
@[simp]
lemma equivalence_preserves_alph {u v : List α} :
    I.trace_equiv u v → u.Alph = v.Alph := by
  intro h
  rw [Finset.ext_iff]
  intro a
  simp [List.Alph]
  simp [I.equivalence_preserves_occurs h]

/-

Block to prove that ab ≡ ba -> (a, b) ∈ I.
Expressed as [swap_exact].

-/

/-
Sub-lemma for [swap_exact_verbose], for the case where `cong` breaks
[a, b] and [b, a] into 4 singletons. Also uses list-length arguments frequently.
-/
variable (I) in
lemma equivalent_singletons {a b : α} {u v : List α}
    (hu : u = [a]) (hv : v = [b]) (h : I.trace_equiv u v) :
    a = b := by
  induction h generalizing a b with
  | refl l =>
    simp [hu] at hv
    exact hv
  | symm _ ih => rw [ih hv hu]
  | trans h1 h2 ih1 ih2 =>
    rename_i u w v
    have h_w := I.trace_equiv_length h1
    simp [hu] at h_w
    symm at h_w
    rw [List.length_eq_one_iff] at h_w
    have ⟨c, h_w⟩ := h_w
    have h_aw : a ∈ w := by
      have h_au : a ∈ u := by simp [hu]
      rw [<- I.equivalence_preserves_occurs h1]
      exact h_au
    rw [h_w] at h_aw
    rw [List.mem_singleton] at h_aw
    rw [<- h_aw] at h_w
    exact ih2 h_w hv
  | cong h1 h2 ih1 ih2 =>
    rename_i l1 l2 l3 l4
    by_cases h_n1 : l1 = []
    · have h_n2 := I.trace_equiv_length h1
      simp [h_n1] at h_n2
      symm at h_n2
      rw [List.length_eq_zero_iff] at h_n2
      simp [h_n1] at hu
      simp [h_n2] at hv
      exact ih2 hu hv
    · rw [<- List.length_eq_zero_iff] at h_n1
      have h_s : l1.length + l3.length = 1 := by
        have h_s : (l1 ++ l3).length = 1 := by simp [hu]
        simp at h_s
        exact h_s
      have h_l1 : l1.length = 1 := by omega
      have h_l2 := I.trace_equiv_length h1
      rw [h_l1] at h_l2
      symm at h_l2
      rw [List.length_eq_one_iff] at h_l1
      rw [List.length_eq_one_iff] at h_l2
      have ⟨c, h_l1⟩ := h_l1
      have ⟨d, h_l2⟩ := h_l2
      simp [h_l1] at hu
      simp [h_l2] at hv
      simp [hu] at h_l1
      simp [hv] at h_l2
      exact ih1 h_l1 h_l2
  | swap b c h => simp at hu

/-
An LLM-generated sub-lemma for [swap_exact_verbose].
-/
omit [Fintype α] [DecidableEq α] in
lemma two_element_list_is {a b : α} {w : List α} (h1 : w.length = 2)
    (h2 : a ∈ w) (h3 : b ∈ w) (hne : a ≠ b) :
    w = [a, b] ∨ w = [b, a] := by
  -- Step 1: Express w as [x, y] since its length is 2
  rcases List.length_eq_two.mp h1 with ⟨x, y, rfl⟩
  -- Step 2: Simplify membership of a and b in [x, y]
  have h2' : a = x ∨ a = y := by simpa using h2
  have h3' : b = x ∨ b = y := by simpa using h3
  -- Step 3: Case analysis on the possible equalities
  rcases h2' with (rfl | rfl) <;> rcases h3' with (rfl | rfl)
  · -- Case where a = x and b = x: contradicts a ≠ b
    exfalso
    exact hne rfl
  · -- Case where a = x and b = y: w = [a, b]
    left
    rfl
  · -- Case where a = y and b = x: w = [b, a]
    right
    rfl
  · -- Case where a = y and b = y: contradicts a ≠ b
    exfalso
    exact hne rfl

/- The compiler seems to be unable to break `I.trace_equiv [a, b] [b, a]`
 into `cong` and `swap` cases. We essentially do those two cases manually
 in the below lemma, arguing via [List.length].
-/
variable (I) in
lemma swap_exact_verbose (a b : α) (u v : List α) (hne : a ≠ b) (hu : u = [a, b]) (hv : v = [b, a])
    (h : I.trace_equiv u v) : I.r a b := by
  induction h generalizing a b with
  | refl l =>
    simp [hu, hne] at hv
  | symm h ih =>
    have ih := ih b a
    exact I.symm (ih (Ne.symm hne) hv hu)
  | trans h1 h2 ih1 ih2 =>
    rename_i u w v
    have h_w := I.trace_equiv_length h1
    simp [hu] at h_w
    symm at h_w
    /- [w] must have length 2. We apply a sub-lemma to prove it must
     then be [a, b] or [b, a], which completes the induction. -/
    have h_aw : a ∈ w := by
      have h_au : a ∈ u := by simp [hu]
      rw [<- I.equivalence_preserves_occurs h1]
      exact h_au
    have h_bw : b ∈ w := by
      have h_bu : b ∈ u := by simp [hu]
      rw [<- I.equivalence_preserves_occurs h1]
      exact h_bu
    have h_w := two_element_list_is h_w h_aw h_bw hne
    cases h_w with
    | inl h_w => exact ih2 a b hne h_w hv
    | inr h_w => exact ih1 a b hne hu h_w
  | cong h1 h2 ih1 ih2 =>
    rename_i l1 l2 l3 l4
    by_cases h_n1 : l1 = []
    -- Either l1 = l2 = [], which we can induct away on l3 and l4;
    · have h_n2 := I.trace_equiv_length h1
      simp [h_n1] at h_n2
      symm at h_n2
      rw [List.length_eq_zero_iff] at h_n2
      simp [h_n1] at hu
      simp [h_n2] at hv
      exact ih2 a b hne hu hv
    · by_cases h_n3 : l3 = []
      -- or l3 = l4 = [], which we can induct away on l1 and l2;
      · have h_n4 := I.trace_equiv_length h2
        simp [h_n3] at h_n4
        symm at h_n4
        rw [List.length_eq_zero_iff] at h_n4
        simp [h_n3] at hu
        simp [h_n4] at hv
        exact ih1 a b hne hu hv
      /- or l1, l2, l3, l4 are singletons
       (this is in fact absurd, but it is a bit tricky to prove it) -/
      · rw [<- List.length_eq_zero_iff] at h_n1
        rw [<- List.length_eq_zero_iff] at h_n3
        have h_s : l1.length + l3.length = 2 := by
          have h_s : (l1 ++ l3).length = 2 := by simp [hu]
          simp at h_s
          exact h_s
        have h_l1 : l1.length = 1 := by omega
        have h_l2 := I.trace_equiv_length h1
        rw [h_l1] at h_l2
        symm at h_l2
        rw [List.length_eq_one_iff] at h_l1
        rw [List.length_eq_one_iff] at h_l2
        have ⟨c, h_l1⟩ := h_l1
        have ⟨d, h_l2⟩ := h_l2
        simp [h_l1] at hu
        simp [h_l2] at hv
        simp [hu] at h_l1
        simp [hv] at h_l2
        simp [I.equivalent_singletons h_l1 h_l2 h1] at hne
  | swap a b ih =>
    simp at hu
    simp [hu] at ih
    exact ih

lemma swap_exact (a b : α) (hne : a ≠ b)
    (h : I.trace_equiv [a, b] [b, a]) : I.r a b := by
  exact (I.swap_exact_verbose a b [a, b] [b, a] hne rfl rfl h)


variable (I) in
omit [DecidableEq α] in
@[simp]
lemma cons_preserves_congruence {u v : List α} (a : α) :
    I.trace_equiv u v → I.trace_equiv (a :: u) (a :: v) := by
  intro h
  induction h with
  | refl l => simp
  | symm _ ih => simp [ih]
  | trans h1 h2 ih1 ih2 => exact trace_equiv.trans ih1 ih2
  | cong h1 h2 ih1 ih2 =>
    exact trace_equiv.cong ih1 h2
  | swap b c h =>
    have h_bc := trace_equiv.swap b c h
    have h_bca := trace_equiv.cong (trace_equiv.refl [a]) h_bc
    simp at h_bca
    exact h_bca

variable (I) in
omit [DecidableEq α] in
lemma reverse_preserves_congruence :
    ∀ {u v : List α}, I.trace_equiv u v → I.trace_equiv (u.reverse) (v.reverse) := by
  intro u v h
  induction h with
  | refl l => simp
  | symm _ ih => simp [ih]
  | trans h1 h2 ih1 ih2 => exact trace_equiv.trans ih1 ih2
  | cong h1 h2 ih1 ih2 => simp [ih1, ih2]
  | swap a b h =>
    simp
    exact trace_equiv.swap b a (I.symm h)

/-

Additional lemmas that were deemed necessary to close the Levi Lemma.
We should refactor to group them with their respective definitions.

-/

@[simp]
lemma cancelLeft_on_concat_prefix_iff_occurs {α} [DecidableEq α] (u v : List α) (a : α) :
    (u ++ v).cancelLeft a = if a ∈ u then (u.cancelLeft a) ++ v else u ++ (v.cancelLeft a) := by
  by_cases h : a ∈ u
  · simp [h]
    induction u with
    | nil => simp at h
    | cons b u IH =>
      by_cases h_ab : a = b
      -- Case where a = b
      · simp [h_ab, List.cancelLeft]
      -- Case where a ≠ b
      · simp [h_ab, List.cancelLeft]
        simp [h_ab] at h
        exact IH h
  · simp [h]
    induction u with
    | nil => simp
    | cons b u IH =>
      simp at h
      obtain ⟨h1, h2⟩ := h
      simp [h2] at IH
      simp [h1, List.cancelLeft]
      exact IH

@[simp]
lemma cancelRight_on_concat_suffix_iff_occurs {α} [DecidableEq α] (u v : List α) (a : α) :
    (u ++ v).cancelRight a = if a ∈ v then u ++ (v.cancelRight a) else u.cancelRight a ++ v := by
  by_cases h : a ∈ v
  · simp [h]
    induction v using List.right_induction with
    | nil => simp at h
    | cons v b IH =>
      by_cases h_ab : a = b
      -- Case where a = b
      · simp [h_ab, <- List.append_assoc]
      -- Case where a ≠ b
      · simp [h_ab, <- List.append_assoc]
        simp [h_ab] at h
        exact IH h
  · simp [h]
    induction v using List.right_induction with
    | nil => simp
    | cons v b IH =>
      simp at h
      obtain ⟨h1, h2⟩ := h
      simp [h1] at IH
      simp [h2, <- List.append_assoc]
      exact IH

/-
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

-/

variable (I) in
@[simp]
lemma cancelLeft_preserves_congruence (a : α) :
    ∀ {u v : List α}, I.trace_equiv u v → I.trace_equiv (u.cancelLeft a) (v.cancelLeft a) := by
  intro u v h
  induction h with
  | refl l => exact trace_equiv.refl (l.cancelLeft a)
  | symm _ ih => exact trace_equiv.symm ih
  | trans h1 h2 ih1 ih2 => exact trace_equiv.trans ih1 ih2
  | cong h1 h2 ih1 ih2 =>
    rename_i l1 l2 l3 l4
    by_cases h_occ : a ∈ l1
    · simp [h_occ]
      rw [I.equivalence_preserves_occurs h1] at h_occ
      simp [h_occ]
      simp [ih1, h2]
    · simp [h_occ]
      rw [I.equivalence_preserves_occurs h1] at h_occ
      simp [h_occ]
      simp [h1, ih2]
  | swap b c h =>
    by_cases h_ab : a = b
    · by_cases h_ac : a = c
      · simp [<- h_ab, <- h_ac]
      · simp [<- h_ab, List.cancelLeft, h_ac]
    · by_cases h_ac : a = c
      · simp [h_ab, <- h_ac, List.cancelLeft]
      · simp [h_ab, h_ac, List.cancelLeft, h]

variable (I) in
@[simp]
lemma cancelRight_preserves_congruence (a : α) :
    ∀ {u v : List α}, I.trace_equiv u v → I.trace_equiv (u.cancelRight a) (v.cancelRight a) := by
  intro u v h
  induction h with
  | refl l => exact trace_equiv.refl (l.cancelRight a)
  | symm _ ih => exact trace_equiv.symm ih
  | trans h1 h2 ih1 ih2 => exact trace_equiv.trans ih1 ih2
  | cong h1 h2 ih1 ih2 =>
    rename_i l1 l2 l3 l4
    by_cases h_occ : a ∈ l3
    · simp [h_occ]
      rw [I.equivalence_preserves_occurs h2] at h_occ
      simp [h_occ]
      simp [h1, ih2]
    · simp [h_occ]
      rw [I.equivalence_preserves_occurs h2] at h_occ
      simp [h_occ]
      simp [ih1, h2]
  | swap b c h =>
    by_cases h_ab : a = b
    · by_cases h_ac : a = c
      · simp [<- h_ab, <- h_ac]
      · simp [<- h_ab, List.cancelRight, List.cancelLeft, h_ac]
    · by_cases h_ac : a = c
      · simp [h_ab, <- h_ac, List.cancelRight, List.cancelLeft]
      · simp [h_ab, h_ac, List.cancelRight, List.cancelLeft, h]

--Todo: Use [Sigma] in place of [S] (everywhere)
variable (I) in
lemma proj_preserves_congruence (S : Alphabet α) :
    ∀ {u v : List α}, I.trace_equiv u v → I.trace_equiv (u.proj S) (v.proj S) := by
  intro u v h
  induction h with
  | refl l => simp
  | symm _ ih => simp [ih]
  | trans h1 h2 ih1 ih2 => exact trace_equiv.trans ih1 ih2
  | cong h1 h2 ih1 ih2 => simp [ih1, ih2]
  | swap b c h =>
    by_cases h_b : b ∈ S
    · by_cases h_c : c ∈ S
      · simp [h_b, h_c, List.proj]
        exact trace_equiv.swap b c h
      · simp [h_b, h_c, List.proj]
    · by_cases h_c : c ∈ S
      · simp [h_b, h_c, List.proj]
      · simp [h_b, h_c, List.proj]

variable (I) in
lemma right_cancel_preserves_cong {u v w : List α} (h : I.trace_equiv (u ++ w) (v ++ w)) :
    I.trace_equiv u v := by
  induction w using List.right_induction with
  | nil =>
    simp at h
    exact h
  | cons w c IH =>
    apply I.cancelRight_preserves_congruence c at h
    simp [<- List.append_assoc] at h
    exact IH h

variable (I) in
lemma left_cancel_preserves_cong {u v w : List α} (h : I.trace_equiv (w ++ u) (w ++ v)) :
    I.trace_equiv u v := by
  induction w with
  | nil =>
    simp at h
    exact h
  | cons c w IH =>
    apply I.cancelLeft_preserves_congruence c at h
    simp [List.cancelLeft] at h
    exact IH h

variable (I) in
lemma left_tail_swap_lemma {w : List α} {a b : α} :
    (I.trace_equiv ([a, b] ++ w) ([b, a] ++ w)) →
    (I.trace_equiv [a, b] [b, a]) := by
  induction w using List.right_induction with
  | nil => simp
  | cons u c IH =>
    intro h
    apply cancelRight_preserves_congruence I c at h
    simp only [<- List.append_assoc, List.cancelRight_prop] at h
    simp at h
    exact IH h

variable (I) in
@[simp]
lemma right_tail_swap_lemma (w : List α) (a b : α) :
    (I.trace_equiv (w ++ [a, b]) (w ++ [b, a])) →
    (I.trace_equiv [a, b] [b, a]) := by
  induction w with
  | nil => simp
  | cons c u IH =>
    intro h
    apply cancelLeft_preserves_congruence I c at h
    simp [List.cancelLeft] at h
    exact IH h

variable (I) in
theorem tail_lemma (u v : List α) (a b : α) :
    (I.trace_equiv (u ++ [a]) (v ++ [b]) ∧ a ≠ b) →
    (I.r a b ∧ ∃ w, I.trace_equiv u (w ++ [b]) ∧ I.trace_equiv v (w ++ [a])) := by
  intro ⟨h_eq, h_ab⟩
  have h_u_wb : I.trace_equiv u (v.cancelRight a ++ [b]) := by
    apply (I.cancelRight_preserves_congruence a) at h_eq
    simp [h_ab] at h_eq
    exact h_eq
  have h_v_wa : I.trace_equiv v (u.cancelRight b ++ [a]) := by
    apply (I.cancelRight_preserves_congruence b) at h_eq
    symm at h_ab
    simp [h_ab] at h_eq
    exact trace_equiv.symm h_eq
  have h_w : I.trace_equiv (v.cancelRight a) (u.cancelRight b) := by
    apply (I.cancelRight_preserves_congruence a) at h_eq
    apply (I.cancelRight_preserves_congruence b) at h_eq
    simp [h_ab] at h_eq
    exact trace_equiv.symm h_eq
  apply (I.trq_right_concat [b]) at h_w
  rw [I.trq_right_trans h_w] at h_u_wb
  have h_w_uv : I.trace_equiv u (u.cancelRight b ++ [b]) ∧ I.trace_equiv v (u.cancelRight b ++ [a])
    := ⟨h_u_wb, h_v_wa⟩
  apply (I.trq_right_concat [a]) at h_u_wb
  apply (I.trq_right_concat [b]) at h_v_wa
  rw [I.trq_right_trans h_v_wa] at h_eq
  apply I.trq_symm at h_eq
  rw [I.trq_right_trans h_u_wb] at h_eq
  simp at h_eq
  apply I.right_tail_swap_lemma (u.cancelRight b) a b at h_eq
  use (I.swap_exact a b h_ab h_eq)
  use u.cancelRight b

variable (I) in
@[simp]
def indep (u v : List α) := ∀ a ∈ u.Alph, ∀ b ∈ v.Alph, I.r a b

variable (I) in
@[simp]
lemma indep_occurs {u v : List α} :
    I.indep u v = (∀ a b, a ∈ u ∧ b ∈ v → I.r a b):= by
  simp [indep, List.Alph]
  constructor
  · intro h a b ha hb
    exact h a ha b hb
  · intro h a ha b hb
    exact h a b ha hb

variable (I) in
@[simp]
lemma indep_commutative {u v : List α} : I.indep u v = I.indep v u := by
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
lemma indep_empty {u : List α} : I.indep u [] := by simp

variable (I) in
@[simp]
lemma indep_cons {u v : List α} (a : α) :
    I.indep (a :: u) v ↔ I.indep [a] v ∧ I.indep u v := by simp

variable (I) in
@[simp]
lemma indep_singleton_right {u v : List α} (a : α) :
    I.indep (u ++ [a]) v ↔ I.indep [a] v ∧ I.indep u v := by simp

variable (I) in
@[simp]
lemma equivalence_preserves_indep {u v w : List α} (h : I.trace_equiv u v) :
    I.indep u w = I.indep v w := by
  induction w with
  | nil => simp
  | cons a w IH =>
    nth_rw 1 [indep_commutative]
    nth_rw 2 [indep_commutative]
    nth_rw 1 [indep_cons]
    nth_rw 2 [indep_cons]
    nth_rw 1 [indep_commutative] at IH
    nth_rw 2 [indep_commutative] at IH
    rw [IH]
    congr 1
    repeat rw [indep_occurs]
    simp [I.equivalence_preserves_occurs h]

variable (I) in
@[simp]
lemma concat_adds_indep (u v w : List α) :
    I.indep w (u ++ v) ↔ (I.indep w u ∧ I.indep w v) := by
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
lemma commute_indep_symbol_preserves_cong {u : List α} {a : α} (h : I.indep [a] u) :
    I.trace_equiv (a :: u) (u ++ [a]) := by
  induction u with
  | nil => simp
  | cons b u IH =>
    rw [I.indep_commutative, I.indep_cons b] at h
    have ⟨h, ih⟩ := h
    rw [I.indep_commutative] at ih
    apply IH at ih
    apply I.cons_preserves_congruence b at ih
    simp
    rw [I.trq_right_trans (trace_equiv.symm ih)]
    have h_ab : I.trace_equiv (a :: b :: u) (b :: a :: u) := by
      simp at h
      have h := trace_equiv.cong (trace_equiv.swap b a h) (trace_equiv.refl u)
      simp at h
      simp [h]
    exact h_ab

variable (I) in
lemma commute_indep_concat_preserves_cong {u v : List α} (h : I.indep u v) :
    I.trace_equiv (u ++ v) (v ++ u) := by
  induction v with
  | nil => simp
  | cons a v IH =>
    rw [I.indep_commutative, I.indep_cons a] at h
    have ⟨h, ih⟩ := h
    rw [I.indep_commutative] at ih
    apply IH at ih
    apply I.cons_preserves_congruence a at ih
    simp
    rw [I.trq_right_trans (I.trq_symm ih)]
    apply I.commute_indep_symbol_preserves_cong at h
    apply I.trq_right_concat v at h
    apply I.trq_symm at h
    simp at h
    exact h

variable (I) in
theorem commutation_lemma (u v w : List α) (a : α) (h_av : a ∉ v) :
    I.trace_equiv (u ++ [a] ++ v) (w ++ [a]) → I.indep [a] v := by
  intro h
  induction v using List.right_induction generalizing w with
  | nil => simp
  | cons x b IH =>
    simp at h_av
    obtain ⟨h_av, h_ab⟩ := h_av
    simp only [<- List.append_assoc] at h
    have h_tail := I.tail_lemma (u ++ [a] ++ x) w b a
    have h_tcond : (I.trace_equiv (u ++ [a] ++ x ++ [b]) (w ++ [a]) ∧ b ≠ a) := by
      use h
      exact mt Eq.symm h_ab
    apply h_tail at h_tcond
    have h_eq := I.cancelRight_preserves_congruence b h
    rw [List.append_assoc] at h_eq
    simp [<- List.append_assoc, mt Eq.symm h_ab] at h_eq
    have h_ax := IH (w.cancelRight b) h_av h_eq
    rw [indep_commutative, indep_singleton_right]
    have ⟨h_abr, _⟩ := h_tcond
    rw [indep_commutative] at h_ax
    simp at h_ax
    simp [h_abr]
    exact h_ax

omit [Fintype α] in
lemma occur_lemma {w : List α} {a : α} (h : a ∈ w) :
    ∃ w' w'', w = (w' ++ [a] ++ w'') ∧ a ∉ w'' := by
  induction w using List.right_induction with
  | nil => simp at h
  | cons w b IH =>
    by_cases h_ab : a = b
    · use w, []
      simp [h_ab]
    · simp [h_ab] at h
      apply IH at h
      have ⟨w', w'', h⟩ := h
      use w', w'' ++ [b]
      simp [h, h_ab]

/-
 Levi Lemma (p10).

 The book's proof of Levi Lemma seems to have a mistake stemming from the
 choices of z1', ..., z4'. It can be salvaged by using the following choices
 instead:

 For case (1),
 u ≡ z1' ++ z2', v' ++ v'' ≡ z3' ++ z4', x ≡ z1' ++ z3', y ≡ z2' ++ z4'
 and
 z1 = z1', z2 = z2', z3 = z3', z4 = z4' ++ [e]

 For case (2),
 u' ++ u'' ≡ z1' ++ z2', v ≡ z3' ++ z4', x ≡ z1' ++ z3', y ≡ z2' ++ z4'
 and
 z1 = z1', z2 = z2' ++ [e], z3 = z3', z4 = z4'

 We follow the book's proof here (but it is somewhat vague in the body of
 cases (1) and (2); we need to fill in some details ourselves.)
-/
variable (I) in
theorem levi_lemma {u v x y : List α} (h : I.trace_equiv (u ++ v) (x ++ y)) :
    ∃ z1 z2 z3 z4, I.indep z2 z3
    ∧ I.trace_equiv u (z1 ++ z2) ∧ I.trace_equiv v (z3 ++ z4)
    ∧ I.trace_equiv x (z1 ++ z3) ∧ I.trace_equiv y (z2 ++ z4) := by
  induction y using List.right_induction generalizing u v with
  -- Per the book we either have y = [],
  | nil =>
    use u, [], v, []
    simp [List.Alph]
    simp at h
    simp [h]
  -- or we have y = w ++ [e], in which case we can induct.
  | cons w e IH =>
    by_cases h_ve : e ∈ v
    -- And then either the rightmost occurrence of <e> in (u ++ v) is in <v>,
    -- leading to case (1): u ++ v = u ++ v' ++ [e] ++ v'',
    · have ⟨v', v'', h_v, h_ve⟩ := occur_lemma h_ve
      have h' := h
      have h_choice : I.trace_equiv (u ++ (v' ++ v'')) (x ++ w) := by
        rw [h_v] at h
        have h := I.cancelRight_preserves_congruence e h
        simp only [<- List.append_assoc] at h
        simp only [h_ve, cancelRight_on_concat_suffix_iff_occurs] at h
        simp at h
        simp [h]
      have ⟨z1', z2', z3', z4', h_ind, h⟩ := IH h_choice
      use z1', z2', z3', z4' ++ [e], h_ind
      simp [h]
      rw [h_v]
      have ⟨h_iu, h_iv, h_ix, h_iy⟩ := h
      simp [I.trq_left_trans (I.trq_right_concat [e] h_iy)]
      /- (The rest of this case boils down to using the fact that (v'', e) ∈ I.
        Unfortunately it currently takes a lot of boilerplate to extract
        and use this fact; to do e.g.

        I.trace_equiv u v ∧ I.trace_equiv v w → I.trace_equiv u w

        or

        I.trace_equiv u v → I.trace.equiv (w ++ u) (w ++ v)

        we need to manually cite [trans] or [cong].
        It would be nice if we could instead use [simp] to normalize
        these.)
      -/
      have h_ve : I.trace_equiv (e :: v'') (v'' ++ [e]) := by
        rw [h_v] at h'
        have h_indep := I.commutation_lemma (u ++ v') v'' (x ++ w) e
        simp only [<- List.append_assoc] at h'
        have h_indep := h_indep h_ve h'
        exact I.commute_indep_symbol_preserves_cong h_indep
      rw [I.trq_left_trans (I.trq_left_concat v' h_ve)]
      simp [<- List.append_assoc]
      exact I.trq_right_concat [e] h_iv
    -- or it is in [u], leading to case (2): u ++ v = u' ++ [e] ++ u'' ++ v
    · have h_ue : e ∈ u := by
        have h_xwe : e ∈ (x ++ (w ++ [e])) := by simp
        apply equivalence_preserves_occurs at h
        rw [<- h] at h_xwe
        simp [h_ve] at h
        exact h
      have ⟨u', u'', h_u, h_ue⟩ := occur_lemma h_ue
      have h' := h
      have h : I.trace_equiv ((u' ++ u'') ++ v) (x ++ w) := by
        rw [h_u] at h
        have h := I.cancelRight_preserves_congruence e h
        simp [<- List.append_assoc, h_ue, h_ve] at h
        exact h
      apply IH at h
      have ⟨z1', z2', z3', z4', h_ind, h⟩ := h
      have ⟨h_iu, h_iv, h_ix, h_iy⟩ := h
      -- (Again, the rest is boilerplate to extract and use the
      -- fact that (u'' ++ v, e) ∈ I).
      have h_ind : I.indep (z2' ++ [e]) z3' := by
        rw [I.indep_singleton_right e, I.indep_commutative, And.comm]
        use h_ind
        have h_uve : e ∉ (u'' ++ v) := by
          simp [h_ve, h_ue]
        have h_ind := I.commutation_lemma u' (u'' ++ v) (x ++ w) e h_uve
        simp [h_u] at h'
        simp at h_ind
        apply h_ind at h'
        simp
        intro z hz
        apply List.mem_append_left z4' at hz
        rw [<- I.equivalence_preserves_occurs h_iv] at hz
        exact I.symm (h' z (Or.inr hz))
      use z1', z2' ++ [e], z3', z4', h_ind
      simp [h]
      rw [h_u]
      constructor
      · simp [h_u, <- List.append_assoc] at h'
        rw [<- List.append_assoc]
        apply I.trq_right_concat [e] at h_iu
        rw [I.trq_right_trans (I.trq_symm h_iu)]
        simp [List.append_assoc]
        apply I.trq_left_concat
        apply I.commute_indep_symbol_preserves_cong
        have h_iue : I.indep [e] u'' := by
          have h_uve : e ∉ (u'' ++ v) := by
            simp [h_ve, h_ue]
          have h_iue := I.commutation_lemma u' (u'' ++ v) (x ++ w) e h_uve
          rw [<- List.append_assoc] at h_iue
          apply h_iue at h'
          rw [concat_adds_indep] at h'
          exact h'.left
        exact h_iue
      · have h_iz4e : I.indep [e] z4' := by
          have h_uve : e ∉ u'' ++ v := by
            simp [h_ve, h_ue]
          have h_iue := I.commutation_lemma u' (u'' ++ v) (x ++ w) e h_uve
          simp [<- List.append_assoc] at h_iue
          simp [h_u, <- List.append_assoc] at h'
          apply h_iue at h'
          simp
          intro z hz
          apply List.mem_append_right z3' at hz
          rw [<- I.equivalence_preserves_occurs h_iv] at hz
          exact h' z (Or.inr hz)
        rw [I.trq_left_trans (I.trq_right_concat [e] h_iy)]
        apply I.trq_symm
        simp
        exact I.trq_left_concat z2' (I.commute_indep_symbol_preserves_cong h_iz4e)


end Independency

-- def trace_equivalence (D) :
-- such that
  -- {([x], [y]) | (x, y) ∈ I_D}
  -- follows monoid structure (axioms)
  -- transitively closed
  --
  -- -> (optional? prove is least congruence)
