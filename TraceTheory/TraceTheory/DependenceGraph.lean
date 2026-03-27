import Mathlib.Data.Fintype.Sum
import Mathlib.Order.WellFounded
import Mathlib.Tactic.FinCases
import TraceTheory.DependenceMorphism

open List

namespace TraceTheory

variable {α : Type*} {D : Dependence α}

variable (D) in
/-- A `DependenceGraph` over `D` is a triple $\gamma=(V,R,\varphi)$ where $V$ is a finite set,
  $R\subseteq V\times V$ and $\varphi:V\to \Sigma$ is a labeling of the vertices.-/
structure DependenceGraph where
  /-- The finite set of vertices of the graph. -/
  V : Type
  /-- The requirement that the vertex set be finite. -/
  [fintype : Fintype V]
  /-- The set of arcs between vertices. `R u v` means there is an edge from `u` to `v`. -/
  R : V → V → Prop
  /-- The labeling function mapping each vertex to a symbol in the alphabet `α`. -/
  φ : V → α
  acyclic : ∀ v, ¬ Relation.TransGen R v v
  d_conn : ∀ v₁ v₂, R v₁ v₂ ∨ R v₂ v₁ ∨ v₁ = v₂ ↔ D.rel (φ v₁) (φ v₂)

/-- A dependence relation `D₁` is a subset of `D₂` if every pair of symbols dependent in `D₁`
is also dependent in `D₂`. -/
def Dependence.Subset (D₁ D₂ : Dependence α) : Prop :=
  ∀ a b, D₁.rel a b → D₂.rel a b

/-- Notation for `Dependence.Subset`. -/
notation:50 D₁ " ⊆ " D₂ => Dependence.Subset D₁ D₂

namespace DependenceGraph

/-- An isomorphism between `γ₁` and `γ₂` consists of a bijection between their
vertex sets that preserves both the vertex labels and the edge relation. -/
structure Iso (γ₁ γ₂: DependenceGraph D) where
  /-- The bijection between vertex sets. -/
  toEquiv : γ₁.V ≃ γ₂.V
  preserves_label' : ∀ v, γ₁.φ v = γ₂.φ (toEquiv v)
  preserves_arcs' : ∀ v₁ v₂, γ₁.R v₁ v₂ ↔ γ₂.R (toEquiv v₁) (toEquiv v₂)

instance (γ₁ γ₂ : DependenceGraph D) : CoeFun (γ₁.Iso γ₂) (fun _ => γ₁.V → γ₂.V) where
  coe f := f.toEquiv.toFun

instance (γ : DependenceGraph D) : Fintype γ.V := γ.fintype

-- Proposition (1.4.4)
/-- The composition of two dependence graphs `γ₁` and `γ₂` over dependence `D`.
  The vertex set is the disjoint union of `γ₁.V` and `γ₂.V`.
  Arcs are preserved within the original graphs, and new arcs are added from `γ₁` to `γ₂`
  whenever the labels of the vertices are dependent in `D`. -/
def compose (γ₁ γ₂ : DependenceGraph D) : DependenceGraph D :=
  let Vcomp := γ₁.V ⊕ γ₂.V
  let Rcomp := fun u v =>
    match u, v with
    | Sum.inl u, Sum.inl v => γ₁.R u v
    | Sum.inl u, Sum.inr v => D.rel (γ₁.φ u) (γ₂.φ v)
    | Sum.inr u, Sum.inl v => False
    | Sum.inr u, Sum.inr v => γ₂.R u v
  let φcomp := Sum.elim γ₁.φ γ₂.φ
  {
    V := Vcomp
    fintype := inferInstance
    R := Rcomp
    φ := φcomp
    acyclic := by
      intro v h
      cases v with
      | inl v₁ =>
        have hγ₁ : ∀ {x y u v},
            x = Sum.inl u →
            y = Sum.inl v →
            Relation.TransGen Rcomp x y →
            Relation.TransGen γ₁.R u v := by
          intro x y u v hx hy hxy
          induction hxy generalizing v with
          | single h_step =>
            rename_i y
            simp only [hx, hy, Rcomp] at h_step
            exact Relation.TransGen.single h_step
          | tail h_before h_step ih =>
            rename_i w y
            cases w with
            | inl w₁ =>
              simp only [hy, Rcomp] at h_step
              exact Relation.TransGen.tail (ih rfl) h_step
            | inr w₂ =>
              exfalso
              simp only [hy, Rcomp] at h_step
        generalize hv₁ : Sum.inl v₁ = v' at h
        exact γ₁.acyclic v₁ (hγ₁ hv₁.symm hv₁.symm h)
      | inr v₂ =>
        have h_right : ∀ (u : γ₂.V) (w : Vcomp),
            Relation.TransGen Rcomp (Sum.inr u) w → Sum.isRight w := by
          intro u w huw
          induction huw with
          | single h_step =>
            rename_i w
            cases w with
            | inl w₁ =>
              exfalso
              simp only [Rcomp] at h_step
            | inr w₂ =>
              exact Sum.isRight_inr
          | tail _ h_rest ih =>
            rename_i x w _
            cases w with
            | inl w₁ =>
              exfalso
              have ⟨y, hy⟩ := Sum.isRight_iff.mp ih
              simp only [Rcomp, hy] at h_rest
            | inr w₂ =>
              exact Sum.isRight_inr
        have hγ₂ : ∀ {x y u v},
            x = Sum.inr u →
            y = Sum.inr v →
            Relation.TransGen Rcomp x y →
            Relation.TransGen γ₂.R u v := by
          intro x y u v hx hy hxy
          induction hxy generalizing v with
          | single h_step =>
            rename_i y
            simp only [hx, hy, Rcomp] at h_step
            exact Relation.TransGen.single h_step
          | tail h_before h_step ih =>
            rename_i w y
            cases w with
            | inl w₁ =>
              exfalso
              rw [hx] at h_before
              have hw₁ := h_right u (Sum.inl w₁) h_before
              simp only [Sum.isRight_inl, Bool.false_eq_true] at hw₁
            | inr w₂ =>
              simp only [hy, Rcomp] at h_step
              exact Relation.TransGen.tail (ih rfl) h_step
        generalize hv₂ : Sum.inr v₂ = v' at h
        exact γ₂.acyclic v₂ (hγ₂ hv₂.symm hv₂.symm h)
    d_conn := by
      intro v₁ v₂
      cases v₁ with
      | inl v₁ =>
        cases v₂ with
        | inl v₂ =>
          simp [Vcomp, Rcomp, φcomp]
          exact γ₁.d_conn v₁ v₂
        | inr v₂ =>
          simp [Vcomp, Rcomp, φcomp]
      | inr v₁ =>
        cases v₂ with
        | inl v₂ =>
          simp [Vcomp, Rcomp, φcomp]
          exact ⟨D.symm _ _, D.symm _ _⟩
        | inr v₂ =>
          simp [Vcomp, Rcomp, φcomp]
          exact γ₂.d_conn v₁ v₂
  }

/-- Two dependence graphs are isomorphic if there exists an `Iso` between them. -/
def Isomorphic (γ₁ γ₂ : DependenceGraph D) : Prop := Nonempty (Iso γ₁ γ₂)

/-- Notation for dependence graph isomorphism. -/
infix:50 " ≃g " => Isomorphic

theorem isomorphic_refl (γ : DependenceGraph D) : γ ≃g γ :=
  Nonempty.intro {
    toEquiv := Equiv.refl γ.V
    preserves_label' := by
      intro v
      rfl
    preserves_arcs' := by
      intro v₁ v₂
      rfl
  }

theorem isomorphic_symm {γ₁ γ₂ : DependenceGraph D} (h : γ₁ ≃g γ₂) : γ₂ ≃g γ₁ :=
  Nonempty.intro {
    toEquiv := h.some.toEquiv.symm
    preserves_label' := by
      intro v₂
      rw [h.some.preserves_label', h.some.toEquiv.apply_symm_apply v₂]
    preserves_arcs' := by
      intro v₂ w₂
      rw [h.some.preserves_arcs']
      rw [h.some.toEquiv.apply_symm_apply v₂, h.some.toEquiv.apply_symm_apply w₂]
  }

theorem isomorphic_trans {γ₁ γ₂ γ₃ : DependenceGraph D} (h₁ : γ₁ ≃g γ₂) (h₂ : γ₂ ≃g γ₃) : γ₁ ≃g γ₃ :=
  Nonempty.intro {
    toEquiv := h₁.some.toEquiv.trans h₂.some.toEquiv
    preserves_label' := by
      intro v₁
      rw [h₁.some.preserves_label', h₂.some.preserves_label', h₁.some.toEquiv.trans_apply]
    preserves_arcs' := by
      intro v₁ w₁
      rw [h₁.some.preserves_arcs', h₂.some.preserves_arcs']
      rw [h₁.some.toEquiv.trans_apply, h₁.some.toEquiv.trans_apply]
  }

/-- The setoid structure on graphs defined by the graph isomorphism equivalence relation over `D`.
  This serves as the basis for constructing the quotient type `DGraph`.-/
instance isomorphicSetoid (D : Dependence α) : Setoid (DependenceGraph D) where
  r := Isomorphic
  iseqv := ⟨isomorphic_refl, isomorphic_symm, isomorphic_trans⟩

/-- The algebra of dependence graphs modulo isomorphism with composition. -/
def DGraph (D : Dependence α) := Quotient (isomorphicSetoid D)

/-- The empty dependence graph, acting as the identity element for graph composition. -/
def emptyGraph (D : Dependence α) : DependenceGraph D where
  V := Empty
  fintype := inferInstance
  R := fun u v => False
  φ := Empty.elim
  acyclic := by simp
  d_conn := by simp

/-- The identity element of the `Graph`, represented by the class of the empty graph. -/
def one (D : Dependence α) : DGraph D :=
  Quotient.mk (isomorphicSetoid D) (emptyGraph D)

theorem compose_congr {γ₁ γ₁' γ₂ γ₂' : DependenceGraph D}
    (h₁ : γ₁ ≃g γ₁') (h₂ : γ₂ ≃g γ₂') :
    (compose γ₁ γ₂) ≃g (compose γ₁' γ₂') := by
  apply Nonempty.intro
  refine ⟨?_, ?_, ?_⟩
  · exact Equiv.sumCongr h₁.some.toEquiv h₂.some.toEquiv
  · intro v
    dsimp [compose]
    cases v with
    | inl v₁ =>
      simp only [Sum.elim_inl, Sum.map_inl, h₁.some.preserves_label']
    | inr v₂ =>
      simp only [Sum.elim_inr, Sum.map_inr, h₂.some.preserves_label']
  · intro v₁ v₂
    rcases v₁ with v₁ | v₁ <;> rcases v₂ with v₂ | v₂ <;> dsimp [compose]
    · rw [h₁.some.preserves_arcs']
    . rw [h₁.some.preserves_label', h₂.some.preserves_label']
    · rfl
    . rw [h₂.some.preserves_arcs']

/-- Multiplication in the `Graph`, induced by the `compose` operation on dependence graphs. -/
def mul (D : Dependence α) : DGraph D → DGraph D → DGraph D :=
  Quotient.lift₂
    (fun γ₁ γ₂ => ⟦compose γ₁ γ₂⟧)
    (by
      intro γ₁ γ₁' γ₂ γ₂' h h'
      apply Quotient.sound
      exact compose_congr h h'
    )

theorem compose_assoc_iso (γ₁ γ₂ γ₃ : DependenceGraph D) :
    (compose (compose γ₁ γ₂) γ₃) ≃g (compose γ₁ (compose γ₂ γ₃)) := by
  apply Nonempty.intro
  refine ⟨?_, ?_, ?_⟩
  · dsimp [compose]
    exact Equiv.sumAssoc _ _ _
  · intro v
    dsimp [compose]
    cases v with
    | inl v₁ =>
      cases v₁ with
      | inl v₁₁ =>
        rw [Equiv.sumAssoc_apply_inl_inl]
        simp only [Sum.elim_inl]
      | inr v₁₂ =>
        rw [Equiv.sumAssoc_apply_inl_inr]
        simp only [Sum.elim_inl, Sum.elim_inr]
    | inr v₂ =>
      rw [Equiv.sumAssoc_apply_inr]
      simp only [Sum.elim_inr]
  · intro v₁ v₂
    rcases v₁ with v₁ | v₁ <;> rcases v₂ with v₂ | v₂
    · rcases v₁ with v₁ | v₁ <;> rcases v₂ with v₂ | v₂ <;> dsimp [compose] <;> rfl
    · rcases v₁ with v₁ | v₁ <;> dsimp [compose] <;> rfl
    · rcases v₂ with v₂ | v₂ <;> dsimp [compose] <;> rfl
    · dsimp [compose]
      rfl

theorem empty_compose_iso (γ : DependenceGraph D) :
    compose (emptyGraph D) γ ≃g γ := by
  apply Nonempty.intro
  refine ⟨?_, ?_, ?_⟩
  · dsimp [compose, emptyGraph]
    exact Equiv.emptySum _ _
  · intro v
    cases v with
    | inl v₁ =>
      cases v₁
    | inr v₂ =>
      dsimp [compose, emptyGraph]
  · intro v₁ v₂
    rcases v₁ with v₁ | v₁ <;> rcases v₂ with v₂ | v₂
    · cases v₁
    · cases v₁
    · cases v₂
    · dsimp [compose, emptyGraph]
      rfl

theorem compose_empty_iso (γ : DependenceGraph D) :
    compose γ (emptyGraph D) ≃g γ := by
  apply Nonempty.intro
  refine ⟨?_, ?_, ?_⟩
  · dsimp [compose, emptyGraph]
    exact Equiv.sumEmpty γ.V Empty
  · intro v
    cases v with
    | inl v₁ =>
      dsimp [compose, emptyGraph]
    | inr v₂ =>
      cases v₂
  · intro v₁ v₂
    rcases v₁ with v₁ | v₁ <;> rcases v₂ with v₂ | v₂
    · dsimp [compose, emptyGraph]
      rfl
    · cases v₂
    · cases v₁
    · cases v₁

instance : Monoid (DGraph D) where
  mul := mul D
  one := one D
  mul_assoc := by
    intro γ₁_q γ₂_q γ₃_q
    refine Quotient.inductionOn₃ γ₁_q γ₂_q γ₃_q (fun γ₁ γ₂ γ₃ => ?_)
    apply Quotient.sound
    exact compose_assoc_iso _ _ _
  one_mul := by
    intro γ_q
    refine Quotient.inductionOn γ_q (fun γ => ?_)
    apply Quotient.sound
    exact empty_compose_iso _
  mul_one := by
    intro γ_q
    refine Quotient.inductionOn γ_q (fun γ => ?_)
    apply Quotient.sound
    exact compose_empty_iso _

variable (D) in
/-- A dependence graph consisting of a single vertex labeled with `a`. -/
def singletonGraph (a : α) : DependenceGraph D where
  V := Unit
  fintype := inferInstance
  R := fun u v => False
  φ := fun v => a
  acyclic := by
    intro v hv
    cases hv <;> contradiction
  d_conn := by
    intro v₁ v₂
    simp only [or_true, D.refl]

variable (D) in
/-- Constructs the canonical dependence graph corresponding to a word `w`.
  Defined by folding `compose` over the list, starting with the empty graph. -/
def fromString (w : List α) : DependenceGraph D :=
  w.foldl (fun γ a => compose γ (singletonGraph D a)) (emptyGraph D)

/-- A vertex is a sink if it has no outgoing edges. -/
def IsSink (γ : DependenceGraph D) (v : γ.V) : Prop :=
  ∀ w, ¬ γ.R v w

theorem exists_sink_of_nonempty_depGraph (γ : DependenceGraph D) (h : Nonempty γ.V) :
    ∃ v, IsSink γ v := by
  classical
  have wf : WellFounded (flip γ.R) := by
    let μ : γ.V → ℕ := fun u => (Finset.univ.filter (fun v => Relation.TransGen γ.R u v)).card
    have μ_wf : WellFounded (Function.onFun Nat.lt μ) :=
      WellFounded.onFun wellFounded_lt
    apply WellFounded.mono μ_wf
    intro a b hab
    dsimp [μ]
    apply Finset.card_lt_card
    constructor
    · intro w
      rw [Finset.mem_filter_univ, Finset.mem_filter_univ]
      intro hw
      exact Relation.TransGen.head hab hw
    · apply Finset.not_subset.mpr
      use a
      constructor
      · rw [Finset.mem_filter_univ]
        exact Relation.TransGen.single hab
      · rw [Finset.mem_filter_univ]
        exact γ.acyclic a
  have ⟨v, _, hv⟩ := wf.has_min (Set.univ : Set γ.V) (Set.nonempty_iff_univ_nonempty.mp h)
  use v
  intro w hw
  replace hv := hv w (Set.mem_univ w)
  dsimp [flip] at hv
  exact hv hw

/-- Removes a vertex `v` from the dependence graph `γ`,
  returning the induced subgraph on $V \setminus \{v\}$. -/
noncomputable def removeVertex (γ : DependenceGraph D) (v : γ.V) : DependenceGraph D where
  V := {u : γ.V // u ≠ v}
  fintype := Fintype.ofFinite {u : γ.V // u ≠ v}
  R := fun u v => γ.R u v
  φ := fun v => γ.φ v
  acyclic := by
    intro u h
    have h_lift : ∀ u v : { u // u ≠ v },
        Relation.TransGen (fun x y => γ.R x.val y.val) u v →
        Relation.TransGen γ.R u.val v.val := by
      intro u v h
      induction h with
      | single h_step =>
        exact Relation.TransGen.single h_step
      | tail h_before h_step ih =>
        exact Relation.TransGen.tail ih h_step
    exact γ.acyclic u (h_lift u u h)
  d_conn := by
    intro ⟨u, hu⟩ ⟨w, hw⟩
    simp only [ne_eq, Subtype.mk.injEq]
    exact γ.d_conn u w

theorem fromString_empty : fromString D [] = emptyGraph D := by rfl

theorem fromString_concat (w : List α) (a : α) :
    fromString D (w ++ [a]) = compose (fromString D w) (singletonGraph D a) := by
  dsimp [fromString]
  rw [foldl_concat]

theorem fromString_surjective :
    ∀ (γ : DependenceGraph D), ∃ (w : List α), fromString D w ≃g γ := by
  intro γ
  let size_lt (γ₁ γ₂ : DependenceGraph D) : Prop := Fintype.card γ₁.V < Fintype.card γ₂.V
  have wf : WellFounded size_lt :=
    InvImage.wf (fun (γ : DependenceGraph D) => Fintype.card γ.V) wellFounded_lt
  induction γ using WellFounded.induction wf with
  | h γ ih =>
    classical
    cases isEmpty_or_nonempty γ.V with
    | inl h_empty =>
      use []
      dsimp [fromString, emptyGraph]
      refine ⟨?_, ?_, ?_⟩
      · simp
        exact Equiv.equivOfIsEmpty Empty γ.V
      · intro v
        simp at v
        cases v
      · intro v₁ v₂
        simp at v₁
        cases v₁
    | inr h_nonempty =>
      have ⟨a, ha⟩ := exists_sink_of_nonempty_depGraph γ h_nonempty
      let γ' := removeVertex γ a
      have h_smaller : Fintype.card γ'.V < Fintype.card γ.V := by
        dsimp [γ', removeVertex]
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        apply Nat.sub_one_lt_of_le Fintype.card_pos
        rfl
      have ⟨w, hw⟩ := ih γ' h_smaller
      use w ++ [γ.φ a]
      rw [fromString_concat]
      apply isomorphic_trans (compose_congr hw (isomorphic_refl (singletonGraph D (γ.φ a))))
      apply Nonempty.intro
      let p : γ.V → Prop := fun v => v = a
      let e : γ'.V ⊕ Unit ≃ γ.V := by
        apply (Equiv.sumCongr (Equiv.refl γ'.V) (Equiv.ofUnique Unit (Subtype p))).trans
        apply (Equiv.sumComm γ'.V (Subtype p)).trans
        exact Equiv.sumCompl p
      refine ⟨e, ?_, ?_⟩
      · intro v
        dsimp [compose, singletonGraph, γ', removeVertex, e]
        cases v with
        | inl v₁ =>
          rw [Sum.elim_inl, Sum.map_inl, id_eq, Sum.swap_inl, Equiv.sumCompl_apply_inr]
        | inr v₂ =>
          rw [Sum.elim_inr, Sum.map_inr, Equiv.ofUnique_apply, Sum.swap_inr]
          rw [Equiv.sumCompl_apply_inl]
          rfl
      · intro v₁ v₂
        dsimp [compose, singletonGraph, γ', removeVertex, e]
        rcases v₁ with v₁ | v₁ <;> rcases v₂ with v₂ | v₂
        · simp only [Sum.map_inl, id_eq, Sum.swap_inl]
          rw [Equiv.sumCompl_apply_inr, Equiv.sumCompl_apply_inr]
        · simp only [Sum.map_inl, id_eq, Sum.swap_inl, Sum.map_inr,
                     Equiv.ofUnique_apply, Sum.swap_inr]
          rw [Equiv.sumCompl_apply_inr, Equiv.sumCompl_apply_inl, Pi.default_apply]
          constructor
          · intro h
            rcases (γ.d_conn v₁.1 a).mpr h with h₁ | h₂ | h₃
            · exact h₁
            · exfalso
              exact ha v₁.1 h₂
            · exfalso
              exact v₁.property h₃
          · intro h
            exact (γ.d_conn v₁.1 a).mp (Or.inl h)
        · simp only [Sum.map_inr, Equiv.ofUnique_apply, Pi.default_def, Sum.swap_inr, Sum.map_inl,
                     id_eq, Sum.swap_inl, false_iff]
          rw [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
          exact ha v₂.1
        · simp only [Sum.map_inr, Equiv.ofUnique_apply, Pi.default_def, Sum.swap_inr, false_iff]
          rw [Equiv.sumCompl_apply_inl]
          intro h
          exact γ.acyclic a (Relation.TransGen.single h)

theorem fromString_append_iso_compose (w₁ w₂ : List α) :
    fromString D (w₁ ++ w₂) ≃g compose (fromString D w₁) (fromString D w₂) := by
  induction w₂ using reverseRecOn with
  | nil =>
    simp only [append_nil, fromString_empty]
    exact isomorphic_symm (compose_empty_iso (fromString D w₁))
  | append_singleton w' a ih =>
    rw [← append_assoc, fromString_concat, fromString_concat]
    apply isomorphic_trans (compose_congr ih (isomorphic_refl (singletonGraph D a)))
    exact compose_assoc_iso _ _ _

theorem card_eq_of_iso {γ₁ γ₂ : DependenceGraph D} (h : γ₁ ≃g γ₂) :
    Fintype.card γ₁.V = Fintype.card γ₂.V := by
  apply Fintype.card_eq.mpr
  apply Nonempty.intro
  exact h.some.toEquiv

theorem card_compose_eq_sum (γ₁ γ₂ : DependenceGraph D) :
    Fintype.card (compose γ₁ γ₂).V = Fintype.card γ₁.V + Fintype.card γ₂.V := by
  dsimp [compose]
  exact Fintype.card_sum

theorem card_fromString_eq_length (w : List α) :
    Fintype.card (fromString D w).V = w.length := by
  induction w using reverseRecOn with
  | nil =>
    simp [fromString, emptyGraph]
  | append_singleton w' a ih =>
    rw [fromString_concat, card_compose_eq_sum, ih]
    dsimp [singletonGraph]
    simp only [length_append, length_cons, length_nil, zero_add]

theorem fromString_length_eq_of_iso {w₁ w₂ : List α} (h : fromString D w₁ ≃g fromString D w₂) :
    w₁.length = w₂.length := by
  rw [← card_fromString_eq_length, ← card_fromString_eq_length]
  exact card_eq_of_iso h

/-- The canonical homomorphism from the free monoid of strings to the `DGraph` monoid. -/
def mk' : List α →* DGraph D where
  toFun := fun w => ⟦fromString D w⟧
  map_one' := by rfl
  map_mul' := by
    intro w₁ w₂
    change ⟦fromString D (w₁ ++ w₂)⟧ = ⟦compose (fromString D w₁) (fromString D w₂)⟧
    apply Quotient.sound
    exact fromString_append_iso_compose _ _

theorem sink_of_compose_singleton (γ : DependenceGraph D) (a : α) :
    IsSink (compose γ (singletonGraph D a)) (Sum.inr Unit.unit) := by
  intro w h_edge
  cases w <;> dsimp [compose, singletonGraph] at h_edge

theorem remove_singleton_iso_self (w : List α) (a : α) :
    let γ := compose (fromString D w) (singletonGraph D a)
    let v_last : γ.V := Sum.inr ()
    removeVertex γ v_last ≃g fromString D w := by
  apply isomorphic_symm
  apply Nonempty.intro
  refine ⟨Equiv.mk ?_ ?_ ?_ ?_, ?_, ?_⟩
  · intro v
    dsimp [compose, removeVertex]
    refine ⟨Sum.inl v, ?_⟩
    simp only [reduceCtorEq, not_false_eq_true]
  · intro ⟨u, hu⟩
    dsimp [compose, removeVertex] at u
    cases u with
    | inl u₁ =>
      exact u₁
    | inr PUnit.unit =>
      exfalso
      apply hu
      rfl
  · intro v
    rfl
  · intro ⟨u, hu⟩
    dsimp [compose, removeVertex] at u
    cases u with
    | inl u₁ =>
      rfl
    | inr PUnit.unit =>
      exfalso
      apply hu
      rfl
  · intro v
    rfl
  · intro v₁ v₂
    rfl

theorem removeVertex_iso_congr {γ₁ γ₂ : DependenceGraph D} (h : γ₁ ≃g γ₂) (v : γ₁.V) :
    removeVertex γ₁ v ≃g removeVertex γ₂ (h.some.toEquiv v) := by
  apply Nonempty.intro
  refine ⟨?_, ?_, ?_⟩
  · refine Equiv.subtypeEquiv h.some.toEquiv ?_
    intro u
    rw [@not_iff_not, Equiv.apply_eq_iff_eq]
  · intro u
    dsimp [removeVertex]
    rw [h.some.preserves_label']
  · intro u₁ u₂
    dsimp [removeVertex]
    rw [h.some.preserves_arcs']

theorem removeVertex_compose_inl_iso {γ₁ γ₂ : DependenceGraph D} (v : γ₁.V) :
    removeVertex (compose γ₁ γ₂) (Sum.inl v) ≃g compose (removeVertex γ₁ v) γ₂ := by
  apply Nonempty.intro
  refine ⟨Equiv.mk ?_ ?_ ?_ ?_, ?_, ?_⟩
  · intro ⟨u, hu⟩
    dsimp [removeVertex, compose]
    cases u with
    | inl u₁ =>
      refine Sum.inl ⟨u₁, ?_⟩
      intro heq
      apply hu
      rw [heq]
    | inr u₂ =>
      exact Sum.inr u₂
  · intro u
    dsimp [removeVertex, compose] at u ⊢
    cases u with
    | inl u₁ =>
      refine ⟨Sum.inl u₁.val, ?_⟩
      simp [u₁.property]
    | inr u₂ =>
      refine ⟨Sum.inr u₂, ?_⟩
      simp
  · intro ⟨u, _⟩
    cases u <;> rfl
  · intro u
    cases u <;> rfl
  · intro ⟨u, hu⟩
    dsimp [compose, removeVertex]
    cases u <;> rfl
  · intro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    dsimp [compose, removeVertex]
    cases u₁ <;> cases u₂ <;> rfl

theorem removeVertex_sink_iso_cancelRight [DecidableEq α]
    (w : List α) (a : α)
    (sink : (fromString D w).V)
    (h_sink : IsSink (fromString D w) sink)
    (h_label : (fromString D w).φ sink = a) :
    removeVertex (fromString D w) sink ≃g fromString D (w ÷ a) := by
  induction w using reverseRecOn with
  | nil =>
    dsimp [fromString, emptyGraph] at sink
    contradiction
  | append_singleton w' b ih =>
    generalize hγ : fromString D (w' ++ [b]) = γ at sink h_sink h_label ⊢
    rw [fromString_concat] at hγ
    subst hγ
    by_cases heq : b = a
    · subst heq
      simp
      have h_is_last : sink = Sum.inr () := by
        cases sink with
        | inl u₁ =>
          exfalso
          have h_edge :
              (compose (fromString D w') (singletonGraph D b)).R (Sum.inl u₁) (Sum.inr ()) := by
            dsimp [compose, singletonGraph] at h_label ⊢
            rw [h_label]
            exact D.refl b
          exact h_sink (Sum.inr ()) h_edge
        | inr u₂ =>
          rfl
      subst h_is_last
      exact remove_singleton_iso_self w' b
    · have heq' : ¬a = b := fun a_1 => heq (Eq.symm a_1)
      simp [append_cancelRight, heq']
      rw [fromString_concat]
      have h_is_left : ∃ u, sink = Sum.inl u := by
        cases sink with
        | inl u₁ =>
          use u₁
        | inr u₂ =>
          dsimp [compose, singletonGraph] at h_label
          contradiction
      have ⟨u, hu⟩ := h_is_left
      subst hu
      have h_sink_u : IsSink (fromString D w') u := by
        intro v h_edge
        have h_edge' :
            (compose (fromString D w') (singletonGraph D b)).R (Sum.inl u) (Sum.inl v) := by
          dsimp [compose]
          exact h_edge
        exact h_sink (Sum.inl v) h_edge'
      have h_label_u : (fromString D w').φ u = a := by
        dsimp [compose] at h_label
        exact h_label
      have h_iso := ih u h_sink_u h_label_u
      apply isomorphic_trans (removeVertex_compose_inl_iso u)
      exact compose_congr h_iso (isomorphic_refl _)

/-- The homomorphism from the free monoid of strings onto the graph monoid defined as
  $\phi(w)=\langle w\rangle$ is a dependence morphism. -/
def dependenceGraphDependenceMorphism [DecidableEq α] :
    DependenceMorphism (inducedIndependence D) (DGraph D) where
  toFun := mk'
  A1 := by
    intro w hw
    replace hw := Quotient.exact hw
    change fromString D w ≈ fromString D [] at hw
    replace hw := fromString_length_eq_of_iso hw
    rw [length_nil] at hw
    exact length_eq_zero_iff.mp hw
  A2 := by
    intro a b h_indep
    apply Quotient.sound
    apply isomorphic_trans (fromString_append_iso_compose [a] [b])
    apply isomorphic_symm
    apply isomorphic_trans (fromString_append_iso_compose [b] [a])
    apply Nonempty.intro
    refine ⟨Equiv.sumComm _ _, ?_, ?_⟩
    · intro v
      dsimp [fromString, compose, emptyGraph, singletonGraph]
      cases v <;> rfl
    · intro v₁ v₂
      dsimp [fromString, compose, emptyGraph, singletonGraph] at v₁ v₂
      dsimp [inducedIndependence] at h_indep
      rcases v₁ with (u₁ | u₁) | (u₁ | u₁)
      · cases u₁
      · rcases v₂ with (u₂ | u₂) | (u₂ | u₂)
        · cases u₂
        · rfl
        · cases u₂
        · dsimp [fromString, compose, emptyGraph, singletonGraph]
          constructor
          · intro h_rel
            exact h_indep (Dependence.symm D b a h_rel)
          · exact False.elim
      · cases u₁
      · rcases v₂ with (u₂ | u₂) | (u₂ | u₂)
        · cases u₂
        · dsimp [fromString, compose, emptyGraph, singletonGraph]
          exact Iff.symm (iff_false_intro h_indep)
        · cases u₂
        · rfl
  A3 := by
    intro w₁ w₂ a heq
    have h_iso := Quotient.exact heq
    have h_a_sink := sink_of_compose_singleton (fromString D w₁) a
    rw [fromString_concat] at h_iso
    let node_a : ((fromString D w₁).compose (singletonGraph D a)).V := Sum.inr Unit.unit
    let img_a := h_iso.some.toEquiv node_a
    have h_a_label : ((fromString D w₁).compose (singletonGraph D a)).φ node_a = a := by rfl
    have h_img_a_sink : IsSink (fromString D w₂) img_a := by
      intro u h_edge
      rw [← h_iso.some.toEquiv.apply_symm_apply u, ← h_iso.some.preserves_arcs'] at h_edge
      exact h_a_sink ((Nonempty.some h_iso).toEquiv.symm u) h_edge
    have h_img_a_label : (fromString D w₂).φ img_a = a := by
      rw [← h_iso.some.preserves_label']
      exact h_a_label
    have h₁ :
        fromString D w₁ ≃g
        removeVertex ((fromString D w₁).compose (singletonGraph D a)) node_a :=
      isomorphic_symm (remove_singleton_iso_self w₁ a)
    have h₂ :
        removeVertex ((fromString D w₁).compose (singletonGraph D a)) node_a ≃g
        removeVertex (fromString D w₂) img_a :=
      removeVertex_iso_congr h_iso node_a
    have h₃ :
        removeVertex (fromString D w₂) img_a ≃g
        fromString D (w₂ ÷ a) :=
      removeVertex_sink_iso_cancelRight w₂ a img_a h_img_a_sink h_img_a_label
    apply Quotient.sound
    exact isomorphic_trans (isomorphic_trans h₁ h₂) h₃
  A4 := by
    intro w₁ w₂ a b ⟨h_iso, hab⟩
    dsimp [inducedIndependence]
    replace ⟨h_iso⟩ := Quotient.exact h_iso
    have h_a_sink := sink_of_compose_singleton (fromString D w₁) a
    rw [fromString_concat, fromString_concat] at h_iso
    let node_a : ((fromString D w₁).compose (singletonGraph D a)).V := Sum.inr Unit.unit
    let node_b : ((fromString D w₂).compose (singletonGraph D b)).V := Sum.inr Unit.unit
    let img_a := h_iso.toEquiv node_a
    have h_img_a_sink : IsSink ((fromString D w₂).compose (singletonGraph D b)) img_a := by
      intro w' h_edge
      rw [← h_iso.toEquiv.apply_symm_apply w'] at h_edge
      rw [← h_iso.preserves_arcs'] at h_edge
      exact h_a_sink _ h_edge
    have h_label_a : ((fromString D w₂).compose (singletonGraph D b)).φ img_a = a := by
      rw [← h_iso.preserves_label']
      rfl
    cases h_img_a : img_a with
    | inl u =>
      have h_no_edge := h_img_a_sink node_b
      rw [h_img_a] at h_no_edge h_label_a
      dsimp [compose, singletonGraph, node_b] at h_no_edge h_label_a
      rw [h_label_a] at h_no_edge
      exact h_no_edge
    | inr v =>
      exfalso
      rw [h_img_a] at h_label_a
      dsimp [compose, singletonGraph] at h_label_a
      exact hab (Eq.symm h_label_a)

/-- The trace monoid and `DGraph` are isomorphic. -/
noncomputable def traceMonoidIsoDGraph [DecidableEq α] :
    Trace (inducedIndependence D) ≃* DGraph D := by
  apply dependenceMorphismIso
    traceDependenceMorphism
    Quotient.mk_surjective
    dependenceGraphDependenceMorphism
    (by
      intro γ_q
      induction γ_q using Quotient.inductionOn with
      | h γ =>
        have ⟨w, hw⟩ := fromString_surjective γ
        use w
        dsimp [dependenceGraphDependenceMorphism, mk']
        apply Quotient.sound
        exact hw
    )

end DependenceGraph

end TraceTheory
