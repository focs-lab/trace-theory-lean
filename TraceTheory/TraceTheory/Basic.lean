import TraceTheory.Defs
import TraceTheory.List

namespace TraceTheory

open Dependence Independence List

variable {α : Type*} {I : Independence α}

theorem length_eq_of_eqv {x y : List α} (h : TraceEqv I x y) :
    x.length = y.length := by
  induction h with
  | swap _ _ _ => rfl
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => simp [ih₁, ih₂]

theorem mem_iff_mem {x y : List α} (a : α) (h : TraceEqv I x y) :
    (a ∈ x ↔ a ∈ y) := by
  induction h with
  | swap _ _ _ => simp [or_comm]
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => simp [ih₁, ih₂]

/-- The mirror rule. -/
theorem reverse_eqv_of_eqv {x y : List α} (h : TraceEqv I x y) :
    TraceEqv I x.reverse y.reverse := by
  induction h with
  | swap a b h => simp [TraceEqv.swap b a (I.symm a b h)]
  | refl u' => apply TraceEqv.refl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => simp [ih₂.compat ih₁]

/-- The projection rule. -/
theorem proj_eqv_of_eqv {x y : List α} {S : Finset α} [DecidableEq α] (h : TraceEqv I x y) :
    TraceEqv I (x.proj S) (y.proj S) := by
  induction h with
  | swap a b h_indep =>
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [proj, ha, hb]
    · apply TraceEqv.swap
      exact h_indep
    · apply TraceEqv.refl
    · apply TraceEqv.refl
    · apply TraceEqv.refl
  | refl _ => apply TraceEqv.refl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => simp [ih₁.compat ih₂]

theorem proj_eq_of_eqv_of_dep {x y : List α} [DecidableEq α]
    (D : Dependence α) (h : TraceEqv D.inducedIndependence x y)
    (a b : α) (h_dep : D.rel a b) :
    x.proj {a, b} = y.proj {a, b} := by
  induction h with
  | swap a' b' h_indep =>
    dsimp [proj]
    by_cases ha' : a' ∈ ({a, b} : Finset α) <;> by_cases hb' : b' ∈ ({a, b} : Finset α)
    · have h_dep : D.rel a' b' := by
        simp at ha' hb'
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · apply D.refl
        · exact h_dep
        · exact D.symm b' a' h_dep
        · apply D.refl
      contradiction
    · simp [filter, ha', hb']
    · simp [filter, ha', hb']
    · simp [filter, ha', hb']
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => simp [ih₁, ih₂]

theorem cancelRight_congr {x y : List α} [DecidableEq α] (a : α) (h : TraceEqv I x y) :
    TraceEqv I (x ÷ a) (y ÷ a) := by
  induction h with
  | swap b c h_indep =>
    by_cases hab : b = a <;> by_cases hac : c = a
    · subst hab hac
      apply TraceEqv.refl
    · simp [cancelRight, hab, hac]
      apply TraceEqv.refl
    · simp [cancelRight, hab, hac]
      apply TraceEqv.refl
    · simp [cancelRight, hab, hac]
      apply TraceEqv.swap
      exact h_indep
  | refl _ => apply TraceEqv.refl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat t₁ t₂ ih₁ ih₂ =>
    rename_i x' y' z w
    by_cases h_mem : a ∈ z
    · simp [h_mem, (mem_iff_mem a t₂).mp h_mem, t₁.compat ih₂]
    · simp [h_mem, (mem_iff_mem a t₂).mpr.mt h_mem, ih₁.compat t₂]

theorem erase_congr {x y : List α} [DecidableEq α] (a : α) (h : TraceEqv I x y) :
    TraceEqv I (x.erase a) (y.erase a) := by
  have h_erase (w : List α) : w.erase a = (w.reverse ÷ a).reverse := by simp [cancelRight]
  simp only [h_erase]
  apply reverse_eqv_of_eqv
  apply cancelRight_congr
  apply reverse_eqv_of_eqv
  exact h

theorem append_cancel_left {w x y : List α} [DecidableEq α] (h : TraceEqv I (w ++ x) (w ++ y)) :
    TraceEqv I x y := by
  induction w with
  | nil => simpa
  | cons a w' ih =>
    replace h := by simpa only [cons_append, erase_cons_head] using erase_congr a h
    exact ih h

theorem append_cancel_right {w x y : List α} [DecidableEq α] (h : TraceEqv I (x ++ w) (y ++ w)) :
    TraceEqv I x y := by
  replace h := by simpa only [reverse_append] using reverse_eqv_of_eqv h
  replace h := by simpa [reverse_append] using reverse_eqv_of_eqv (append_cancel_left h)
  exact h

theorem append_cancel_middle {l r x y : List α} [DecidableEq α]
    (h : TraceEqv I (l ++ x ++ r) (l ++ y ++ r)) :
    TraceEqv I x y :=
  append_cancel_left (append_cancel_right h)

instance [DecidableEq α] : CancelMonoid (Trace I) where
  mul_left_cancel := by
    intro t₁ t₂ t₃
    refine Quotient.inductionOn₃ t₁ t₂ t₃ (fun x₁ x₂ x₃ => ?_)
    intro heq
    apply Quotient.sound
    simp only at heq
    exact append_cancel_left (Quotient.exact heq)
  mul_right_cancel := by
    intro t₁ t₂ t₃
    refine Quotient.inductionOn₃ t₁ t₂ t₃ (fun x₁ x₂ x₃ => ?_)
    intro heq
    apply Quotient.sound
    simp only at heq
    exact append_cancel_right (Quotient.exact heq)

instance : Membership α (Trace I) where
  mem t a := Quotient.lift
    (fun (x : List α) => a ∈ x)
    (by
      intro x y heqv
      simp only [eq_iff_iff]
      exact mem_iff_mem a heqv
    )
    t

theorem append_left_right {I : Independence α} {x y : List α}
    (l r : List α) (h : TraceEqv I x y) :
    TraceEqv I (l ++ x ++ r) (l ++ y ++ r) :=
  TraceEqv.compat (TraceEqv.compat (TraceEqv.refl l) h) (TraceEqv.refl r)

lemma eqvGen_append_right {w x y : List α}
    (h : Relation.EqvGen (SwapOnce I) x y) :
    Relation.EqvGen (SwapOnce I) (x ++ w) (y ++ w) := by
  induction h with
  | rel x y h_swap =>
    apply Relation.EqvGen.rel
    rcases h_swap with ⟨x', y', a, b, h_indep⟩
    simpa using SwapOnce.swap x' (y' ++ w) a b h_indep
  | refl _ => apply Relation.EqvGen.refl
  | symm _ _ _ ih => apply Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => apply Relation.EqvGen.trans _ _ _ ih₁ ih₂

lemma eqvGen_append_left {w x y : List α}
    (h : Relation.EqvGen (SwapOnce I) x y) :
    Relation.EqvGen (SwapOnce I) (w ++ x) (w ++ y) := by
  induction h with
  | rel x y h_swap =>
    apply Relation.EqvGen.rel
    rcases h_swap with ⟨x', y', a, b, h_indep⟩
    simpa using SwapOnce.swap (w ++ x') y' a b h_indep
  | refl _ => apply Relation.EqvGen.refl
  | symm _ _ _ ih => apply Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => apply Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem eqv_iff_eqvGen_swapOnce {x y : List α} :
    TraceEqv I x y ↔ Relation.EqvGen (SwapOnce I) x y := by
  constructor
  · intro h
    induction h with
    | swap a b h_indep =>
      apply Relation.EqvGen.rel
      simpa using SwapOnce.swap [] [] a b h_indep
    | refl _ => apply Relation.EqvGen.refl
    | symm _ ih => apply Relation.EqvGen.symm _ _ ih
    | trans _ _ ih₁ ih₂ => apply Relation.EqvGen.trans _ _ _ ih₁ ih₂
    | compat t₁ t₂ ih₁ ih₂ =>
      rename_i w₁ w₂ w₃ w₄
      apply Relation.EqvGen.trans (w₁ ++ w₃) (w₂ ++ w₃) (w₂ ++ w₄)
      · apply eqvGen_append_right ih₁
      · apply eqvGen_append_left ih₂
  · intro h
    induction h with
    | rel x y h_comm =>
      rcases h_comm with ⟨x', y', a, b, h_indep⟩
      apply append_left_right
      exact TraceEqv.swap a b h_indep
    | refl _ => apply TraceEqv.refl
    | symm _ _ _ ih => apply TraceEqv.symm ih
    | trans _ _ _ _ _ ih1 ih2 => apply TraceEqv.trans ih1 ih2

lemma eqv_length_eq_two {a b : α} {x : List α} (h : TraceEqv I [a, b] x) :
    x = [a, b] ∨ x = [b, a] := by
  rcases length_eq_two.mp (length_eq_of_eqv h).symm with ⟨c, d, rfl⟩
  by_cases heq : a = b
  · subst heq
    have hc : c = a := by simpa using (mem_iff_mem c h.symm).mp
    have hd : d = a := by simpa using (mem_iff_mem d h.symm).mp
    simp [hc, hd]
  · have ha : a = c ∨ a = d := by simpa using (mem_iff_mem a h).mp
    have hb : b = c ∨ b = d := by simpa using (mem_iff_mem b h).mp
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | contradiction | exact Or.inl rfl | exact Or.inr rfl

lemma eqv_singletons {a b : α} (h : TraceEqv I [a] [b]) : a = b := by
  generalize hx : [a] = x at h
  generalize hy : [b] = y at h
  induction h generalizing a b with
  | swap _ _ _ => cases hx
  | refl _ =>
    subst hy
    injection hx
  | symm _ ih => exact (ih hy hx).symm
  | trans t₁ t₂ _ _ =>
    have ht₁ := mem_iff_mem a t₁
    have ht₂ := mem_iff_mem a t₂
    have h_trans := ht₁.trans ht₂
    subst hx hy
    simpa using h_trans
  | compat t₁ t₂ ih₁ ih₂ =>
    rcases singleton_eq_append_iff.mp hx with ⟨hw₁, hw₃⟩ | ⟨hw₁, hw₃⟩
    <;> rcases singleton_eq_append_iff.mp hy with ⟨hw₂, hw₄⟩ | ⟨hw₂, hw₄⟩
    · exact ih₂ hw₃.symm hw₄.symm
    · have ht₁ := length_eq_of_eqv t₁
      subst hw₁ hw₂
      contradiction
    · have ht₁ := length_eq_of_eqv t₁
      subst hw₁ hw₂
      contradiction
    · exact ih₁ hw₁.symm hw₂.symm

theorem indep_of_comm_eqv_of_ne {a b : α} (h : TraceEqv I [a, b] [b, a]) (hne : a ≠ b) :
    I.rel a b := by
  generalize hx : [a, b] = x at h
  generalize hy : [b, a] = y at h
  induction h generalizing a b with
  | swap c d h_rel =>
    injection hx
    injection hy
    simp_all
  | refl _ =>
    cases hx
    cases hy
    contradiction
  | symm _ ih => exact I.symm b a (ih (hne.symm) hy hx)
  | trans t₁ t₂ ih₁ ih₂ =>
    rw [← hx] at t₁
    rcases eqv_length_eq_two t₁ with h₁ | h₂
    · exact ih₂ hne h₁.symm hy
    · exact ih₁ hne hx h₂.symm
  | compat t₁ t₂ ih₁ ih₂ =>
    rename_i w₁ w₂ w₃ w₄
    have h₁ : w₁.length + w₃.length = 2 := by simp [← length_append, ← hx]
    have h₂ : w₂.length + w₄.length = 2 := by simp [← length_append, ← hy]
    have ht₁ := length_eq_of_eqv t₁
    have ht₂ := length_eq_of_eqv t₂
    rcases Nat.add_eq_two_iff.mp h₁ with ⟨hw₁, hw₃⟩ | ⟨hw₁, hw₃⟩ | ⟨hw₁, hw₃⟩
    <;> rcases Nat.add_eq_two_iff.mp h₂ with ⟨hw₂, hw₄⟩ | ⟨hw₂, hw₄⟩ | ⟨hw₂, hw₄⟩
    · rw [length_eq_zero_iff.mp hw₁, nil_append] at hx
      rw [length_eq_zero_iff.mp hw₂, nil_append] at hy
      exact ih₂ hne hx hy
    · rw [hw₁, hw₂] at ht₁
      contradiction
    . rw [hw₁, hw₂] at ht₁
      contradiction
    · rw [hw₁, hw₂] at ht₁
      contradiction
    · rcases length_eq_one_iff.mp hw₁ with ⟨c, hc⟩
      rcases length_eq_one_iff.mp hw₂ with ⟨d, hd⟩
      subst hc hd
      have heq : c = d := eqv_singletons t₁
      simp at hx hy
      rw [← hx.left, ← hy.left] at heq
      contradiction
    · rw [hw₁, hw₂] at ht₁
      contradiction
    · rw [hw₁, hw₂] at ht₁
      contradiction
    · rw [hw₁, hw₂] at ht₁
      contradiction
    · rw [length_eq_zero_iff.mp hw₃, append_nil] at hx
      rw [length_eq_zero_iff.mp hw₄, append_nil] at hy
      exact ih₁ hne hx hy

theorem indep_and_exists_of_eqv_of_tail_ne {x y : List α} {a b : α} [DecidableEq α]
    (h : TraceEqv I (x ++ [a]) (y ++ [b]))
    (hne : a ≠ b) :
    I.rel a b ∧
    ∃ w, TraceEqv I x (w ++ [b]) ∧ TraceEqv I y (w ++ [a]) := by
  have h_cancel_a := by simpa [hne] using cancelRight_congr a h
  have h_cancel_b := by simpa [hne.symm] using (cancelRight_congr b h).symm
  have h_cancel_ab := by simpa [hne] using cancelRight_congr b h_cancel_a
  have h_cancel_b_concat_b := h_cancel_a.trans (h_cancel_ab.compat (TraceEqv.refl [b])).symm
  have h_cancel_b_concat_ba := h_cancel_b_concat_b.compat (TraceEqv.refl [a])
  have h_cancel_b_concat_ab := h_cancel_b.compat (TraceEqv.refl [b])
  have h_tail := by simpa using h_cancel_b_concat_ab.symm.trans (h.symm.trans h_cancel_b_concat_ba)
  have h_ab_ba := append_cancel_left h_tail
  exact ⟨indep_of_comm_eqv_of_ne h_ab_ba hne, x ÷ b, h_cancel_b_concat_b, h_cancel_b⟩

theorem independent_symm {x y : List α} (h : I.Independent x y) :
    I.Independent y x := by
  intro a ha b hb
  exact I.symm b a (h b hb a ha)

theorem indep_of_comm_singleton {w x y : List α} {a : α} [DecidableEq α]
    (h : TraceEqv I (x ++ [a] ++ y) (w ++ [a])) (h_mem : a ∉ y) :
    I.Independent [a] y := by
  induction y using reverseRecOn generalizing w with
  | nil => simp
  | append_singleton y' b ih =>
    intro a' ha' b' hb'
    simp at ha' hb' h_mem
    subst ha'
    rcases h_mem with ⟨h_mem', hne⟩
    rw [eq_comm] at hne
    rw [← append_assoc] at h
    have hr := (indep_and_exists_of_eqv_of_tail_ne h hne).left
    replace h := cancelRight_congr b h
    replace h := by simpa only [append_singleton_cancelRight, Ne.symm hne, ↓reduceIte] using h
    replace h := by simpa using ih h h_mem'
    rcases hb' with hb' | rfl
    · exact h b' hb'
    · exact I.symm b' a' hr

theorem comm_singleton_of_indep {x : List α} {a : α} (h : I.Independent [a] x) :
    TraceEqv I (x ++ [a]) ([a] ++ x) := by
  induction x using reverseRecOn with
  | nil => apply TraceEqv.refl
  | append_singleton x' b ih =>
    simp only [Independent, mem_cons, not_mem_nil, or_false, mem_append, forall_eq] at h
    have h_indep : I.Independent [a] x' := by
      intro a' ha' b' hb'
      simp only [mem_cons, not_mem_nil, or_false] at ha'
      subst ha'
      exact h b' (Or.inl hb')
    have ht := ih h_indep
    have hb := ht.compat (TraceEqv.refl [b])
    have hab : TraceEqv I (x' ++ [b] ++ [a]) (x' ++ [a] ++ [b]) := by
      have hr := h b
      simp only [or_true, forall_const, append_assoc, cons_append, nil_append] at hr ⊢
      exact (TraceEqv.refl x').compat (TraceEqv.swap b a (I.symm a b hr))
    exact hab.trans hb

theorem indep_of_indep_of_eqv {x y z: List α}
    (h : I.Independent x y) (ht : TraceEqv I y z) :
    I.Independent x z := by
  intro a ha b hb
  have h_alph := mem_iff_mem b ht
  have h_mem := h_alph.mpr hb
  exact h a ha b h_mem

theorem indep_of_indep_append_right {w x y: List α} (h : I.Independent w (x ++ y)) :
    I.Independent w x ∧ I.Independent w y := by
  constructor
  · intro a ha b hb
    apply h
    apply ha
    apply mem_append.mpr
    left
    exact hb
  · intro a ha b hb
    apply h
    apply ha
    apply mem_append.mpr
    right
    exact hb

theorem comm_append_of_indep {x y : List α} (h : I.Independent x y) :
    TraceEqv I (x ++ y) (y ++ x) := by
  induction x using reverseRecOn with
  | nil =>
    rw [nil_append, append_nil]
    exact TraceEqv.refl _
  | append_singleton x' a ih =>
    replace h := indep_of_indep_append_right (independent_symm h)
    have ha := comm_singleton_of_indep (independent_symm h.right)
    have hw'a := ((TraceEqv.refl x').compat ha).symm
    rw [← append_assoc, ← append_assoc] at hw'a
    apply hw'a.trans
    rw [← append_assoc]
    exact (ih (independent_symm h.left)).compat (TraceEqv.refl [a])

lemma indep_and_exists_of_equiv_of_head_ne {a b : α} {w x : List α} [DecidableEq α]
    (I : Independence α) (h : TraceEqv I ([a] ++ w) ([b] ++ x)) (hne : a ≠ b) :
    I.rel a b ∧ ∃ u v, x = u ++ [a] ++ v ∧ I.Independent [a] u := by
  have h_rev := reverse_eqv_of_eqv h
  simp at h_rev
  have ⟨h_indep, w_rev', _, hx_rev⟩ := indep_and_exists_of_eqv_of_tail_ne h_rev hne
  constructor
  · exact h_indep
  · have ha := (mem_iff_mem a hx_rev).mpr
    simp at ha
    have ⟨u, v, hx⟩ := leftmost_occurrence ha
    use u, v
    constructor
    · exact hx.left
    · rw [hx.left] at hx_rev
      simp only [reverse_append, reverse_cons, reverse_nil, nil_append] at hx_rev
      rw [← List.append_assoc] at hx_rev
      have h_mem_rev : a ∉ u.reverse := by
        rw [mem_reverse]
        exact hx.right
      have h_indep_rev := indep_of_comm_singleton hx_rev h_mem_rev
      simp [mem_reverse] at h_indep_rev ⊢
      exact h_indep_rev

lemma indep_of_indep_flatten_right {x : List α} {ys : List (List α)}
    (i : ℕ) (hi : i < ys.length) (h : Independent I x ys.flatten) :
    Independent I x (ys[i]) := by
  induction ys generalizing i with
  | nil => contradiction
  | cons v vs' ih =>
    rw [flatten_cons] at h
    cases i with
    | zero => exact (indep_of_indep_append_right h).left
    | succ i' =>
      simp only [length_cons, Nat.add_lt_add_iff_right] at hi
      exact ih i' hi (indep_of_indep_append_right h).right

theorem levi_lemma {u v x y : List α} [DecidableEq α] (h : TraceEqv I (u ++ v) (x ++ y)) :
    ∃ z₁ z₂ z₃ z₄, I.Independent z₂ z₃
    ∧ TraceEqv I u (z₁ ++ z₂) ∧ TraceEqv I v (z₃ ++ z₄)
    ∧ TraceEqv I x (z₁ ++ z₃) ∧ TraceEqv I y (z₂ ++ z₄) := by
  induction y using reverseRecOn generalizing u v with
  | nil =>
    use u, [], v, []
    simp_all [TraceEqv.refl, TraceEqv.symm]
  | append_singleton w e ih =>
    by_cases hev : e ∈ v
    · rcases rightmost_occurrence hev with ⟨v', v'', rfl, hv''⟩
      have h_cancel : TraceEqv I (u ++ (v' ++ v'')) (x ++ w) := by
        have he := by simpa only [append_cancelRight] using cancelRight_congr e h
        simpa [hv''] using he
      rcases ih h_cancel with ⟨z₁', z₂', z₃', z₄', h_indep, ht₁, ht₂, ht₃, ht₄⟩
      use z₁', z₂', z₃', z₄' ++ [e], h_indep
      and_intros
      · exact ht₁
      · have hv' : TraceEqv I (v' ++ [e] ++ v'') (v' ++ v'' ++ [e]) := by
          have he : TraceEqv I (v'' ++ [e]) ([e] ++ v'') := by
            simp only [← append_assoc] at h
            exact comm_singleton_of_indep (indep_of_comm_singleton h hv'')
          simpa using TraceEqv.symm ((TraceEqv.refl v').compat he)
        simpa using hv'.trans (ht₂.compat (TraceEqv.refl [e]))
      · exact ht₃
      · simpa using ht₄.compat (TraceEqv.refl _)
    · have heu : e ∈ u := by
        have h_alph := by simpa using mem_iff_mem e h
        simp_all
      rcases rightmost_occurrence heu with ⟨u', u'', rfl, hu''⟩
      have h_cancel : TraceEqv I (u' ++ u'' ++ v) (x ++ w) := by
        have he := by simpa only [append_cancelRight] using cancelRight_congr e h
        simpa [hev, hu''] using he
      rcases ih h_cancel with ⟨z₁', z₂', z₃', z₄', h_indep, ht₁, ht₂, ht₃, ht₄⟩
      have h_indep' : I.Independent [e] (u'' ++ v) := by
        rw [← append_assoc, append_assoc] at h
        exact indep_of_comm_singleton h (not_mem_append hu'' hev)
      replace h_indep : I.Independent (z₂' ++ [e]) z₃' := by
        intro a ha b hb
        simp only [mem_append, mem_cons, not_mem_nil, or_false] at ha
        rcases ha with ha | rfl
        · exact h_indep a ha b hb
        · have h_indep'' := by
            simpa using indep_of_indep_of_eqv (indep_of_indep_append_right h_indep').right ht₂
          exact h_indep'' b (Or.inl hb)
      use z₁', z₂' ++ [e], z₃', z₄', h_indep
      and_intros
      · have hu' : TraceEqv I (u' ++ [e] ++ u'') (u' ++ u'' ++ [e]) := by
          have he : TraceEqv I (u'' ++ [e]) ([e] ++ u'') :=
            comm_singleton_of_indep (indep_of_indep_append_right h_indep').left
          simpa using TraceEqv.symm ((TraceEqv.refl u').compat he)
        simpa using hu'.trans (ht₁.compat (TraceEqv.refl [e]))
      · exact ht₂
      · exact ht₃
      · have hz : TraceEqv I (z₂' ++ z₄' ++ [e]) (z₂' ++ [e] ++ z₄') := by
          have he : TraceEqv I (z₄' ++ [e]) ([e] ++ z₄') :=
            comm_singleton_of_indep
              (indep_of_indep_append_right
                (indep_of_indep_of_eqv (indep_of_indep_append_right h_indep').right ht₂)).right
          simpa using (TraceEqv.refl z₂').compat he
        simpa using (ht₄.compat (TraceEqv.refl [e])).trans hz

theorem levi_lemma_gen {u v : List α} {ts : List (List α)} [DecidableEq α]
    (h : TraceEqv I (u ++ v) ts.flatten) :
    ∃ ps qs : List (List α),
      ps.length = ts.length ∧
      qs.length = ts.length ∧
      TraceEqv I u ps.flatten ∧
      TraceEqv I v qs.flatten ∧
      (∀ i (ht : i < ts.length) (hp : i < ps.length) (hq : i < qs.length),
        TraceEqv I ts[i] (ps[i] ++ qs[i])) ∧
      (∀ i j (hi : i < qs.length) (hj : j < ps.length), i < j →
        Independent I qs[i] ps[j]) := by
  induction ts generalizing u v with
  | nil =>
    simp only [List.flatten_nil] at h
    have h_len := length_eq_of_eqv h
    simp only [List.length_append, List.length_nil] at h_len
    have hu : u = [] := List.length_eq_zero_iff.mp (by omega)
    have hv : v = [] := List.length_eq_zero_iff.mp (by omega)
    subst hu hv
    use [], []
    simp [TraceEqv.refl]
  | cons t tsuf ih =>
    rcases levi_lemma h with ⟨p, psuf, q, qsuf, h_ind, h_up, h_vq, h_tpq, h_tpq_suf⟩
    rcases ih h_tpq_suf.symm with ⟨ps_i, qs_i, ih_p_len, ih_q_len, ih_p, ih_q, ih_tpq, ih_ind⟩
    use p :: ps_i, q :: qs_i
    and_intros
    · simp [ih_p_len]
    · simp [ih_q_len]
    · apply TraceEqv.trans h_up
      simp only [List.flatten_cons]
      exact TraceEqv.compat (TraceEqv.refl p) ih_p
    · apply TraceEqv.trans h_vq
      simp only [List.flatten_cons]
      exact TraceEqv.compat (TraceEqv.refl q) ih_q
    · intro i ht hp hq
      cases i with
      | zero => exact h_tpq
      | succ i' => apply ih_tpq i'
    · intro i j hi hj hij
      cases j with
      | zero => contradiction
      | succ j' =>
        cases i with
        | zero =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
          exact indep_of_indep_flatten_right j' hj
            (indep_of_indep_of_eqv (independent_symm h_ind) ih_p)
        | succ i' =>
          apply ih_ind i' j'
          exact Nat.succ_lt_succ_iff.mp hij

theorem projection_lemma {x y : List α} [DecidableEq α] (D : Dependence α) :
    TraceEqv D.inducedIndependence x y ↔
    ∀ a b, D.rel a b → x.proj {a, b} = y.proj {a, b} := by
  constructor
  · apply proj_eq_of_eqv_of_dep
  · intro h
    induction x using reverseRecOn generalizing y with
    | nil =>
      have hy_nil : y = [] := by
        have h_symb : ∀ a, proj {a, a} [] = proj {a, a} y := fun x => h x x (D.refl x)
        cases y with
        | nil => rfl
        | cons c _ => simpa [proj] using h_symb c
      subst hy_nil
      apply TraceEqv.refl
    | append_singleton x' c ih =>
      have h_mem : c ∈ y := by
        have hc := by simpa [proj] using h c c (D.refl c)
        apply mem_of_mem_filter
        rw [← hc]
        simp
      rcases rightmost_occurrence h_mem with ⟨y', y'', heq, h_mem⟩
      have h_indep : D.inducedIndependence.Independent [c] y'' := by
        intro c hc b hb
        simp at hc
        subst hc
        dsimp [inducedIndependence]
        by_cases h_dep : D.rel c b
        · have hc := h c b h_dep
          rw [heq] at hc
          simp only [proj_append] at hc
          have hy''_nonempty : proj {c, b} y'' ≠ [] := by
            intro h_empty
            have h_b_in : b ∈ y''.filter (· ∈ ({c, b} : Finset α)) := by
              rw [mem_filter]
              simp [hb]
            simp only [proj] at h_empty
            rw [h_empty] at h_b_in
            contradiction
          have h_lhs_end : (proj {c, b} x' ++ proj {c, b} [c]).getLast? = some c := by simp [proj]
          have h_rhs_end :
              (proj {c, b} y' ++ proj {c, b} [c] ++ proj {c, b} y'').getLast? =
              (proj {c, b} y'').getLast? := by
            exact getLast?_append_of_ne_nil _ hy''_nonempty
          rw [← hc, h_lhs_end] at h_rhs_end
          have h_absurd : c ∈ y'' := by simpa [proj] using mem_of_getLast? h_rhs_end.symm
          contradiction
        · exact h_dep
      have h_comm : TraceEqv (inducedIndependence D) y (y' ++ y'' ++ [c]) := by
        rw [heq, append_assoc, append_assoc]
        apply TraceEqv.compat (TraceEqv.refl y')
        apply TraceEqv.symm
        apply comm_singleton_of_indep
        exact h_indep
      apply TraceEqv.symm
      apply TraceEqv.trans h_comm
      refine TraceEqv.compat ?_ (TraceEqv.refl [c])
      apply TraceEqv.symm
      apply ih
      intro a b h_dep
      have h_proj := h a b h_dep
      rw [heq] at h_proj
      dsimp [proj]
      by_cases hc_in : c ∈ ({a, b} : Finset α)
      · have hy''_empty : y''.filter (· ∈ ({a, b} : Finset α)) = [] := by
          apply filter_eq_nil_iff.mpr
          intro c' hc'
          simp at hc_in ⊢
          have hc'_indep := h_indep c (mem_singleton_self c) c' hc'
          rcases hc_in with rfl | rfl <;> constructor <;> intro hc'_eq <;> subst hc'_eq
          · exact (inducedIndependence D).irrefl c' hc'_indep
          · exact hc'_indep h_dep
          · exact hc'_indep (D.symm c' c h_dep)
          · exact (inducedIndependence D).irrefl c' hc'_indep
        dsimp [proj] at h_proj
        rw [filter_append, hy''_empty, append_nil]
        nth_rw 2 [filter_append] at h_proj
        rw [hy''_empty, append_nil, filter_append, filter_append] at h_proj
        exact List.append_cancel_right h_proj
      · simp at hc_in
        simp [proj, filter_append, hc_in] at h_proj
        simp
        exact h_proj

namespace Trace

theorem exists_gcp {u v w : List α} [DecidableEq α]
    (hu : IsPrefix I ⟦u⟧ ⟦w⟧) (hv : IsPrefix I ⟦v⟧ ⟦w⟧) :
    ∃ g,
      IsPrefix I ⟦g⟧ ⟦u⟧ ∧ IsPrefix I ⟦g⟧ ⟦v⟧ ∧
      ∀ g', IsPrefix I ⟦g'⟧ ⟦u⟧ → IsPrefix I ⟦g'⟧ ⟦v⟧ → IsPrefix I ⟦g'⟧ ⟦g⟧ := by
  have ⟨u', hu'⟩ := hu
  have ⟨v', hv'⟩ := hv
  simp at hu' hv'
  replace hu' := Quotient.exact hu'
  replace hv' := Quotient.exact hv'
  have ⟨z₁, z₂, z₃, _, h_indep, huz, _, hvz, _⟩ := levi_lemma (hu'.trans hv'.symm)
  use z₁
  and_intros
  · use z₂
    apply Quotient.sound
    exact huz.symm
  · use z₃
    apply Quotient.sound
    exact hvz.symm
  · intro g' hg'u hg'v
    have ⟨w₁, hw₁⟩ := hg'u
    have ⟨w₂, hw₂⟩ := hg'v
    replace hw₁ := Quotient.exact hw₁
    replace hw₂ := Quotient.exact hw₂
    replace hw₁ := hw₁.trans huz
    replace hw₂ := hw₂.trans hvz
    have ⟨y₁, y₂, y₃, y₄, h_indep_yy, hy_g', _, hy_z₁, hy_z₂⟩ := levi_lemma hw₁
    have h_y₂_empty : y₂ = [] := by
      have hyw : TraceEqv I (y₂ ++ w₂) (y₃ ++ z₃) := by
        have hywz := (hy_g'.compat (TraceEqv.refl w₂)).symm.trans hw₂
        replace hywz := (hywz.trans (hy_z₁.compat (TraceEqv.refl z₃)))
        rw [append_assoc, append_assoc] at hywz
        exact append_cancel_left hywz
      by_cases he : y₂ = []
      · exact he
      · exfalso
        let ⟨a, ha⟩ := exists_mem_of_ne_nil y₂ he
        have ha_z₂ := (mem_iff_mem a hy_z₂).mpr (mem_append.mpr (Or.inl ha))
        have ha_yz := (mem_iff_mem a hyw).mp (mem_append.mpr (Or.inl ha))
        simp only [mem_append] at ha_yz
        have ha_y₃ : a ∈ y₃ := by
          rcases ha_yz with hay | haz
          · exact hay
          · exfalso
            exact I.irrefl a (h_indep a ha_z₂ a haz)
        exact I.irrefl a (h_indep_yy a ha a ha_y₃)
    rw [h_y₂_empty, append_nil] at hy_g'
    use y₃
    apply Quotient.sound
    exact (hy_g'.compat (TraceEqv.refl y₃)).trans hy_z₁.symm

theorem exists_lcd {u v w : List α} [DecidableEq α]
    (hu : IsPrefix I ⟦u⟧ ⟦w⟧) (hv : IsPrefix I ⟦v⟧ ⟦w⟧) :
    ∃ d,
      IsPrefix I ⟦u⟧ ⟦d⟧ ∧ IsPrefix I ⟦v⟧ ⟦d⟧ ∧
      ∀ d', IsPrefix I ⟦u⟧ ⟦d'⟧ → IsPrefix I ⟦v⟧ ⟦d'⟧ → IsPrefix I ⟦d⟧ ⟦d'⟧ := by
  have ⟨u', hu'⟩ := hu
  have ⟨v', hv'⟩ := hv
  simp at hu' hv'
  replace hu' := Quotient.exact hu'
  replace hv' := Quotient.exact hv'
  have ⟨z₁, z₂, z₃, z₄, h_indep, huz, hu'z, hvz, hv'z⟩ := levi_lemma (hu'.trans hv'.symm)
  use z₁ ++ z₂ ++ z₃
  and_intros
  · use z₃
    apply Quotient.sound
    exact huz.compat (TraceEqv.refl z₃)
  · use z₂
    apply Quotient.sound
    have hz := ((TraceEqv.refl z₁).compat (comm_append_of_indep h_indep)).symm
    rw [← append_assoc, ← append_assoc] at hz
    apply (hvz.compat (TraceEqv.refl z₂)).trans
    exact hz
  · intro d' hud' hvd'
    have ⟨w₁, hw₁⟩ := hud'
    have ⟨w₂, hw₂⟩ := hvd'
    replace hw₁ := Quotient.exact hw₁
    replace hw₂ := Quotient.exact hw₂
    have huv : TraceEqv I (u ++ w₁) (v ++ w₂) := hw₁.trans hw₂.symm
    have hzw : TraceEqv I (z₂ ++ w₁) (z₃ ++ w₂) := by
      have huzw := huz.compat (TraceEqv.refl w₁)
      have hvzw := hvz.compat (TraceEqv.refl w₂)
      have huvzw := huzw.symm.trans (huv.trans hvzw)
      rw [append_assoc, append_assoc] at huvzw
      exact append_cancel_left huvzw
    have ⟨y₁, y₂, y₃, y₄, _, hy_z₂, hy_w₁, hy_z₃, _⟩ := levi_lemma hzw
    have h_y₁_empty : y₁ = [] := by
      have h_indep_yy : I.Independent (y₁ ++ y₂) (y₁ ++ y₃) := by
        intro a ha b hb
        exact h_indep a ((mem_iff_mem a hy_z₂).mpr ha) b ((mem_iff_mem b hy_z₃).mpr hb)
      by_cases he : y₁ = []
      · exact he
      · exfalso
        let ⟨a, ha⟩ := exists_mem_of_ne_nil y₁ he
        have ha_left : a ∈ y₁ ++ y₂ := mem_append.mpr (Or.inl ha)
        have ha_right : a ∈ y₁ ++ y₃ := mem_append.mpr (Or.inl ha)
        have h_rel := h_indep_yy a ha_left a ha_right
        exact I.irrefl a h_rel
    rw [h_y₁_empty, nil_append] at hy_z₂ hy_z₃
    have hd' := hw₁.symm.trans (huz.compat (TraceEqv.refl w₁))
    replace hd' := hd'.trans ((TraceEqv.refl (z₁ ++ z₂)).compat hy_w₁)
    replace hd' :=
      hd'.trans ((TraceEqv.refl (z₁ ++ z₂)).compat (hy_z₃.symm.compat (TraceEqv.refl y₄)))
    rw [← append_assoc] at hd'
    use y₄
    apply Quotient.sound
    exact hd'.symm

theorem not_mem_one (a : α) : a ∉ (1 : Trace I) := by
  intro h
  rcases h

theorem exists_mem_of_ne_one (t : Trace I) (h : t ≠ 1) : ∃ a, a ∈ t := by
  rcases t with ⟨_ | ⟨a, w⟩⟩
  · exact (h rfl).elim
  · exact ⟨a, List.mem_cons_self⟩

theorem mem_mul_iff {a : α} {s t : Trace I} : a ∈ s * t ↔ a ∈ s ∨ a ∈ t := by
  rcases s
  rcases t
  exact List.mem_append

/-- Predicate for dependence of symbols `a` and `b` in trace `t`. -/
def DepEdge (t : Trace I) (a b : α) := I.inducedDependence.rel a b ∧ a ∈ t ∧ b ∈ t

/-- Predicate for transitive dependence of symbols `a` and `b` in trace `t`. -/
def DepPath (t : Trace I) (a b : α) := Relation.TransGen t.DepEdge a b

/-- A trace `t` is connected if all its symbols are transitively dependent. -/
def IsConnected (I : Independence α) (t : Trace I) := ∀ a ∈ t, ∀ b ∈ t, t.DepPath a b

/-- Traces `u` and `v` are independent if every symbol in `u` is independent of
  every symbol in `v`. -/
def Independent (u v : Trace I) := ∀ a ∈ u, ∀ b ∈ v, I.rel a b

theorem not_depPath_mul_of_indep {a b : α} {u v : Trace I}
    (huv : u.Independent v) (ha : a ∈ u) (hb : b ∈ v) :
    ¬ (u * v).DepPath a b := by
  intro h
  induction h with
  | single h =>
    rename_i b
    exact h.1 (huv a ha b hb)
  | tail h h_tail ih =>
    rename_i b c
    simp only [imp_false] at ih
    have hbu : b ∈ u := by
      have hmul := mem_mul_iff.mp h_tail.2.1
      simp_all only [or_false]
    simp [DepEdge, inducedDependence] at h_tail
    exact h_tail.1 (huv b hbu c hb)

theorem not_isConnected_mul_of_indep {u v : Trace I}
    (h : u.Independent v) (hu : u ≠ 1) (hv : v ≠ 1) :
    ¬ (u * v).IsConnected I := by
  by_contra h_con
  have ⟨a, ha⟩ := exists_mem_of_ne_one u hu
  have ⟨b, hb⟩ := exists_mem_of_ne_one v hv
  have h_ab_con := h_con a (mem_mul_iff.mpr (Or.inl ha)) b (mem_mul_iff.mpr (Or.inr hb))
  have h_ab_dis := not_depPath_mul_of_indep h ha hb
  exact h_ab_dis h_ab_con

theorem mk'_eq_one_iff {x : List α} : ⟦x⟧ = (1 : Trace I) ↔ x = [] := by
  cases x with
  | nil =>
    simp only [iff_true]
    rfl
  | cons a u =>
    constructor
    · intro h
      simpa using length_eq_of_eqv (Quotient.exact h)
    · simp

def isEmpty : Trace I → Bool :=
  Quotient.lift List.isEmpty
    (by
      intro x y heqv
      cases x with
      | nil => rw [mk'_eq_one_iff.mp (Eq.symm (Quotient.sound heqv))]
      | cons a x' =>
        cases y with
        | nil => rw [mk'_eq_one_iff.mp (Quotient.sound heqv)]
        | cons b y' => rfl
    )

@[simp]
theorem isEmpty_iff {t : Trace I} : t.isEmpty = true ↔ t = 1:= by
  constructor
  · intro h
    rcases t
    rw [List.isEmpty_iff.mp h]
    rfl
  · intro h
    rw [h]
    rfl

theorem prod_filter_not_isEmpty (L : List (Trace I)) :
    (L.filter (fun x => !x.isEmpty)).prod = L.prod := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    by_cases ht : t.isEmpty = true
    · simp [isEmpty_iff.mp ht, ih]
    · simp [ht, ih]

end Trace

end TraceTheory
