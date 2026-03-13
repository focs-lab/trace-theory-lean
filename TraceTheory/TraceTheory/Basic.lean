import TraceTheory.Defs

open List

namespace TraceTheory

variable {α : Type*} {I : Independence α}

theorem length_eq_of_eqv {u v : List α} (h : TraceEqv I u v) :
    u.length = v.length := by
  induction h with
  | swap _ _ _ => rfl
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => simp [ih₁, ih₂]

theorem mem_iff_mem {u v : List α} (a : α) (h : TraceEqv I u v) :
    (a ∈ u ↔ a ∈ v) := by
  induction h with
  | swap _ _ _ => simp [or_comm]
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => simp [ih₁, ih₂]

/-- The mirror rule. -/
theorem reverse_eqv_of_eqv {u v : List α} (h : TraceEqv I u v) :
    TraceEqv I u.reverse v.reverse := by
  induction h with
  | swap a b h => simp [TraceEqv.swap b a (I.symm a b h)]
  | refl u' => apply TraceEqv.refl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => simp [ih₂.compat ih₁]

/-- The projection rule. -/
theorem proj_eqv_of_eqv {u v : List α} {S : Finset α} [DecidableEq α] (h : TraceEqv I u v) :
    TraceEqv I (proj S u) (proj S v) := by
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

theorem proj_eq_of_eqv {u v : List α} [DecidableEq α]
    (D : Dependence α) (h : TraceEqv (inducedIndependence D) u v)
    (a b : α) (h_dep : D.rel a b) :
    proj {a, b} u = proj {a, b} v := by
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
      dsimp [inducedIndependence] at h_indep
      contradiction
    · simp [filter, ha', hb']
    · simp [filter, ha', hb']
    · simp [filter, ha', hb']
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | compat _ _ ih₁ ih₂ => simp [ih₁, ih₂]

theorem cancelRight_congr {u v : List α} [DecidableEq α] (a : α) (h : TraceEqv I u v) :
    TraceEqv I (u ÷ a) (v ÷ a) := by
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
    expose_names
    by_cases h_mem : a ∈ w₃
    · simp [h_mem, (mem_iff_mem a t₂).mp h_mem, t₁.compat ih₂]
    · simp [h_mem, (mem_iff_mem a t₂).mpr.mt h_mem, ih₁.compat t₂]

theorem erase_congr {u v : List α} [DecidableEq α] (a : α) (h : TraceEqv I u v) :
    TraceEqv I (u.erase a) (v.erase a) := by
  have h_erase (w : List α) : w.erase a = (w.reverse ÷ a).reverse := by simp [cancelRight]
  simp only [h_erase]
  apply reverse_eqv_of_eqv
  apply cancelRight_congr
  apply reverse_eqv_of_eqv
  exact h

theorem append_cancel_left {w u v : List α} [DecidableEq α] (h : TraceEqv I (w ++ u) (w ++ v)) :
    TraceEqv I u v := by
  induction w with
  | nil => simpa
  | cons a w' ih =>
    replace h := erase_congr a h
    simp only [cons_append, erase_cons_head] at h
    exact ih h

theorem append_cancel_right {w u v : List α} [DecidableEq α] (h : TraceEqv I (u ++ w) (v ++ w)) :
    TraceEqv I u v := by
  replace h := reverse_eqv_of_eqv h
  simp only [reverse_append] at h
  replace h := reverse_eqv_of_eqv (append_cancel_left h)
  simp only [reverse_reverse] at h
  exact h

theorem append_cancel_middle {l r u v : List α} [DecidableEq α]
    (h : TraceEqv I (l ++ u ++ r) (l ++ v ++ r)) :
    TraceEqv I u v :=
  append_cancel_left (append_cancel_right h)

instance [DecidableEq α] : CancelMonoid (Trace I) where
  mul_left_cancel := by
    intro t₁ t₂ t₃
    refine Quotient.inductionOn₃ t₁ t₂ t₃ (fun w₁ w₂ w₃ => ?_)
    intro heq
    apply Quotient.sound
    simp only at heq
    exact append_cancel_left (Quotient.exact heq)
  mul_right_cancel := by
    intro t₁ t₂ t₃
    refine Quotient.inductionOn₃ t₁ t₂ t₃ (fun w₁ w₂ w₃ => ?_)
    intro heq
    apply Quotient.sound
    simp only at heq
    exact append_cancel_right (Quotient.exact heq)

lemma eqv_length_eq_two {a b : α} {w : List α} (h : TraceEqv I [a, b] w) :
    w = [a, b] ∨ w = [b, a] := by
  rcases length_eq_two.mp (length_eq_of_eqv h).symm with ⟨c, d, rfl⟩
  by_cases heq : a = b
  · subst heq
    have hc : c = a := by simpa using (mem_iff_mem c h.symm).mp
    have hd : d = a := by simpa using (mem_iff_mem d h.symm).mp
    simp [hc, hd]
  · have ha : a = c ∨ a = d := by simpa using (mem_iff_mem a h).mp
    have hb : b = c ∨ b = d := by simpa using (mem_iff_mem b h).mp
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · contradiction
    · left
      rfl
    · right
      rfl
    · contradiction

lemma eqv_singletons {a b : α} (h : TraceEqv I [a] [b]) : a = b := by
  generalize hu : ([a] : List α) = u at h
  generalize hv : ([b] : List α) = v at h
  induction h generalizing a b with
  | swap _ _ _ => cases hu
  | refl _ =>
    subst hv
    injection hu
  | symm _ ih => exact (ih hv hu).symm
  | trans t₁ t₂ _ _ =>
    have ht₁ := mem_iff_mem a t₁
    have ht₂ := mem_iff_mem a t₂
    have h_trans := ht₁.trans ht₂
    subst hu hv
    simpa using h_trans
  | compat t₁ t₂ ih₁ ih₂ =>
    rcases singleton_eq_append_iff.mp hu with ⟨hw₁, hw₃⟩ | ⟨hw₁, hw₃⟩
    <;> rcases singleton_eq_append_iff.mp hv with ⟨hw₂, hw₄⟩ | ⟨hw₂, hw₄⟩
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
  generalize hu : [a, b] = u at h
  generalize hv : [b, a] = v at h
  induction h generalizing a b with
  | swap c d h_rel =>
    injection hu
    injection hv
    simp_all
  | refl _ =>
    cases hu.trans hv.symm
    contradiction
  | symm _ ih => exact I.symm b a (ih (hne.symm) hv hu)
  | trans t₁ _ ih₁ ih₂ =>
    expose_names
    rw [← hu] at t₁
    rcases eqv_length_eq_two t₁ with h₁ | h₂
    · exact ih₂ hne h₁.symm hv
    · exact ih₁ hne hu h₂.symm
  | compat t₁ t₂ ih₁ ih₂ =>
    expose_names
    have h₁ : w₁.length + w₃.length = 2 := by simp [← length_append, ← hu]
    have h₂ : w₂.length + w₄.length = 2 := by simp [← length_append, ← hv]
    have ht₁ := length_eq_of_eqv t₁
    have ht₂ := length_eq_of_eqv t₂
    rcases Nat.add_eq_two_iff.mp h₁ with ⟨hw₁, hw₃⟩ | ⟨hw₁, hw₃⟩ | ⟨hw₁, hw₃⟩
    <;> rcases Nat.add_eq_two_iff.mp h₂ with ⟨hw₂, hw₄⟩ | ⟨hw₂, hw₄⟩ | ⟨hw₂, hw₄⟩
    · rw [length_eq_zero_iff.mp hw₁, nil_append] at hu
      rw [length_eq_zero_iff.mp hw₂, nil_append] at hv
      exact ih₂ hne hu hv
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
      simp at hu hv
      rw [← hu.left, ← hv.left] at heq
      contradiction
    · rw [hw₁, hw₂] at ht₁
      contradiction
    · rw [hw₁, hw₂] at ht₁
      contradiction
    · rw [hw₁, hw₂] at ht₁
      contradiction
    · rw [length_eq_zero_iff.mp hw₃, append_nil] at hu
      rw [length_eq_zero_iff.mp hw₄, append_nil] at hv
      exact ih₁ hne hu hv

theorem indep_and_exists_of_eqv_of_tail_ne {u v : List α} {a b : α} [DecidableEq α]
    (h : TraceEqv I (u ++ [a]) (v ++ [b]))
    (hne : a ≠ b) :
    I.rel a b ∧
    ∃ w, TraceEqv I u (w ++ [b]) ∧ TraceEqv I v (w ++ [a]) := by
  have h_cancel_a := by simpa [hne] using cancelRight_congr a h
  have h_cancel_b := by simpa [hne.symm] using (cancelRight_congr b h).symm
  have h_cancel_ab := by simpa [hne] using cancelRight_congr b h_cancel_a
  have h_cancel_b_concat_b := h_cancel_a.trans (h_cancel_ab.compat (TraceEqv.refl [b])).symm
  have h_cancel_b_concat_ba := h_cancel_b_concat_b.compat (TraceEqv.refl [a])
  have h_cancel_b_concat_ab := h_cancel_b.compat (TraceEqv.refl [b])
  have h_tail := by simpa using h_cancel_b_concat_ab.symm.trans (h.symm.trans h_cancel_b_concat_ba)
  have h_ab_ba := append_cancel_left h_tail
  exact ⟨indep_of_comm_eqv_of_ne h_ab_ba hne, u ÷ b, h_cancel_b_concat_b, h_cancel_b⟩

theorem independent_symm {u v : List α} (h : Independent I u v) :
    Independent I v u := by
  intro a ha b hb
  exact I.symm b a (h b hb a ha)

theorem indep_of_comm_singleton {u v w : List α} {a : α} [DecidableEq α]
    (h : TraceEqv I (u ++ [a] ++ v) (w ++ [a])) (h_mem : a ∉ v) :
    Independent I [a] v := by
  induction v using reverseRecOn generalizing w with
  | nil => simp
  | append_singleton x b ih =>
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
    rcases hb' with h₁ | h₂
    · exact h b' h₁
    · subst h₂
      exact I.symm b' a' hr

theorem comm_singleton_of_indep {w : List α} {a : α} (h : Independent I [a] w) :
    TraceEqv I (w ++ [a]) ([a] ++ w) := by
  induction w using reverseRecOn with
  | nil => apply TraceEqv.refl
  | append_singleton w' b ih =>
    simp at h
    have haw' : Independent I [a] w' := by
      intro a' ha' b' hb'
      simp at ha'
      subst ha'
      exact h b' (Or.intro_left (b' = b) hb')
    have ht := ih haw'
    have hb := ht.compat (TraceEqv.refl [b])
    have hab : TraceEqv I (w' ++ [b] ++ [a]) (w' ++ [a] ++ [b]) := by
      have hr := h b
      simp at hr ⊢
      exact (TraceEqv.refl w').compat (TraceEqv.swap b a (I.symm a b hr))
    exact hab.trans hb

theorem indep_of_indep_of_eqv {u v w: List α}
    (h : Independent I u v) (ht : TraceEqv I v w) :
    Independent I u w := by
  intro a ha b hb
  have h_alph := mem_iff_mem b ht
  have h_mem := h_alph.mpr hb
  exact h a ha b h_mem

theorem indep_of_indep_append_right {u v w: List α} (h : Independent I w (u ++ v)) :
    Independent I w u ∧ Independent I w v := by
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

theorem levi_lemma {u v x y : List α} [DecidableEq α] (h : TraceEqv I (u ++ v) (x ++ y)) :
    ∃ z₁ z₂ z₃ z₄, Independent I z₂ z₃
    ∧ TraceEqv I u (z₁ ++ z₂) ∧ TraceEqv I v (z₃ ++ z₄)
    ∧ TraceEqv I x (z₁ ++ z₃) ∧ TraceEqv I y (z₂ ++ z₄) := by
  induction y using reverseRecOn generalizing u v with
  | nil =>
    use u, [], v, []
    simp [TraceEqv.refl] at *
    exact h.symm
  | append_singleton w e ih =>
    by_cases hev : e ∈ v
    · have ⟨v', v'', hv, hv''⟩ := rightmost_occurrence hev
      have h_cancel := cancelRight_congr e h
      subst hv
      simp only [append_cancelRight] at h_cancel
      simp [hv''] at h_cancel
      have ⟨z₁', z₂', z₃', z₄', h_indep, ht₁, ht₂, ht₃, ht₄⟩ := ih h_cancel
      use z₁', z₂', z₃', z₄' ++ [e], h_indep
      replace ht₄ := ht₄.compat (TraceEqv.refl [e])
      have he : TraceEqv I (v'' ++ [e]) ([e] ++ v'') := by
        simp [← append_assoc] at h
        exact comm_singleton_of_indep (indep_of_comm_singleton h hv'')
      have hv'e := TraceEqv.symm ((TraceEqv.refl v').compat he)
      simp only [← append_assoc] at hv'e ⊢
      replace ht₂ := hv'e.trans (ht₂.compat (TraceEqv.refl [e]))
      exact ⟨ht₁, ht₂, ht₃, ht₄⟩
    · have heu : e ∈ u := by
        have h_alph := by simpa using mem_iff_mem e h
        exact Or.resolve_right h_alph hev
      have ⟨u', u'', hu, hu''⟩ := rightmost_occurrence heu
      have h_cancel := cancelRight_congr e h
      subst hu
      simp only [append_cancelRight] at h_cancel
      simp [hev, hu''] at h_cancel
      rw [← append_assoc] at h_cancel
      have ⟨z₁', z₂', z₃', z₄', h_indep, ht₁, ht₂, ht₃, ht₄⟩ := ih h_cancel
      have h_indep' : Independent I [e] (u'' ++ v) := by
        rw [← append_assoc, append_assoc] at h
        exact indep_of_comm_singleton h (not_mem_append hu'' hev)
      replace h_indep : Independent I (z₂' ++ [e]) z₃' := by
        intro a ha b hb
        simp at ha
        rcases ha with h₁ | h₂
        · exact h_indep a h₁ b hb
        · subst h₂
          have h_indep'' := indep_of_indep_of_eqv (indep_of_indep_append_right h_indep').right ht₂
          simp at h_indep''
          exact h_indep'' b (Or.inl hb)
      use z₁', z₂' ++ [e], z₃', z₄', h_indep
      have heu'' : TraceEqv I (u'' ++ [e]) ([e] ++ u'') :=
        comm_singleton_of_indep (indep_of_indep_append_right h_indep').left
      have hu'e := TraceEqv.symm ((TraceEqv.refl u').compat heu'')
      simp only [← append_assoc] at hu'e
      replace ht₁ := hu'e.trans (ht₁.compat (TraceEqv.refl [e]))
      have hez₄' : TraceEqv I (z₄' ++ [e]) ([e] ++ z₄') := by
        have h_indep'' := indep_of_indep_of_eqv (indep_of_indep_append_right h_indep').right ht₂
        exact comm_singleton_of_indep (indep_of_indep_append_right h_indep'').right
      have hz₂'e := (TraceEqv.refl z₂').compat hez₄'
      simp only [← append_assoc] at hz₂'e ⊢
      replace ht₄ := (ht₄.compat (TraceEqv.refl [e])).trans hz₂'e
      exact ⟨ht₁, ht₂, ht₃, ht₄⟩

theorem projection_lemma {u v : List α} [DecidableEq α] (D : Dependence α) :
    TraceEqv (inducedIndependence D) u v ↔
    ∀ a b, D.rel a b → proj {a, b} u = proj {a, b} v := by
  constructor
  · apply proj_eq_of_eqv
  · intro h
    induction u using reverseRecOn generalizing v with
    | nil =>
      have hv : v = [] := by
        have h_symb : ∀ x, proj {x, x} [] = proj {x, x} v := fun x => h x x (D.refl x)
        dsimp [proj] at h_symb
        cases v with
        | nil =>
          rfl
        | cons c _ =>
          have h_absurd := h_symb c
          simp at h_absurd
      subst hv
      apply TraceEqv.refl
    | append_singleton u' c ih =>
      have hv : c ∈ v := by
        have hc := h c c (D.refl c)
        simp [proj] at hc
        apply mem_of_mem_filter
        rw [← hc]
        simp
      have ⟨v', v'', heq, hc⟩ := rightmost_occurrence hv
      have h_indep : Independent (inducedIndependence D) [c] v'' := by
        intro c hc b hb
        simp at hc
        subst hc
        dsimp [inducedIndependence]
        by_cases h_dep : D.rel c b
        · have hc' := h c b h_dep
          rw [heq] at hc'
          dsimp [proj] at hc'
          simp only [filter_append] at hc'
          have hv''_nonempty : v''.filter (· ∈ ({c, b} : Finset α)) ≠ [] := by
            intro h_empty
            have h_b_in : b ∈ v''.filter (· ∈ ({c, b} : Finset α)) := by
              rw [mem_filter]
              simp [hb]
            rw [h_empty] at h_b_in
            contradiction
          have h_lhs_end :
              (u'.filter (· ∈ ({c, b} : Finset α)) ++
              [c].filter (· ∈ ({c, b} : Finset α))).getLast? = some c := by
            simp
          have h_rhs_end :
              (v'.filter (· ∈ ({c, b} : Finset α)) ++
              [c].filter (· ∈ ({c, b} : Finset α)) ++
              v''.filter (· ∈ ({c, b} : Finset α))).getLast?
              = (v''.filter (· ∈ ({c, b} : Finset α))).getLast? := by
            exact getLast?_append_of_ne_nil _ hv''_nonempty
          rw [← hc', h_lhs_end] at h_rhs_end
          have h_absurd : c ∈ v'' := by
            have h_mem := mem_of_getLast? h_rhs_end.symm
            simp at h_mem
            exact h_mem
          contradiction
        · exact h_dep
      have h_comm : TraceEqv (inducedIndependence D) v (v' ++ v'' ++ [c]) := by
        rw [heq, append_assoc, append_assoc]
        apply TraceEqv.compat (TraceEqv.refl v')
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
      · have hw''_empty : v''.filter (· ∈ ({a, b} : Finset α)) = [] := by
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
        rw [filter_append, hw''_empty, append_nil]
        nth_rw 2 [filter_append] at h_proj
        rw [hw''_empty, append_nil, filter_append, filter_append] at h_proj
        exact List.append_cancel_right h_proj
      · simp at hc_in
        simp [proj, filter_append, hc_in] at h_proj
        simp
        exact h_proj

theorem exists_gcp {u v w : List α} [DecidableEq α]
    (hu : isPrefix I ⟦u⟧ ⟦w⟧) (hv : isPrefix I ⟦v⟧ ⟦w⟧) :
    ∃ g, isPrefix I ⟦g⟧ ⟦u⟧ ∧ isPrefix I ⟦g⟧ ⟦v⟧
    ∧ (∀ g', isPrefix I ⟦g'⟧ ⟦u⟧ → isPrefix I ⟦g'⟧ ⟦v⟧ → isPrefix I ⟦g'⟧ ⟦g⟧) := by
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

theorem comm_append_of_indep {w₁ w₂ : List α} (h : Independent I w₁ w₂) :
    TraceEqv I (w₁ ++ w₂) (w₂ ++ w₁) := by
  induction w₁ using reverseRecOn with
  | nil =>
    rw [nil_append, append_nil]
    exact TraceEqv.refl _
  | append_singleton w' a ih =>
    replace h := indep_of_indep_append_right (independent_symm h)
    have ha := comm_singleton_of_indep (independent_symm h.right)
    have hw'a := ((TraceEqv.refl w').compat ha).symm
    rw [← append_assoc, ← append_assoc] at hw'a
    apply hw'a.trans
    rw [← append_assoc]
    exact (ih (independent_symm h.left)).compat (TraceEqv.refl [a])

theorem exists_lcd {u v w : List α} [DecidableEq α]
    (hu : isPrefix I ⟦u⟧ ⟦w⟧) (hv : isPrefix I ⟦v⟧ ⟦w⟧) :
    ∃ d, isPrefix I ⟦u⟧ ⟦d⟧ ∧ isPrefix I ⟦v⟧ ⟦d⟧
    ∧ (∀ d', isPrefix I ⟦u⟧ ⟦d'⟧ → isPrefix I ⟦v⟧ ⟦d'⟧ → isPrefix I ⟦d⟧ ⟦d'⟧) := by
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
      have h_indep_yy : Independent I (y₁ ++ y₂) (y₁ ++ y₃) := by
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

end TraceTheory
