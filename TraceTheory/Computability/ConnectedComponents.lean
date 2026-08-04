import Mathlib.Algebra.Group.PUnit
import TraceTheory.Computability.Hashiguchi
import TraceTheory.Computability.RegularExpressions

namespace TraceTheory

open Computability Dependence RegularExpression Trace Independence

variable {α : Type} {I : Independence α}

noncomputable instance : ∀ w x y, Decidable (List.DepPath I w x y) :=
  fun w x y => Classical.propDecidable (List.DepPath I w x y)

/-
  Helper function for the connected-components decomposition of a word.
  Decomposes a word `w` with respect to (transitive) dependence of symbols in `w₀`; see also `ccDec`.
-/
noncomputable def ccDec_aux (I : Independence α) (w₀ w : List α) : List (List α) :=
  match w with
  | [] => [[]]
  | a :: w =>
    match ccDec_aux I w₀ w with
    | [] => [] -- dummy value, unreachable by construction
    | v :: vs =>
      match v with
      | [] => [a] :: vs
      | b :: v =>
        if List.DepPath I w₀ a b
          then (a :: b :: v) :: vs
          else [a] :: (b :: v) :: vs

/-
  Connected-components decomposition of a given word `w`.
  The word is split between any pair of successive letters which are not connected;
  that is, the two letters are not transitively dependent in `w`.
-/
noncomputable def ccDec (I : Independence α) (w : List α) : List (List α) := ccDec_aux I w w

noncomputable def ccDec_aux_conn (I : Independence α) (w₀ w : List α) : Prop :=
  match w with
  | [] => True -- by convention
  | a :: w =>
    match ccDec_aux I w₀ w with
    | [] => False
    | v :: _ =>
      match v with
      | [] => True -- by convention to make casework easier (first char is inserted as `[[·]]` and not `[·] :: _`)
      | b :: _ => List.DepPath I w₀ a b

lemma ccDec_aux_nonempty (w₀ w : List α) : (ccDec_aux I w₀ w) ≠ [] := by
  induction w with
  | nil => simp [ccDec_aux]
  | cons a u ih =>
    simp [ccDec_aux]
    cases hs : ccDec_aux I w₀ u
    · simp [hs] at ih
    · simp
      rename_i c_head c_tail
      cases c_head with
      | nil => simp
      | cons b c_head =>
        simp
        by_cases hab : List.DepPath I w₀ a b
        all_goals simp [hab]

lemma ccDec_aux_zero_idx {w₀ w : List α} : 0 < (ccDec_aux I w₀ w).length := List.length_pos_iff.mpr (ccDec_aux_nonempty _ _)

lemma ccDec_aux_nonempty_head (I : Independence α) (u w : List α) (h : w ≠ []) :
    (ccDec_aux I u w)[0]'(ccDec_aux_zero_idx) ≠ [] := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    suffices hs_dec : ∃ _1 _2 _3, (ccDec_aux I u (a :: w)) = (_1 ::_2) :: _3 from by
      replace ⟨_1, _2, _3, hs_dec⟩ := hs_dec
      rw [List.getElem_of_eq hs_dec]
      simp
    simp [ccDec_aux]
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact ccDec_aux_nonempty _ _ ht
    · rename_i c_head c_tail
      simp [ht]
      cases c_head with
      | nil => simp
      | cons b c_head =>
        simp
        by_cases hab : List.DepPath I u a b
        all_goals simp [hab]

lemma ccDec_aux_len_C {u w : List α} {a : α} (h : ccDec_aux_conn I u (a :: w)) :
    (ccDec_aux I u (a :: w)).length = (ccDec_aux I u w).length := by
  simp [ccDec_aux_conn] at h
  let t := ccDec_aux I u w
  have ht : ccDec_aux I u w = t := rfl
  rcases t
  · simp [ht] at h
  · rename_i c_head c_tail
    simp [ht] at h
    cases c_head with
    | nil => simp [ccDec_aux, ht]
    | cons b c_head =>
      simp at h
      simp [ccDec_aux, ht, h]

lemma ccDec_aux_len_D {u w : List α} {a : α} (h : ¬ ccDec_aux_conn I u (a :: w)) :
    (ccDec_aux I u (a :: w)).length = (ccDec_aux I u w).length + 1 := by
  simp [ccDec_aux_conn] at h
  let t := ccDec_aux I u w
  have ht : ccDec_aux I u w = t := rfl
  rcases t
  · exfalso
    exact ccDec_aux_nonempty _ _ ht
  · rename_i c_head c_tail
    simp [ht] at h
    cases c_head with
    | nil =>
      cases w with
      | nil => simp at h
      | cons b w =>
        have := ccDec_aux_nonempty_head I u (b :: w) (List.cons_ne_nil b w)
        simp [List.getElem_of_eq ht] at this
    | cons b c_head =>
      simp at h
      simp [ccDec_aux, ht, h]

lemma ccDec_aux_len_D' {u w : List α} {a : α} (h : ¬ ccDec_aux_conn I u (a :: w)) :
    (ccDec_aux I u (a :: w)).length - 1 = (ccDec_aux I u w).length := by
  simp [ccDec_aux_len_D h]

lemma ccDec_aux_tail_C {u w : List α} {a : α} (h : ccDec_aux_conn I u (a :: w))
    (i : ℕ) (hi : i < (ccDec_aux I u (a :: w)).length) (hiz : i > 0) :
    (ccDec_aux I u (a :: w))[i] = (ccDec_aux I u w)[i]'(by rw [← ccDec_aux_len_C h]; exact hi) := by
  by_cases hw : w = []
  · simp [hw, ccDec_aux] at hi
    simp [hi] at hiz
  simp [ccDec_aux_conn] at h
  let t := ccDec_aux I u w
  have ht : ccDec_aux I u w = t := rfl
  rcases t
  · rw [ccDec_aux_len_C h] at hi
    simp [ht] at hi
  · rename_i c_head c_tail
    simp [ht] at h
    have : c_head ≠ [] := by
      have := ccDec_aux_nonempty_head I u w hw
      rw [List.getElem_of_eq ht] at this
      exact this
    cases c_head with
    | nil => simp at this
    | cons b c_head =>
      simp at h
      simp [ccDec_aux, ht, h] at hi ⊢
      have : ((a :: b :: c_head) :: c_tail)[i] =
          ((a :: b :: c_head) :: c_tail)[i - 1 + 1]'(Nat.add_lt_of_lt_sub (Nat.sub_lt_right_of_lt_add hiz hi)) := by
        rw [getElem_congr _ (show i - 1 + 1 = i from Nat.sub_add_cancel (Nat.succ_le_of_lt hiz))]
        simp
      rw [this]
      have : ((b :: c_head) :: c_tail)[i] =
          ((b :: c_head) :: c_tail)[i - 1 + 1]'(Nat.add_lt_of_lt_sub (Nat.sub_lt_right_of_lt_add hiz hi)) := by
        rw [getElem_congr _ (show i - 1 + 1 = i from Nat.sub_add_cancel (Nat.succ_le_of_lt hiz))]
        simp
      rw [this]
      simp

lemma ccDec_aux_tail_D {u w : List α} {a : α} (h : ¬ ccDec_aux_conn I u (a :: w))
    (i : ℕ) (hi : i + 1 < (ccDec_aux I u (a :: w)).length) :
    (ccDec_aux I u (a :: w))[i + 1] = (ccDec_aux I u w)[i]'(by rw [← ccDec_aux_len_D' h]; exact Nat.lt_sub_of_add_lt hi) := by
  by_cases hw : w = []
  · simp [hw, ccDec_aux_conn, ccDec_aux] at h
  simp [ccDec_aux_conn] at h
  let t := ccDec_aux I u w
  have ht : ccDec_aux I u w = t := rfl
  rcases t
  · rw [ccDec_aux_len_D h] at hi
    simp [ht] at hi
  · rename_i c_head c_tail
    simp [ht] at h
    have : c_head ≠ [] := by
      have := ccDec_aux_nonempty_head I u w hw
      rw [List.getElem_of_eq ht] at this
      exact this
    cases c_head with
    | nil => simp at this
    | cons b c_head =>
      simp at h
      simp [ccDec_aux, ht, h] at ⊢

lemma ccDec_aux_tail_D' {u w : List α} {a : α} (h : ¬ ccDec_aux_conn I u (a :: w))
    (i : ℕ) (hi : i - 1 < (ccDec_aux I u w).length) (hiz : i ≠ 0) :
    (ccDec_aux I u (a :: w))[i]'(by rw [ccDec_aux_len_D h]; exact lt_add_of_tsub_lt_right hi) = (ccDec_aux I u w)[i - 1] := by
  cases i with
  | zero => simp at hiz
  | succ i => apply ccDec_aux_tail_D h i

lemma ccDec_aux_elem_nonempty (u w : List α) (i : ℕ) (hi : i < (ccDec_aux I u w).length) (hz : w ≠ []) :
    (ccDec_aux I u w)[i] ≠ [] := by
  induction w generalizing i with
  | nil => simp at hz
  | cons a w ih =>
    clear hz
    by_cases hiz : i = 0
    · suffices hs_dec : (∃ _1 _2 _3, (ccDec_aux I u (a :: w)) = (_1 :: _2) :: _3) ∨ (ccDec_aux I u (a :: w)) = [] from by
        rcases hs_dec with ⟨hs_dec⟩
        · replace ⟨_1, _2, _3, hs_dec⟩ := hs_dec
          simp [hs_dec, hiz]
        · rename_i hs_dec
          simp [hs_dec] at hi
      simp [ccDec_aux]
      cases ccDec_aux I u w
      · simp
      · rename_i c_head c_tail
        simp
        cases c_head with
        | nil => simp
        | cons b c_head =>
          simp
          by_cases hab : List.DepPath I u a b
          all_goals simp [hab]
    · have hw : w ≠ [] := by
        by_contra hw
        simp [hw, ccDec_aux] at hi
        exact hiz hi
      by_cases hab : ccDec_aux_conn I u (a :: w)
      · rw [ccDec_aux_tail_C hab i hi (Nat.zero_lt_of_ne_zero hiz)]
        apply ih
        exact hw
      · rw [ccDec_aux_tail_D' hab i (by rw [ccDec_aux_len_D hab] at hi; omega) hiz]
        apply ih
        exact hw

lemma ccDec_aux_elem_nonempty_len (u w : List α) (i : ℕ) (hi : i < (ccDec_aux I u w).length) (hz : w ≠ []) :
    0 < (ccDec_aux I u w)[i].length :=
  List.length_pos_iff.mpr (@ccDec_aux_elem_nonempty α I _ _ _ hi hz)

lemma ccDec_aux_flatten (I : Independence α) (u w : List α) :
    (ccDec_aux I u w).flatten = w := by
  induction w with
  | nil => simp [ccDec_aux]
  | cons a w ih =>
    simp [ccDec_aux]
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact (ccDec_aux_nonempty _ _) ht
    · rename_i c_head c_tail
      simp [ht] at ih ⊢
      cases c_head with
      | nil => simp at ih ⊢; exact ih
      | cons b c_head =>
        by_cases hab : List.DepPath I u a b
        all_goals simp [hab] at ih ⊢; exact ih

lemma ccDec_flatten_prefix2 (L : List (List α)) (h : 1 < L.length) :
    List.IsPrefix (L[0] ++ L[1]) L.flatten := by
  cases L with
  | nil => simp at h
  | cons w L =>
    cases L with
    | nil => simp at h
    | cons v L => simp

lemma List.flatten_infix (L : List (List α)) (i : ℕ) (hi : i < L.length) :
    List.IsInfix L[i] L.flatten := by
  induction L generalizing i with
  | nil => simp at hi
  | cons w L ih =>
    cases i with
    | zero => exact List.infix_append_left
    | succ i =>
      simp
      exact List.infix_append_of_infix_right (ih i (Nat.succ_lt_succ_iff.mp hi))

lemma List.flatten_adj_infix (L : List (List α)) (i : ℕ) (hi : i + 1 < L.length) :
    List.IsInfix (L[i] ++ L[i + 1]) L.flatten := by
  induction L generalizing i with
  | nil => simp at hi
  | cons w L ih =>
    cases i with
    | zero =>
      cases L with
      | nil => simp at hi
      | cons v L =>
        simp [← List.append_assoc]
        exact List.infix_append_left
    | succ i =>
      simp
      exact List.infix_append_of_infix_right (ih i (Nat.succ_lt_succ_iff.mp hi))

lemma List.flatten_suffix (L : List (List α)) (h : L ≠ []) :
    List.IsSuffix (L.getLast h) L.flatten := by
  induction L with
  | nil => simp at h
  | cons w L ih =>
    cases L with
    | nil => simp
    | cons v L =>
      simp at ih ⊢
      exact List.suffix_append_of_suffix ih

lemma ccDec_aux_infix (I : Independence α) (u w : List α) (i : ℕ) (hi : i < (ccDec_aux I u w).length) :
    List.IsInfix (ccDec_aux I u w)[i] w := by
  nth_rw 2 [← ccDec_aux_flatten I u w]
  exact List.flatten_infix (ccDec_aux I u w) i hi

lemma ccDec_aux_adj_infix (I : Independence α) (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) :
    List.IsInfix ((ccDec_aux I u w)[i] ++ (ccDec_aux I u w)[i + 1]) w := by
  nth_rw 7 [← ccDec_aux_flatten I u w]
  exact List.flatten_adj_infix (ccDec_aux I u w) i hi

lemma ccDec_aux_prefix2 (I : Independence α) (u w : List α) (h : 1 < (ccDec_aux I u w).length) :
    List.IsPrefix ((ccDec_aux I u w)[0] ++ (ccDec_aux I u w)[1]) w := by
  nth_rw 7 [← ccDec_aux_flatten I u w]
  exact ccDec_flatten_prefix2 (ccDec_aux I u w) h

lemma ccDec_aux_suffix (I : Independence α) (u w : List α) :
    List.IsSuffix ((ccDec_aux I u w).getLast (ccDec_aux_nonempty u w)) w := by
  nth_rw 3 [← ccDec_aux_flatten I u w]
  exact List.flatten_suffix (ccDec_aux I u w) (ccDec_aux_nonempty u w)

lemma ccDec_across_infix (I : Independence α) (w : List α) (h : 1 < (ccDec I w).length) :
    List.IsInfix (
      ((ccDec I w).getLast (ccDec_aux_nonempty w w)) ++ (ccDec I w)[0] ++ (ccDec I w)[1]
    ) (w ++ w) := by
  unfold ccDec
  have ⟨s, hs⟩ := ccDec_aux_suffix I w w
  have ⟨t, ht⟩ := ccDec_aux_prefix2 I w w h
  use s, t
  simp only [List.append_assoc] at ht ⊢
  simp [ht]
  simp only [← List.append_assoc]
  rw [hs]

lemma ccDec_aux_head_conn (u w : List α) (hwu : w ⊆ u) :
    ∀ m n, m ∈ (ccDec_aux I u w)[0]'(ccDec_aux_zero_idx) → n ∈ (ccDec_aux I u w)[0]'(ccDec_aux_zero_idx) →
    List.DepPath I u m n := by
  induction w with
  | nil => simp [ccDec_aux]
  | cons a w ih =>
    intro m n hm hn
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact (ccDec_aux_nonempty _ _) ht
    · rename_i c_head c_tail
      cases c_head with
      | nil =>
        simp [ccDec_aux, ht] at hm hn
        rw [hm, hn]
        exact List.depPath_refl (hwu List.mem_cons_self)
      | cons b c_head =>
        simp [ccDec_aux, ht] at hm hn
        by_cases hab : List.DepPath I u a b
        · simp [hab] at hm hn
          simp [ht] at ih
          replace ih := ih (List.subset_of_cons_subset hwu)
          by_cases hma : m = a <;> by_cases hna : n = a
          · rw [hma, hna]
            exact List.depPath_refl (hwu List.mem_cons_self)
          · rw [hma]
            simp [hna] at hn
            cases hn with
            | inl hn =>
              rw [hn]
              exact hab
            | inr hn =>
              replace ih := ih b n (by simp) (by simp [hn])
              exact Relation.TransGen.trans hab ih
          · rw [hna]
            simp [hma] at hm
            cases hm with
            | inl hm =>
              rw [hm, List.depPath_symm]
              exact hab
            | inr hm =>
              replace ih := ih b m (by simp) (by simp [hm])
              rw [List.depPath_symm]
              exact Relation.TransGen.trans hab ih
          · simp [hma, hna] at hm hn
            exact ih m n hm hn
        · simp [hab] at hm hn
          rw [hm, hn]
          exact List.depPath_refl (hwu List.mem_cons_self)

lemma ccDec_aux_elem_conn (u w : List α) (hwu : w ⊆ u) (i : ℕ) (hi : i < (ccDec_aux I u w).length) :
    ∀ m n, m ∈ (ccDec_aux I u w)[i] → n ∈ (ccDec_aux I u w)[i] →
    List.DepPath I u m n := by
  induction w generalizing i with
  | nil => simp [ccDec_aux]
  | cons a w ih =>
    by_cases hiz : i = 0
    · simp [hiz]
      apply ccDec_aux_head_conn
      exact hwu
    · by_cases hab : ccDec_aux_conn I u (a :: w)
      · rw [ccDec_aux_tail_C hab]
        apply ih (List.subset_of_cons_subset hwu)
        exact Nat.zero_lt_of_ne_zero hiz
      · replace hi : i - 1 < (ccDec_aux I u w).length := by
          rw [ccDec_aux_len_D hab] at hi
          cases i with
          | zero => simp at hiz
          | succ i => exact Nat.succ_lt_succ_iff.mp hi
        rw [ccDec_aux_tail_D' hab i hi hiz]
        apply ih (List.subset_of_cons_subset hwu)

lemma ccDec_aux_adj_head_char_indep (u w : List α) (h : 1 < (ccDec_aux I u w).length) (hw : w ≠ []) :
    ¬List.DepPath I u
    ((ccDec_aux I u w)[0].getLast (ccDec_aux_elem_nonempty u w 0 ccDec_aux_zero_idx hw))
    ((ccDec_aux I u w)[1][0]'(List.length_pos_iff.mpr (ccDec_aux_elem_nonempty u w 1 h hw))) := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    let t := ccDec_aux I u w
    have ht : ccDec_aux I u w = t := rfl
    rcases t
    · exfalso
      exact (ccDec_aux_nonempty _ _) ht
    · rename_i c_head c_tail
      by_cases hw' : w = []
      · simp [hw', ccDec_aux] at h -- #1 of 3 actually useful parts?
      cases c_head with
      | nil =>
        have := ccDec_aux_nonempty_head I u w hw'
        simp [List.getElem_of_eq ht] at this
      | cons b c_head =>
        simp [ccDec_aux, ht]
        by_cases hab : List.DepPath I u a b
        · simp [hab] -- #2 of 3 actually useful parts?
          simp [ht] at ih
          simp [ccDec_aux, ht, hab] at h
          exact ih h hw'
        · simp [hab] -- #3 of 3 actually useful parts?

lemma ccDec_aux_adj_char_indep (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) (hw : w ≠ []) :
    ¬List.DepPath I u
    ((ccDec_aux I u w)[i].getLast (ccDec_aux_elem_nonempty u w i (Nat.lt_of_succ_lt hi) hw))
    ((ccDec_aux I u w)[i + 1][0]'(List.length_pos_iff.mpr (ccDec_aux_elem_nonempty u w (i + 1) hi hw))) := by
  induction w generalizing i with
  | nil => simp at hw
  | cons a w ih =>
    by_cases hw : w = []
    · simp [hw, ccDec_aux] at hi
    cases i with
    | zero => exact ccDec_aux_adj_head_char_indep u (a :: w) (Nat.lt_of_succ_le hi) (List.cons_ne_nil a w)
    | succ i =>
      by_cases hab : ccDec_aux_conn I u (a :: w)
      · rw [List.getLast.congr_simp _ _ (ccDec_aux_tail_C hab (i + 1) (Nat.lt_of_succ_lt hi) (Nat.zero_lt_succ i))]
        rw [List.getElem_of_eq (ccDec_aux_tail_C hab (i + 2) hi (Nat.zero_lt_succ (i + 1)))]
        exact ih _ _ hw
      · rw [List.getLast.congr_simp _ _ (ccDec_aux_tail_D hab i (Nat.lt_of_succ_lt hi))]
        rw [List.getElem_of_eq (ccDec_aux_tail_D hab (i + 1) hi)]
        exact ih _ _ hw

lemma ccDec_aux_adj_indep (u w : List α) (i : ℕ) (hi : i + 1 < (ccDec_aux I u w).length) (hwu : w ⊆ u) :
    I.Independent (ccDec_aux I u w)[i] (ccDec_aux I u w)[i + 1] := by
  by_cases hw : w = []
  · simp [hw, ccDec_aux] at hi
  intro p hp q hq
  by_contra hpq
  apply ccDec_aux_adj_char_indep u w i hi hw
  rw [List.getLast_eq_getElem]
  have hqR : List.DepPath I u q (((ccDec_aux I u w)[i + 1]'hi)[0]'(List.length_pos_of_mem hq)) :=
    ccDec_aux_elem_conn u w hwu (i + 1) hi _ _ hq (List.getElem_mem (List.length_pos_of_mem hq))
  refine Relation.TransGen.trans ?_ hqR
  replace hpq : List.DepPath I u p q := by
    unfold List.DepPath List.DepEdge inducedDependence
    simp
    apply Relation.TransGen.single
    use hpq
    use hwu (List.IsInfix.mem hp (ccDec_aux_infix I u w i (Nat.lt_of_succ_lt hi)))
    exact hwu (List.IsInfix.mem hq (ccDec_aux_infix I u w (i + 1) hi))
  refine Relation.TransGen.trans ?_ hpq
  exact ccDec_aux_elem_conn u w hwu i (Nat.lt_of_succ_lt hi) _ _ (by simp) hp

lemma ccDec_disconnected_len (w : List α) (h : ¬ List.IsConnected I w) :
    (ccDec I w).length ≥ 2 := by
  by_contra h_len
  simp at h_len
  replace h_len : (ccDec I w).length = 1 := Nat.eq_of_le_of_lt_succ ccDec_aux_zero_idx h_len
  let t := ccDec I w
  have ht : ccDec I w = t := rfl
  rcases t
  · simp [ht] at h_len
  · rename_i c_head c_tail
    have h_conn := @ccDec_aux_head_conn α I w w (List.Subset.refl _)
    unfold ccDec at ht h_len
    simp [ht] at h_conn
    simp [ht] at h_len
    rw [h_len] at ht
    replace ht : (ccDec_aux I w w).flatten = c_head := by simp [ht]
    rw [ccDec_aux_flatten] at ht
    rw [ht] at h
    simp [List.IsConnected] at h
    replace ⟨m, hm, n, hn, h⟩ := h
    replace h_conn := (h_conn m n hm hn)
    rw [← ht] at h
    exact h h_conn

-----

variable [Fintype α] [LinearOrder α] [DecidableRel I.rel]

omit [Fintype α] [DecidableRel I.rel] in
lemma lexNF_infix_is_lexNF {s t : List α} (hst : List.IsInfix s t) (ht : IsLexNF I t) :
    IsLexNF I s := by
  apply (isLexNF_iff_factorCondition _ _).mp at ht
  apply (isLexNF_iff_factorCondition _ _).mpr
  replace ⟨s', s'', hst⟩ := hst
  intro y u z a b hs
  replace ht := ht (s' ++ y) u (z ++ s'') a b
  simp [← hst, hs] at ht
  exact ht

omit [Fintype α] [DecidableRel I.rel] in
lemma lexNF_concat_of_indep {u v : List α} (h_indep : I.Independent u v) (huv : IsLexNF I (u ++ v))
    (hu : u ≠ []) (hv : v ≠ []) :
    (u[0]'(List.length_pos_iff.mpr hu) < v[0]'(List.length_pos_iff.mpr hv)) := by
  apply (isLexNF_iff_factorCondition _ _).mp at huv

  rcases u
  · simp at hu
  rename_i a u

  rcases v
  · simp at hv
  rename_i b v

  replace huv := huv [] u v b a
  simp at huv h_indep ⊢

  by_contra h_ge
  have h_ne : a ≠ b := by
    by_contra h_eq
    rw [h_eq] at h_indep
    exact (I.irrefl _) h_indep.1.1
  have h_gt : b < a := by
    simp at h_ge
    exact lt_of_le_of_ne h_ge (Ne.symm h_ne)

  have ⟨c, hcs, hac⟩ := huv (I.symm _ _ h_indep.1.1) h_gt
  exact hac (I.symm _ _ (h_indep.2 c hcs).1)

lemma lexNF_ccDec_adj_order {w : List α} (hw : w ∈ lexNFLanguage I) (hz : w ≠ []) (i : ℕ)
    (hi : i + 1 < (ccDec_aux I w w).length) :
    (ccDec_aux I w w)[i][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) <
    (ccDec_aux I w w)[i + 1][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) := by
  apply (mem_lexNFLanguage_iff_factorCondition _ _).mp at hw
  apply (isLexNF_iff_factorCondition _ _).mpr at hw
  have h_infix := lexNF_infix_is_lexNF (ccDec_aux_adj_infix I w w i hi) hw

  apply lexNF_concat_of_indep (ccDec_aux_adj_indep w w i hi (by simp)) h_infix
  use (ccDec_aux_elem_nonempty w w i (Nat.lt_of_succ_lt hi) hz)
  exact ccDec_aux_elem_nonempty w w (i + 1) hi hz

lemma lexNF_ccDec_order {w : List α} (hw : w ∈ lexNFLanguage I) (hz : w ≠ []) (i j : ℕ)
    (hij : i < j) (hj : j < (ccDec_aux I w w).length) :
    (ccDec_aux I w w)[i][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) <
    (ccDec_aux I w w)[j][0]'(ccDec_aux_elem_nonempty_len _ _ _ _ hz) := by
  induction hij with
  | refl => exact lexNF_ccDec_adj_order hw hz i hj
  | step hij ih =>
    clear j
    rename_i j
    exact lt_trans (ih (Nat.lt_of_succ_lt hj)) (lexNF_ccDec_adj_order hw hz j hj)

instance {I : Independence α} {u : List α} :
    Trans (List.DepPath I u) (List.DepPath I u) (List.DepPath I u) where
  trans := Relation.TransGen.trans

omit [Fintype α] [LinearOrder α] in
lemma ccDec_aux_across_indep (I : Independence α) (u w : List α) (hi : 1 < (ccDec_aux I u w).length) (hwu : w ⊆ u) :
    I.Independent ((ccDec_aux I u w).getLast (ccDec_aux_nonempty _ _)) (ccDec_aux I u w)[0] ∨
    (I.Independent ((ccDec_aux I u w).getLast (ccDec_aux_nonempty _ _) ++ (ccDec_aux I u w)[0]) (ccDec_aux I u w)[1] ∧
    2 < (ccDec_aux I u w).length) := by
  by_cases hw : w = []
  · simp [hw, ccDec_aux]
  by_contra h
  rw [not_or] at h
  rcases h with ⟨hs, hl⟩
  apply hl
  clear hl

  apply And.intro
  · by_contra hl
    apply @ccDec_aux_adj_char_indep α I u w 0 (Nat.add_lt_of_lt_sub' hi) hw
    simp at hl hs ⊢
    have ⟨a, ha, b, hb, hab⟩ := hl
    have ⟨c, hc, d, hd, hcd⟩ := hs
    clear hl hs
    cases ha with
    | inl ha =>
      calc
        List.DepPath I u ((ccDec_aux I u w)[0].getLast (ccDec_aux_nonempty_head I u w hw)) d :=
          ccDec_aux_elem_conn u w hwu _ _ _ _ (List.getLast_mem _) hd
        List.DepPath I u d c := by
          apply Relation.TransGen.single
          use fun h => hcd (I.symm _ _ h)
          apply And.intro
          · exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) hd)
          · rw [List.getLast_eq_getElem _] at hc
            exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) hc)
        List.DepPath I u c a := by
          rw [List.getLast_eq_getElem _] at ha hc
          exact ccDec_aux_elem_conn u w hwu _ _ _ _ hc ha
        List.DepPath I u a b := by
          apply Relation.TransGen.single
          use hab
          apply And.intro
          · rw [List.getLast_eq_getElem _] at ha
            exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) ha)
          · exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) hb)
        List.DepPath I u b ((ccDec_aux I u w)[1][0]'(ccDec_aux_elem_nonempty_len u w 1 hi hw)) :=
          ccDec_aux_elem_conn u w hwu _ _ _ _ hb (List.getElem_mem _)
    | inr ha =>
      calc
        List.DepPath I u ((ccDec_aux I u w)[0].getLast (ccDec_aux_nonempty_head I u w hw)) a :=
          ccDec_aux_elem_conn u w hwu _ _ _ _ (List.getLast_mem _) ha
        List.DepPath I u a b := by
          apply Relation.TransGen.single
          use hab
          apply And.intro
          · exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) ha)
          · exact hwu (List.IsInfix.subset (ccDec_aux_infix _ _ _ _ _) hb)
        List.DepPath I u b ((ccDec_aux I u w)[1][0]'(ccDec_aux_elem_nonempty_len u w 1 hi hw)) :=
          ccDec_aux_elem_conn u w hwu _ _ _ _ hb (List.getElem_mem _)
  · by_contra hl
    simp at hl
    replace hi := Nat.le_antisymm hl hi
    replace hi : (ccDec_aux I u w).length - 1 = 1 := Eq.symm (Nat.eq_sub_of_add_eq' (Eq.symm hi))
    have hs' : I.Independent (ccDec_aux I u w)[0] (ccDec_aux I u w)[1] := ccDec_aux_adj_indep u w 0 _ hwu
    rw [List.getLast_eq_getElem, getElem_congr rfl hi _] at hs
    exact hs (independent_symm hs')

lemma connected_of_lexNF_sq {w : List α}
    (hw : w ∈ lexNFLanguage I)
    (hww : w ++ w ∈ lexNFLanguage I) :
    Trace.IsConnected I ⟦w⟧ := by
  rw [← Trace.isConnected_eq]
  apply (mem_lexNFLanguage_iff_factorCondition _ _).mp at hww
  apply (isLexNF_iff_factorCondition _ _).mpr at hww

  by_cases hz : w = []
  · simp [hz, List.IsConnected]
  by_contra h_con
  have h_con_ww : ¬List.IsConnected I (w ++ w) := by
    contrapose h_con
    intro a ha b hb
    replace h_con := h_con a (List.mem_append_left w ha) b (List.mem_append_left w hb)
    exact List.depPath_sub (List.append_subset_of_subset_of_subset (by simp) (by simp)) h_con
  have h_dec_w_len := @ccDec_disconnected_len α I w h_con
  have h_dec_ww_len := @ccDec_disconnected_len α I (w ++ w) h_con_ww
  unfold ccDec at h_dec_ww_len

  have h_across_indep := ccDec_aux_across_indep I w w (Nat.lt_of_succ_le h_dec_w_len) (by simp)
  cases h_across_indep with
  | inl h_across_indep =>
    have h_across_infix := ccDec_across_infix I w (Nat.lt_of_succ_le h_dec_w_len)
    replace h_across_infix : List.IsInfix
        (((ccDec_aux I w w).getLast (ccDec_aux_nonempty _ _)) ++
        ((ccDec_aux I w w)[0]'(ccDec_aux_zero_idx)))
        (w ++ w) := by
      unfold ccDec at h_across_infix
      replace ⟨s, t, h_across_infix⟩ := h_across_infix
      use s, (ccDec_aux I w w)[1] ++ t
      simp only [← List.append_assoc] at h_across_infix ⊢
      exact h_across_infix
    have h_across_lexNF := lexNF_infix_is_lexNF h_across_infix hww
    have h_last_ne : (ccDec_aux I w w).getLast (ccDec_aux_nonempty _ _) ≠ [] := by
      rw [List.getLast_eq_getElem]
      exact ccDec_aux_elem_nonempty w w _ _ hz
    rw [List.getLast_eq_getElem] at h_across_indep h_across_lexNF
    have h_gt := lexNF_concat_of_indep h_across_indep h_across_lexNF
        (ccDec_aux_elem_nonempty w w _ _ hz) (ccDec_aux_nonempty_head I w w hz)
    have h_lt := lexNF_ccDec_order hw hz 0 ((ccDec_aux I w w).length - 1) (Nat.zero_lt_sub_of_lt h_dec_w_len)
        (Nat.sub_one_lt_of_lt h_dec_w_len)
    exact LT.lt.asymm h_gt h_lt
  | inr h_across_indep =>
    replace ⟨h_across_indep, h_dec_w_len2⟩ := h_across_indep
    have h_across_infix := ccDec_across_infix I w (Nat.lt_of_succ_le h_dec_w_len)
    have h_across_lexNF := lexNF_infix_is_lexNF h_across_infix hww
    unfold ccDec at h_across_lexNF
    rw [List.getLast_eq_getElem] at h_across_indep h_across_lexNF
    have h_across_ne : (ccDec I w)[(ccDec I w).length - 1] ++ (ccDec I w)[0] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (ccDec_aux_nonempty_head I w w hz)
    have h_gt := lexNF_concat_of_indep
      h_across_indep h_across_lexNF
      h_across_ne
      (ccDec_aux_elem_nonempty w w 1 (Nat.lt_of_succ_le h_dec_w_len) hz)
    rw [List.getElem_append_left (ccDec_aux_elem_nonempty_len _ _ _ _ hz)] at h_gt
    have h_lt := lexNF_ccDec_order hw hz 1 ((ccDec_aux I w w).length - 1) (Nat.lt_sub_of_add_lt h_dec_w_len2)
        (Nat.sub_one_lt_of_lt h_dec_w_len)
    exact LT.lt.asymm h_gt h_lt

end TraceTheory
