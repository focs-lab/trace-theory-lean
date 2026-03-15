import TraceTheory.Language
import TraceTheory.Lemmas
import TraceTheory.MyhillNerode
import TraceTheory.RegularExpressions

namespace TraceTheory

variable {α : Type} {I : Independence α}


/-- Main component of Theorem 4.1 (ii) => (iii).

  For a rational expression X, if every iterative factor of L(X) is connected,
  then X' is star-connected (for some rational expression X' with L(X) = L(X')).

  It is strictly necessary that we use an X' not necessarily equal to X.
  Consider X = {a ∪ b}∗ · ∅; where `a` and `b` are not connected. Then L(X) = ∅ so every
  iterative factor is connected, but X is not star-connected.

  Note that P · ∅ or ∅ · P are the only cases where this patch is needed.
-/
theorem connectedIterativeFactors_equiv_starConnected' (X : RegularExpression α)
    (hconn : ∀ s, isIterativeFactor X.matches' s → @isConnected α I s) :
    ∃ Y, RegularExpression.isStarConnected I Y ∧ X.matches' = Y.matches' := by
  induction X with
  | zero => use RegularExpression.zero, trivial
  | epsilon => use RegularExpression.epsilon, trivial
  | char a => use RegularExpression.char a, trivial
  | plus P Q ihP ihQ =>
    have ihP_cond : (∀ s, isIterativeFactor P.matches' s → @isConnected α I s) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      use u, v
      intro ts hts
      replace h := h ts hts
      have h_match_subset : ∀ p ∈ P.matches', p ∈ P.matches' + Q.matches' := by
        simp [Language.add_def]
        intro p hp
        apply (Set.mem_union _ _ _).mpr
        simp [hp]
      exact h_match_subset _ h
    have ⟨P', hP'⟩ := ihP ihP_cond

    have ihQ_cond : (∀ s, isIterativeFactor Q.matches' s → @isConnected α I s) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      use u, v
      intro ts hts
      replace h := h ts hts
      have h_match_subset : ∀ q ∈ Q.matches', q ∈ P.matches' + Q.matches' := by
        simp [Language.add_def]
        intro q hq
        apply (Set.mem_union _ _ _).mpr
        simp [hq]
      exact h_match_subset _ h
    have ⟨Q', hQ'⟩ := ihQ ihQ_cond

    use P' + Q'
    simp [RegularExpression.isStarConnected, hP', hQ']
  | comp P Q ihP ihQ =>
    by_cases hpe : ¬ ∃ p, p ∈ P.matches'
    · use RegularExpression.zero
      simp [RegularExpression.isStarConnected]
      rw [Language.zero_def]
      apply Language.ext
      intro x
      apply Iff.intro
      all_goals intro h
      · rw [Language.mul_def] at h
        replace ⟨u, hu, v, hv, h⟩ := h
        exact hpe ⟨u, hu⟩
      · exact False.elim h

    by_cases hqe : ¬ ∃ q, q ∈ Q.matches'
    · use RegularExpression.zero
      simp [RegularExpression.isStarConnected]
      rw [Language.zero_def]
      apply Language.ext
      intro x
      apply Iff.intro
      all_goals intro h
      · rw [Language.mul_def] at h
        replace ⟨u, hu, v, hv, h⟩ := h
        exact hqe ⟨v, hv⟩
      · exact False.elim h

    simp at hpe hqe

    have ihP_cond : (∀ s, isIterativeFactor P.matches' s → @isConnected α I s) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      have ⟨q, hq⟩ := hqe
      use u, v ++ q
      intro ts hts
      replace h := h ts hts
      unfold RegularExpression.matches'
      use u ++ ts.flatten ++ v, h, q, hq
      simp
    have ⟨P', hP'⟩ := ihP ihP_cond

    have ihQ_cond : (∀ s, isIterativeFactor Q.matches' s → @isConnected α I s) := by
      intro s ⟨u, v, h⟩
      apply hconn s
      have ⟨p, hp⟩ := hpe
      use p ++ u, v
      intro ts hts
      replace h := h ts hts
      unfold RegularExpression.matches'
      use p, hp, u ++ ts.flatten ++ v, h
      simp
    have ⟨Q', hQ'⟩ := ihQ ihQ_cond

    use P' * Q'
    simp [RegularExpression.isStarConnected, hP', hQ']
  | star P ih =>
    have ih_cond : ∀ (s : List α), isIterativeFactor P.matches' s → @isConnected α I s := by
      intro s ⟨u, v, h⟩
      apply hconn
      use u, v
      intro ts hts
      replace h := h ts hts
      simp [Language.kstar_def]
      use [u ++ ts.flatten ++ v]
      simp [<- List.append_assoc]
      exact h
    have ⟨P', hP'⟩ := ih ih_cond
    use P'.star
    simp [RegularExpression.isStarConnected, hP']
    intro s hs
    apply hconn
    use [], []
    intro ts hts
    simp [Language.kstar_def]
    use ts
    simp
    intro y hy
    rw [hts y hy, hP'.right]
    exact hs

/-- Theorem 4.1 (ii) => (iii) -/
theorem connectedIterativeFactors_equiv_starConnected (T : Set (Trace I)) (X : RegularExpression α) (himg : T = toTrace X.matches')
    (hconn : ∀ s, isIterativeFactor X.matches' s → @isConnected α I s) :
    ∃ P, RegularExpression.isStarConnected I P ∧ T = (RegularExpression.matches_trace I P) := by
  simp [RegularExpression.matches_toTrace]
  have ⟨P, hP⟩ := connectedIterativeFactors_equiv_starConnected' X hconn
  use P
  simp [hP, himg]



/-- Theorem 4.1 (iii) => (iv) -/
theorem starConnected_is_cRational (X : RegularExpression α) (h : RegularExpression.isStarConnected I X) :
    RegularExpression.matches_trace I X = RegularExpression.matches_cstar_trace I X := by
  induction X with
  | zero => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace]
  | epsilon => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace]
  | char _ => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace]
  | plus P Q ihP ihQ => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace, ihP h.1, ihQ h.2]
  | comp P Q ihP ihQ => simp [RegularExpression.matches_trace, RegularExpression.matches_cstar_trace, ihP h.1, ihQ h.2]
  | star P ih =>
    unfold RegularExpression.matches_trace RegularExpression.matches_cstar_trace
    simp [<- ih h.1]
    unfold RegularExpression.isStarConnected at h
    have hP_conn : (∀ t ∈ RegularExpression.matches_trace I P, isConnectedT t) := by
      intro t ht
      rcases t with ⟨w₀⟩
      rw [show Quot.mk (⇑(TraceSetoid I)) w₀ = ⟦w₀⟧ from rfl] at ht ⊢
      rw [RegularExpression.matches_toTrace] at ht
      simp [toTrace] at ht
      rcases ht with ⟨w, hw⟩
      rw [<- hw.2, <- isConnected_toTrace]
      exact h.2 w hw.1
    rw [connectedComponents_of_connected _ hP_conn]
    rw [kstar_eq_minusEps_trace]



lemma depTrClIn_refl {w : List α} {a : α} (h : a ∈ w) : @dependencyTransClosureIn α I w a a := by
  unfold dependencyTransClosureIn dependencyIn
  apply Relation.TransGen.single
  simp [Dependence.refl, h]

noncomputable instance : ∀ w x y, Decidable (@dependencyTransClosureIn α I w x y) :=
  fun w x y => Classical.propDecidable (dependencyTransClosureIn w x y)

noncomputable def sep_aux (w₀ w : List α) (p : α) : List (List α × List α) :=
  match w with
  | [] => [⟨[], []⟩]
  | a :: w =>
    match sep_aux w₀ w p with
    | [] => [] -- dummy value, unreachable by construction
    | v :: vs =>
      if @dependencyTransClosureIn α I w₀ a p
        then match v.2 with
        | [] => ⟨a :: v.1, v.2⟩ :: vs
        | _ :: _ => ⟨[a], []⟩ :: v :: vs
        else ⟨v.1, a :: v.2⟩ :: vs

noncomputable def sep (w : List α) (p : α) : List (List α × List α) := @sep_aux α I w w p

lemma sep_aux_nonempty (w₀ w : List α) (p : α) : (@sep_aux α I w₀ w p) ≠ [] := by
  induction w with
  | nil => simp [sep_aux]
  | cons a u ih =>
    simp [sep_aux]
    cases hs : sep_aux w₀ u p
    · simp [hs] at ih
    · simp
      by_cases ha : @dependencyTransClosureIn α I w₀ a p
      · rename_i s_head s_tail
        cases s_head.2
        all_goals simp [ha]
      · simp [ha]

lemma sep_aux_zero_idx {w₀ w : List α} {p : α} : 0 < (@sep_aux α I w₀ w p).length := List.length_pos_iff.mpr (sep_aux_nonempty _ _ _)

lemma sep_nonempty (w : List α) (p : α) : (@sep α I w p) ≠ [] := sep_aux_nonempty w w p

lemma sep_invar (u w : List α) (a p : α) (i : Fin (@sep_aux α I (u ++ [p]) (w ++ [p]) p).length) :
    (@sep_aux α I (u ++ [p]) (a :: w ++ [p]) p)[i] = (@sep_aux α I (u ++ [p]) (w ++ [p]) p)[i] ∨
    (@sep_aux α I (u ++ [p]) (a :: w ++ [p]) p)[i] = (@sep_aux α I (u ++ [p]) (w ++ [p]) p)[i]
  := by
  simp [sep_aux]

lemma sep_aux_1_nonempty_head (u w : List α) (p : α) (h : w ≠ []) :
    ((@sep_aux α I (u ++ [p]) (w ++ [p]) p)[0]'(sep_aux_zero_idx)).1 ≠ [] := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    clear h
    by_cases hw : w = []
    · simp [hw, sep_aux, depTrClIn_refl]
      by_cases hau : @dependencyTransClosureIn α I (u ++ [p]) a p
      all_goals simp [hau]
    · simp [hw] at ih
      let t := @sep_aux α I (u ++ [p]) (w ++ [p]) p
      have ht : @sep_aux α I (u ++ [p]) (w ++ [p]) p = t := rfl
      rcases t
      · exfalso
        exact sep_aux_nonempty _ _ _ ht
      · rename_i s_head s_tail
        by_cases hau : @dependencyTransClosureIn α I (u ++ [p]) a p
        · suffices hs_dec : ∃ _1 _2 _3 _4, (@sep_aux α I (u ++ [p]) (a :: w ++ [p]) p) = (_1 ::_2, _3) :: _4 from by
            replace ⟨_1, _2, _3, _4, hs_dec⟩ := hs_dec
            rw [List.getElem_of_eq hs_dec]
            simp
          simp [sep_aux, ht, hau]
          cases s_head.2
          · simp
          · simp
        · simp [sep_aux, ht, hau]
          have hs_dec : (@sep_aux α I (u ++ [p]) (w ++ [p]) p)[0]'(sep_aux_zero_idx) = (s_head :: s_tail)[0] := List.getElem_of_eq ht _
          simp [hs_dec] at ih
          exact ih

lemma sep_aux_1_nonempty (u w : List α) (p : α) (i : Fin (@sep_aux α I (u ++ [p]) (w ++ [p]) p).length) (h : w ≠ []) :
    (@sep_aux α I (u ++ [p]) (w ++ [p]) p)[i].1 ≠ [] := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    clear h
    by_cases hw : w = []
    · rcases i with ⟨i, hi⟩
      simp [hw, sep_aux, depTrClIn_refl]
      by_cases hau : @dependencyTransClosureIn α I (u ++ [p]) a p
      all_goals simp [hau]
    · simp [hw] at ih
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => exact sep_aux_1_nonempty_head _ _ _ (by simp)
      | succ i =>
        by_cases hau : @dependencyTransClosureIn α I (u ++ [p]) a p
        · let temp := @sep_aux α I (u ++ [p]) (w ++ [p]) p
          have htemp : @sep_aux α I (u ++ [p]) (w ++ [p]) p = temp := rfl
          rcases temp
          · exfalso
            exact sep_aux_nonempty _ _ _ htemp
          · rename_i s_head s_tail
            suffices hs_dec : (∃ _1 _2, (@sep_aux α I (u ++ [p]) (a :: w ++ [p]) p) = _1 :: _2) from by
              replace ⟨_1, _2, hs_dec⟩ := hs_dec
              have h_2ne : (_2[i]'(by rw [hs_dec] at hi; exact Nat.succ_lt_succ_iff.mp hi)).1 ≠ [] := by
                simp [sep_aux, htemp, hau] at hs_dec
                contrapose hs_dec
                cases s_head.2
                · simp
                  intro _
                  contrapose hs_dec
                  rw [<- List.getElem_of_eq hs_dec]
                · simp
                  intro _
                  contrapose hs_dec
                  rw [<- List.getElem_of_eq hs_dec, <- List.getElem_of_eq htemp]
                  · exact ih ⟨i, by sorry⟩
                  · rw [<- htemp]
                    sorry
              rw [Fin.getElem_fin]
              rw [List.getElem_of_eq hs_dec]
              simp [h_2ne]
            simp [sep_aux, htemp, hau]
            cases s_head.2
            · simp
            · simp
        · suffices hs_dec : (∃ _1 _2, (@sep_aux α I (u ++ [p]) (a :: w ++ [p]) p) = _1 :: _2) from by
            replace ⟨_1, _2, hs_dec⟩ := hs_dec
            have h_2ne : (_2[i]'(by rw [hs_dec] at hi; exact Nat.succ_lt_succ_iff.mp hi)).1 ≠ [] := by
              sorry
            rw [Fin.getElem_fin]
            rw [List.getElem_of_eq hs_dec]
            simp [h_2ne]
          simp [sep_aux, hau]
          let temp := @sep_aux α I (u ++ [p]) (w ++ [p]) p
          have htemp : @sep_aux α I (u ++ [p]) (w ++ [p]) p = temp := rfl
          rcases temp
          · exfalso
            exact sep_aux_nonempty _ _ _ htemp
          · simp [htemp]

lemma sep_aux_2_nonempty (u w : List α) (p : α) (i : Fin (@sep_aux α I (u ++ [p]) (w ++ [p]) p).length) (h : w ≠ []) (hi : i.1 > 0) :
    (@sep_aux α I (u ++ [p]) (w ++ [p]) p)[i].2 ≠ [] := by sorry



def proj2 (S : Set α) (hd : ∀ x, Decidable (x ∈ S)) (w : List α) : List α := w.filter (· ∈ S)

lemma proj2_prop {S : Set α} {hd : ∀ x, Decidable (x ∈ S)} {w : List α} {a : α} : a ∈ proj2 S hd w → a ∈ S := by
  induction w with
  | nil => simp [proj2]
  | cons b u ih =>
    intro h
    by_cases hab : a = b
    · simp [proj2, <- hab] at h
      exact h
    · simp [proj2] at h
      exact h.2

variable [LinearOrder α] in
theorem lexNf_dup_lexNf_isConnected {w : List α} (h : IsLexNf I (w ++ w)) : @isConnected α I w := by
  have h' : IsLexNf I w := by
    contrapose h
    simp [IsLexNf] at h ⊢
    rcases h with ⟨u, h⟩
    use w ++ u
    exact ⟨TraceEqv.compat (TraceEqv.refl w) h.1, List.append_left_lt h.right⟩

  by_contra h_con
  simp [isConnected] at h_con
  choose a ha b hb h_con using h_con
  let A := {x | @dependencyTransClosureIn α I w a x}
  let B := {x | ¬ @dependencyTransClosureIn α I w a x}
  have hA_dec : ∀ x, Decidable (x ∈ A) := fun x => Classical.propDecidable (x ∈ A)
  have hB_dec : ∀ x, Decidable (x ∈ B) := fun x => Classical.propDecidable (x ∈ B)
  let u := proj2 A hA_dec w
  let v := proj2 B hB_dec w
  have : Independent I u v := by
    intro j hj k hk
    have hjw : j ∈ w := List.mem_of_mem_filter hj
    have hkw : k ∈ w := List.mem_of_mem_filter hk
    unfold u at hj
    unfold v at hk
    replace hj := proj2_prop hj
    replace hk := proj2_prop hk
    replace hj : @dependencyTransClosureIn α I w a j := hj
    replace hk : ¬@dependencyTransClosureIn α I w a k := hk
    by_contra hjk

    have : @dependencyTransClosureInCoe α I w a k := by
      rcases hj with ⟨ha', hjw', hj⟩
      have : @dependencyIn α I w ⟨j, hjw'⟩ ⟨k, hkw⟩ := hjk ∘ fun a => a
      use ha', hkw
      unfold dependencyTransClosureIn at hj ⊢
      exact Relation.TransGen.tail hj this

    exact hk this

  have : a ∈ u := by
    have ha_A : a ∈ A := ⟨ha, ha, Relation.TransGen.single ((inducedDependence I).refl a)⟩
    exact List.mem_filter_of_mem ha (decide_eq_true ha_A)
  have : b ∈ v := by
    have hb_B : b ∈ B := by simp [B, dependencyTransClosureInCoe, h_con]
    exact List.mem_filter_of_mem hb (decide_eq_true hb_B)


end TraceTheory
