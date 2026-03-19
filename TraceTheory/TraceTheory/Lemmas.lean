import Mathlib.Computability.Language
import Mathlib.Data.Finset.Pi
import TraceTheory.Basic

namespace TraceTheory

variable {α : Type*} {I : Independence α}

def alph_mem (a : α) (t : Trace I) :=
  Quotient.lift
    (fun (s : List α) => a ∈ s)
    (by
      intro u v h
      simp
      exact mem_iff_mem a h)
    t

instance : Membership α (Trace I) where
  mem l a := alph_mem a l

lemma eps_is_empty (a : α) : a ∉ (1 : Trace I) := by
  intro h
  rcases h

lemma empty_is_eps (t : Trace I) (h : t ≠ 1) : ∃ a, a ∈ t := by
  rcases t with ⟨_ | ⟨a, w⟩⟩
  · exact (h rfl).elim
  · exact ⟨a, List.mem_cons_self⟩

lemma mem_append {a : α} {s t : Trace I} : a ∈ s * t ↔ a ∈ s ∨ a ∈ t := by
  rcases s
  rcases t
  exact List.mem_append

lemma mems_lift (w : List α) : {a : α // a ∈ w} = {a : α // a ∈ mk' (I := I) w} :=
  rfl

def dependencyIn (t : Trace I) (a b : α) :=
  (inducedDependence I).rel a b ∧ a ∈ t ∧ b ∈ t

def dependencyTransClosureIn (t : Trace I) (a b : α) :=
  Relation.TransGen (dependencyIn t) a b

def IsConnected (I : Independence α) (t : Trace I) :=
  ∀ a b : {a : α // a ∈ t}, dependencyTransClosureIn t a b

def IsIterativeFactor (X : Language α) (t : List α) :=
  ∃ u v, ∀ n : ℕ, u ++ t ^ n ++ v ∈ X

def toTrace (I : Independence α) (X : Language α) : Set (Trace I) := mk' '' X

def kstar (T : Set (Trace I)) :=
  {r | ∃ ts : List (Trace I), (∀ t' ∈ ts, t' ∈ T) ∧ r = ts.prod}

def IndependentT (u v : Trace I) := ∀ a b, a ∈ u → b ∈ v → I.rel a b

def connectedComponents (X : Set (Trace I)) : Set (Trace I) :=
  {u | IsConnected I u ∧ u ≠ 1 ∧ ∃ v, u * v ∈ X ∧ IndependentT u v}

open Computability in
theorem kstar_toTrace_comm (L : Language α) :
    toTrace I (L∗) = kstar (toTrace I L) := by
  simp [Language.kstar_def, Set.image, toTrace, kstar]
  ext t
  simp only [Set.mem_setOf]
  constructor
  · intro ⟨ws, hws, ht⟩
    induction ws generalizing t with
    | nil => exact ⟨[], by simp_all⟩
    | cons w ws' ih =>
      rw [forall_apply_eq_imp_iff] at ih
      simp only [List.mem_cons, forall_eq_or_imp] at hws
      rcases ih hws.right with ⟨ts, hts, hws'⟩
      use ⟦w⟧ :: ts
      constructor
      · rw [List.forall_mem_cons]
        exact ⟨⟨w, hws.left, rfl⟩, hts⟩
      · rw [← ht, List.prod_cons, ← hws']
        rfl
  · intro ⟨ts, hts, ht⟩
    induction ts generalizing t with
    | nil => exact ⟨[], by simp_all⟩
    | cons s ts' ih =>
      rw [forall_eq_apply_imp_iff] at ih
      simp only [List.mem_cons, forall_eq_or_imp] at hts
      rcases ih hts.right with ⟨ws, hws, hws'⟩
      rcases hts.left with ⟨w, hw⟩
      use [w] ++ ws
      constructor
      · simp only [List.cons_append, List.nil_append, List.mem_cons, forall_eq_or_imp]
        exact ⟨hw.left, hws⟩
      · rw [ht, List.prod_cons, ← hws', ← hw.right]
        rfl

lemma append_indep_is_disconnected_chars {u v : Trace I}
    (huv : IndependentT u v) (a b : α) (ha : a ∈ u) (hb : b ∈ v) :
    ¬ (dependencyTransClosureIn (u * v)) a b := by
  intro h
  induction h with
  | single h =>
    rename_i b
    have hab := huv a b ha hb
    exact h.1 hab
  | tail h h_tail ih =>
    rename_i b c
    simp at ih
    have hbu : b ∈ u := by
      have hb_uv := mem_append.mp h_tail.2.1
      simp [ih] at hb_uv
      exact hb_uv
    simp [dependencyIn, inducedDependence] at h_tail
    unfold IndependentT at huv
    exact h_tail.1 (huv b c hbu hb)

lemma append_indep_is_disconnected
    (u v : Trace I) (h : IndependentT u v) (hu : u ≠ 1) (hv : v ≠ 1) :
    ¬IsConnected I (u * v) := by
  by_contra h_con
  have ⟨a, ha⟩ := empty_is_eps u hu
  have ⟨b, hb⟩ := empty_is_eps v hv
  have h_ab_con := h_con ⟨a, mem_append.mpr (Or.inl ha)⟩ ⟨b, mem_append.mpr (Or.inr hb)⟩
  have h_ab_dis := append_indep_is_disconnected_chars h a b ha hb
  exact h_ab_dis h_ab_con

lemma connectedComponents_of_connected (T : Set (Trace I)) (h : ∀ t ∈ T, IsConnected I t) :
    connectedComponents T = T \ {1} := by
  apply Set.ext
  intro t
  apply Iff.intro
  · intro ⟨ht, htz, v, htv, htv_id⟩
    simp [htz]
    replace h := h (t * v) htv
    have hvz : v = 1 := by
      by_contra hvz
      exact append_indep_is_disconnected t v htv_id htz hvz h
    rw [hvz, mul_one] at htv
    exact htv
  · intro ⟨ht, htz⟩
    use (h t ht), htz, 1
    rw [mul_one]
    use ht
    unfold IndependentT
    simp [eps_is_empty]

lemma empty_iff {w : List α} : ⟦w⟧ = (1 : Trace I) ↔ w = [] := by
  cases w with
  | nil =>
    simp only [iff_true]
    rfl
  | cons a u =>
    apply Iff.intro
    · intro h
      have h_au := length_eq_of_eqv (Quotient.exact h)
      simp at h_au
    · simp

def Trace.isEmpty : Trace I → Bool :=
  Quotient.lift List.isEmpty
    (by
      intro u v huv
      cases u with
      | nil => rw [empty_iff.mp (Eq.symm (Quotient.sound huv))]
      | cons a u =>
        cases v with
        | nil => rw [empty_iff.mp (Quotient.sound huv)]
        | cons b v => rfl
    )

@[simp]
theorem isEmpty_iff {t : Trace I} : t.isEmpty = true ↔ t = 1:= by
  apply Iff.intro
  · intro h
    rcases t with ⟨s⟩
    rw [List.isEmpty_iff.mp h]
    rfl
  · intro h
    rw [h]
    rfl

lemma prod_filter_not_isEmpty (L : List (Trace I)) :
    (L.filter (fun x => !x.isEmpty)).prod = L.prod := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    by_cases ht : t.isEmpty = true
    · simp [isEmpty_iff.mp ht, ih]
    · simp [ht, ih]

lemma kstar_eq_minusEps (L : Language α) : KStar.kstar (L \ {[]}) = KStar.kstar L := by
  apply Set.ext
  intro w
  apply Iff.intro
  · intro ⟨ls, hw, hls⟩
    use ls
    simp [hw]
    exact fun y hy => Set.diff_subset (hls y hy)
  · intro ⟨ls, hls, ht⟩
    use ls.filter (!·.isEmpty)
    simp
    apply And.intro
    · simp [hls, List.flatten_filter_not_isEmpty]
    · intro y hy hyz
      exact Set.mem_diff_singleton.mpr ⟨ht y hy, hyz⟩

lemma kstar_eq_minusEps_trace (T : Set (Trace I)) : kstar (T \ {1}) = kstar T := by
  apply Set.ext
  intro t
  apply Iff.intro
  · intro ⟨ls, hls, ht⟩
    use ls
    simp [ht]
    exact fun y hy => Set.diff_subset (hls y hy)
  · intro ⟨ls, hls, ht⟩
    use ls.filter (!Trace.isEmpty ·)
    simp
    constructor
    · intro y hy hyz
      exact ⟨hls y hy, isEmpty_iff.ne.mp (ne_true_of_eq_false hyz)⟩
    · simp [prod_filter_not_isEmpty, ht]

end TraceTheory
