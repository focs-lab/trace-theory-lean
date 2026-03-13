import TraceTheory.Trace
import Mathlib.Data.Finset.Pi

namespace Trace

variable {α : Type} {I : Independence α}

variable {α : Type} {I : Independence α}

--def langOf (t : List α) : Language α := {t}
--def kstar (L : Language α) : Language α := L∗

def alph_mem (a : α) (t : Trace I) :=
  Quotient.lift (fun (s : List α) => a ∈ s) (by intro u v h; simp; exact mem_iff_mem a h) t

instance : Membership α (Trace I) where
  mem l a := alph_mem a l

lemma eps_is_empty (a : α) : a ∉ @Trace.mk' α I [] := by
  intro h
  rcases h

lemma empty_is_eps (t : Trace I) : t ≠ ⟦[]⟧ → ∃ a, a ∈ t := by
  intro h
  rcases t
  rename_i w
  replace h : w ≠ [] := fun a => h (congrArg (Quot.mk ⇑(traceSetoid I)) a)
  exact List.exists_mem_of_ne_nil w h

lemma mem_append {a : α} {s t : Trace I} : a ∈ s * t ↔ a ∈ s ∨ a ∈ t := by
  rcases s
  rcases t
  exact List.mem_append

lemma mems_lift (w : List α) : {a : α // a ∈ w} = {a : α // a ∈ @mk' α I w} := rfl

/-- The Dependence relation induced by an Independence `I`. -/
def inducedDependence {α : Type} (I : Independence α) : Dependence α where
  rel := fun a b => ¬ I.rel a b
  refl := by
    intro a
    exact I.irrefl a
  symm := by
    intro a b hab hba
    exact hab (I.symm b a hba)

--@[simp]
--lemma mul_canonical {a b : Trace I} : mul a b = a * b := by rfl

--instance : Mul (Trace I) :=
--  ⟨(mul · ·)⟩

@[simp]
lemma left_id (t : Trace I) : ↑(⟦[]⟧) * t = t := by
  rcases t
  rfl

@[simp]
lemma right_id (t : Trace I) : t * ↑(⟦[]⟧) = t := by
  rcases t with ⟨w⟩
  simp [show Quot.mk (⇑(traceSetoid I)) w = ⟦w⟧ from rfl, HMul.hMul, Mul.mul]

--lemma mul_def : (⟦u⟧ : Trace I) * ⟦v⟧ = ⟦u ++ v⟧ :=
--  rfl

def traceFlatten (L : List (Trace I)) := List.foldl (fun (u : Trace I) v => u * v) ⟦[]⟧ L

lemma traceFlatten_append {u : Trace I} (L : List (Trace I)) : traceFlatten (u :: L) = u * traceFlatten L := by
  unfold traceFlatten
  simp
  rw [<- right_id u]
  rw [List.foldl_assoc]
  simp


def dependencyIn' (s : List α) (a b : {a : α // a ∈ s}) := (inducedDependence I).rel a b

def dependencyTransClosureIn' (s : List α) (a b : {a : α // a ∈ s}) := Relation.TransGen (@dependencyIn' α I s) a b

def isConnected' (s : List α) := ∀ a b : {a : α // a ∈ s}, @dependencyTransClosureIn' α I s a b


def dependencyIn (t : Trace I) (a b : {a : α // a ∈ t}) := (inducedDependence I).rel a b

def dependencyTransClosureIn (t : Trace I) (a b : {a : α // a ∈ t}) := Relation.TransGen (dependencyIn t) a b

def isConnected (t : Trace I) := ∀ a b : {a : α // a ∈ t}, dependencyTransClosureIn t a b


lemma dependencyIn_toTrace (s : List α) : @dependencyIn' α I s = @dependencyIn α I ⟦s⟧ := rfl

lemma dependencyTransClosureIn_toTrace (s : List α) : @dependencyTransClosureIn' α I s = @dependencyTransClosureIn α I ⟦s⟧ := rfl

lemma isConnected_toTrace (s : List α) : @isConnected' α I s = @isConnected α I ⟦s⟧ := rfl


def isIterativeFactor (X : Language α) (t : List α) :=
    ∃ u v, ∀ (ts : List (List α)), (∀ t' ∈ ts, t' = t) → u ++ ts.flatten ++ v ∈ X

def toTrace (X : Language α) : Set (Trace I) := (fun s => ⟦s⟧) '' X


def kstar (T : Set (Trace I)) := {r | ∃ ts : List (Trace I), (∀ t' ∈ ts, t' ∈ T) ∧ r = traceFlatten ts}

def independent' (u v : Trace I) := ∀ a b, a ∈ u → b ∈ v → I.rel a b

def connectedComponents (X : Set (Trace I)) : Set (Trace I) := {u | isConnected u ∧ u ≠ ⟦[]⟧ ∧ ∃ v, u * v ∈ X ∧ independent' u v}


-- open Computability

lemma kstar_toTrace_commutes (L : Language α) : @toTrace α I (KStar.kstar L) = kstar (toTrace L) := by
  simp [Language.kstar_def, Set.image, toTrace]
  apply Set.ext
  intro t
  apply Iff.intro
  all_goals simp [kstar]
  · intro w ws hw
    induction ws generalizing w t with
    | nil =>
      intro hL ht
      use []
      simp at hw
      rw [hw] at ht
      simp [ht, traceFlatten]
    | cons u ws ih =>
      simp at ih
      intro hL ht
      replace ih := ih (fun y hy => hL y (List.mem_cons_of_mem u hy))
      choose ts hts using ih
      use ⟦u⟧ :: ts
      apply And.intro
      · intro s hs
        cases hs with
        | head => use u; simp [hL]
        | tail s hs => exact hts.left s hs
      · simp [<- ht, hw]
        -- rw [<- mul_def]
        rw [traceFlatten_append, <- hts.right]
        rfl
  · intro ts hts ht
    induction ts generalizing t with
    | nil =>
      use []
      simp [ht, traceFlatten]
      use []
      simp
    | cons s ts ih =>
      simp at ih
      replace ih := ih (fun y hy => hts y (List.mem_cons_of_mem s hy))
      choose w hws hw using ih
      rcases s with ⟨u⟩
      rw [show Quot.mk (⇑(traceSetoid I)) u = ⟦u⟧ from rfl] at ht hts
      replace hts := hts ⟦u⟧
      simp at hts
      choose u' hu' using hts
      use u' ++ w
      apply And.intro
      · rcases hws with ⟨ws, hws⟩
        use u' :: ws
        simp [hws.left, hu']
        exact hws.right
      · simp [ht]
        rw [traceFlatten_append, <- hw, <- hu'.right]
        rfl

lemma append_indep_is_disconnected_chars (u v : Trace I) (huv : independent' u v)
    (a b : { a // a ∈ u * v }) (ha : a.1 ∈ u) (hb : b.1 ∈ v) :
    ¬ (dependencyTransClosureIn (u * v)) a b := by
  intro h
  induction h with
  | single h =>
    rename_i b
    apply h
    exact huv a b ha hb
  | tail h h_tail ih =>
    rename_i b c
    simp at ih
    have hbu : b.1 ∈ u :=  by
      have hb_uv := mem_append.mp b.2
      simp [ih] at hb_uv
      exact hb_uv
    simp [dependencyIn, inducedDependence] at h_tail
    unfold independent' at huv
    exact h_tail (huv b c hbu hb)

lemma append_indep_is_disconnected (u v : Trace I) (h : independent' u v) (hu : u ≠ ⟦[]⟧) (hv : v ≠ ⟦[]⟧) :
    ¬isConnected (u * v) := by
  by_contra h_con
  have ⟨a, ha⟩ := empty_is_eps u hu
  have ⟨b, hb⟩ := empty_is_eps v hv
  have h_ab_con := h_con ⟨a, mem_append.mpr (Or.inl ha)⟩ ⟨b, mem_append.mpr (Or.inr hb)⟩
  have h_ab_dis := append_indep_is_disconnected_chars u v h ⟨a, mem_append.mpr (Or.inl ha)⟩ ⟨b, mem_append.mpr (Or.inr hb)⟩ ha hb
  exact h_ab_dis h_ab_con

lemma connectedComponents_of_connected (T : Set (Trace I)) (h : ∀ t ∈ T, isConnected t) :
    connectedComponents T = T \ {⟦[]⟧} := by
  apply Set.ext
  intro t
  apply Iff.intro
  · intro ⟨ht, htz, v, htv, htv_id⟩
    simp [htz]
    replace h := h (t * v) htv
    have hvz : v = ⟦[]⟧ := by
      by_contra hvz
      exact append_indep_is_disconnected t v htv_id htz hvz h
    rw [hvz, right_id] at htv
    exact htv
  · intro ⟨ht, htz⟩
    use (h t ht), htz, ⟦[]⟧
    rw [right_id]
    use ht
    unfold independent'
    simp [show ⟦[]⟧ = mk' [] from rfl, eps_is_empty]

lemma empty_iff {w : List α} : (⟦w⟧ : Trace I) = ⟦[]⟧ ↔ w = [] := by
  cases w with
  | nil => simp
  | cons a u =>
    apply Iff.intro
    · intro h
      have h_au := length_eq_of_equiv (Quotient.exact h)
      simp at h_au
    · simp

def isEmpty : Trace I → Bool := Quotient.lift List.isEmpty (by
  intro u v huv
  cases u with
  | nil => rw [empty_iff.mp (Eq.symm (Quotient.sound huv))]
  | cons a u =>
    cases v with
    | nil => rw [empty_iff.mp (Quotient.sound huv)]
    | cons b v => rfl
)

lemma isEmpty_iff {t : Trace I} : t.isEmpty = true ↔ t = ⟦[]⟧ := by
  apply Iff.intro
  · intro h
    rcases t with ⟨s⟩
    rw [List.isEmpty_iff.mp h]
    rfl
  · intro h
    rw [h]
    rfl

lemma traceFlatten_filter_not_isEmpty :
    ∀ {L : List (Trace I)}, traceFlatten (List.filter (!·.isEmpty) L) = traceFlatten L
  | [] => rfl
  | t :: L => by
    by_cases ht : t.isEmpty
    · apply isEmpty_iff.mp at ht
      simp [ht]
      simp [show isEmpty ⟦[]⟧ = true from rfl]
      exact traceFlatten_filter_not_isEmpty (L := L)
    · simp [ht]
      repeat rw [traceFlatten_append]
      rw [traceFlatten_filter_not_isEmpty (L := L)]

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

lemma kstar_eq_minusEps_trace (T : Set (Trace I)) : kstar (T \ {⟦[]⟧}) = kstar T := by
  apply Set.ext
  intro t
  apply Iff.intro
  · intro ⟨ls, hls, ht⟩
    use ls
    simp [ht]
    exact fun y hy => Set.diff_subset (hls y hy)
  · intro ⟨ls, hls, ht⟩
    use ls.filter (!·.isEmpty)
    simp
    apply And.intro
    · intro y hy hyz
      exact ⟨hls y hy, Trace.isEmpty_iff.ne.mp (ne_true_of_eq_false hyz)⟩
    · simp [traceFlatten_filter_not_isEmpty, ht]

end Trace
