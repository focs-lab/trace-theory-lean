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

end Trace
