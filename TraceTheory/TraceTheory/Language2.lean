import TraceTheory.Trace
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Finset.Pi

namespace Trace

variable {α : Type} {I : Independence α}

lemma indep_of_flatten {u : List α} {vs : List (List α)} (i : Fin vs.length) (h : independent I u vs.flatten) :
    independent I u vs[i] := by
  replace ⟨i, hi⟩ := i
  induction vs generalizing i with
  | nil =>
    simp at hi
  | cons v vs' ih =>
    simp at h ⊢
    cases i with
    | zero => exact (indep_of_concat h).left
    | succ i =>
      simp at hi
      exact ih (indep_of_concat h).right i hi

/-- (i) → (ii) of Corollary (2.3) in `Partial Commutation and Traces`.
  Note that t₁, t₂, …, tₙ is expressed as a list [ts], and (t₁ ++ t₂ ++ … ++ tₙ) via [ts.flatten].
  Similarly, p₁, …, pₙ is [ps] and q₁, …, qₙ is [qs]. -/
theorem levi_lemma_gen (u v : List α) (ts : List (List α)) [DecidableEq α] (h : TraceEquiv I (u ++ v) ts.flatten) :
    ∃ (ps qs : List (List α)),
    ps.length = ts.length
    ∧ qs.length = ts.length
    ∧ TraceEquiv I u ps.flatten
    ∧ TraceEquiv I v qs.flatten
    ∧ (∀ i : Fin (min ts.length (min ps.length qs.length)), TraceEquiv I ts[i] (ps[i] ++ qs[i]))
    ∧ ∀ i : Fin qs.length, ∀ j : Fin ps.length, i.val < j.val → independent I qs[i] ps[j] := by
  induction ts generalizing u v with
  | nil =>
    simp at h ⊢
    replace h := length_eq_of_equiv h
    simp at h
    simp [h, TraceEquiv.refl]
    intro ⟨i, hi⟩
    simp at hi
  | cons t tsuf ih =>
    have ⟨p, psuf, q, qsuf, h_ind, h_up, h_vq, h_tpq, h_tpq_suf⟩ := levi_lemma h
    replace ih := ih psuf qsuf h_tpq_suf.symm
    have ⟨ps_i, qs_i, ih_p_len, ih_q_len, ih_p, ih_q, ih_tpq, ih_ind⟩ := ih
    clear ih
    use p :: ps_i, q :: qs_i
    repeat' apply And.intro
    · simp [ih_p_len]
    · simp [ih_q_len]
    · apply TraceEquiv.trans h_up
      simp
      exact TraceEquiv.compat (TraceEquiv.refl p) ih_p
    · apply TraceEquiv.trans h_vq
      simp
      exact TraceEquiv.compat (TraceEquiv.refl q) ih_q
    · intro ⟨i, hi⟩
      by_cases hzi : i = 0
      · simp [hzi, h_tpq]
      · cases i with
        | zero => contradiction
        | succ i =>
          simp at hi ⊢
          exact ih_tpq ⟨i, by simp; exact hi⟩
    · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      cases j with
      | zero => contradiction
      | succ j =>
        cases i with
        | zero =>
          simp at hj ⊢
          have h_ind_ps := indep_of_indep_of_equiv (indep_symm h_ind) ih_p
          exact indep_of_flatten ⟨j, hj⟩ h_ind_ps
        | succ i =>
          simp at hi hj hij ⊢
          exact ih_ind ⟨i, hi⟩ ⟨j, hj⟩ hij




variable {M : Type} [Monoid M]
variable {α : Type} [Monoid α]
variable {σ : Type}

-- We need [DecidableEq N] to match the definition of `IsRecognizableDFMA`; see the latter.
def IsRecognizable (S : Set M) : Prop :=
  ∃ N : Type, ∃ _ : Monoid N, ∃ _ : Fintype N, ∃ _ : DecidableEq N, ∃ φ : M →* N, S = φ⁻¹' (φ '' S)

variable (α σ) in
/-- (Deterministic) M-automaton. Following the convention of `Mathlib.Computability.DFA`,
  the finiteness of `σ` is not imposed here and should be handled separately. -/
structure DFMA where
  step : σ → α → σ
  start : σ
  accept : Set σ
  idempotent (q : σ) : step q 1 = q
  composition (q : σ) (u v : α) : step (step q u) v = step q (u * v)

namespace DFMA

variable {A : DFMA α σ}

def eval (x : α) : σ := A.step A.start x

def eval_set (S : Set α) : Set σ := S.image A.eval

def accepts : Set α := {x | A.eval x ∈ A.accept}

end DFMA

-- We need [DecidableEq σ] to derive the finiteness of (σ → σ) through `Finset.pi`.
def IsRecognizableDFMA (S : Set M) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ _ : DecidableEq σ, ∃ A : DFMA M σ, S = A.accepts

/-- Prop 4.1 (i) => (iii) -/
theorem recognizable_is_recognizableDFMA (S : Set M) :
    IsRecognizable S → IsRecognizableDFMA S := by
  unfold IsRecognizable IsRecognizableDFMA
  intro ⟨N, N_mon, N_fin, N_dec, φ, h⟩
  use N, N_fin, N_dec
  use {
    step := fun n m => n * (φ m)
    start := 1
    accept := φ '' S
    idempotent := by simp
    composition := by
      intro q u v
      rw [map_mul φ u v]
      exact mul_assoc q (φ u) (φ v)
  }
  unfold DFMA.accepts DFMA.eval DFMA.step
  simp
  apply Set.ext_iff.mpr
  intro x
  apply Iff.intro
  · intro hx
    apply Set.mem_setOf.mpr
    use x
  · intro hx
    apply Set.mem_setOf.mp at hx
    rcases hx with ⟨y, hy, hy_eq⟩
    rw [h, Set.mem_preimage, ← hy_eq]
    exact ⟨y, hy, rfl⟩

def fintype_to_fintype_is_fintype (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] :
    Fintype (α → β) := by
  rename_i hα hβ _
  refine ⟨?_, ?_⟩
  · have proj := (@Fintype.elems α).pi fun _ => @Fintype.elems β hβ
    exact proj.map {
      toFun f := fun a => f a (Fintype.complete a)
      inj' := by
        simp [Function.Injective]
        intro f g h
        apply funext
        intro a
        have h_eq_at : (fun a => f a (Fintype.complete a)) a = (fun a => g a (Fintype.complete a)) a := by rw[h]
        simp at h_eq_at
        exact funext fun x => h_eq_at
    }
  · intro f
    simp
    use fun a h => f a
    simp
    exact fun a h => Fintype.complete (f a)

/-- Prop 4.1 (iii) => (i) -/
theorem recognizableDFMA_is_recognizable (S : Set M) :
    IsRecognizableDFMA S → IsRecognizable S := by
  unfold IsRecognizable IsRecognizableDFMA
  intro ⟨σ, σ_fin, σ_dec, A, hA⟩
  use σ → σ
  let fn_mon : Monoid (σ → σ) := {
    mul := fun f g => g ∘ f
    mul_assoc := fun f g h => rfl
    one := id
    one_mul := fun f => rfl
    mul_one := fun f => rfl
  }
  use fn_mon, fintype_to_fintype_is_fintype σ σ, instDecidableEqOfLawfulBEq
  use {
    toFun := fun m => (fun x => A.step x m)
    map_one' := by apply funext A.idempotent
    map_mul' := by
      intro f g
      apply funext
      intro x
      rw [<- A.composition]
      rfl
  }
  simp [hA, DFMA.accepts, DFMA.eval]
  apply Set.ext_iff.mpr
  intro m
  apply Iff.intro
  · intro hm
    apply Set.mem_setOf.mp at hm
    apply Set.mem_setOf.mpr
    simp
    use m
  · intro hm
    apply Set.mem_setOf.mpr
    apply Set.mem_setOf.mp at hm
    simp at hm
    rcases hm with ⟨m', hm', hm_eq⟩
    replace hm_eq : (fun x => A.step x m') A.start = (fun x => A.step x m) A.start := by rw [hm_eq]
    simp at hm_eq
    rw [hm_eq] at hm'
    exact hm'


variable {T : Set M}

def syntacticCongr (T : Set M) (x y : M) := ∀ u v : M, u * x * v ∈ T ↔ u * y * v ∈ T

def syntacticSetoid (T : Set M) : Setoid (M) where
  r := syntacticCongr T
  iseqv := Equivalence.mk
    (fun _ _ _ => Set.MapsTo.mem_iff (fun ⦃_⦄ a => a) fun ⦃_⦄ a => a)
    (fun {_ _} a u v => (fun {_ _} => iff_comm.mp) (a u v))
    (fun {_ _ _} a a_1 u v => Iff.trans (a u v) (a_1 u v))

def syntacticMonoid (T : Set M) := Quotient (syntacticSetoid T)

instance : Monoid (syntacticMonoid T) where
  mul := Quotient.lift₂
    (fun w₁ w₂ => ⟦w₁ * w₂⟧)
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      apply Quotient.sound
      intro u v
      have hT₁ := ha u (b₁ * v)
      have hT₂ := hb (u * a₂) v
      rename_i hM _
      calc
        u * (a₁ * b₁) * v ∈ T ↔ u * a₁ * (b₁ * v) ∈ T := by simp only [hM.mul_assoc]
        _ ↔ u * a₂ * (b₁ * v) ∈ T := hT₁
        _ ↔ u * a₂ * b₁ * v ∈ T := by simp only [hM.mul_assoc]
        _ ↔ u * a₂ * b₂ * v ∈ T := hT₂
        _ ↔ u * (a₂ * b₂) * v ∈ T := by simp only [hM.mul_assoc]
    )
  one := Quotient.mk (syntacticSetoid T) 1
  mul_assoc := by
    intro t₁ t₂ t₃
    refine Quotient.inductionOn₃ t₁ t₂ t₃ (fun w₁ w₂ w₃ => ?_)
    apply Quotient.sound
    rename_i hM _
    rw [hM.mul_assoc]
    intro u v
    rfl
  one_mul := by
    intro t
    refine Quotient.inductionOn t (fun w => ?_)
    apply Quotient.sound
    rename_i hM _
    rw [hM.one_mul]
    intro u v
    rfl
  mul_one := by
    intro t
    refine Quotient.inductionOn t (fun w => ?_)
    apply Quotient.sound
    rename_i hM _
    rw [hM.mul_one]
    intro u v
    rfl


/-- Prop 4.1 (ii) => (i) -/
theorem finSyntacticIndex_is_recognizable :
    Finite (syntacticMonoid T) → IsRecognizable T := by
  intro h
  use syntacticMonoid T, by infer_instance, Fintype.ofFinite _, Classical.typeDecidableEq (syntacticMonoid T)
  use {
    toFun := fun m => ⟦m⟧
    map_one' := by rfl
    map_mul' := by intro x y; rfl
  }
  simp
  apply Set.ext_iff.mpr
  intro x
  simp
  apply Iff.intro
  · intro hx
    use x
  · intro ⟨y, ⟨hy, hxy⟩⟩
    apply @Quotient.exact _ _ y x at hxy
    replace hxy := hxy 1 1
    simp at hxy
    exact hxy.mp hy

/-- Prop 4.1 (i) => (ii) -/
theorem recognizable_is_finSyntacticIndex :
    IsRecognizable T → Finite (syntacticMonoid T) := by
  unfold IsRecognizable
  intro ⟨N, N_mon, N_fin, N_dec, φ, h⟩
  have h_img_syn : ∀ a b, φ a = φ b → syntacticCongr T a b := by
    intro a b hab u v
    rw [h]
    simp [hab]
  let f : φ '' Set.univ → syntacticMonoid T := fun ⟨n, hn⟩ => ⟦Classical.choose hn⟧
  have f_surj : Function.Surjective f := by
    intro q
    have ⟨m, hm⟩ := Quotient.exists_rep q
    use ⟨φ m, Set.mem_image_of_mem φ trivial⟩
    rw [<- hm]
    apply Quotient.sound
    intro u v
    apply h_img_syn
    have hm : φ m ∈ ⇑φ '' Set.univ := Set.mem_image_of_mem (⇑φ) trivial
    exact (Classical.choose_spec hm).2
  exact Finite.of_surjective f f_surj

/-- Prop 4.1 (i) => (iv) -/
theorem recognizable_has_recognizablePreImage (L : Type) [Monoid L] (φ : L →* M) :
    IsRecognizable T → IsRecognizable (φ ⁻¹' T) := by
  intro h
  unfold IsRecognizable at h ⊢
  rcases h with ⟨N, N_mon, N_fin, N_dec, ψ, hψ⟩
  use N, N_mon, N_fin, N_dec
  use {
    toFun := ψ ∘ φ
    map_one' := by simp
    map_mul' := by simp
  }
  simp
  ext x
  apply Iff.intro
  · intro hx
    rw [Set.mem_preimage] at hx
    rw [Set.mem_preimage, Set.mem_image]
    use x
    simp [hx]
  · intro hx
    rw [Set.mem_preimage, Set.mem_image] at hx
    obtain ⟨y, hy, h⟩ := hx
    have hφy : φ y ∈ T := by rwa [Set.mem_preimage] at hy
    have : ψ (φ x) ∈ ψ '' T := by
      rw [Set.mem_image]
      exact ⟨φ y, hφy, h⟩
    have : φ x ∈ ψ ⁻¹' (ψ '' T) := by rwa [Set.mem_preimage]
    rw [← hψ] at this
    rw [Set.mem_preimage]
    exact this

noncomputable def preImage_syntacticMonoid_iso (L : Type) [Monoid L] (φ : L →* M) (hφ : Function.Surjective φ) :
    syntacticMonoid (φ ⁻¹' T) ≃* syntacticMonoid T := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact Quotient.lift (fun l => ⟦φ l⟧) (by
        intro a b hab
        simp
        apply Quotient.sound
        intro u v
        have ⟨u', hu'⟩ := hφ u
        have ⟨v', hv'⟩ := hφ v
        replace hab := hab u' v'
        rw [Set.mem_preimage] at hab
        simp [hu', hv'] at hab
        exact hab
      )
    · exact Quotient.lift (fun m => ⟦Classical.choose (hφ m)⟧) (by
        intro a b hab
        simp
        apply Quotient.sound
        intro u v
        simp [Set.mem_preimage]
        rw [Classical.choose_spec (hφ a), Classical.choose_spec (hφ b)]
        exact hab (φ u) (φ v)
      )
    · intro x
      rcases x
      rename_i l
      simp
      apply Quotient.sound
      intro u v
      simp [Set.mem_preimage]
      rw [Classical.choose_spec (hφ (φ l))]
    · intro x
      rcases x
      rename_i m
      simp
      apply Quotient.sound
      intro u v
      rw [Classical.choose_spec (hφ m)]
  · intro x y
    rcases x
    rcases y
    rename_i l₁ l₂
    apply Quotient.sound
    intro u v
    rw [MonoidHom.map_mul φ l₁ l₂]

/-- Prop 4.1 (iv) => (i) -/
theorem recognizablePreImage_is_recognizable (L : Type) [Monoid L] (φ : L →* M) (hφ : Function.Surjective φ) :
    IsRecognizable (φ ⁻¹' T) → IsRecognizable T := by
  intro h
  apply recognizable_is_finSyntacticIndex at h
  apply finSyntacticIndex_is_recognizable
  have ψ := @preImage_syntacticMonoid_iso M _ T L _ φ hφ
  exact ψ.finite_iff.mp h


--def langOf (t : List α) : Language α := {t}
--def kstar (L : Language α) : Language α := L∗

variable {α : Type} {I : Independence α}

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

namespace RegularExpression

def isStarConnected (I : Independence α) : RegularExpression α → Prop
  | 0 => True
  | 1 => True
  | RegularExpression.char _ => True
  | P + Q => isStarConnected I P ∧ isStarConnected I Q
  | P * Q => isStarConnected I P ∧ isStarConnected I Q
  | RegularExpression.star P => isStarConnected I P ∧ (∀ s ∈ P.matches', @isConnected' α I s)

-- Interpretation of this RegularExpression as operating on trace languages.
def matches_trace (I : Independence α) : RegularExpression α → Set (Trace I)
  | 0 => {}
  | 1 => {⟦[]⟧}
  | RegularExpression.char a => {⟦[a]⟧}
  | P + Q => (matches_trace I P) ∪ (matches_trace I Q)
  | P * Q => {t | ∃ p : (matches_trace I P), ∃ q : (matches_trace I Q), t = p * q}
  | RegularExpression.star P => kstar (matches_trace I P)

def isStarConnected_trace (I : Independence α) : RegularExpression α → Prop
  | 0 => True
  | 1 => True
  | RegularExpression.char _ => True
  | P + Q => isStarConnected I P ∧ isStarConnected I Q
  | P * Q => isStarConnected I P ∧ isStarConnected I Q
  | RegularExpression.star P => isStarConnected I P ∧ (∀ t ∈ matches_trace I P, @isConnected α I t)

-- Interpretation of this RegularExpression as a <c-rational expression> operating on trace languages.
def matches_cstar_trace (I : Independence α) : RegularExpression α → Set (Trace I)
  | 0 => {}
  | 1 => {⟦[]⟧}
  | RegularExpression.char a => {⟦[a]⟧}
  | P + Q => (matches_cstar_trace I P) ∪ (matches_cstar_trace I Q)
  | P * Q => {t | ∃ p : (matches_cstar_trace I P), ∃ q : (matches_cstar_trace I Q), t = p * q}
  | RegularExpression.star P => kstar (connectedComponents (matches_cstar_trace I P))

/-- Interpreting this RegularExpression as operating on Trace Languages gives the same matching set
  as interpreting (as usual) on String Languages and then projecting to Traces.
-/
theorem matches_toTrace (P : RegularExpression α) : (matches_trace I P) = toTrace P.matches' := by
  induction P with
  | zero => simp [toTrace, matches_trace, Language.zero_def]
  | epsilon => simp [toTrace, matches_trace, Language.one_def]
  | char a =>
    simp [toTrace, matches_trace, Set.image]
    apply Set.ext_iff.mpr
    intro t
    apply Iff.intro
    · simp
      intro h
      use [a]
      exact ⟨rfl, Eq.symm h⟩
    · simp
      intro x hx hat
      replace hx : x = [a] := hx
      rw [<- hat, hx]
  | plus P Q ihP ihQ =>
    unfold matches_trace RegularExpression.matches'
    simp [ihP, ihQ]
    apply Set.ext_iff.mpr
    intro t
    apply Iff.intro
    · intro h
      cases h
      all_goals
        rename_i h
        simp [toTrace] at h
        have ⟨x, hx⟩ := h
        use x
        simp [hx, Language.add_def]
    · intro h
      simp [Language.add_def, toTrace] at h
      have ⟨x, ⟨hx, hxt⟩⟩ := h
      simp [<- hxt, toTrace]
      cases hx with
      | inl hx => apply Or.inl; use x
      | inr hx => apply Or.inr; use x
  | comp P Q ihP ihQ =>
    unfold matches_trace RegularExpression.matches' toTrace
    rw [Set.image]
    apply Set.ext_iff.mpr
    intro t
    apply Iff.intro
    all_goals simp
    · simp [ihP, ihQ, toTrace]
      intro u hu v hv ht
      simp [Language.mul_def]
      use u; simp [hu]
      use v; simp [hv]
      rw [ht]
      rfl
    · simp [Language.mul_def]
      intro w u hu v hv hw ht
      simp [ihP, ihQ, toTrace]
      use u; simp [hu]
      use v; simp [hv]
      rw [<- ht, <- hw]
      rfl
  | star P ih =>
    unfold matches_trace RegularExpression.matches'
    rw [kstar_toTrace_commutes, ih]


@[simp]
lemma matches_toTrace_dist (P Q : RegularExpression α) :
    @toTrace α I (P.matches' + Q.matches') = toTrace P.matches' ∪ toTrace Q.matches' := by
  rw [show P.matches' + Q.matches' = (P + Q).matches' from rfl]
  repeat rw [<- RegularExpression.matches_toTrace]
  simp [RegularExpression.matches_trace]


end RegularExpression

/-- Main component of Theorem 4.1 (ii) => (iii).

  For a rational expression X, if every iterative factor of L(X) is connected,
  then X' is star-connected (for some rational expression X' with L(X) = L(X')).

  It is strictly necessary that we use an X' not necessarily equal to X.
  Consider X = {a ∪ b}∗ · ∅; where `a` and `b` are not connected. Then L(X) = ∅ so every
  iterative factor is connected, but X is not star-connected.

  Note that P · ∅ or ∅ · P are the only cases where this patch is needed.
-/
theorem connectedIterativeFactors_equiv_starConnected' (X : RegularExpression α)
    (hconn : ∀ s, isIterativeFactor X.matches' s → @isConnected' α I s) :
    ∃ Y, RegularExpression.isStarConnected I Y ∧ X.matches' = Y.matches' := by
  induction X with
  | zero => use RegularExpression.zero, trivial
  | epsilon => use RegularExpression.epsilon, trivial
  | char a => use RegularExpression.char a, trivial
  | plus P Q ihP ihQ =>
    have ihP_cond : (∀ s, isIterativeFactor P.matches' s → @isConnected' α I s) := by
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

    have ihQ_cond : (∀ s, isIterativeFactor Q.matches' s → @isConnected' α I s) := by
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

    have ihP_cond : (∀ s, isIterativeFactor P.matches' s → @isConnected' α I s) := by
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

    have ihQ_cond : (∀ s, isIterativeFactor Q.matches' s → @isConnected' α I s) := by
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
    have ih_cond : ∀ (s : List α), isIterativeFactor P.matches' s → @isConnected' α I s := by
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
    (hconn : ∀ s, isIterativeFactor X.matches' s → @isConnected' α I s) :
    ∃ P, RegularExpression.isStarConnected I P ∧ T = (RegularExpression.matches_trace I P) := by
  simp [RegularExpression.matches_toTrace]
  have ⟨P, hP⟩ := connectedIterativeFactors_equiv_starConnected' X hconn
  use P
  simp [hP, himg]

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
    have hP_conn : (∀ t ∈ RegularExpression.matches_trace I P, t.isConnected) := by
      intro t ht
      rcases t with ⟨w₀⟩
      rw [show Quot.mk (⇑(traceSetoid I)) w₀ = ⟦w₀⟧ from rfl] at ht ⊢
      rw [RegularExpression.matches_toTrace] at ht
      simp [toTrace] at ht
      rcases ht with ⟨w, hw⟩
      rw [<- hw.2, <- isConnected_toTrace]
      exact h.2 w hw.1
    rw [connectedComponents_of_connected _ hP_conn]
    rw [kstar_eq_minusEps_trace]


end Trace
