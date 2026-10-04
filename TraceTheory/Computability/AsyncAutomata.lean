import TraceTheory.Computability.MyhillNerode
import TraceTheory.History

namespace TraceTheory

variable {α : Type} {n : ℕ}

/-- A distributed alphabet: each action has a nonempty set of participating processes. -/
structure Distribution (α : Type) (n : ℕ) where
  loc : α → Finset (Fin n)
  loc_nonempty : ∀ a, (loc a).Nonempty

namespace Distribution

/-- The independence induced by a distributed alphabet (PDF, section 1.6). -/
def independence (d : Distribution α n) : Independence α where
  rel a b := Disjoint (d.loc a) (d.loc b)
  irrefl a := by
    intro h
    obtain ⟨p, hp⟩ := d.loc_nonempty a
    exact Finset.disjoint_left.mp h hp hp
  symm _ _ h := h.symm

/-- A distribution represents `I` when disjoint actions are exactly the independent ones. -/
def Compatible (d : Distribution α n) (I : Independence α) : Prop :=
  ∀ a b, I.rel a b ↔ Disjoint (d.loc a) (d.loc b)

/-- Local alphabets, in the notation already used by `History`. -/
def alphabets [Fintype α] (d : Distribution α n) (p : Fin n) : Finset α :=
  Finset.univ.filter (fun a => p ∈ d.loc a)

@[simp]
theorem mem_alphabets [Fintype α] (d : Distribution α n) (p : Fin n) (a : α) :
    a ∈ d.alphabets p ↔ p ∈ d.loc a := by simp [alphabets]

theorem alphabets_cover [Fintype α] (d : Distribution α n) :
    ∀ a, ∃ p, a ∈ d.alphabets p := by
  intro a
  obtain ⟨p, hp⟩ := d.loc_nonempty a
  exact ⟨p, (d.mem_alphabets p a).mpr hp⟩

theorem sigmaDependence_rel [Fintype α] (d : Distribution α n) (a b : α) :
    (History.SigmaDependence d.alphabets d.alphabets_cover).rel a b ↔
      ¬ Disjoint (d.loc a) (d.loc b) := by
  simp [History.SigmaDependence, Finset.disjoint_left]

end Distribution

variable (d : Distribution α n) (Q : Fin n → Type)

/-- A tuple containing only the local states of the participants in `a`. -/
abbrev ParticipantState (a : α) := ∀ p : {p // p ∈ d.loc a}, Q p.val

/-- A deterministic asynchronous automaton (PDF, section 1.5).
Finiteness is imposed separately, as for `DFA` and `DFMA` in this repository. -/
structure AsyncDFA where
  step : ∀ a, ParticipantState d Q a → ParticipantState d Q a
  start : ∀ p, Q p
  accept : Set (∀ p, Q p)

namespace AsyncDFA

variable {d Q} (A : AsyncDFA d Q)

/-- An action reads and updates its participants; every other state is left untouched. -/
def globalStep (q : ∀ p, Q p) (a : α) : ∀ p, Q p :=
  fun p => if h : p ∈ d.loc a then A.step a (fun r => q r.val) ⟨p, h⟩ else q p

@[simp]
theorem globalStep_of_not_mem (q : ∀ p, Q p) (a : α) (p : Fin n)
    (h : p ∉ d.loc a) : A.globalStep q a p = q p := by
  simp [globalStep, h]

@[simp]
theorem globalStep_of_mem (q : ∀ p, Q p) (a : α) (p : Fin n)
    (h : p ∈ d.loc a) :
    A.globalStep q a p = A.step a (fun r => q r.val) ⟨p, h⟩ := by
  simp [globalStep, h]

theorem globalStep_local (q r : ∀ p, Q p) (a : α)
    (h : ∀ p ∈ d.loc a, q p = r p) (p : Fin n) (hp : p ∈ d.loc a) :
    A.globalStep q a p = A.globalStep r a p := by
  have hr : (fun p : {p // p ∈ d.loc a} => q p.val) = (fun p : {p // p ∈ d.loc a} => r p.val) :=
    funext fun p => h p.val p.property
  simp only [globalStep_of_mem A _ a p hp, hr]

/-- Independent actions commute from every global state, not just reachable states. -/
theorem step_comm_of_disjoint (q : ∀ p, Q p) (a b : α)
    (h : Disjoint (d.loc a) (d.loc b)) :
    A.globalStep (A.globalStep q a) b = A.globalStep (A.globalStep q b) a := by
  have hab := Finset.disjoint_left.mp h
  have ha : (fun p : {p // p ∈ d.loc a} => A.globalStep q b p.val) =
      (fun p : {p // p ∈ d.loc a} => q p.val) := by
    funext p
    exact A.globalStep_of_not_mem q b p.val (hab p.property)
  have hb : (fun p : {p // p ∈ d.loc b} => A.globalStep q a p.val) =
      (fun p : {p // p ∈ d.loc b} => q p.val) := by
    funext p
    exact A.globalStep_of_not_mem q a p.val (fun hp => hab hp p.property)
  funext p
  by_cases hpa : p ∈ d.loc a
  · have hpb := hab hpa
    rw [A.globalStep_of_not_mem _ b p hpb, A.globalStep_of_mem _ a p hpa,
      A.globalStep_of_mem _ a p hpa, ha]
  · by_cases hpb : p ∈ d.loc b
    · rw [A.globalStep_of_not_mem _ a p hpa, A.globalStep_of_mem _ b p hpb,
        A.globalStep_of_mem _ b p hpb, hb]
    · simp only [A.globalStep_of_not_mem _ a p hpa,
        A.globalStep_of_not_mem _ b p hpb]

/-- Forgetting the distribution gives an ordinary DFA on global states. -/
def toDFA : DFA α (∀ p, Q p) where
  step := A.globalStep
  start := A.start
  accept := A.accept

abbrev evalFrom (q : ∀ p, Q p) (w : List α) := A.toDFA.evalFrom q w
abbrev eval (w : List α) := A.toDFA.eval w
abbrev accepts : Language α := A.toDFA.accepts

@[simp]
theorem evalFrom_append (q : ∀ p, Q p) (u v : List α) :
    A.evalFrom q (u ++ v) = A.evalFrom (A.evalFrom q u) v :=
  List.foldl_append

/-- Runs depend only on the trace of the input. -/
theorem evalFrom_eq_of_traceEqv {I : Independence α} (hcompat : d.Compatible I)
    {u v : List α} (h : TraceEqv I u v) (q : ∀ p, Q p) :
    A.evalFrom q u = A.evalFrom q v := by
  induction h generalizing q with
  | swap a b hab =>
    exact A.step_comm_of_disjoint q a b ((hcompat a b).mp hab)
  | refl => rfl
  | symm _ ih => exact (ih q).symm
  | trans _ _ ihu ihv => exact (ihu q).trans (ihv q)
  | compat _ _ ihu ihv =>
    simp only [evalFrom_append, ihu q, ihv]

theorem accepts_traceEqv {I : Independence α} (hcompat : d.Compatible I)
    {u v : List α} (h : TraceEqv I u v) : u ∈ A.accepts ↔ v ∈ A.accepts := by
  change A.evalFrom A.start u ∈ A.accept ↔ A.evalFrom A.start v ∈ A.accept
  rw [A.evalFrom_eq_of_traceEqv hcompat h]

/-- The word action descends to an action of the trace monoid. -/
def toDFMA {I : Independence α} (hcompat : d.Compatible I) :
    DFMA (Trace I) (∀ p, Q p) where
  step q := Quotient.lift (A.evalFrom q)
    (fun _ _ h => A.evalFrom_eq_of_traceEqv hcompat h q)
  start := A.start
  accept := A.accept
  idempotent _ := rfl
  composition q u v := Quotient.inductionOn₂ u v (fun _ _ => (A.evalFrom_append q _ _).symm)

/-- The easy direction of Zielonka: finite asynchronous automata recognize trace languages. -/
theorem recognizable_accepts [∀ p, Fintype (Q p)] {I : Independence α}
    (hcompat : d.Compatible I) : IsRecognizable (A.toDFMA hcompat).accepts := by
  classical
  exact recognizableDFMA_is_recognizable _
    ⟨_, inferInstance, inferInstance, A.toDFMA hcompat, rfl⟩

theorem accepts_eq_preimage {I : Independence α} (hcompat : d.Compatible I) :
    A.accepts = Trace.mk' I ⁻¹' (A.toDFMA hcompat).accepts := rfl

theorem accepts_isRegular [∀ p, Fintype (Q p)] : A.accepts.IsRegular := by
  exact Language.isRegular_iff.mpr ⟨_, inferInstance, A.toDFA, rfl⟩

end AsyncDFA

end TraceTheory
