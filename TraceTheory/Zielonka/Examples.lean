import TraceTheory.Computability.Zielonka

namespace TraceTheory.Zielonka.Examples

/-- Actions `false` and `true` belong to different processes; process 2 is idle. -/
def separated : Distribution Bool 3 where
  loc a := {if a then 1 else 0}
  loc_nonempty _ := Finset.singleton_nonempty _

def toggle : AsyncDFA separated (fun _ => Bool) where
  step _ q p := !q p
  start _ := false
  accept := {q | q 0 = true ∧ q 1 = true}

example : toggle.eval [false, true] = toggle.eval [true, false] := by
  exact toggle.step_comm_of_disjoint toggle.start false true (by decide)

example (w : List Bool) : toggle.eval w 2 = false := by
  have h (q : Fin 3 → Bool) : toggle.evalFrom q w 2 = q 2 := by
    induction w generalizing q with
    | nil => rfl
    | cons a w ih =>
      change toggle.evalFrom (toggle.globalStep q a) w 2 = q 2
      rw [ih, toggle.globalStep_of_not_mem]
      cases a <;> decide
  exact h toggle.start

example : [false, true] ∈ toggle.accepts := by
  change toggle.eval [false, true] 0 = true ∧ toggle.eval [false, true] 1 = true
  decide
example : [false, false, true] ∉ toggle.accepts := by
  change ¬ (toggle.eval [false, false, true] 0 = true ∧
    toggle.eval [false, false, true] 1 = true)
  decide

/-- A three-way synchronization updates all three local states jointly. -/
def shared : Distribution Unit 3 where
  loc _ := Finset.univ
  loc_nonempty _ := ⟨0, Finset.mem_univ _⟩

def synchronize : AsyncDFA shared (fun _ => Bool) where
  step _ q _ := !(q ⟨0, Finset.mem_univ _⟩)
  start p := p == 1
  accept := {q | ∀ p, q p = true}

example : [()] ∈ synchronize.accepts := by
  change ∀ p, synchronize.eval [()] p = true
  decide

/-- The zero-process boundary permits an empty alphabet. -/
def emptyDistribution : Distribution Empty 0 where
  loc := Empty.elim
  loc_nonempty a := a.elim

def emptyAutomaton : AsyncDFA emptyDistribution (fun _ => Unit) where
  step a := a.elim
  start _ := ()
  accept := Set.univ

example : [] ∈ emptyAutomaton.accepts := by trivial

local instance : Monoid Unit where
  mul _ _ := ()
  one := ()
  mul_assoc _ _ _ := rfl
  one_mul x := by cases x; rfl
  mul_one x := by cases x; rfl

private def unitHom (M : Type) [Monoid M] : M →* Unit where
  toFun _ := ()
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem recognizable_empty (M : Type) [Monoid M] :
    IsRecognizable (∅ : Set M) := by
  refine ⟨Unit, inferInstance, inferInstance, inferInstance, unitHom M, ?_⟩
  simp

private theorem recognizable_full (M : Type) [Monoid M] :
    IsRecognizable (Set.univ : Set M) := by
  refine ⟨Unit, inferInstance, inferInstance, inferInstance, unitHom M, ?_⟩
  ext x
  constructor
  · intro _
    exact ⟨x, Set.mem_univ x, rfl⟩
  · intro _
    trivial

/-- The public construction applies with independent actions and an idle process. -/
theorem separated_empty_language :
    ∃ (Q : Fin 3 → Type) (_ : ∀ p, Fintype (Q p)) (A : AsyncDFA separated Q),
      A.accepts = (∅ : Set (List Bool)) := by
  simpa using zielonka separated (I := separated.independence) (fun _ _ => Iff.rfl)
    ∅ (recognizable_empty (Trace separated.independence))

/-- Full trace languages are handled across a three-way synchronization. -/
theorem shared_full_language :
    ∃ (Q : Fin 3 → Type) (_ : ∀ p, Fintype (Q p)) (A : AsyncDFA shared Q),
      A.accepts = Set.univ := by
  simpa using zielonka shared (I := shared.independence) (fun _ _ => Iff.rfl)
    Set.univ (recognizable_full (Trace shared.independence))

/-- The public construction also covers an empty alphabet with zero processes. -/
theorem zero_process_full_language :
    ∃ (Q : Fin 0 → Type) (_ : ∀ p, Fintype (Q p)) (A : AsyncDFA emptyDistribution Q),
      A.accepts = Set.univ := by
  simpa using zielonka emptyDistribution (I := emptyDistribution.independence)
    (fun _ _ => Iff.rfl) Set.univ (recognizable_full (Trace emptyDistribution.independence))

end TraceTheory.Zielonka.Examples
