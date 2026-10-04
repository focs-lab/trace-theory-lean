import TraceTheory.Zielonka.Residues

namespace TraceTheory.Zielonka

open Classical
noncomputable section

variable {α M : Type} {n : ℕ} {I : Independence α} {w : List α} {a : α}

/-- The event enumeration extends by the new last occurrence. -/
theorem finRange_append_event : List.finRange (w ++ [a]).length =
    (List.finRange w.length).map (oldEvent w a) ++ [lastEvent w a] := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    by_cases hi : i < w.length
    · simp [List.getElem_append_left, hi]
      apply Fin.ext
      rfl
    · have hieq : i = w.length := by simp at h₁; omega
      subst i
      simp [List.getElem_append_right, lastEvent]

/-- Projection of embedded old events preserves the projected word exactly. -/
theorem project_map_oldEvent (s : Finset (Event w)) :
    project (w ++ [a]) (s.map (oldEvent w a)) = project w s := by
  unfold project
  rw [finRange_append_event, List.filter_append, List.map_append]
  have hn : lastEvent w a ∉ s.map (oldEvent w a) := by
    intro h
    obtain ⟨e, _, he⟩ := Finset.mem_map.mp h
    have hv := congrArg Fin.val he
    have := e.isLt
    simp at hv
    omega
  simp only [List.filter_cons, hn, decide_false, Bool.false_eq_true, ↓reduceIte,
    List.filter_nil, List.map_nil, List.append_nil]
  rw [List.filter_map, List.map_map]
  simp only [Function.comp_def]
  have hpred : (fun e : Event w => decide (oldEvent w a e ∈ s.map (oldEvent w a))) =
      (fun e => decide (e ∈ s)) := by
    funext e
    simp
  rw [hpred]
  simp only [label_oldEvent]

/-- Downward closure commutes with embedding old occurrences. -/
theorem down_map_oldEvent (s : Finset (Event w)) :
    down I (s.map (oldEvent w a)) = (down I s).map (oldEvent w a) := by
  ext e
  simp only [mem_down, Finset.mem_map]
  constructor
  · rintro ⟨f, ⟨g, hg, rfl⟩, hef⟩
    rcases event_append_cases e with ⟨e, rfl⟩ | rfl
    · exact ⟨e, ⟨g, hg, (before_oldEvent_iff _ _).mp hef⟩, rfl⟩
    · exact (not_before_last_old g hef).elim
  · rintro ⟨e, ⟨f, hf, hef⟩, rfl⟩
    exact ⟨oldEvent w a f, ⟨f, hf, rfl⟩, before_oldEvent hef⟩

variable (d : Distribution α n)

/-- The indexed primary cut of an idle process retains its occurrences. -/
theorem primaryCut_append_nonparticipant (p : Fin n) (R : Finset (Fin n))
    (hp : p ∉ d.loc a) :
    primaryCut d I (w ++ [a]) p R = (primaryCut d I w p R).map (oldEvent w a) := by
  ext e
  simp only [mem_primaryCut, Finset.mem_map, primary_append_nonparticipant d _ _ hp]
  constructor
  · rintro ⟨r, hr, he⟩
    cases h : primary d I w p r with
    | none => simp [h] at he
    | some f =>
      simp only [h, Option.map_some, Option.some.injEq] at he
      exact ⟨f, ⟨r, hr, h⟩, he⟩
  · rintro ⟨f, ⟨r, hr, he⟩, rfl⟩
    exact ⟨r, hr, by simp [he]⟩

/-- Lemma 1.34: primary residues of an idle process are unchanged. -/
theorem primary_residue_append_nonparticipant (p : Fin n) (R : Finset (Fin n))
    (hp : p ∉ d.loc a) :
    view d I (w ++ [a]) p \ down I (primaryCut d I (w ++ [a]) p R) =
      (view d I w p \ down I (primaryCut d I w p R)).map (oldEvent w a) := by
  rw [view_append_nonparticipant d p hp, primaryCut_append_nonparticipant d p R hp,
    down_map_oldEvent, Finset.map_sdiff]

variable [Monoid M] (φ : Trace I →* M)

theorem primaryEffect_append_nonparticipant (p : Fin n) (R : Finset (Fin n))
    (hp : p ∉ d.loc a) :
    primaryEffect d φ (w ++ [a]) p R = primaryEffect d φ w p R := by
  unfold primaryEffect residueEffect
  rw [primary_residue_append_nonparticipant d p R hp, project_map_oldEvent]

end
end TraceTheory.Zielonka
