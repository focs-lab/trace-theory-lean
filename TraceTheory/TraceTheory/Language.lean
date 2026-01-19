import Mathlib.Data.List.Lex
import TraceTheory.Trace

open Trace

namespace Language

variable {α : Type} [LinearOrder α]

/-- Lexicographic Normal Form.
A word x is in normal form if it is minimal among all words equivalent to it. -/
def IsLexNf (I : Independence α) (x : List α) : Prop :=
  ∀ w, TraceEquiv I x w → x ≤ w

/-- The condition to be in Lexicographic Normal Form.
For all factorizations x = ybuaz, where (a, b) ∈ I, and a < b,
there exists a letter of u which does not commute with a. -/
def SatisfiesFactorCondition (I : Independence α) (x : List α) : Prop :=
  ∀ (y u z : List α) (a b : α),
    x = y ++ [b] ++ u ++ [a] ++ z →
    I.rel a b →
    a < b →
    ∃ c ∈ u, ¬ I.rel a c

lemma factorCondition_of_lexNf (I : Independence α) (x : List α) (h : IsLexNf I x) :
    SatisfiesFactorCondition I x := by
  intro y u z a b hx h_indep h_lt
  contrapose! h
  unfold IsLexNf
  push_neg
  use y ++ [a] ++ [b] ++ u ++ z
  rw [hx]
  constructor
  · have h_comm_au : TraceEquiv I ([a] ++ u) (u ++ [a]) := by
      apply equiv_comm_append_of_indep
      intro c hc
      simp at hc
      rw [hc]
      exact h
    apply TraceEquiv.compat _ (TraceEquiv.refl z)
    simp only [List.append_assoc]
    apply TraceEquiv.compat (TraceEquiv.refl y)
    apply TraceEquiv.trans (TraceEquiv.compat (TraceEquiv.refl [b]) (TraceEquiv.symm h_comm_au))
    simp only [← List.append_assoc]
    exact TraceEquiv.compat (TraceEquiv.swap b a (I.symm a b h_indep)) (TraceEquiv.refl u)
  · simp
    apply List.append_left_lt
    apply List.cons_lt_cons_iff.mpr
    left
    exact h_lt

lemma lexNf_of_factorCondition
    (I : Independence α) (x : List α) (h : SatisfiesFactorCondition I x) :
    IsLexNf I x := by
  sorry

theorem isLexNf_iff_factorCondition (I : Independence α) (x : List α) :
    IsLexNf I x ↔ SatisfiesFactorCondition I x := by
  constructor
  · apply factorCondition_of_lexNf
  · apply lexNf_of_factorCondition
