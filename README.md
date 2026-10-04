# Trace Theory Lean

This repository contains a formalization of Mazurkiewicz trace theory in the Lean theorem prover.

## Structure

### Core
- `Defs.lean` contains fundamental definitions for traces.
- `Basic.lean` contains basic properties of the algebra of traces.
- `DependenceMorphism.lean` provides a way to show isomorphism to the algebra of traces via dependence morphisms.

### Isomorphic Algebras
- `DependenceGraph.lean` contains a definition of the algebra of dependence graphs and proof of its isomorphism to traces.
- `Histories.lean` contains a definition of the algebra of histories and proof of its isomorphism to traces.

### Ochmański's Theorem
- `Language.lean` contains basic definitions and lemmas for trace languages.
- `MyhillNerode.lean` supplies a proof of the Myhill-Nerode theorem in the context of monoids.
- `Hashiguchi.lean` contains a proof of Hashiguchi's theorem on recognizable trace closures.
- `RegularExpressions.lean` reinterprets mathlib4's `RegularExpression` on traces.
- `Ochmanski.lean` contains the proof of Ochmański's theorem on recognizable trace languages and lemmas leading up to it.

### Misc
- `List.lean` contains misc. definitions and lemmas for `List` (string) manipulation.
- `Occurrence.lean` formalizes ordering of symbol occurrences.
- `Kleene.lean` supplies a full proof of Kleene's theorem together with mathlib4.

### Zielonka's Theorem
- `Computability/AsyncAutomata.lean` defines distributions and deterministic asynchronous automata with transitions restricted to participating processes.
- `Computability/Zielonka.lean` proves `zielonka` and `recognizable_iff_async` for every compatible finite distribution.
- `Zielonka/` develops causal views, finite gossip, primary residues, and the automaton construction. The proof follows Mukund's *Automata on Distributed Alphabets*, Sections 1.7–1.8 (Theorem 1.36), using finite recognizing-monoid values for residue effects. `EventGraph.lean` relates indexed events to the existing dependence graphs; `Examples.lean` checks boundary cases and simple distributions.

## Naming Convention

General guideline:

- `a, b, c, d, e` for symbols.
- `i, j, k` for indices.
- `n, m` for sizes.
- `u, v, w, x, y, z` for strings, `x', x''` or `x₁, x₂` or `p, q, r` for factoring.
- `s, t, u, v` for traces or monoid elements.
- `S` for (subsets of) alphabets.
- `X` for word (string) languages.
- `T` for trace langauges.
