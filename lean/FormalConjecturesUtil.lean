/-
Copyright 2025, 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This compatibility file reproduces only the four definitions needed for the
standalone Graph Conjecture 2 proof attempt.
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Archimedean

/-!
# Minimal Formal Conjectures compatibility layer

This file contains only the four definitions used by
`WrittenOnTheWallII/GraphConjecture2.lean`.  They are copied verbatim in
meaning from the corresponding Formal Conjectures utility files, so the proof
can be checked without cloning the full repository.
-/

namespace SimpleGraph

open Classical Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

/-- The same quantity as a real number. -/
noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

/-- Average of `indepNeighbors` over all vertices. -/
noncomputable def averageIndepNeighbors (G : SimpleGraph α) : ℝ :=
  (∑ v ∈ Finset.univ, indepNeighbors G v) / (Fintype.card α : ℝ)

/-- Maximum number of leaves over all spanning trees of `G`. -/
noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  let leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  let numLeaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (numLeaves T : ℝ)) spanningTrees)

end SimpleGraph
