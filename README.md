# Written on the Wall II, Graph Conjecture 2 — Lean Proof

Written on the Wall II (WOWII), Graph Conjecture 2 is an open problem in
graph theory concerning the number of leaves in spanning trees.

[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) is
a public repository of conjecture statements formalized in Lean using
mathlib. Its
[Lean entry for this problem](https://github.com/google-deepmind/formal-conjectures/blob/5a60e068cceb4edffa992dd0bdbda8c6c17185c5/FormalConjectures/WrittenOnTheWallII/GraphConjecture2.lean)
is marked `@[category research open]`.

This repository presents a Lean proof of that formalized target.

You can check the Lean4Web version in your browser:
[Open in Lean4Web](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fwowii-graph-conjecture-2-lean%2Fmain%2Flean4web%2FGraphConjecture2Lean4Web.lean).

## Formalized target

```lean
theorem conjecture2 (G : SimpleGraph α) (hG : G.Connected) :
    2 * (G.averageIndepNeighbors - 1) ≤ G.Ls
```

In ordinary mathematical language, this says that for every finite connected
simple graph, the maximum number of leaves in a spanning tree is at least twice
the average neighbourhood independence number minus two. The proof handles the
one-vertex case separately and uses the main graph-theoretic argument when the
vertex type is nontrivial.

## Status

- Status: locally checked proof
- Local build: Lean 4.27.0 / mathlib v4.27.0
- Lean4Web compatibility target: Latest Mathlib with Lean v4.33.0-rc1
  on 2026-07-26
- `sorry` / `admit`: none
- `#print axioms conjecture2`:
  `[propext, Classical.choice, Quot.sound]`
- `sorryAx`: not present

## Files

```text
lean/       pinned local version
lean4web/   single-file Lean4Web version
```

The two versions do not import each other.

## Check locally

```bash
cd lean
lake update
lake exe cache get
lake build GraphConjecture2
```

## Lean4Web

Open <https://live.lean-lang.org/> and load:

```text
lean4web/GraphConjecture2Lean4Web.lean
```

The compatibility target used while preparing the file was:

```text
Lean4Web project: Latest Mathlib
Lean version:     v4.33.0-rc1
Date:             2026-07-26
```

“Latest Mathlib” is a moving environment and is not pinned by the source
file. The file therefore includes:

```lean
#eval Lean.versionString
#check conjecture2
#print axioms conjecture2
```

The pinned local project in `lean/` is the reproducible reference build.

## Mathematical explanation (AI-generated)

For each vertex `v`, let `μ(v)` be the independence number of the graph
induced by the neighbours of `v`. Let `μ̄` be the average of `μ(v)`, and let
`Ls(G)` be the largest leaf count among spanning trees of `G`.

The proof attempt proceeds as follows.

1. Choose a triangle-free spanning subgraph `H ≤ G` with the maximum possible
   number of edges.
2. For a vertex `v`, replace every edge of `H` incident to `v` by edges from
   `v` to a maximum independent set in `G[N(v)]`. The replacement remains
   triangle-free. Maximality of `H` therefore gives
   `μ(v) ≤ degree H v`.
3. Sum the endpoint degree sums over all edges of `H`. Using the handshake
   lemma and Cauchy–Schwarz gives an edge `uv` whose endpoint degree sum is at
   least twice the average degree of `H`, and hence at least `2μ̄`.
4. Because `H` is triangle-free, the double star formed from the edges at
   `u` and `v` is acyclic. Extend it to a maximal acyclic subgraph of the
   connected graph `G`; this is a spanning tree.
5. For a finite nontrivial tree `T`,
   `leafCount T = 2 + ∑ x, (degree T x - 2)`. Since the spanning tree contains
   the double star, its leaf count is at least
   `degree H u + degree H v - 2`.

Combining these inequalities gives:

```text
Ls(G) ≥ 2(μ̄ - 1).
```

For a one-vertex connected graph, the average neighbourhood independence
number and `Ls` are both zero, so the inequality holds directly.

The Lean proof uses a maximal acyclic extension in Step 4 instead of
formalizing a vertex-by-vertex extension of the double star.

## AI Usage Disclosure

This formalization is assisted by ChatGPT 5.6 sol and Codex GPT 5.6 sol with xhigh reasoning.
