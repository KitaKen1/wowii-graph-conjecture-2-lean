# Lean4Web version

`GraphConjecture2Lean4Web.lean` is the single-file version of the proof.

Compatibility target:

```text
Lean4Web project: Latest Mathlib
Lean version:     v4.33.0-rc1
Date:             2026-07-26
```

This identifies the environment targeted by the file; it does not pin
Lean4Web itself. The site’s “Latest Mathlib” project changes over time.

## Run

1. Open <https://live.lean-lang.org/>.
2. Select **Load**.
3. Load `GraphConjecture2Lean4Web.lean`.
4. Wait for the complete file to elaborate.
5. Inspect the final `#check` and `#print axioms` messages.

The file also runs:

```lean
#eval Lean.versionString
```

to display the actual Lean version used by the current web session.

Expected axiom output:

```text
[propext, Classical.choice, Quot.sound]
```

There should be no `sorryAx`.

## Status

This proof is shared for review. Lean4Web’s “Latest Mathlib” environment
changes over time, so successful local checking of the pinned project in
`../lean/` is the reproducible reference result.
