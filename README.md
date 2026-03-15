# FP Lean 4 Curriculum — Revised Edition

A 14-week literate Lean 4 curriculum for a first course in typed
functional programming.  Every file in this project compiles cleanly:
no `sorry`, no `by`.  All proofs are in term mode.

## Design commitments

**Students are expected to emerge fluent in computational and logical
types, but not in proof construction.**

- Propositions are types from Week 1.
- `decide` is a term-mode proof producer for decidable propositions.
- All provided proofs are term-mode: `by` never appears.
- `sorry` never appears.
- Full Mathlib notations are used throughout.
- The logic progression (Bool/Prop → propositional → predicate →
  set/relation) is distributed across all 14 weeks.
- The `Float`/`DecidableEq` lesson appears in Week 7 as a central topic.

## Course structure

| Unit | Weeks | Theme |
|------|-------|-------|
| 1 | 1–3 | Expressions, Functions, Recursion |
| 2 | 4–7 | Algebraic Datatypes, Lists, Trees, Decidability |
| 3 | 8–9 | Higher-Order Functions, Specifications |
| 4 | 10 | Sets and Relations |
| 5 | 11–12 | Abstract Types, Type Classes |
| 6 | 13–14 | Streams, Curry-Howard |

## Building

Requires Lean 4 and Lake.  Run `lake build` in this directory.
First build downloads Mathlib (several GB) and may take 30–60 minutes.

```bash
lake build
```

If you see only `Build completed successfully`, every proof in the
curriculum compiles.

## File naming convention

Each file is named `Week{NN}_{Title}.lean`.  Prose appears in
`/-! @@@ ... @@@ -/` blocks for rendering by the course's HTML pipeline.

## Assessment forms

Students are assessed on five competencies (no proof production required):

1. **Specification writing**: given a function and English description,
   write the correct Lean type expressing its specification.

2. **Specification reading**: given a Lean proposition, state in English
   what it asserts; give a satisfying and falsifying example.

3. **Type inhabitation**: write a term the compiler accepts at a given type.
   The compiler is the primary grader.

4. **Counterexample finding**: given a function and an incorrect
   specification, find a concrete input that witnesses the mismatch.

5. **Decidability identification**: given a proposition, state whether
   `decide` closes it, which other term if not, and why.

Exams are written by hand.

## What changed from v1

- **No `by` anywhere.** Every proof is a term.
- **No `sorry` anywhere.** Every theorem statement is backed by a
  complete term-mode proof.
- Week 10 replaces Cost Semantics with **Sets and Relations**, completing
  the stated logic progression.
- Logic track distributed across all weeks; Bool/Prop distinction
  appears in Week 1.
- Week 7 develops `DecidableEq` and the `Float`/IEEE 754 lesson as
  primary content.
- Week 3 renamed "Recursion and Termination" (not "Induction").
- Week 14 reframed as *recognition* of Curry-Howard, not introduction.
- Assessment section added to README.
