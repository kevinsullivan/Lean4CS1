# A First Course in Typed Functional Programming — Lean 4 Edition

This repository contains a complete 14-week first-semester undergraduate curriculum
in typed functional programming, realised in **literate Lean 4 (v4.28.0)**.

## Philosophy

Three ideas organise every file:
1. A **program** is a mathematical object — an expression with a type and a value.
2. A **specification** is logically prior to its implementation.
3. **Proofs and programs** are the same artifact viewed from two directions
   (the Curry–Howard correspondence, encountered gradually, stated plainly in Week 14).

## Literate convention

All prose commentary is delimited by `/- @@@ ... @@@ -/`.
The rendering pipeline converts these blocks to HTML or LaTeX;
everything outside them is typeset as Lean 4 source.

## Structure

```
FPCourse/
  Unit1/   Weeks 1–3   Computation as mathematical evaluation
  Unit2/   Weeks 4–7   Inductive datatypes and structural reasoning
  Unit3/   Weeks 8–9   Higher-order functions and equational proofs
  Unit4/   Week 10     Cost semantics: work and span
  Unit5/   Weeks 11–12 Abstract types and module specifications
  Unit6/   Weeks 13–14 Lazy evaluation, streams, and synthesis
```

## Building

```
lake build
```

All files type-check with `leanprover/lean4:v4.28.0`.
Student exercises are marked `sorry`; replacing each `sorry` with a correct
proof or definition is the primary homework activity.
