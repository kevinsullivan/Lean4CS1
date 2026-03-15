-- FPCourse/Unit1/Week01_ExpressionsTypes.lean

/- @@@
# Unit 1 — Computation as Mathematical Evaluation

## Week 1: Expressions, Types, and Values

### Overview

This week establishes the three foundational ideas of the entire course:

- An **expression** is a syntactic object — something you write down.
- A **value** is what an expression *evaluates to* — the result of computation.
- A **type** classifies expressions, and is determined *before* evaluation begins.

These are not merely technical distinctions.  They reflect a deep claim about
what programs are: not a sequence of instructions to a machine, but
*mathematical objects* that can be reasoned about with the same rigour we apply
to polynomials, sets, or logical formulas.

Lean 4 makes this claim concrete.  Every expression you write is checked for
type-correctness *before* it is run.  A program that fails to type-check is
not just incorrect — it is *ill-formed*, in the same sense that
`2 + "hello"` is ill-formed in arithmetic.
@@@ -/

namespace Week01

/- @@@
### 1.1  The REPL as a scientific instrument

`#check` reports the *type* of an expression without evaluating it.
`#eval`  evaluates an expression and prints the result.

Think of `#check` as asking "what kind of thing is this?" and `#eval` as
asking "what is its value?"  Separating these two questions is the first
discipline of typed functional programming.
@@@ -/

#check 42          -- Nat
#check (42 : Int)  -- Int  (type annotation overrides inference)
#check true        -- Bool
#check 'A'         -- Char
#check "hello"     -- String
#check (1, true)   -- Nat × Bool  (a product type)
#check ()          -- Unit        (the unique value of the unit type)

#eval 2 + 3        -- 5
#eval String.length "lean"   -- 4
#eval (10 : Int) - 15        -- -5

/- @@@
### 1.2  Types as constraints

The type of an expression constrains which values it can evaluate to.
`Nat` contains `0, 1, 2, …` but not `-1`.
`Bool` contains only `true` and `false`.
`Nat × Bool` contains pairs whose first component is a natural number
and whose second is a boolean.

This constraint is enforced *statically*: the compiler rejects an expression
whose type is inconsistent before any evaluation takes place.
The following would be a compile error (uncomment to see):

```
-- #check (1 : Nat) + true   -- ERROR: type mismatch
```

**Type annotation syntax**: writing `(e : T)` asserts that expression `e`
should have type `T`.  The compiler verifies this claim.
@@@ -/

-- Explicit annotations — each of these is a checked claim
example : Nat  := 7
example : Int  := -3
example : Bool := (1 < 2)
example : Nat × Bool := (5, false)
example : Unit := ()

/- @@@
### 1.3  Base types

| Type   | Inhabitants                          | Notes                        |
|--------|--------------------------------------|------------------------------|
| `Nat`  | 0, 1, 2, …                          | Non-negative integers        |
| `Int`  | …, -2, -1, 0, 1, 2, …               | All integers                 |
| `Bool` | `true`, `false`                      | Booleans                     |
| `Char` | Unicode code points                  | Written `'A'`, `'λ'`, etc.  |
| `String` | Sequences of characters            | Written `"…"`                |
| `Unit` | `()` (exactly one value)             | The "trivial" type           |

`Unit` might seem useless, but it is important: it corresponds to *truth*
in the logical reading of types we will reach in Week 14.
@@@ -/

/- @@@
### 1.4  Product types

The type `A × B` (read "A times B") is the type of ordered pairs
whose first component has type `A` and whose second has type `B`.

The *introduction rule* for products is the pair constructor `(a, b)`.
The *elimination rules* are the projections `Prod.fst` and `Prod.snd`
(or the dot notation `.1` and `.2`).
@@@ -/

def myPair : Nat × Bool := (3, true)

#eval myPair.1    -- 3
#eval myPair.2    -- true

-- Nested products
example : Nat × Bool × String := (1, false, "hi")

/- @@@
### 1.5  Type derivations as proofs

To know the type of a compound expression, we derive it from the types
of its sub-expressions using *typing rules*.  This derivation is itself
a mathematical proof.

**Example**: what is the type of `(1 + 2, not true)`?

1. `1 : Nat` and `2 : Nat`, so by the rule for `+`: `1 + 2 : Nat`.
2. `true : Bool`, so by the rule for `not`: `not true : Bool`.
3. By the rule for pairs: `(1 + 2, not true) : Nat × Bool`.

We can state this as a checked fact in Lean:
@@@ -/

-- The type of the pair is exactly what the derivation says
example : (1 + 2, !true) = (3, false) := rfl

-- rfl (reflexivity) proves that two expressions evaluate to the same value.
-- It only works when both sides reduce to definitionally equal terms.

/- @@@
### 1.6  Progress and Preservation (stated informally)

Two meta-theorems underpin the whole type system:

- **Progress**: every well-typed expression that is not yet a value can take
  an evaluation step.  A well-typed program is never "stuck".
- **Preservation**: every evaluation step preserves the type of the expression.
  If `e : T` and `e` steps to `e'`, then `e' : T`.

Together these say: a well-typed program evaluates safely to a value of
the declared type.  We will see formal proofs of these properties in Week 14.
@@@ -/

/- @@@
### Exercises

1. Use `#check` to find the type of each expression below.
   Predict the type *before* running `#check`.

   ```
   2 ^ 10
   (3 : Int) * (-2 : Int)
   (true && false) || true
   ("hello", 42, ())
   ```

2. Write a type annotation for each of the following values:
   - The number `100` viewed as an `Int`
   - The pair of the string `"lean"` and the boolean `true`
   - The triple `(0, 0, 0)` of natural numbers

3. Explain in one sentence why `#check (1 : Nat) - 2` reports type `Nat`
   even though the mathematical result would be negative.
   (Hint: `Nat` subtraction is *saturating* — it returns `0` when the
   mathematical result would be negative.)
@@@ -/

-- Exercise stubs (replace `sorry` with your answer)
example : (100 : Int) = 100 := by norm_num
example : ("lean", true) = ("lean", true) := rfl
example : ((0 : Nat), (0 : Nat), (0 : Nat)) = (0, 0, 0) := rfl

end Week01
