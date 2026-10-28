--- E0.1

--- a: yes. Decidable predicate. Basic type, product
--- b: yes. decidable predicate. Basic type, sum
--- c: yes. decidable predicate. Basic type, a is uninhabited,
--- d: yes. decidable predicate. Basic type, product. a is uninhabited

#guard decide (2 < 3 ∧ 3 < 4) = true
#guard decide (2 < 3 ∨ 3 < 2) = true
#guard decide (¬ (2 = 3)) = true
#guard decide (¬ (2 < 3 ∧ 3 < 2)) = true

--- E0.2

/-! @@@
DERIVATION of twice : (α → α) → α → α
  goal: (α → α) → α → α
  step 1 [→I]  fun (f: α → α) => ? ⟶ goal: α → α, with f : α → α
  step 2 [→I]  fun (x : α) => ? ⟶ goal: α, with f : α → α, x: α
  step 3 [→E]  f (f x) : α          ⟶ closed
  ∎
@@@ -/

def twice : (α → α) → α → α :=
  fun f x => f (f x)

#guard twice (· * 2) 3 = 12
#guard twice (fun b => !b) false = false
#guard twice (· + 1) 0 = 2

--- it says that if you have a proof that P → P, and a proof of P, then it
--- implies P

--- E0.3
def mapOption : (α → β) → Option α → Option β :=
  fun f x => match x with
  | none => none
  | some n => some (f n)

--- It uses function and sum since option is basically a sum

--- E0.4
#eval (5 - 6) + 6 ≠ 5

--- Side condition: it holds when a ≥ b



--- E1.1

#check Nat.add 3 4
-- adds two natural numbers, yes curried since x -> x ->. 2
#check Nat.mul 3 4
-- multiplies two natural numbers, yes curried since x -> x ->. 2
#check String.append "hello" "Kevin"
-- appends two strings and not curried. 2

-- Every inhabitant can return one of the two types. It cannot compare or process the values passed in any way
-- because this is for all possible types, so any operation must be able to be applied to any type. Not
-- even equality works because you need the DecidableEQ condition.


--- E.1.2

def myStrNat : String × Nat := ("lean", 4)

def MyStrNatSpec : Prop := myStrNat.1 = "lean" ∧ myStrNat.2 > 0
#guard myStrNat.1 = "lean"
#guard myStrNat.2 = 4
#guard decide (myStrNat.1 = "lean" ∧ myStrNat.2 > 0) = true


-- E.1.3

-- a) decide can close it rfl. atomic, yes carries decision procedure.
-- b) decide can close it rfl. built from connectives, yes carries decision procedure.
-- c) decide can close it rfl. built from connectives, yes carries decision procedure.
-- d) no. float equality is undecidable on computers. No decidableEq instance. atomic. no decision procedure.
-- NaN is not equal to itself so it breaks propositional equality

#guard decide (17 * 23 = 391) = true
#guard decide (100 < 200 ∧ 200 < 300) = true
#guard decide (¬ (5 * 5 = 26)) = true
-- (d) has no check on purpose: say why `decide` cannot close Float equality.
--     (Hint: what would DecidableEq Float have to certify about NaN?  §1.2, revisited Week 7.)


-- E.1.4

#guard 3 - 5 + 5 ≠ 3
--- Side condition: it holds when a ≥ b


-- E.2.1
-- “pred' undoes successor: ∀ n, pred' (n + 1) = n, with pred' 0 = 0”
def pred' (n: Nat) : Nat := n - 1

#guard pred' 0 = 0
#guard pred' 1 = 0
#guard pred' 5 = 4
#guard decide (∀ n ∈ ([0, 1, 2, 3, 10] : List Nat), pred' (n + 1) = n) = true


-- E.2.2

-- It accidentally holds at n = 2. double 2 = 2 + 2 = 4


-- E.2.3

#check @And.intro

-- computationally (the constructor that builds a pair of proofs)
-- logically (a proof of P ∧ Q from a proof of P and a proof of Q)

theorem add_zero_comm (n : Nat) : n + 0 = n → n = n + 0 :=
  fun h => h.symm

-- symm closes it because the two sides of the equation are literally written the same
-- so it is definitely equal

#guard decide ((1 < 2) ∧ (2 < 3)) = true


-- E.2.4

-- a) decidable
-- b) decidable
-- c) decidable
-- d) decidable
#guard decide ((True ∧ False)) = false
-- e) infinite domain so it's technically undecidable. decidability needs
-- a finite domain




-- E.3.1

/-! @@@
DERIVATION of  sumTo : Nat → Nat
  goal: Nat → Nat
  step 1 [→I]   fun (k : Nat) => ?     ⟶ goal: Nat, with k : Nat
  step 2        base case / step case on k (0 or n+1), per §3.1
                  | 0     => ?
                  | n + 1 => ?          ⟶ goals: Nat (base), Nat (step, with n : Nat)
  step 3 [use 0]        0                    ⟶ closed (base case)
  step 4 [use sumTo n]  (n + 1) + sumTo n    ⟶ closed (step case)
  ∎
@@@ -/

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

#guard sumTo 0 = 0
#guard sumTo 1 = 1
#guard sumTo 3 = 6
#guard sumTo 10 = 55


-- E.3.2

def SumToClosedForm : Prop := ∀ n : Nat, sumTo n = n * (n + 1) / 2
#guard sumTo 5 = 5 * (5 + 1) / 2
#guard sumTo 10 = 10 * (10 + 1) / 2
#guard decide (∀ n ∈ List.range 20, sumTo n = n * (n + 1) / 2) = true


-- E.3.3

#guard sumTo 3 ≠ 3 * 3 / 2 -- sumTo 3 = 6. 3*3 = 9/2 = 4.5 ≠ 3
#guard sumTo 5 ≠ 5 * 5 / 2

-- you have to do n* (n+1) / 2. not n^2 / 2

-- E.3.4

-- a) structural, so rfl test can close it. bounded
-- b) well-founded. bounded
-- c) decidable. finite domain. bounded
-- d) undecidable since infinite domain.
