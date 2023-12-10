import Mathlib.Tactic
import Mathlib.Algebra.NeZero
import Mathlib.Logic.IsEmpty
import Axler.Chapter1.MyComplex
import Axler.Chapter1.Complex
import Axler.Chapter1.Rn

/-!

# Chapter 1

-/

/-
## Section 1A: Complex and `R^n`

### Complex (1.1 and 1.2)

`Complex` is built into Mathlib, but it's instructive to build a version of complex numbers
and prove the basic laws in Lean4. We do this in `Axler.Chapter1.MyComplex` (with a little more work,
we could prove that the `Complex` numbers form a field -- this is the (https://github.com/ImperialCollegeLondon/complex-number-game)[Complex Number Game]
which with a little work is instructive to port to Lean4)

In `Axler.Chapter1.Complex` we prove the same laws using the built-in implementations.

### `R^n` and `F^n`

`R^n` in Lean4 is `Fin n → R`. This might be confusing if you think about a vector in, say,
`R^3` as a vector `[x, y z]`, but if we think of that vector instead as a specific vector that
maps `0, 1, 2` to `x`, `y`, `z`, then `Fin 3 → ℝ` is the set of all such mappings.

We can get a specific vector via the built-in notaton `![]`. For example, if we previously have
defined `x`, `y`, and `z` as reals, `![x, y z]` gives us a function of the type `Fin 3 → ℝ`
-/
variable (x y z: ℝ)
#check ![x, y, z]
/-

In Mathlib, the laws for vector addition are encapsulated in `AddCommMonoid`, and we get a built-in
lawful implementation of vector addition in Mathlib via definitions in the `Pi` namespace (`Pi` here
refers to Π-types, or the types of dependent functions, of which `Fin 3 → ℝ` is an instance). Again,
it can be instructive to build an implementation of these definitions and prove that they implement the
laws for `AddCommMonoid`, which is done in `Axler.Chapter1.Rn`. Again, though, we get the automagic
version for free:
-/
#synth (n: ℕ) → AddCommMonoid (Fin n → ℝ)

/-
We can extend these defintions and proofs to all fields via a bit more work in `Axler.Chapter1.Fn`. Again, we
need not do this manually, because this is built-in via Mathlib:
-/
variable {F: Type _}
variable [Field F]
#synth (n: ℕ) -> AddCommMonoid (Fin n → F)

/-
## Exercises 1A

Exercises 1-6, 11, 13, and 14 are proved in `Axler.Chapter1.Fn`
-/

/- Exercise 9-/
-- example : ∃x, ![(4 : ℝ) , -3, 1, 7] + (2 * x) = ![5, 9, -6, 8] := by
--   use ![1/2, 6, -7/2, 1/2]
--   sorry

/- Exercise 12-/
example {n: ℕ} {a: Fin n → F } {x y: F}: x • (y • a) = (x * y) • a := by rw [smul_smul]
/- Exercise 15-/
example {n: ℕ} {a: Fin n →F} {x y : F}: (x + y) • a = x • a + y • a := by rw [add_smul]

/-
## Section 1B: Vector Spaces
-/

/-

### 1.22: `F^n` is a vector space over `𝔽`

In Mathlib, vector spaces are `Module`s over `Field`s (algebraically, modules are generalizations of
vector spaces to rings); so what we want is to show that the `Module` laws can be proven for a
suitable implementation of `F^n`

We prove this in `Axler.Chapter1.Fn` and this is built in to Mathlib:
-/

#synth (n: ℕ) → Module F (Fin n → F)

/-

### 1.23: `F^∞` is a vector space over `F`

Here our vectors are functions that map each value of `ℕ` to a real, or `f: ℕ → ℝ` and therefore we
can prove the desired property with a one liner (of course, we could also trivially modify `Axler.Chapter1.Fn`
so that our `term` is defined as  `ℕ → ℝ` and all the proofs would be identical)
-/

#synth Module F (ℕ → F)

/-
### 1.25: `F^𝑆` is a vector space

In Mathlib, we are already ahead here, because we've thought about vectors as functions.

Again, this is built-in to the `Pi` representation, and we could easily modify `Axler.Chapter1.Fn` in terms
of general types, rather than the specific type `Fin n`

In Lean4 and Mathlib, types are more general than `Set`, so we can prove this over an arbitrary type or
a Mathlib `Set` proper.
-/

variable {α : Type _}
#synth Module F (α → F)
#synth Module F (Set α → F)

/-
### 1.26 uniqueness of the additive identity

From now on we are generally going to be dealing with arbitrary vectors that conform to the
`AddCommGroup` axioms that form a vector space over field `F`: `Module F V`
-/

variable [Field F] [AddCommGroup V] [Module F V]

example {a b: V}: a + b = a ↔ b = 0 := add_right_eq_self

/-
### 1.27: uniqueness of the additive inverse
-/

example {a b c: V}: a + b = 0 → a + c = 0 → b = c := fun h1 => fun h2 => neg_unique h1 h2

/-
### 1.30: the number 0 times a vector

This is `zero_smul` in the `Module` laws
-/

/-
### 1:31: a number times the vector 0

-/

example {a: V} {x: F}: a = 0 → x • a = 0 := fun h => smul_eq_zero_of_right x h

/-
### 1.32: the number −1 times a vector
-/

example {a: V}: (-1: F) • a = -a := neg_one_smul F a

/-
## Exercises 1B
-/

/-
### Exercise 1
-/

example {a: V}: -(-a) = a := neg_neg a

/-
### Exercise 2
Suppose 𝑎 ∈ 𝐅,𝑣 ∈ 𝑉,and 𝑎𝑣 = 0.Prove that 𝑎 = 0 or 𝑣 = 0
-/

example {v: V} {a: F}: a • v = 0 ↔ a = 0 ∨ v = 0 := smul_eq_zero

/-
### Exercise 3

Suppose 𝑣, 𝑤 ∈ 𝑉. Explain why there exists a unique 𝑥 ∈ 𝑉 such that 𝑣 + 3𝑥 = 𝑤.
-/
variable [CharZero F] -- make sense of 3, etc.

example {v w: V}: ∃x, v + (3: F )•x = w := by
  use ((3⁻¹: F) • (w - v))
  rw [smul_smul, mul_inv_cancel, one_smul, add_comm, sub_add_cancel]
  exact three_ne_zero

-- a more general proof
example {v w: V} {a: F}: a ≠ 0 → ∃x, v + a•x = w := fun h =>
  ⟨a⁻¹ • (w - v), by
    rw [smul_smul, mul_inv_cancel, one_smul, add_comm, sub_add_cancel]; assumption⟩

/-
### Exercise 4

The empty set is not a vector space. The empty set fails to satisfy only one of the requirements
listed in the definition of a vector space (1.20). Which one?

In Mathlib, it's easier to do this backwards and prove that an arbitrary vector space is not empty.

This is witnessed through the `zero` element of the vector space via `Zero.nonempty`
-/

example: ¬IsEmpty V := not_isEmpty_of_nonempty V


/-
### Exercise 5

Show that in the definition of a vector space (1.20), the additive inverse condition can be replaced with the condition that
0𝑣 = 0 for all 𝑣 ∈ 𝑉.
Here the 0 on the left side is the number 0, and the 0 on the right side is the
additive identity of 𝑉.
-/

example: ∀(v: V), (0: F)•v = 0 → ∃w, v + w = 0 := fun v h => by
  use ((-1: F) • v)
  rw [←one_smul F v, smul_comm, one_smul F ((-1: F) • v), ←add_smul, add_right_neg, h]
