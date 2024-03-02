import Mathlib.Tactic
import Mathlib.Algebra.NeZero
import Mathlib.Logic.IsEmpty
import Mathlib.Data.Real.EReal
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Algebra.Module.Equiv
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Data.Fin.VecNotation
import Axler.Chapter1.MyComplex
import Axler.Chapter1.Complex
import Axler.Chapter1.Rn
import Axler.Chapter1.Vc

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

In Mathlib, the laws for vector addition are encapsulated in `AddCommGroup`, and we get a built-in
lawful implementation of vector addition in Mathlib via definitions in the `Pi` namespace (`Pi` here
refers to Π-types, or the types of dependent functions, of which `Fin 3 → ℝ` is an instance). Again,
it can be instructive to build an implementation of these definitions and prove that they implement the
laws for `AddCommGroup`, which is done in `Axler.Chapter1.Rn`. Again, though, we get the automagic
version for free:
-/
#synth (n: ℕ) → AddCommGroup (Fin n → ℝ)

/-
We can extend these defintions and proofs to all fields via a bit more work in `Axler.Chapter1.Fn`. Again, we
need not do this manually, because this is built-in via Mathlib:
-/
variable {F: Type _}
variable [Field F]
#synth (n: ℕ) -> AddCommGroup (Fin n → F)

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

variable {α : Type*}
#synth Module F (α → F)
#synth Module F (Set α → F)

/-
From now on we are generally going to be dealing with arbitrary vectors that conform to the
`AddCommGroup` axioms that form a vector space over field `F`: `Module F V` so we set up our
variables accordingly.
-/

variable [Field F] [AddCommGroup V] [Module F V]

/-
### 1.26 uniqueness of the additive identity
-/


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

Here we want to show that `v - v = 1•v + -1• v = (1 + -1) • v = 0 • v` so we can use our updated axiom
-/

example: ∀(v: V), (0: F)•v = 0 → ∃w, v + w = 0 := fun v h => by
  use ((-1: F) • v)
  rw [←one_smul F v, smul_comm, one_smul F ((-1: F) • v), ←add_smul, add_right_neg]; assumption

/-
### Exercise 6

Let ∞ and −∞ denote two distinct objects, neither of which is in 𝐑.
Define an addition and scalar multiplication on 𝐑 ∪ {∞, −∞} as you could guess from the notation. Specifically, the sum and product of two real numbers is as usual, and for 𝑡 ∈ 𝐑 define
𝑡*∞ =
* t < 0: −∞
* t = 0: 0
* t > 0: ∞

𝑡*-∞ =
* t < 0: ∞
* t = 0: 0
* t > 0: -∞

𝑡 + ∞ = ∞ + 𝑡 = ∞ + ∞ = ∞,
𝑡+(−∞) = (−∞)+𝑡 = (−∞)+(−∞) = −∞,
∞+(−∞) = (−∞)+∞ = 0.

With these operations of addition and scalar multiplication, is 𝐑 ∪ {∞, −∞}
a vector space over 𝐑? Explain.

First, we note that the defition proposed is exactly that of the `Mathlib.Data.Real.EReal`
implementation of extended reals.

We also note there's no automagic here:
--#synth Module EReal EReal
-- Errors "failed to synthesize instance Semiring EReal"

The issue is that multiplcation does not commute, so we can't get a defintion
of multiplcation by either `ℝ` or `EReal` that follows the laws.

We want to get a proof that commutation is violated: `¬∀ (x y z: EReal), x * z + y * z = (x + y) * z`
-/


-- `1*⊥ + -1*⊥ = ⊥`
lemma EReal.one_mul_add:  1*⊥ + (-1: EReal )*⊥ = (⊥: EReal) := by
  have h: (⊥: EReal) = ⊥ + ⊤ := rfl
  have h2: (⊥: EReal) + ⊤ = (1: EReal) *⊥ + (-1: EReal)*⊥ := by
    have h3 : (⊥ : EReal) = 1*⊥ := Linarith.without_one_mul rfl
    have h4: (⊤: EReal) = -⊥ := rfl
    have h5: (-⊥ : EReal) = -1 * ⊥ := neg_eq_neg_one_mul ⊥
    rw [h3, h4, h5]
    simp
  rw [h, h2]
  simp

-- but `(1 + -1)*⊥ = 0`
lemma EReal.one_add_mul: ((1: EReal) + (-1: EReal))*⊥ = 0 := by
  have h: (1: EReal) + -1 = 1 - 1 := rfl
  have h2: (1: EReal) - 1 = 0 := by rw [←EReal.coe_one, ←EReal.coe_sub, sub_self, EReal.coe_zero]
  rw [h, h2, zero_mul]

lemma EReal.one_mul_add_ne_one_add_mul: 1*⊥ + (-1: EReal )*⊥ ≠ ((1: EReal) + -1)*⊥ :=  by
  rw [EReal.one_mul_add, EReal.one_add_mul]
  exact bot_ne_zero

theorem not_all_add_mul: ¬∀ (x y z: EReal), x * z + y * z = (x + y) * z := fun h =>
  let h2  :=  EReal.one_mul_add_ne_one_add_mul
  h2 (h 1 (-1: EReal) ⊥)

/-
### Exercise 7

Suppose `𝑆` is a nonempty set. Let `𝑉_𝑆` denote the set of functions from `𝑆` to `𝑉`.
Define a natural addition and scalar multiplication on `𝑉_𝑆`, and show that `𝑉_𝑆` is a vector space with these definitions.

We can perform the addition pointwise, since the underlying vectors add properly, and use the field
over which the vector space is defined for scalar multiplication, and again this is automagic in Mathlib.
-/

#synth Module F (α → V) -- note again that types are more general than `Set` in Lean and `Mathlib`


/-
### Exercise 8

Suppose 𝑉 is a real vector space.
* The complexification of `𝑉`, denoted by `𝑉^𝐂` , equals `𝑉 × 𝑉`. An element of
`𝑉^𝐂` is an ordered pair `(𝑢,𝑣)`,where `𝑢,𝑣 ∈ 𝑉`,but we write this as `𝑢 + 𝑖𝑣`
* Addition on `𝑉^𝐂` is defined by
```∀ 𝑢_1,𝑣_1,𝑢_2,𝑣_2 ∈ 𝑉, (𝑢_1 +𝑖𝑣_1) + (𝑢_2 +𝑖𝑣_2) = (𝑢_1 +𝑢_2) + 𝑖(𝑣_1 +𝑣_2) ```.
* Complex scalar multiplication on `𝑉^𝐂` is defined by `(𝑎 + 𝑏𝑖)(𝑢 + 𝑖𝑣) = (𝑎𝑢 − 𝑏𝑣) + 𝑖(𝑎𝑣 + 𝑏𝑢)`
for all `𝑎, 𝑏 ∈ 𝐑` and all `𝑢, 𝑣 ∈ 𝑉`.

Prove that with the definitions of addition and scalar multiplication as above,
`𝑉^𝐂` is a complex vector space.
Think of 𝑉 as a subset of `𝑉^𝐂` by identifying `𝑢 ∈ 𝑉` with `𝑢 + 𝑖0`. The construction of `𝑉^𝐂` from `𝑉`
can then be thought of as generalizing the construction of `ℂ^𝑛` from `ℝ^𝑛`.

We do this two different ways. The first, in keeping with the level of proof tools we have in LADR right now,
takes the construction of `V^C` literally, and shows that as defined, `V^C` is a vector space with scalar multiplication
by `ℂ`.

This basic appraoch is in `Axler.Chapter1.Vc`

The second approach uses more of the power of `Mathlib` but requires more mathmatics than is currently presented in LADR.
(It uses linear maps, which are the subject of Chapter 3, and tensor products, which are in 9A)

Here, we treat the complexification of a real vector space as the tensor product of the vector space with `ℂ`. Again,
proof this is a complex vector space is built in to `Mathlib`.

We'd then like to show that we aren't cheating by showing that the tensor product is, indeed, equivalent
to the product of our vector space. To show equivalence of two types in `Mathlib` in general we need to make an
`Equiv` that provides functions that map each way (to and from), then show that the maps are inverses of one another.
Here we prove a stronger equivalence,`LinearEquiv`, which adds an additional constraint that addition and
scalar multiplication are preserved across the equivalence.
-/

variable (V) [AddCommGroup V] [Module ℝ V]

open scoped TensorProduct

#synth Module ℂ (ℂ ⊗[ℝ] V)

/--
Trivial linear map betwen `V × V` and `ℂ ⊗[ℝ] V` that treats the first part as real and the second as imaginary
-/
noncomputable def toFun: V × V →ₗ[ℝ] ℂ ⊗[ℝ] V where
  toFun p := match p with
  |  ⟨fst, snd⟩ => ((1: ℂ) ⊗ₜ[ℝ] fst) + Complex.I ⊗ₜ[ℝ] snd
  map_add' p1 p2 := by dsimp; simp [TensorProduct.tmul_add]; abel_nf
  map_smul' r p := by dsimp; simp [TensorProduct.tmul_smul]

/--
Trivial inverted map, that contructs a `Prod` by scaling a vector by the real and imaginary parts of a complex number
-/
noncomputable def invFun: ℂ ⊗[ℝ] V →ₗ[ℝ] V × V :=
  TensorProduct.lift <| LinearMap.mk₂
  ℝ (fun z v ↦ (z.re • v, z.im • v))
    (by intros; ext <;> dsimp <;> rw [add_smul])
    (by intros; ext <;> dsimp <;> simp [mul_smul])
    (by intros; ext <;> dsimp <;> simp [smul_add])
    (by intros; ext <;> dsimp <;> rw [smul_comm])

theorem toFun_invFun_comp_eq_id: LinearMap.comp (@toFun V _ _) (@invFun V _ _) = LinearMap.id := by
  simp only [toFun, invFun]; ext z v; dsimp; simp [TensorProduct.tmul_add, TensorProduct.smul_tmul]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', ←TensorProduct.add_tmul (z.re • 1) (z.im • Complex.I) v]
  simp only [Complex.real_smul, mul_one, Complex.re_add_im]

theorem invFun_toFun_comp_eq_id: LinearMap.comp (@invFun V _ _) (@toFun V _ _) = LinearMap.id := by
  simp only [toFun, invFun]; apply LinearMap.ext; intro p; simp

/--
Our proof of equivalence
-/
noncomputable def prod_rLinearEquiv_ComplexTensor: (V × V) ≃ₗ[ℝ] (ℂ ⊗[ℝ] V) :=
  LinearEquiv.ofLinear (@toFun V _ _) (@invFun V _ _) (@toFun_invFun_comp_eq_id V _ _) (@invFun_toFun_comp_eq_id V _ _)

/-
## 1C: Subspaces


We have `variable (V) [AddCommGroup V] [Module 𝔽 V]` as the `Mathlib` declaration for a vector space over `𝔽`

A subspace is a restiction of `V` such that the subspace laws are preserved, which in `Mathlib` is expressed a `Set` over `V`
plus the three laws, wrapped up in a `Submodule` definition -/

/-
### 1.35 example (1):
If `𝑏 ∈ 𝔽`, then `{(𝑥_1,𝑥_2,𝑥_3,𝑥_4) ∈ 𝔽^4 ∶ 𝑥_3 = 5*𝑥_4 + 𝑏}` is a subspace of 𝐅^4 if and only if `𝑏 = 0`

We first show that `0 ∈ {(𝑥_1,𝑥_2,𝑥_3,𝑥_4) ∈ 𝔽^4 ∶ 𝑥_3 = 5*𝑥_4 + 𝑏}` if and only if `b = 0`, then, setting
`b = 0`, that the resulting `Set` is a `Submodule`
-/

theorem ex_1_iff_eq_zero : (b: F) → 0 ∈ {f: Fin 4 → F | 5*(f 2) = (f 4) + b} ↔ b = 0 := by
  intro b; simp only [Set.mem_setOf_eq, Pi.zero_apply, mul_zero, zero_add]
  constructor <;> intro h <;> exact h.symm

def ex1_Subspoace: Submodule F (Fin 4 → F) where
  carrier := {f: Fin 4 → F | 5*(f 2) = (f 4)}
  zero_mem' := by simp only [Set.mem_setOf_eq, Pi.zero_apply, mul_zero]
  add_mem' := by simp only [Set.mem_setOf_eq, Pi.add_apply]; intro a b h1 h2; rw [mul_add, h1, h2]
  smul_mem' := by
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
    intro c f h1
    have h2: 5 * (c * f 2) = c * (5 * f 2) := by ring_nf
    rw [h2, h1]

/-
### 1.35 example (2)

The set of continuous real-valued functions on the interval `[0,1]` is a subspace
of `𝐑^{[0,1]}`

This example, and the next two, require additional constructs from `Mathlib`

(mostly taken from https://github.com/martincmartin/linear_algebra_done_right/)
-/

def ex2_Subspace: Submodule ℝ ( Set.Icc (0 : ℝ) (1 : ℝ) → ℝ) where
  carrier := {f | Continuous f}
  zero_mem' := by simp only [Set.mem_setOf_eq]; exact continuous_zero
  add_mem' := by simp only [Set.mem_setOf_eq]; intro a b h1 h2; exact h1.add h2
  smul_mem' := by simp only [Set.mem_setOf_eq]; intro a f h; exact continuous_const.mul h

/-
### 1.35 example (3)

The set of differentiable real-valued functions on `ℝ` is a subspace of `ℝ^ℝ`
(mostly taken from https://github.com/martincmartin/linear_algebra_done_right/)
-/

def ex3_Subspace: Submodule ℝ (ℝ → ℝ ) where
  carrier := {f | Differentiable ℝ f}
  zero_mem' := differentiable_const _
  add_mem' :=  Differentiable.add
  smul_mem' c _ := (differentiable_const c).smul

/-
### 1.35 example (4)

The set of differentiable real-valued functions `𝑓` on the interval `(0, 3)` such that `𝑓′(2) = 𝑏` is a
subspaceof `ℝ^{(0,3)}` if and only if `𝑏 = 0`.

Just like ex 1 above, the issue here is with the existence of `0` -- our `0` function is the constant
function that sends all values to `0`, which implies that `f'(x) = 0` for all `x`.

(portions borrowed from https://github.com/martincmartin/linear_algebra_done_right/)

-/

theorem ex4_iff_eq_zero : (b: ℝ) → 0 ∈ {f | (∀ x ∈ Set.Ioo (0 : ℝ)  (3: ℝ), DifferentiableAt ℝ f x) ∧ (HasDerivAt f (b: ℝ)  (2: ℝ))} ↔ b = 0 := by
  intro b
  constructor <;> intro h
  . have h2:= hasDerivAt_const (2:ℝ) (0: ℝ)
    rw [←@Pi.zero_def] at h2
    exact HasDerivAt.unique h.right h2
  . constructor
    . intro _ _
      exact differentiableAt_const 0
    . rw [h]
      apply hasDerivAtFilter_const

def ex4_Subspace: Submodule ℝ (ℝ → ℝ) where
  carrier := { f | (∀ x ∈ Set.Ioo (0 : ℝ)  (3: ℝ), DifferentiableAt ℝ f x) ∧ (HasDerivAt f 0 2)}
  zero_mem' := by
    constructor
    . intro _ _
      exact differentiableAt_const 0
    . apply hasDerivAtFilter_const
  add_mem' := by
    intro a b h1 h2
    constructor
    . intro x h
      rcases (h1.left x h) with ⟨ f'x, f_has ⟩
      rcases (h2.left x h) with ⟨ g'x, g_has ⟩
      use f'x + g'x
      exact f_has.add g_has
    . have h3:= h1.right.add h2.right
      simp [@Pi.add_def] at *
      assumption
  smul_mem' := by
    intro a f hf
    cases' hf with hf1 hf2
    constructor
    . intro b h
      have h2 := (hf1 b h).smul_const a
      simp [@Pi.smul_def] at *
      simp_rw [mul_comm a (f _)]
      exact h2
    . have h := hf2.smul_const a
      simp [@Pi.smul_def] at *
      simp_rw [mul_comm a (f _)]
      exact h

/-
### 1.35 Example 5

The set of all sequences of complex numbers with limit `0` is a subspace of `ℂ^{∞}`

(mostly taken from https://github.com/martincmartin/linear_algebra_done_right/)

-/

open Filter Topology

def ex5_Subspace : Subspace ℂ (ℕ → ℂ) where
  carrier := {u | Tendsto u Filter.atTop (𝓝 0)}
  add_mem' := by
    simp
    intro u v hu hv
    have h := hu.add hv
    simp [Pi.add_def] at *
    assumption
  zero_mem' := tendsto_const_nhds
  smul_mem' := by
    simp
    intro c u hu
    have := hu.const_mul c
    simp [Pi.add_def] at *
    assumption

/-
### Sums of Subspaces
-/

/-
#### Example 1.37

Suppose `𝑈` is the set of all elements of `𝔽^3` whose second and third coordinates equal 0, and `𝑊` is the set of all elements of `𝐅^3` whose first and third coordinates equal 0:
`𝑈={(𝑥,0,0) ∈ 𝐅^3 ∶𝑥 ∈ 𝐅}` and `𝑊={(0,𝑦,0) ∈ 𝐅^3 ∶𝑦 ∈ 𝐅}`.
Then as you should verify.

`𝑈+𝑊={(𝑥,𝑦,0) ∈ 𝐅^3 ∶𝑥,𝑦 ∈ 𝐅}`

We first prove that `U` and `W` are subspaces, then that `U + W` have the form provided, then that `U + W` are subspaces.

-/
open Pointwise

def subspace_ex1_37_U: Submodule ℝ (Fin 3 → ℝ) where
  carrier :=  { ![x₁, 0, 0] | (x₁: ℝ)}
  zero_mem' := by simp
  add_mem' := by aesop
  smul_mem' := by simp

def subspace_ex1_37_V: Submodule ℝ (Fin 3 → ℝ) where
  carrier := { ![0, x₂, 0] |  (x₂ : ℝ)}
  zero_mem' := by simp
  smul_mem' := by simp
  add_mem' := by aesop

theorem ex1_37: { ![x₁, 0, 0] | (x₁: ℝ)} + { ![0, x₂, 0] |  (x₂ : ℝ)} = { ![x₁, x₂, 0] | (x₁: ℝ) (x₂: ℝ)} := by
  ext x ; simp [Set.mem_add]

def subspace_ex1_37_VU: Submodule ℝ (Fin 3 → ℝ) where
  carrier :=  { ![x₁, x₂, 0] | (x₁: ℝ) (x₂: ℝ)}
  zero_mem' := by simp
  smul_mem' := by aesop
  add_mem' := by aesop


#check (subspace_ex1_37_U + subspace_ex1_37_V)

/-
#### Example 1.38

`𝑈 = {(𝑥,𝑥,𝑦,𝑦) ∈ 𝐅^4 ∶𝑥,𝑦 ∈ 𝐅}` and `𝑊={(𝑥,𝑥,𝑥,𝑦) ∈ 𝐅^4 ∶𝑥,𝑦 ∈ 𝐅}`

prove

`𝑈 + 𝑊 = {(𝑥,𝑥,𝑦,𝑧) ∈ 𝐅^4 ∶𝑥,𝑦,𝑧 ∈ 𝐅}`
-/

def subspace_ex1_38_U: Submodule F (Fin 4 → F) where
  carrier :=  { ![x, x, y, y] | (x: F) (y: F)}
  zero_mem' := by simp
  smul_mem' := by aesop
  add_mem' := by aesop

def subspace_ex1_38_W: Submodule F (Fin 4 → F) where
  carrier :=  { ![x, x, x, y] | (x: F) (y: F)}
  zero_mem' := by simp
  smul_mem' := by aesop
  add_mem' := by aesop

theorem ex1_38: { ![x, x, y, y] | (x: F) (y: F)} + { ![x, x, x, y] | (x: F) (y: F)} = { ![x, x, y, z] | (x: F) (y: F) (z: F)} := by
  ext x ; simp [Set.mem_add]; constructor
  . intro h
    rcases h with ⟨a, b, c, d, h⟩
    use (a + c), (b + c), (b + d)
  . intro h
    rcases h with ⟨a, b, c, h⟩
    use a, b, 0, (c - b)
    simp_all

/-

Axler, Linear Algebra Done Right, Example 1.40:

"Suppose `𝑉_1, ..., 𝑉_𝑚` are subspaces of `𝑉`. Then `𝑉_1 + ⋯ + 𝑉_𝑚` is the smallest subspace of `𝑉`
containing `𝑉_1, ..., 𝑉_𝑚`."

We know `V_1 + ... + V_m` is a subspace because the `Submodule.pointwiseAddCommMonoid` instance
proves additive closure.

If we can prove the claim of "smallest" for pairs of subspaces `U` and `V` we can prove for arbitrary
additve chains.

There's a subtlty here -- Mathlib's version of `+` for `Submodule` is actually `⊔` (`Sup`) under the hood, and
and the actual proof relies on very general proof machinery about lattices (through `Submodule`'s inheritence
from `AddSubmonoid` which has a `CompleteLattice` implementation).

In practice, it would be rare to use `Pointwise` and the below theorem would be written
`{V₁ V₂ W : Submodule F V} : (∀ x : V, x ∈ V₁ ∨ x ∈ V₂ → x ∈ W) → V₁ ⊔ V₁ ≤ W`

credit to Patrick Massot for the proof
-/
open Pointwise

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
theorem ex_1_40 {V₁ V₂ W : Submodule F V} : (∀ x : V, x ∈ V₁ ∨ x ∈ V₂ → x ∈ W) → V₁ + V₁ ≤ W := by
  intro h
  simp only [Submodule.add_eq_sup]
  apply sup_le; intro _ _; aesop
