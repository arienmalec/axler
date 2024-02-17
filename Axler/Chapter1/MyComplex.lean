import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!

# MyComplex

Axler 1.3: prove the properties of complex arithmetic

First, do this de novo in lean by definng a datatype `MyComplex` and proving from
first principles (next we will show this via the built in `Complex` type):

## Commutativity
𝛼 + 𝛽 = 𝛽 + 𝛼 and 𝛼𝛽 = 𝛽𝛼 for all 𝛼, 𝛽 ∈ 𝐂
## Associativity
(𝛼 + 𝛽) + 𝜆 = 𝛼 + (𝛽 + 𝜆) and (𝛼𝛽)𝜆 = 𝛼(𝛽𝜆) for all 𝛼, 𝛽, 𝜆 ∈ 𝐂

## Identities
𝜆 + 0 = 𝜆 and 𝜆1 = 𝜆 for all 𝜆 ∈ 𝐂

## Existence of additive inverse
For every 𝛼 ∈ 𝐂, there exists a unique 𝛽 ∈ 𝐂 such that 𝛼 + 𝛽 = 0

## Existence of multiplicative inverse
For every 𝛼 ∈ 𝐂 with 𝛼 ≠ 0, there exists a unique 𝛽 ∈ 𝐂 such that 𝛼𝛽 = 1

## Distributive property
𝜆(𝛼 + 𝛽) = 𝜆𝛼 + 𝜆𝛽 for all 𝜆, 𝛼, 𝛽 ∈ 𝐂.

-/

/-- Representation of a complex number with `Real`-valued real and imaginary parts
-/
@[ext]
structure MyComplex where
  mk ::
    /-- The real part-/
    (re: Real)
    /-- The imaginary part-/
    (im: Real)

namespace MyComplex


section zero

instance hasZero: Zero MyComplex where
  zero := ⟨0,0⟩

/-- Real part of `0`-/
@[simp]
theorem zero_re : (0 : MyComplex).re = 0 := rfl

/-- Imaginary part of `0`-/
@[simp]
theorem zero_im : (0 : MyComplex).im = 0 := rfl

/-- The norm squared of a complex number is zero iff the complex number is zero -/
-- We need this later on for `mul_add`
theorem normSq_eq_zero_iff {x: MyComplex}: x = 0 ↔ (x.re^2 + x.im^2) = 0 := by
  constructor <;> intro h
  . simp only [MyComplex.ext_iff, zero_re, zero_im] at h
    rw [h.left, h.right]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  . have h2: x.re^2 ≥ 0 := sq_nonneg x.re
    have h3: x.im^2 ≥ 0 := sq_nonneg x.im
    have h4: x.re^2 = 0 ∧ x.im^2 = 0 := (add_eq_zero_iff' h2 h3).mp h
    have h5: x.re = 0 := sq_eq_zero_iff.mp h4.left
    have h6: x.im = 0 := sq_eq_zero_iff.mp h4.right
    exact MyComplex.ext x 0 h5 h6


end zero
section one

instance hasOne: One MyComplex where
  one := ⟨1,0⟩

/- Real part of one-/
@[simp]
theorem one_re: (1: MyComplex).re = 1 := rfl

/- Imaginary part of one-/
@[simp]
theorem one_im: (1: MyComplex).im = 0 := rfl

end one

section add
instance hasAdd: Add MyComplex where
  add (x y: MyComplex) := ⟨x.re + y.re, x.im + y.im⟩

/- Real part of `x + y` -/
@[simp]
theorem add_re (x y: MyComplex): (x + y).re = x.re + y.re := rfl
/- Imaginary part of `x + y` -/
@[simp]
theorem add_im (x y: MyComplex): (x + y).im = x.im + y.im := rfl

/- Zero is the additive identity: 𝜆 + 0 = 𝜆 -/
nonrec theorem add_zero: ∀x: MyComplex, x + 0 = x := by
  intro x ; ext
  . simp only [add_re, zero_re, add_zero]
  . simp only [add_im, zero_im, add_zero]

/- Addition is commmutative: 𝛼 + 𝛽 = 𝛽 + 𝛼 -/
theorem add_comm (x y: MyComplex): x + y = y + x := by
  simp [MyComplex.ext_iff, add_re, add_im] ; ring_nf ; simp only [and_self]

/- Addition is associative: (𝛼 + 𝛽) + 𝜆 = 𝛼 + (𝛽 + 𝜆)-/
theorem add_assoc (x y: MyComplex): x + (y + z) = (x + y) + z := by
  ext<;> simp <;> ring

end add

section neg

instance hasNeg: Neg MyComplex where
  neg (x: MyComplex) := ⟨-x.re, -x.im⟩

/- Real part of `-z`-/
@[simp]
theorem neg_re (z: MyComplex): (-z).re = -(z.re) := rfl

/- Imaginary part of `-z`-/
@[simp]
theorem neg_im (z: MyComplex): (-z).im = -z.im := rfl

/- Existence of additive inverse: For every 𝛼 ∈ 𝐂, there exists a unique 𝛽 ∈ 𝐂 such that 𝛼 + 𝛽 = 0-/
theorem exists_add_inv: ∀x : MyComplex, ∃y, x + y = 0 := fun x =>
  ⟨-x, by
    ext
    . rw [add_re, neg_re, zero_re, add_neg_self]
    . rw [add_im, neg_im, zero_im, add_neg_self]⟩

end neg

section mul

instance: Mul MyComplex where
  mul (x y: MyComplex) := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

/- Real part of `z * w`-/
@[simp]
theorem mul_re (z w: MyComplex): (z * w).re = z.re * w.re - z.im * w.im := rfl

/- Imaginary part of `z * w`-/
@[simp]
theorem mul_im (z w: MyComplex): (z * w).im = z.re * w.im + z.im * w.re := rfl


/- Zero-product: `x * 0 = 0`-/
@[simp]
nonrec theorem mul_zero (x: MyComplex): x * 0 = 0 := by
  ext
  . rw [mul_re, zero_re, zero_im, mul_zero, mul_zero, sub_zero]
  . rw [mul_im, zero_im, zero_re, mul_zero, mul_zero, _root_.add_zero]

/- Multiplicative identity: `𝜆1 = 𝜆` for all `𝜆 ∈ 𝐂`-/
@[simp]
theorem mul_one (x: MyComplex): x * 1 = x := by
  simp only [MyComplex.ext_iff, one_re, one_im, mul_re, mul_im]; ring_nf; simp only [and_self]

/- Multiplication is commutative: `𝛼𝛽 = 𝛽𝛼` for all `𝛼, 𝛽 ∈ 𝐂`-/
theorem mul_comm (x y: MyComplex): x * y = y * x := by
   simp only [MyComplex.ext_iff, mul_re, mul_im]; ring_nf; simp only [and_true]

/- Multiplication is associative: `(𝛼𝛽)𝜆 = 𝛼(𝛽𝜆) for all 𝛼, 𝛽, 𝜆 ∈ 𝐂`-/
theorem mul_assoc (x y z: MyComplex): x * (y * z) = (x * y) * z := by
   simp only [MyComplex.ext_iff, mul_re, mul_im]; ring_nf; simp only [and_true]

end mul

section inv

noncomputable instance hasInv: Inv MyComplex where
  inv (x : MyComplex) := ⟨x.re / (x.re^2 + x.im^2), -x.im/(x.re^2 + x.im^2)⟩

/- Real part of `z⁻¹`-/
@[simp]
theorem inv_re (z : MyComplex): z⁻¹.re = z.re / (z.re^2 + z.im^2) := rfl

/- Imaginary part of `z⁻¹`-/
@[simp]
theorem inv_im (x: MyComplex): x⁻¹.im = -x.im/(x.re^2 + x.im^2) := rfl

/-Existence of multiplicative inverse: For every 𝛼 ∈ 𝐂 with 𝛼 ≠ 0, there exists a unique 𝛽 ∈ 𝐂 such that 𝛼𝛽 = 1-/
theorem exists_mul_inv: ∀ x : MyComplex, x ≠ 0 →  ∃y, x * y = 1 := by
  intro x h
  use x⁻¹
  unfold MyComplex.hasInv
  ext
  . simp only [mul_re, inv_re, inv_im, one_re, mul_add]
    field_simp
    rw [←sq, ← sq, ←sub_div, sub_neg_eq_add, div_eq_mul_inv, mul_inv_cancel]
    by_contra h2
    have h3 := normSq_eq_zero_iff.mpr h2
    contradiction
  . simp only [mul_im, inv_re, inv_im, one_im, mul_add]
    field_simp
    rw [_root_.mul_comm x.re]; field_simp

end inv

/- Distributive property: 𝜆(𝛼 + 𝛽) = 𝜆𝛼 + 𝜆𝛽 for all 𝜆, 𝛼, 𝛽 ∈ 𝐂.-/
theorem mul_add {x y z: MyComplex}: x * (y + z) = x*y + x*z := by
  simp only [MyComplex.ext_iff, mul_re, add_re, add_im, mul_im]
  constructor <;> ring_nf

end MyComplex
