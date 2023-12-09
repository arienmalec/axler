import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Complex

Axler 1.3, using Mathlib to show the basic properties

-/

/-
## Commutativity
𝛼 + 𝛽 = 𝛽 + 𝛼 and 𝛼𝛽 = 𝛽𝛼 for all 𝛼, 𝛽 ∈ 𝐂
-/
example {x y : ℂ}: x + y = y + x := Complex.instCommSemiringComplex.add_comm x y
example {x y : ℂ}: x * y = y * x := Complex.instCommSemiringComplex.mul_comm x y

/-
## Associativity
(𝛼 + 𝛽) + 𝜆 = 𝛼 + (𝛽 + 𝜆) and (𝛼𝛽)𝜆 = 𝛼(𝛽𝜆) for all 𝛼, 𝛽, 𝜆 ∈ 𝐂
-/
example {x y z: ℂ}: x + y + z = x + (y + z) := Complex.instCommSemiringComplex.add_assoc x y z
example {x y z: ℂ}: x * y * z = x * (y * z) := Complex.instCommSemiringComplex.mul_assoc x y z

/--
## Identities
𝜆 + 0 = 𝜆 and 𝜆1 = 𝜆 for all 𝜆 ∈ 𝐂
-/
example: ∀ x : ℂ, x * 0 = 0 := mul_zero
example: ∀ x : ℂ, x * 1 = x := mul_one

/--
## Existence of additive inverse
For every 𝛼 ∈ 𝐂, there exists a unique 𝛽 ∈ 𝐂 such that 𝛼 + 𝛽 = 0
-/
theorem exists_add_inv: ∀ x : ℂ, ∃y, x + y = 0 := by
  intro x
  use -x
  exact add_right_neg x

/--
## Existence of multiplicative inverse
For every 𝛼 ∈ 𝐂 with 𝛼 ≠ 0, there exists a unique 𝛽 ∈ 𝐂 such that 𝛼𝛽 = 1
-/
theorem exists_mul_inv: ∀x : ℂ , x≠ 0 → ∃y, x * y = 1 := by
  intro x h
  use x⁻¹
  simp only [ne_eq, Complex.ext_iff, Complex.zero_re, Complex.zero_im, not_and, Complex.mul_re,
    Complex.inv_re, Complex.inv_im, Complex.one_re, Complex.mul_im, Complex.one_im]
  field_simp
  rw [←sub_div, sub_neg_eq_add, ←Complex.normSq_apply, add_comm, mul_comm, add_neg_self,
      eq_self, true_or, and_true]
  apply mul_inv_cancel
  simp only [ne_eq, map_eq_zero, h, not_false_eq_true]

/-
## Distributive property
𝜆(𝛼 + 𝛽) = 𝜆𝛼 + 𝜆𝛽 for all 𝜆, 𝛼, 𝛽 ∈ 𝐂.
-/
example {x y z: ℂ}: x * (y + z) = x * y + x * z := mul_add x y z
