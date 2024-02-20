import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Basic

variable (V: Type*)
variable [AddCommGroup V] [Module ℝ V]

/--
Literal translation of `V_C`. We could follow the definition even more literaly by making `Vc` a `Prod`
but it's interesting to see how this definition parallels the construction of `ℂ` we did (and `Prod`
itself is just a structure anyway).
-/
@[ext]
structure Vc where
  /-- First element, seen as a real part-/
  r: V
  /-- Second element, seen as imaginary -/
  i: V

namespace Vc

/-- We use the definition of addition we were provided -/
instance addVc: Add (Vc V) where
  add a b := ⟨a.r + b.r, a.i + b.i⟩

@[simp]
theorem add_r {ar ai br bi : V}: ((⟨ar, ai⟩ : Vc V) + (⟨br, bi⟩ : (Vc V))).r  = ar + br := rfl

@[simp]
theorem add_i {ar ai br bi : V}: ((⟨ar, ai⟩ : Vc V) + (⟨br, bi⟩ : (Vc V))).i  = ai + bi := rfl

/-- We also need to define `Zero` and negation -/
instance zeroVc: Zero (Vc V) where
  zero := ⟨0, 0⟩

@[simp]
theorem zero_r: (0 : Vc V).r = 0 := rfl

@[simp]
theorem zero_i: (0 : Vc V).i = 0 := rfl

instance negVc: Neg (Vc V) where
  neg w := ⟨-w.r, w.i⟩

@[simp]
theorem neg_r {ar ai : V}: (-⟨ar, ai⟩: Vc V).r = -ar := rfl

@[simp]
theorem neg_i {ar ai : V}: (-⟨ar, ai⟩: Vc V).i = ai := rfl

/-- Then our scalar multiplication by `ℝ × ℝ`-/
instance rSmulVc: SMul (ℝ × ℝ)  (Vc V) where
  smul c w :=
    match c with
    | (a, b) => ⟨(a • w.r) - b • w.i, a  • w.i + b • w.r⟩

@[simp]
theorem smul_r {a b: ℝ} {wr wi : V}: ((a, b) • (⟨wr, wi⟩ : Vc V)).r = (a • wr) - b • wi := rfl
@[simp]
theorem smul_i {a b: ℝ} {wr wi : V}: ((a, b) • (⟨wr, wi⟩ : Vc V)).i = a  • wi + b • wr := rfl


/--
We show that `Vc V` follows the laws for a vector
-/
instance: AddCommMonoid (Vc V) where
  add_assoc a b c := by
    ext
    . rw [add_r, add_r, add_r, add_r, add_assoc]
    . rw [add_i, add_i, add_i, add_i, add_assoc]
  zero_add a := by
    ext
    . rw [add_r, zero_r, zero_add]
    . rw [add_i, zero_i, zero_add]
  add_zero a := by
    ext
    . rw [add_r, zero_r, add_zero]
    . rw [add_i, zero_i, add_zero]
  add_comm a b := by
    ext
    . rw [add_r, add_r, add_comm]
    . rw [add_i, add_i, add_comm]


namespace complex

/-- We use our scalar multiplication by `ℝ × ℝ` to provide a scalar multiplication by `ℂ`
    by deconstructing the value into a `Prod` of real and imaginary parts-/
def complex_smul (c : ℂ) (w: Vc V):= (c.re, c.im) • w

instance cSmulVc: SMul ℂ (Vc V) where
  smul c w := complex_smul _ c w

/-- We then prove the scalar multiplcation laws for this definition and package them into a `Module` instance.
    The general pattern here is to decompose back to statements in terms of `ℝ • V` and rely on our assumption
    that `V` is a real vector space for the rest of the proof-/

nonrec theorem one_smul {w: Vc V}: (1: ℂ) • w = w := by
  simp only [HSMul.hSMul, SMul.smul]; unfold complex_smul
  ext
  . rw [Complex.one_re, Complex.one_im, smul_r]; simp
  . rw [Complex.one_re, Complex.one_im, smul_i]; simp

theorem zero_smul {w: Vc V}: (0: ℂ) • w = 0 := by
  simp only [HSMul.hSMul, SMul.smul] ; unfold complex_smul; rw [Complex.zero_re, Complex.zero_im]
  ext <;> (first | rw [smul_r] | rw [smul_i]) <;> simp

theorem smul_zero {z: ℂ}: z • (0: Vc V) = 0 := by
  simp only [HSMul.hSMul, SMul.smul]; unfold complex_smul
  ext <;> (first | rw [smul_r] | rw [smul_i]) <;> simp

nonrec theorem mul_smul {x y: ℂ} {w: Vc V}: (x * y) • w = x • y • w := by
  simp only [HSMul.hSMul, SMul.smul]
  unfold complex_smul; rw [Complex.mul_re, Complex.mul_im]
  ext
  . rw [smul_r, smul_r, sub_smul, add_smul, mul_smul, mul_smul, mul_smul, mul_smul, smul_i,
        smul_r, smul_sub, smul_add]
    abel_nf
  . rw [smul_i, smul_i, sub_smul, add_smul, mul_smul, mul_smul, mul_smul, mul_smul, smul_i,
        smul_r, smul_sub, smul_add]
    abel_nf

nonrec theorem smul_add : ∀ (x : ℂ) (w z : Vc V), x • (w + z) = x • w + x • z := by
  intro x w z
  simp only [HSMul.hSMul, SMul.smul] ; unfold complex_smul; ext
  . rw [smul_r, add_r, add_i, add_r, smul_r, smul_r, smul_add, smul_add]; abel_nf
  . rw [smul_i, add_i, add_r, add_i, smul_i, smul_i, smul_add, smul_add]; abel_nf

nonrec theorem add_smul: ∀ (x y : ℂ) (w : Vc V), (x + y) • w = x • w + y • w := by
  intro x y w
  simp only [HSMul.hSMul, SMul.smul]; unfold complex_smul ; ext
  . rw [smul_r, Complex.add_re, add_smul, Complex.add_im, add_r, add_smul, smul_r, smul_r]; abel_nf
  . rw [smul_i, Complex.add_re, add_smul, Complex.add_im, add_i, add_smul, smul_i, smul_i]; abel_nf

instance vcModule: Module ℂ (Vc V) where
  smul a w := complex_smul _ a w
  one_smul w := @one_smul _ _ _ w
  zero_smul w := @zero_smul _ _ _ w
  smul_zero z := @smul_zero _ _ _ z
  mul_smul x y w := @mul_smul _ _ _ x y w
  smul_add x w z := @smul_add _ _ _ x w z
  add_smul x y w:= @add_smul _ _ _ x y w

end complex
end Vc
