import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic

variable (F: Type _)
variable [Field F]

@[ext]
structure Fn (n: ℕ) where
  term: Fin n → F

variable {F}

instance addRn {n: ℕ}: Add (Fn F n) where
  add a b := ⟨fun n => a.term n + b.term n⟩

@[simp]
theorem term_add_apply {n: ℕ} {a b : (Fn F n)} {x: Fin n}: (a + b).term x = a.term x + b.term x := rfl

instance smulRn: SMul F (Fn F n) where
  smul x a := ⟨fun n => x * a.term n⟩

@[simp]
theorem term_smul_apply {a : Fn F n} {x: F} {y: Fin n}: (x • a).term y = x • (a.term y) := rfl

instance zeroRn: Zero (Fn F n) where
  zero := ⟨fun _ => 0⟩

@[simp]
theorem zero_term: (0 :Fn F n).term x = 0 := rfl

instance negRn: Neg (Fn F n) where
  neg r := ⟨fun n => -(r.term n)⟩

@[simp]
theorem neg_term {a: Fn F n}: (-a).term = -(a.term) := rfl


instance addCommGroupRn: AddCommGroup (Fn F n) where
  add_comm a b := by  ext ; simp [add_comm]
  add_assoc a b c := by ext ; simp [add_assoc]
  zero := zeroRn.zero
  add_zero a := by ext ; simp only [term_add_apply, add_zero, zero_term]
  zero_add a := by ext ; simp only [term_add_apply, zero_add, zero_term]
  add_left_neg a := by ext; simp

instance moduleRn: Module F (Fn F n) where
  one_smul a := by ext; simp
  zero_smul a := by ext; simp
  smul_zero a := by ext; simp
  smul_add a b c := by ext; simp [mul_add]
  add_smul a b c := by ext; simp [add_mul]
  mul_smul a b c := by ext; simp [mul_assoc]
