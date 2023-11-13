-- This file is a translation of Linear Algebra Done Right, 3rd edition
-- (henceforth LADR) by Sheldon Alxer into Lean.  The goal is for the student
-- who is familiar with LADR, but less familiar with Lean, to see how various
-- definitions and theorems in the book are translated into canonical Lean.
--
-- This section contains two parts, the first on complex numbers, the second on
-- tuples.
--
-- Some of LADR's conventions clash with Lean's.  For example it uses λ as a
-- scalar variable, whereas Lean uses it to define anonymous functions.  Also,
-- LADR uses α as a complex variable, whereas Lean uses it as a type variable.
-- When these clashes occur, I follow the Lean convention, and so the choice of
-- variable in this file may differ from LADR's.


import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.Basic
-- import Mathlib.Init.Data.Fin.Basic

import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic

-- import Mathlib.Data.Complex.Basic

namespace LADR

-- 1.1 Definition complex numbers
-- LADR defines it as an ordered pair; more appropriate in Lean is a structure,
-- and this is also how mathlib defines it.

@[ext]
structure Complex : Type where
  re : ℝ
  im : ℝ

-- priority := 2000 is only needed to shadow the existing ℂ.  The Mathlib
-- definition of ℂ just omits that.
notation (priority := 2000) "ℂ" => Complex


namespace Complex

-- @[ext]
-- theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
--   | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

-- "The idea is to assume we have the square root of -1, denoted I."
@[simp] def I : ℂ := ⟨0, 1⟩

-- "If a ∈ ℝ, we identify a + 0I with the real number a.""
@[coe]
def ofReal' (r : ℝ) : ℂ :=
  ⟨r, 0⟩
instance : Coe ℝ ℂ :=
  ⟨ofReal'⟩


-- These lemmas help the simplifier work with coerced real numbers.
@[simp, norm_cast] theorem ofReal_re (r : ℝ) : (r : ℂ).re = r := rfl
@[simp, norm_cast] theorem ofReal_im (r : ℝ) : (r : ℂ).im = 0 := rfl

-- It can also help Lean to simplify expressions if we tell it about zero and
-- one.
instance : Zero ℂ := ⟨(0 : ℝ)⟩
@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl

instance : One ℂ := ⟨(1 : ℝ)⟩
@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl


-- Define addition on ℂ in a way that lets use use '+' for it.
instance : Add ℂ :=  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
-- We need to repeat the definition so the simplifier will use it, and also so
-- we can refer to it by name, e.g. with `rw`.
@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl


-- Define multiplication on ℂ in a way that lets use use '*' for it.
instance : Mul ℂ :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
-- We need to repeat the definition so the simplifier will use it, and also so
-- we can refer to it by name, e.g. with `rw`.
@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl

-- Using multiplication as defined above, we verify that I^2 = -1.
@[simp] lemma I_mul_I : I * I = (-1 : ℝ) :=  by ext <;> simp

-- In Lean, natural numbers aren't a subset of real numbers, but rather a
-- completely different set of objects.  So, the natuarl number 5 is different
-- than the real number 5.  When we write "5" without specifying the type, Lean
-- often interprets it as a natural number.

-- To get Lean to automatically coerce the integer literal to a complex number,
-- we need to prove that the complex numbers are an "addative commutative group
-- with one."  This is too long and involved for someone with the background
-- assumed by LADR.  So here, we explicitly cast literals to complex numbers.
-- Rest assured that, when using the definition of complex number in mathlib,
-- we can avoid all this explicit typing.


-- Providing these lets us work with examples containing natural number literals.
-- instance : OfNat Complex n where
--   ofNat := { re := n, im := (0 : ℝ)  }

-- instance : NatCast ℂ where
--   natCast n := { re := n, im := 0 }

-- @[simp] theorem ofNat_re (n : ℕ) [OfNat ℝ n] : (n : ℂ).re = (n : ℝ) := rfl
-- @[simp] theorem ofNat_im (n : ℕ) [OfNat ℝ n] : (n : ℂ).im = (0 : ℝ) := rfl

-- example: (2 : ℂ).re * (4 : ℂ).re = 8 := by
--   rw [ofNat_re 2]


-- Example 1.2 "Evaluate (2 + 3 * I) * (4 + 5 * I)"
example : ((2: ℝ) + (3: ℝ)  * I) * ((4: ℝ) + (5: ℝ) * I) = ((-7: ℝ) + (22 : ℝ) * I) :=
  calc
    ((2: ℝ) + (3: ℝ) * I) * ((4: ℝ) + (5: ℝ) * I) =
        (2 * 4 : ℝ) + (2: ℝ) * ((5: ℝ) * I) + ((3: ℝ) * I) * (4: ℝ) + ((3: ℝ) * I) * ((5: ℝ) * I) := by
      ext <;> norm_num
    _ = (8: ℝ) + (10: ℝ) * I + (12: ℝ) * I + (-15: ℝ) := by ext <;> norm_num
    _ = (-7 : ℝ) + (22 : ℝ) * I := by ext <;> norm_num



-- 1.3 Properties of complex arithmetic
variable (z w v : ℂ)

-- commutativity
theorem add_comm : z + w = w + z :=
  by ext <;> simp [AddCommSemigroup.add_comm]

-- 1.4 Example "Show that αβ = βα for all α, β ∈ ℂ"
theorem mul_comm : z * w = w * z :=
  by ext <;> simp <;> ring

-- associativity
theorem add_assoc : z + w + v = z + (w + v) :=
  by ext <;> simp [AddSemigroup.add_assoc]

theorem mul_assoc : z * w * v = z * (w * v) :=
  by ext <;> simp <;> ring

-- identities
theorem add_id : z + 0 = z :=
  by ext <;> simp

theorem mul_id : z * 1 = z :=
  by ext <;> simp


-- 1.5 -α, subtraction, 1/α, division

-- LADR takes an axiomatic approach, that is, it states that the additive
-- inverse is the complex number with given properties, then later derives a
-- formula for it.  Lean prefers us to instead define it in terms of the
-- formula, then prove the properties.

instance : Neg ℂ := ⟨fun z => ⟨-z.re, -z.im⟩⟩
@[simp] lemma neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : ℂ) : (-z).im = -z.im := rfl

instance : Sub ℂ := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
@[simp] lemma sub_re (z w : ℂ) : (z - w).re = z.re - w.re := rfl
@[simp] lemma sub_im (z w : ℂ) : (z - w).im = z.im - w.im := rfl

-- additive inverse
theorem add_inv : z + -z = 0 := by ext <;> simp


-- The formula for the multiplicative inverse uses the conjugate, which is why
-- we define it here before the inverse, whereas LADR doesn't even define it in
-- this section.
def conjugate : ℂ → ℂ := (fun z : ℂ => ⟨z.re, (-z.im)⟩)
@[simp] theorem conjugate_re (z : ℂ) : (conjugate z).re = z.re := rfl
@[simp] theorem conjugate_im (z : ℂ) : (conjugate z).im = -z.im := rfl

def norm_sq : ℂ → ℝ := (fun z => z.re * z.re + z.im * z.im)
@[simp] theorem norm_sq_def (z : ℂ) : norm_sq z = z.re * z.re + z.im * z.im := rfl

noncomputable instance : Inv ℂ := ⟨fun z => conjugate z * ((norm_sq z)⁻¹:ℝ)⟩
theorem inv_def (z : ℂ) : z⁻¹ = (conjugate z) * ((norm_sq z)⁻¹:ℝ) := rfl
@[simp] lemma inv_re (z : ℂ) : (z⁻¹).re = z.re / norm_sq z := by simp [inv_def, division_def]
@[simp] lemma inv_im (z : ℂ) : (z⁻¹).im = -z.im / norm_sq z := by simp [inv_def, division_def]


-- To prove z * (z ⁻¹), we need the following theorems.
private theorem aux {x y : ℝ} (h : x * x + y * y = 0) : x = 0 :=
by
  simp [← sq] at h
  have h' : x^2 = 0 := by
    apply le_antisymm _ (sq_nonneg x)
    rw [← h]
    apply le_add_of_nonneg_right (sq_nonneg y)
  exact pow_eq_zero h'


theorem zero_of_norm_sq_zero :
  z.norm_sq = 0 → z = 0 :=
  by
    intro h
    ext
    . exact aux h
    simp at h
    rw [AddCommSemigroup.add_comm] at h
    exact aux h

-- multiplicative inverse
theorem mul_inv (h : z ≠ 0) : z * z⁻¹ = 1 := by
  ext
  · simp [h]
    ring_nf
    simp [← right_distrib, mul_inv]
    apply mul_inv_cancel
    intro hsq
    apply h
    apply zero_of_norm_sq_zero
    simp [← sq]
    exact hsq
  simp [h]
  ring


-- distributive property
theorem distrib : v * (z + w) = v * z + v * w := by ext <;> simp <;> ring

end Complex


-- 1.6 Notation F

namespace Example_1_6
variable {F : Type _} [Field F] (a b : F) (m n : ℕ)

example : (a^m)^n = a^(m*n) := (pow_mul a m n).symm

example : (a * b)^m = a ^ m * b ^ m := mul_pow a b m
end Example_1_6

/-
  1.8  Definition  tuple, length
  1.10 all tuples of a given length
  LADR calls them lists, but that has a different meaning in Lean.  LADR says
  "Many mathematicians call a list of length n an n-tuple", so we'll call them
  "tuples".
 -/

-- A tuple of length n
-- `fin n` is the subtype of `ℕ` consisting of natural numbers strictly smaller
-- than `n`.
@[reducible]
def Tuple (α : Type _) (n : ℕ) := Fin n → α

namespace Tuple


-- 1.9 Example lists versus sets.

example : ( ![3, 5] : Tuple ℕ 2) ≠ (![5, 3] : Tuple ℕ 2) :=
by
  rw [Function.ne_iff]
  use 0
  simp

example : ({3, 5} : Set ℕ) = {5, 3} :=
by
  ext n
  simp
  tauto

-- Note that these are different types, so even trying to write that they are
-- not equal produces a type error:
#check ![4, 4, 4]
#check ![4, 4]


example : ({4, 4, 4} : Set ℕ) = {4} := by simp

example : ({4, 4} : Set ℕ) = {4} := by simp

variable {F : Type _} [Field F]


-- 1.10
-- We denote F^n as tuple F n.

-- 1.12  Definition  addition in F^n

variable {n : ℕ} (x y : Tuple F n)

instance : Add (Tuple F n) :=
  ⟨fun x y i => (x i) + (y i)⟩

@[simp]
theorem plus_eq_add : x + y = fun i => x i + y i :=
  rfl


example : ![2, 3] + ![5, 7] = ![7, 10] := by simp


-- 1.13  Commutativity of addition in F^n
theorem tuple_add_comm : x + y = y + x := by
  funext
  simp
  apply add_comm

-- 1.14  Definition 0
instance : Zero (Tuple F n) :=
  ⟨fun i => 0⟩

@[simp]
theorem zero_zero : (0 : Tuple F n) = fun i => 0 :=
  rfl

example : 0 = ![(0 : ℝ), 0] := by
  funext i
  rw [zero_zero]
  -- dsimp
  cases' i with val property
  interval_cases val
  · simp
  simp

variable (v : Tuple F n)

theorem add_zero : v + 0 = v := by simp

theorem zero_add : 0 + v = v := by simp

-- 1.16  Definition  additive inverse in F^n
instance : Neg (Tuple F n) :=
  ⟨fun v i => -v i⟩

@[simp]
theorem neg_neg {v : Tuple F n} : -v = fun i => -v i :=
  rfl

theorem add_neg : v + -v = 0 := by simp

theorem neg_add : -v + v = 0 := by simp

instance : SMul F (Tuple F n) :=
  ⟨fun a v i => a * v i⟩

@[simp]
theorem smul_mul {a : F} : a • v = fun i => a * v i :=
  rfl

end Tuple

end LADR
