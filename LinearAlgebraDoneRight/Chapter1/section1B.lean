-- Now that you've had a taste for how complex numbers and tuples are defined,
-- from now on we won't use our definitions from the last section, but rather
-- the definitions that come with Lean.

import Mathlib.Algebra.Field.Basic
import Mathlib.GroupTheory.GroupAction.Pi

-- 1.19  Definition  vector space

-- In LADR, a vector space is a set V and field F, along with two functions,
-- addition and scalar multiplication of vectors.  It also requries that certain
-- properties hold.  Some of those properties include "there exists," for
-- example "∀ v : V, ∃ w : V, v + w = 0."  Lean prefers an alternate approach,
-- where instead of "there exists" properties, we provide a function which,
-- given v, returns w.

-- Lean has a vary useful ability to take *implicit arguments*.  For example,
-- when you want to apply the theorem "0 + v = v" to a particular v, you don't
-- need to explicitly specify the VectorSpace, it can usually infer it.  Not
-- having to explicitly write the VectorSpace everywhere saves a lot of reading
-- & generally focuses on what's important, rather than what's understood.  For
-- example, in Linear Algebra Done Right, Axler says "from now on, V is a vector
-- space" and then doesn't need to repeat it over and over for each theorm.

-- Some theorems don't depend on the field of scalars and will work with any
-- field, e.g. the theorm that the negative (addative inverse) of a vector is
-- unique.  In this case, Lean can go looking for the field, but since any field
-- will do, it won't have a lot of guideance and can get stuck.  And anyway this
-- work is useless, since the field isn't even used in the proof.

-- So, we separate out the parts that involve only addition, including the zero
-- and negation, into a class of their own that doesn't even mention field.  In
-- abstract algebra, this is an additive commutative group, so we call it
-- add_comm_group.

-- Put this in its own namespace, since there is already an add_comm_group in
-- mathlib, and it gets included when we include field.
namespace LADR

-- "extends has_add" adds a function 'add' to VectorSpace that uses infix
-- notation, e.g. 'u + v'.  Similarly with the other "extends" clauses.
@[ext]
class AddCommGroup (V : Type _) extends Add V, Zero V, Neg V where
  add_comm : ∀ u v : V, u + v = v + u
  add_assoc : ∀ u v w : V, u + v + w = u + (v + w)
  add_zero : ∀ v : V, v + 0 = v
  add_right_inv : ∀ v : V, v + -v = 0

@[ext]
class VectorSpace (F : Type _) (V : Type _) [Field F] [AddCommGroup V] extends SMul F V where
  smul_assoc : ∀ a b : F, ∀ v : V, (a * b) • v = a • b • v
  mul_ident : ∀ v : V, (1 : F) • v = v
  left_distrib : ∀ a : F, ∀ u v : V, a • (u + v) = a • u + a • v
  right_distrib : ∀ a b : F, ∀ v : V, (a + b) • v = a • v + b • v

-- "F^n is a vector space over F, as you should verify."
variable {F : Type _} [field_f: Field F] {n : ℕ}

instance nTupleAddCommGroup : AddCommGroup (Fin n → F)
    where
  add u v := u + v
  zero := 0
  neg v := -v
  add_comm := add_comm
  add_assoc := add_assoc
  add_zero := add_zero
  add_right_inv := add_neg_self

-- Should this use instance or def?
def nTupleVectorSpace : VectorSpace F (Fin n → F)
    where
  smul a v := a • v
  smul_assoc := smul_assoc
  mul_ident := one_smul F
  left_distrib := by
    intro a u v
    funext
    simp
    apply field_f.left_distrib
  right_distrib := by
    intro a b v
    funext
    simp
    apply field_f.right_distrib

-- 1.22  Example  F^∞
-- We defined an n-tuple as a map from `fin n` to F, so a natural definition of
-- an infinite tuple is just a map from ℕ to F.
instance infTupleAddCommGroup : AddCommGroup (ℕ → F)
    where
  add u v := u + v
  zero := 0
  neg v := -v
  add_comm := add_comm
  add_assoc := add_assoc
  add_zero := add_zero
  add_right_inv := add_neg_self

def infTupleVectorSpace : VectorSpace F (ℕ → F)
    where
  smul a v := a • v
  smul_assoc := smul_assoc
  mul_ident := one_smul F
  left_distrib := by
    intro a u v
    funext
    simp
    apply field_f.left_distrib
  right_distrib := by
    intro a b v
    funext
    simp
    apply field_f.right_distrib

-- 1.23  Notation  F^S
-- In Lean, we generally use types where most mathematicians use sets.  Also in
-- Lean, the type of functions from S to F is 'S → F'.
-- 1.24  Example  F^S is a vector space
variable (S : Type _)

instance funAddCommGroup : AddCommGroup (S → F)
    where
  add u v := u + v
  zero := 0
  neg v := -v
  add_comm := add_comm
  add_assoc := add_assoc
  add_zero := add_zero
  add_right_inv := add_neg_self

def funVectorSpace : VectorSpace F (S → F)
    where
  smul a v x := a * v x
  smul_assoc := smul_assoc
  mul_ident := one_smul F
  left_distrib := by
    intro a u v
    funext
    apply field_f.left_distrib
  right_distrib := by
    intro a b v
    funext
    apply field_f.right_distrib

namespace VectorSpace

-- 1.25  Unique additive identity
-- "A vector space has a unique additive identity"
theorem unique_add_ident {V : Type _} [AddCommGroup V] {z : V} (h : ∀ v : V, v + z = v) : z = 0 :=
  calc
    z = z + 0 := by rw [AddCommGroup.add_zero]
    _ = 0 + z := by rw [AddCommGroup.add_comm]
    _ = 0 := by rw [h]

-- 1.26  Unique additive inverse
-- "Every element in a vector space has a unique additive inverse"
theorem zero_add {V : Type _} [AddCommGroup V] {v : V} : 0 + v = v :=
  by
  rw [AddCommGroup.add_comm]
  apply AddCommGroup.add_zero

theorem unique_add_inv {V : Type _} [AddCommGroup V] {v w : V} (h : v + w = 0) : w = -v :=
  calc
    w = w + 0 := by rw [AddCommGroup.add_zero]
    _ = w + (v + -v) := by rw [← AddCommGroup.add_right_inv]
    _ = w + v + -v := by rw [AddCommGroup.add_assoc]
    _ = v + w + -v := by rw [AddCommGroup.add_comm w v]
    _ = 0 + -v := by rw [h]
    _ = -v := by rw [zero_add]

-- 1.27  Notation  -v, w - v
-- We started with -v, before proving it was unique.
-- Notation for 'w - v'
instance {V : Type _} [AddCommGroup V] : Sub V :=
  ⟨fun w v => w + -v⟩

@[simp]
theorem sub_add_neg {V : Type _} [AddCommGroup V] (u v : V) : u - v = u + -v :=
  rfl

-- 1.28  Notation  V
variable {V : Type _} [AddCommGroup V] [VectorSpace F V]

-- 1.29  The number 0 times a vector
-- Lean proofs are very explicit, so we tend to use lots of helper lemmas for
-- things that most mathematicians wouldn't even mention in their proofs.
theorem sub_self {v : V} : v - v = 0 := by simp; apply AddCommGroup.add_right_inv

theorem add_sub_cancel {u v : V} : u + v - v = u :=
  by
  simp
  rw [AddCommGroup.add_assoc, AddCommGroup.add_right_inv, AddCommGroup.add_zero]

-- All the (0 : F) here is really distracting.  Is there a way to get Lean to
-- understand that in 0 • v, the zero is not a natural number but from the
-- field?
theorem zero_vec_eq_zero {v : V} : (0 : F) • v = 0 :=
  by
  apply Eq.symm
  calc
    0 = (0 : F) • v - (0 : F) • v := by rw [sub_self]
    _ = ((0 : F) + (0 : F)) • v - (0 : F) • v := by simp
    _ = (0 : F) • v + (0 : F) • v - (0 : F) • v := by rw [right_distrib]
    _ = (0 : F) • v := by apply add_sub_cancel

-- 1.30  A number times the vector 0
theorem field_zero_eq_zero {a : F} : a • (0 : V) = 0 :=
  calc
    a • (0 : V) = a • (0 : V) + a • (0 : V) - a • (0 : V) := by rw [add_sub_cancel]
    _ = a • (0 + 0 : V) - a • (0 : V) := by rw [left_distrib]
    _ = a • (0 : V) - a • (0 : V) := by rw [AddCommGroup.add_zero]
    _ = 0 := by rw [sub_self]

-- 1.31  The number -1 times a vector
theorem neg_one_smul_is_neg {v : V} : (-1 : F) • v = -v :=
  by
  rw [← unique_add_inv]
  calc
    v + (-1 : F) • v = (1 : F) • v + (-1 : F) • v := by rw [mul_ident]
    _ = ((1 : F) + (-1 : F)) • v := by rw [right_distrib]
    _ = (0 : F) • v := by simp
    _ = 0 := zero_vec_eq_zero

end VectorSpace

end LADR
