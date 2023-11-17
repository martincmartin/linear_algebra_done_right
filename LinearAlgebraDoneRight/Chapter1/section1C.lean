-- Chapter 1 Section C: Subgroups

import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.SetLike.Basic

import «LinearAlgebraDoneRight».Chapter1.section1B

import Mathlib.Data.Fin.VecNotation


namespace LADR

-- 1.32  Definition  Subspace
-- 1.34  Conditions of a subspace

-- Note that we don't have the problem with "extends" that we had for
-- VectorSpace, since this is a structure not a class, and structures can't use
-- implicit search.  We make it a structure because the carrier isn't a type but
-- a field of the structure.

-- LADR defines a subspace as a subset that's also a vector space, then derives
-- the standard conditions.  Because showing the standard conditions is the most
-- common way of demonstrating that a subset is indeed a subspace, it's easier
-- to put those in the Lean definition, then derive that the result is indeed a
-- vector space.

-- Actually, this isn't neccesarily a subgroup, since this isn't closed under
-- inverse.  However, our only interest in this is when it is extended to a
-- Subspace, and in that case, it will be a Subgroup.
structure AddCommSubgroup (V : Type _) [AddCommGroup V] where
  carrier : Set V
  add_mem' : ∀ {u v : V}, u ∈ carrier → v ∈ carrier → u + v ∈ carrier
  zero_mem' : (0 : V) ∈ carrier

-- Start of SetLike boilerplate.
namespace AddCommSubgroup

variable {G : Type _} [AddCommGroup G]

instance : SetLike (AddCommSubgroup G) G :=
  ⟨AddCommSubgroup.carrier, fun p q h => by cases p ; cases q ; congr⟩

@[simp]
theorem mem_carrier {p : AddCommSubgroup G} : v ∈ p.carrier ↔ v ∈ (p : Set G) :=
  Iff.rfl

@[ext]
theorem ext {p q : AddCommSubgroup G} (h : ∀ v, v ∈ p ↔ v ∈ q) : p = q :=
  SetLike.ext h

end AddCommSubgroup
-- end of SetLike boilerplate.

-- Because this is a structure rather than a class, it's ok to extend AddCommSubgroup
structure Subspace (F : Type _) (V : Type _) [Field F] [AddCommGroup V] [VectorSpace F V] extends
    AddCommSubgroup V where
  smul_mem' : ∀ (c : F) {v : V}, v ∈ carrier → c • v ∈ carrier


namespace Subspace

variable {F : Type _} {V : Type _} [Field F] [AddCommGroup V] [VectorSpace F V]

-- Beginning of SetLike boilerplate.
instance : SetLike (Subspace F V) V where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

@[simp]
theorem mem_carrier {p : Subspace F V} : v ∈ p.carrier ↔ v ∈ (p : Set V) :=
  Iff.rfl

@[ext]
theorem ext {p q : Subspace F V} (h : ∀ v, v ∈ p ↔ v ∈ q) : p = q :=
  SetLike.ext h
-- End of SetLike boilerplate.

variable (p : Subspace F V)

-- 1.34 Conditions for a subspace

-- A subset U of V is a itself a vector space if and only if it satisfies the
-- three 'subspace' conditions above.

-- Our definition of Subspace is that it satisfies those three conditions.  So
-- here we show that Subspace is indeed a vector space.

-- Elements of ↥p are pairs: an element of the original V, plus a proof that
-- the element is in p.carrier.
instance  : AddCommGroup p
    where
  add u v := ⟨u.1 + v.1, by apply p.add_mem'; simp; simp⟩
  zero := ⟨0, p.zero_mem'⟩
  neg v := ⟨-v.1, by rw [← @VectorSpace.neg_one_smul_is_neg F _ V]; apply p.smul_mem'; simp⟩
  add_comm := by intros; ext; apply AddCommGroup.add_comm
  add_assoc := by intros; ext; apply AddCommGroup.add_assoc
  add_zero := by intro; ext; apply AddCommGroup.add_zero
  add_right_inv := by intros; ext; apply AddCommGroup.add_right_inv

instance vectorSpace' : VectorSpace F p
    where
  smul s v := ⟨s • v.1, by apply p.smul_mem'; simp⟩
  smul_assoc := by intros; ext; apply VectorSpace.smul_assoc
  mul_ident := by intros; ext; apply VectorSpace.mul_ident
  left_distrib := by intros; ext; apply VectorSpace.left_distrib
  right_distrib := by intros; ext; apply VectorSpace.right_distrib

-- And so p, our Subspace, is also a VectorSpace over F.
instance : VectorSpace F p :=
  p.vectorSpace'

end Subspace

-- Next, show that for any subset of a vector space that is itself a vector
-- space, using the same + and * operations,  must satisfy the three subspace
-- conditions, that is, it's a Subgroup.

variable {F : Type _} {V : Type _} [Field F] [acgV: AddCommGroup V] [vsV : VectorSpace F V]

-- We need the assumption that p is a VectorSpace.
variable {W : Set V} [acgW: AddCommGroup W] [vsW : VectorSpace F W]

namespace AddCommGroup

theorem self_eq_add_right {u v : V} : u = u + v ↔ v = 0 := by
  constructor
  . intro h
    calc
      v = 0 + v := by rw [VectorSpace.zero_add]
      _ = u + -u + v := by rw [AddCommGroup.add_right_inv]
      _ = -u + u + v := by rw [AddCommGroup.add_comm u]
      _ = -u + (u + v) := by rw [AddCommGroup.add_assoc]
      _ = -u + u := by rw [← h]
      _ = 0 := by rw [AddCommGroup.add_comm (-u), AddCommGroup.add_right_inv]
  intro h
  rw [h, AddCommGroup.add_zero]

end AddCommGroup

-- Construct a Subspace object, which records the three conditions, from a
-- subset that is also a VectorSpace, assuming that add and smul are the same.
--
-- Thanks to Yakov Pechersky for formalizing it this way.
def toSubspace (h_add : ∀ x y : W, ((x + y : W) : V) = x + y)
  (h_smul : ∀ (c : F) (w : W), c • w = c • (w : V)) : Subspace F V where
  carrier := W
  add_mem' := by
    intros u v hu hv
    specialize h_add ⟨u, hu⟩ ⟨v, hv⟩
    dsimp only at h_add
    simp [← h_add]
  zero_mem' := by
    specialize h_add 0 0
    rw [acgW.add_zero] at h_add
    rw [AddCommGroup.self_eq_add_right] at h_add
    simp [← h_add]
  smul_mem' := by
    intros c v hv
    specialize h_smul c ⟨v, hv⟩
    dsimp only at h_smul
    simp [← h_smul]


-- 1.33  Example  {(x₁, x₂, 0) : x₁, x₂ ∈ F} is a subspace of F^3.

variable {F : Type _} [myfield : Field F] -- (x₁ x₂ : F)

def firstTwo : (Set (Fin 3 → F)) := {![x₁, x₂, 0] | (x₁ : F) (x₂ : F)}

def firstTwoSubspace : Subspace F (Fin 3 → F) where
  carrier := firstTwo
  add_mem' := by
    simp [firstTwo]
    intros u v u₁ u₂ ueq v₁ v₂ veq
    use (u₁ + v₁)
    use (u₂ + v₂)
    rw [← ueq, ← veq]
    simp
  zero_mem' := by simp [firstTwo]
  smul_mem' := by
    simp [firstTwo]
    intros c v v₁ v₂ veq
    rw [← veq]
    simp
    use c * v₁
    use c * v₂


end LADR
