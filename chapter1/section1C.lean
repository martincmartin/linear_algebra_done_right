-- Subgroups

import Mathlib.Algebra.Field.Basic
import Mathlib.Data.SetLike.Basic

import chapter1.section1B

-- import Mathlib.Algebra.Module.Submodule.Basic

-- Note that we don't have the problem with "extends" that we had for
-- vector_space, since this is a structure not a class, and structures can't use
-- implicit search.  We make it a structure because the carrier isn't a type but
-- a field of the structure.
--
-- How submodule is structured:
--
-- universes u'' u' u v w
-- variables {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}
--
-- structure submodule (R : Type u) (M : Type v) [semiring R]
--  [add_comm_monoid M] [module R M] extends add_submonoid M, sub_mul_action R M : Type v.
--
-- structure add_submonoid (M : Type*) [add_zero_class M] extends add_subsemigroup M :=
-- (zero_mem' : (0 : M) ∈ carrier)
--
-- Note: This is actually an additive submanga, i.e. the only constraint is that
-- we must be closed under addition.  Associativity of M would be specified
-- elsewhere, and when that's true, this is also an additive sub semigroup.  So
-- they chose the name for the (much) more common usecase of subsemigroup.
--
-- structure add_subsemigroup (M : Type*) [has_add M] :=
-- (carrier : set M)
-- (add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
--
-- class add_zero_class (M : Type u) extends has_zero M, has_add M :=
-- (zero_add : ∀ (a : M), 0 + a = a)
-- (add_zero : ∀ (a : M), a + 0 = a)
--
-- structure sub_mul_action (R : Type u) (M : Type v) [has_smul R M] : Type v :=
-- (carrier : set M)
-- (smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier)
-- So we could (try to) not split into two classes this time, and just have one
-- subspace structure.  But it seems natural, having introduced the concept of
-- commutative group in the last section, to create a commutative subgroup here.

namespace LADR

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

variable {F : Type _} [Field F] {n : ℕ}

variable {V : Type _} [AddCommGroup V] [VectorSpace F V]

namespace VectorSpace

theorem neg_one_smul_is_neg {v : V} : (-1 : F) • v = -v :=
  sorry

end VectorSpace

end LADR

namespace LADR

-- LADR defines a subspace as a subset that's also a vector space, then derives
-- the standard conditions.  Because showing the standard conditions is the most
-- common way of demonstrating that a subset is indeed a subspace, it's easier
-- to put those in the Lean definition, then derive that the result is indeed a
-- vector space.
-- Since we split the vector space into two structures, here we need a "sub" for
-- each.
structure AddCommSubgroup (V : Type _) [AddCommGroup V] where
  carrier : Set V
  add_mem' : ∀ {u v : V}, u ∈ carrier → v ∈ carrier → u + v ∈ carrier
  zero_mem' : (0 : V) ∈ carrier

-- Should we show that a subgroup is also a group?
namespace AddCommSubgroup

variable {V : Type _} [AddCommGroup V] {v : V}

#print AddCommSubgroup

instance : SetLike (AddCommSubgroup V) V :=
  ⟨AddCommSubgroup.carrier, fun p q h => by cases p ; cases q ; congr⟩

@[simp]
theorem mem_carrier {p : AddCommSubgroup V} : v ∈ p.carrier ↔ v ∈ (p : Set V) :=
  Iff.rfl

@[ext]
theorem ext {p q : AddCommSubgroup V} (h : ∀ v, v ∈ p ↔ v ∈ q) : p = q :=
  SetLike.ext h

end AddCommSubgroup

-- Because this is a structure rather than a class, it's ok to extend add_comm_subgroup
structure Subspace (F : Type _) (V : Type _) [Field F] [AddCommGroup V] [VectorSpace F V] extends
    AddCommSubgroup V where
  smul_mem' : ∀ (c : F) {v : V}, v ∈ carrier → c • v ∈ carrier


namespace Subspace

variable {F : Type _} {V : Type _} [Field F] [AddCommGroup V] [VectorSpace F V]

variable {v : V}

instance blah : SetLike (Subspace F V) V where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h
  -- ⟨Subspace.toAddCommSubgroup.carrier, fun p q h => by cases p <;> cases q <;> congr⟩

@[simp]
theorem mem_carrier {p : Subspace F V} : v ∈ p.carrier ↔ v ∈ (p : Set V) :=
  Iff.rfl
#align LADR.subspace.mem_carrier LADR.Subspace.mem_carrier

@[ext]
theorem ext {p q : Subspace F V} (h : ∀ v, v ∈ p ↔ v ∈ q) : p = q :=
  SetLike.ext h
#align LADR.subspace.ext LADR.Subspace.ext

variable (p : Subspace F V)

-- 1.34 Conditions for a subspace
-- A subset U of V is a itself a vector space if and only if it satisfies the
-- 'subspace' conditions above.
-- First, show the reverse, i.e. when p satisfies the subspace conditions, then
-- it is a vector space.
-- Elements of ↥p are pairs: an element of the original V, plus a proof that
-- the element is in p.carrier.
-- For v: ↥p, ↑v is ... that first element, of the original V?
-- variables (p)
instance fooblah : AddCommGroup p
    where
  add u v := ⟨u.1 + v.1, by apply p.add_mem'; simp; simp⟩
  zero := ⟨0, p.zero_mem'⟩
  neg v := ⟨-v.1, by rw [← @vector_space.neg_one_smul_is_neg F _ V]; apply p.smul_mem'; simp⟩
  add_comm := by intros; ext; simp; apply AddCommGroup.add_comm
  add_assoc := by intros; ext; simp; apply AddCommGroup.add_assoc
  add_zero := by intros; ext; simp; rw [AddCommGroup.add_zero]
  add_right_inv := by intros; ext; simp; rw [add_comm_group.add_right_inv]
#align LADR.subspace.fooblah LADR.Subspace.fooblah

--variables {FF : Type*} {VV : Type*}
--variables [field FF] {add_comm_group_VV : add_comm_group VV}
--variables [vs : vector_space FF VV]
--variables (q : subspace FF VV)
@[simp]
theorem add_subspace {u v : p} : ↑(u + v) = u.1 + v.1 :=
  rfl
#align LADR.subspace.add_subspace LADR.Subspace.add_subspace

instance vectorSpace' : VectorSpace F p
    where
  smul s v := ⟨s • v.1, by apply p.smul_mem'; simp⟩
  smul_assoc := by intros; simp; apply vector_space.smul_assoc
  mul_ident := by intros; ext; simp; rw [vector_space.mul_ident]
  left_distrib := by intros; ext; simp; rw [vector_space.left_distrib]
  right_distrib := by intros; ext; simp; rw [vector_space.right_distrib]
#align LADR.subspace.vector_space' LADR.Subspace.vectorSpace'

instance : VectorSpace F p :=
  p.vectorSpace'

end Subspace

-- Next, show that for any subset of a vector space that is itself a vector
-- space, it must satisfy the three subspace conditions.
/-
structure subset_of_vector_space (F : Type*) (V : Type*)
  [field F] [vector_space F V] :=
(carrier : set V)

namespace subset_of_vector_space

-- variables [vector_space F V]
-- variable {v : V}


instance : set_like (subset_of_vector_space F V) V :=
⟨ subset_of_vector_space.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : subset_of_vector_space F V} : v ∈ p.carrier ↔ v ∈ (p : set V) := iff.rfl

@[ext] theorem ext {p q : subset_of_vector_space F V} (h : ∀ v, v ∈ p ↔ v ∈ q) : p = q := set_like.ext h

-- So the different sets and types are confusing to me.

-- "v ∈ p" is for elements of the big vector space being in the small one.  I
-- think there's an implicit coercion in there somewhere, maybe p to p.carrier.
-- "(u : p) ∈ p" doesn't typecheck.



theorem bar {p : subset_of_vector_space F V} [hp : vector_space F p] : (0 : p) ∈ p := sorry

-- Wait, do we have the same + here?  Not neccesarily.  Hmm.
theorem foo {p : subset_of_vector_space F V} [hp : vector_space F p] : (0 : V) ∈ p :=
begin
  -- Prove that the zero vector of p is also a zero vector in V, then apply
  -- unique_add_ident.
  have  hhh : (0 : V) = (0 : p),
  { apply eq.symm,
    apply vector_space.unique_add_ident,
    intro v,
    sorry },
  simp [hhh]
end

end subset_of_vector_space
-/
end LADR
