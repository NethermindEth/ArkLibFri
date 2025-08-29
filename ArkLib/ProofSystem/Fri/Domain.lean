import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

import ArkLib.Data.FieldTheory.NonBinaryField.Basic

class IsCyclicC (G : Type) [Pow G ℤ] where
  gen : G
  zpow_surjective : Function.Surjective (gen ^ · : ℤ → G)

instance {G} [Pow G ℤ] [inst : IsCyclicC G] : IsCyclic G where
  exists_zpow_surjective := ⟨inst.gen, inst.zpow_surjective⟩

class Smooth2 (n : ℕ) (G : Type) [Pow G ℤ] [Monoid G] [inst : IsCyclicC G] where
  smooth : orderOf inst.gen = 2 ^ n

variable {F : Type} [NonBinaryField F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicC D] [DSmooth : Smooth2 n D]

namespace Fri

namespace Domain

@[simp]
def evalDomain (i : ℕ) : Subgroup Fˣ :=
  Subgroup.zpowers (DIsCyclicC.gen ^ (2 ^ i))

lemma D_def : D = evalDomain D 0 := by
  unfold evalDomain
  simp only [pow_zero, pow_one]
  have := DIsCyclicC.zpow_surjective
  unfold Function.Surjective at this
  ext x
  apply Iff.intro
  · intros h
    rcases this ⟨x, h⟩ with ⟨a, h⟩
    simp only at h
    refine Subgroup.mem_zpowers_iff.mpr ?_
    exists a
    have : x = (DIsCyclicC.gen ^ a) := by
      norm_cast
      rw [h]
    rw [this]
  · intros h
    rw [Subgroup.mem_zpowers_iff] at h
    rcases h with ⟨k, h⟩
    norm_cast at h
    rw [←h]
    exact (DIsCyclicC.gen ^ k).2

instance {i : ℕ} : IsCyclicC (evalDomain D i) := by
  unfold evalDomain
  constructor
  swap
  · refine ⟨DIsCyclicC.gen.1 ^ 2 ^ i, ?_⟩
    simp
  · unfold Function.Surjective
    rintro ⟨b, h⟩
    have : ∃ n : ℤ, b = (DIsCyclicC.gen.1 ^ 2 ^ i) ^ n := by
      refine Subgroup.exists_mem_zpowers.mp ?_
      exists b
    rcases this with ⟨a, h'⟩
    exists a
    simp only [h']
    rfl

lemma pow_2_pow_i_mem_Di_of_mem_D :
  ∀ {x : Fˣ} (i : ℕ),
    x ∈ D → x ^ (2 ^ i) ∈ evalDomain D i := by
  intros x i h
  simp only [evalDomain]
  have := DIsCyclicC.2
  unfold Function.Surjective at this
  rcases this ⟨x, h⟩ with ⟨a, h⟩
  simp only at h
  have : x = DIsCyclicC.gen ^ a := by
    norm_cast
    rw [h]
  rw [this]
  refine Subgroup.mem_zpowers_iff.mpr ?_
  exists a
  rw [←zpow_natCast, ←zpow_natCast, zpow_comm]

lemma sqr_mem_D_succ_i_of_mem_D_i : ∀ {x : Fˣ} {i : ℕ},
  x ∈ evalDomain D i → x ^ 2 ∈ evalDomain D (i + 1) := by
  intros x i h
  simp only [evalDomain] at h
  simp only [evalDomain]
  rw [Subgroup.mem_zpowers_iff] at h ⊢
  rcases h with ⟨k, h⟩
  exists k
  rw [←h]
  have {x : Fˣ} {n : ℕ} : x ^ n = x ^ (n : ℤ) := by rfl
  rw [this, this, this, ←zpow_mul, ←zpow_mul, ←zpow_mul]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [@mul_comm ℤ _ k 2, ←mul_assoc]
  rfl

lemma gen_def {i : ℕ} :
    (IsCyclicC.gen : evalDomain D i) =
      ⟨
        DIsCyclicC.gen ^ (2 ^ i),
        by
          apply pow_2_pow_i_mem_Di_of_mem_D
          exact DIsCyclicC.gen.2
      ⟩ := by
  rfl

instance {i : ℕ} : Smooth2 (n - i) (evalDomain D i) where
  smooth := by
    simp
    rw [gen_def]
    by_cases h : i ≤ n
    · have : (2 ^ n).gcd (2 ^ i) = 2 ^ i := by
        refine Eq.symm (Nat.gcd_greatest ?_ ?_ fun e a a ↦ a)
        · exact (Nat.pow_dvd_pow_iff_le_right (by decide)).mpr h
        · exact dvd_refl _
      rw [Subgroup.orderOf_mk, orderOf_pow', orderOf_submonoid, DSmooth.smooth, this]
      · exact Nat.pow_div h (by decide)
      · aesop
    · rw [not_le] at h
      have : ∃ k : ℕ, i = n + k := Nat.exists_eq_add_of_le (by linarith)
      rcases this with ⟨k, h'⟩
      have : n - i = 0 := by
        refine Nat.sub_eq_zero_of_le (by linarith)
      rw
        [
          this, h', pow_zero, Subgroup.orderOf_mk, orderOf_eq_one_iff,
           Nat.pow_add 2 n k, pow_mul, ←DSmooth.smooth
        ]
      norm_cast
      rw [pow_orderOf_eq_one]
      exact one_pow _


lemma one_in_doms (i : ℕ) : 1 ∈ evalDomain D i := by
  simp only [evalDomain]
  apply OneMemClass.one_mem

lemma minus_one_in_doms {i : ℕ} (h : i < n) :
    -1 ∈ evalDomain D i := by
  unfold evalDomain
  rw [Subgroup.mem_zpowers_iff]
  exists ((2 ^ (n - (i + 1))))
  norm_cast
  rw [←pow_mul, ←pow_add]
  have : (i + (n - (i + 1))) = n - 1 := by
    refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add' h).mp) (Nat.le_sub_one_of_lt h) ?_)
    exact Eq.symm (Nat.Simproc.sub_add_eq_comm n i 1)
  rw [this]
  have : ((DIsCyclicC.gen.1 ^ 2 ^ (n - 1)) ^ 2) = 1 := by
    rw [←pow_mul]
    have : 2 ^ (n - 1) * 2 = 2 ^ n := by
      apply Nat.two_pow_pred_mul_two
      linarith
    rw [this, ←DSmooth.smooth]
    norm_cast
    rw [pow_orderOf_eq_one]
  have alg {x : Fˣ} : x^2 = 1 → x = 1 ∨ x = -1 := by
    intros h
    refine (Units.inv_eq_self_iff x).mp ?_
    have {a b : Fˣ} (c : Fˣ) : c * a = c * b → a = b := by
      intros h
      have : c⁻¹ * (c * a) = c⁻¹ * (c * a) := by rfl
      rw (occs := .pos [2]) [h] at this
      rw [←mul_assoc, ←mul_assoc, inv_mul_cancel, one_mul, one_mul] at this
      exact this
    apply this x
    simp only [mul_inv_cancel, h.symm, pow_two]
  have cast : (DIsCyclicC.gen ^ 2 ^ (n - 1)).1 = (DIsCyclicC.gen.1 ^ 2 ^ (n - 1)) := by rfl
  rw [cast]
  specialize alg this
  rcases alg with alg | alg
  · have gen_ord := DSmooth.smooth
    rw [orderOf_eq_iff (by simp)] at gen_ord
    have gen_ord :=
      gen_ord.2
        (2 ^ (n - 1))
        (by apply Nat.two_pow_pred_lt_two_pow; linarith)
        (by simp)
    exfalso
    apply gen_ord
    norm_cast at alg
  · assumption

lemma dom_n_eq_triv : evalDomain D n = ⊥ := by
  unfold evalDomain
  rw [Subgroup.zpowers_eq_bot, ←DSmooth.smooth]
  norm_cast
  exact pow_orderOf_eq_one IsCyclicC.gen

instance {i : Fin (n + 1)} : OfNat (evalDomain D i) 1 where
  ofNat := ⟨1, one_in_doms D i⟩

instance domain_neg_inst {i : Fin n} : Neg (evalDomain D i.1) where
  neg := fun x => ⟨_, minus_one_in_doms D i.2⟩ * x

end Domain

namespace CosetDomain

open Pointwise

variable (x : Fˣ)

@[simp]
def evalDomain (i : ℕ) : Set Fˣ :=
  (x ^ (2 ^ i)) • (Domain.evalDomain D i)

lemma D_def : evalDomain D x 0 = x • D := by simp [Domain.D_def D]

private lemma op_der_eq : Monoid.toMulAction Fˣ = Units.mulAction' := by
  unfold Units.mulAction' Monoid.toMulAction
  congr
  ext g m
  simp only [Units.val_mul]
  unfold_projs
  rfl

lemma pow_2_pow_i_mem_Di_of_mem_D :
  ∀ {a : Fˣ} (i : ℕ),
    a ∈ evalDomain D x 0 → a ^ (2 ^ i) ∈ evalDomain D x i := by
  unfold evalDomain
  intros a i h
  have h : x⁻¹ * a ∈ Domain.evalDomain D 0 := by
    simp only [pow_zero, pow_one] at h
    apply (mem_leftCoset_iff _).mp
    convert h
    exact op_der_eq
  rw [←Domain.D_def] at h
  have h := Domain.pow_2_pow_i_mem_Di_of_mem_D D i h
  have : (x⁻¹ * a) ^ 2 ^ i = (x ^ (2 ^ i))⁻¹ * (a ^ (2 ^ i)) := by field_simp
  rw [this] at h
  convert (mem_leftCoset_iff _).mpr h
  exact op_der_eq.symm

lemma sqr_mem_D_succ_i_of_mem_D_i : ∀ {a : Fˣ} {i : ℕ},
    a ∈ evalDomain D x i → a ^ 2 ∈ evalDomain D x (i + 1) := by
  unfold evalDomain
  intros a i h
  have h : (x ^ 2 ^ i)⁻¹ * a ∈ Domain.evalDomain D i := by
    apply (mem_leftCoset_iff _).mp
    convert h
    exact op_der_eq
  have h := Domain.sqr_mem_D_succ_i_of_mem_D_i D h
  have : ((x ^ 2 ^ i)⁻¹ * a) ^ 2 = (x ^ 2 ^ (i + 1))⁻¹ * (a ^ 2) := by
    have : ((x ^ 2 ^ i)⁻¹ * a) ^ 2 = ((x ^ 2 ^ i) ^ 2)⁻¹ * (a ^ 2) := by field_simp
    rw [this]
    have : (x ^ 2 ^ i) ^ 2 = x ^ 2 ^ (i + 1) := by
      rw [pow_two, ←pow_add]
      congr 1
      grind
    rw [this]
  rw [this] at h
  convert (mem_leftCoset_iff _).mpr h
  exact op_der_eq.symm

lemma neg_mem_dom_of_mem_dom : ∀ {a : Fˣ} (i : Fin n),
    a ∈ evalDomain D x i → - a ∈ evalDomain D x i := by
  unfold evalDomain
  rintro a ⟨i, i_prop⟩ h
  have mem : (x ^ 2 ^ i)⁻¹ * a ∈ Domain.evalDomain D i := by
    apply (mem_leftCoset_iff _).mp
    convert h
    exact op_der_eq

  have : (x ^ 2 ^ i)⁻¹ * -a ∈ ↑(Domain.evalDomain D i) := by
    have : (x ^ 2 ^ i)⁻¹ * -a = ((x ^ 2 ^ i)⁻¹ * a) * (- 1) := by field_simp
    rw [this]
    exact
      (
        Subgroup.mul_mem_cancel_right
          (Domain.evalDomain D i)
          (Domain.minus_one_in_doms D i_prop)
      ).mpr mem
  convert (mem_leftCoset_iff _).mpr this
  exact op_der_eq.symm

lemma dom_n_eq_triv : evalDomain D x n = {x ^ (2 ^ n)} := by
  unfold evalDomain
  rw [Domain.dom_n_eq_triv]
  simp

instance domain_neg_inst {i : Fin n} : Neg (evalDomain D x i) where
  neg := fun a => ⟨_, neg_mem_dom_of_mem_dom D x i a.2⟩

end CosetDomain

end Fri
