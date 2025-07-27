import Mathlib.GroupTheory.SpecificGroups.Cyclic

import ArkLib.Data.FieldTheory.NonBinaryField.Basic

namespace Fri

namespace Domain

-- class Smooth (p : ℕ) (G : Type) extends Group G, IsCyclic G where
--   smooth : ∃ n : ℕ, orderOf (Classical.choose exists_zpow_surjective) = p ^ n

-- instance {i : Fin n} : Smooth 2 (evalDomain gen i.castSucc) where
--   smooth := sorry

variable {F : Type} [NonBinaryField F]
variable (gen : Fˣ)
variable {n : ℕ}

@[simp]
def evalDomain (i : Fin (n + 1)) : Subgroup Fˣ :=
  Subgroup.zpowers (gen ^ (2 ^ i.val))

@[simp]
def D (n : ℕ) : Subgroup Fˣ := evalDomain gen (0 : Fin (n + 1))

lemma D_def : D gen n = Subgroup.zpowers gen := by unfold D evalDomain; simp

instance : IsCyclic (D gen n) := by
  rw [D_def, Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  exists gen

instance {i : Fin (n + 1)} : IsCyclic (evalDomain gen i) := by
  unfold evalDomain
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  exists ((gen ^ 2 ^ i.1))

lemma pow_2_pow_i_mem_Di_of_mem_D {gen : Fˣ} :
  ∀ {x : Fˣ} (i : Fin (n + 1)),
    x ∈ (D gen n) → x ^ (2 ^ i.val) ∈ evalDomain gen i := by
  intros x i h
  simp only [D, evalDomain, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, pow_one] at h
  simp only [evalDomain]
  rw [Subgroup.mem_zpowers_iff] at h ⊢
  rcases h with ⟨k, h⟩
  exists k
  rw [←h]
  have {x : Fˣ} {n : ℕ} : x ^ n = x ^ (n : ℤ) := by rfl
  rw [this, this, ←zpow_mul, ←zpow_mul]
  ring_nf

lemma sqr_mem_D_succ_i_of_mem_D_i {gen : Fˣ} : ∀ {x : Fˣ} {i : Fin n},
  x ∈ evalDomain gen i.castSucc → x ^ 2 ∈ evalDomain gen i.succ := by
  intros x i h
  simp only [evalDomain, Fin.coe_castSucc] at h
  simp only [evalDomain, Fin.val_succ]
  rw [Subgroup.mem_zpowers_iff] at h ⊢
  rcases h with ⟨k, h⟩
  exists k
  rw [←h]
  have {x : Fˣ} {n : ℕ} : x ^ n = x ^ (n : ℤ) := by rfl
  rw [this, this, this, ←zpow_mul, ←zpow_mul, ←zpow_mul]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [@mul_comm ℤ _ k 2, ←mul_assoc]
  have : (2 : ℤ) ^ (i.val + 1) = 2 ^ i.val * 2 := by
    ring
  rw [this]

lemma one_in_doms (i : Fin n) : 1 ∈ evalDomain gen i.castSucc := by
  simp only [evalDomain, Fin.coe_castSucc]
  apply OneMemClass.one_mem

variable [gen_ord : Fact (orderOf gen = (2 ^ n))]

lemma minus_one_in_doms (i : Fin n) :
    -1 ∈ evalDomain gen i.castSucc := by
  unfold evalDomain
  have h : i.castSucc.1 < n := by
    simp
  rw [Subgroup.mem_zpowers_iff]
  exists ((2 ^ (n - (i.castSucc.1 + 1))))
  norm_cast
  rw [←pow_mul, ←pow_add]
  have : (↑i.castSucc.1 + (n - (↑i.castSucc.1 + 1))) = n - 1 := by
    refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add' h).mp) (Nat.le_sub_one_of_lt h) ?_)
    exact Eq.symm (Nat.Simproc.sub_add_eq_comm n (↑i.castSucc) 1)
  rw [this]
  have : ((gen ^ 2 ^ (n - 1)) ^ 2) = 1 := by
    rw [←pow_mul]
    have : 2 ^ (n - 1) * 2 = 2 ^ n := by
      apply Nat.two_pow_pred_mul_two
      linarith [i.2]
    rw [this, ←(@Fact.out _ gen_ord), pow_orderOf_eq_one]
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
  specialize alg this
  rcases alg with alg | alg
  · rw [orderOf_eq_iff (by simp)] at gen_ord
    have gen_ord :=
      (@Fact.out _ gen_ord).2
        (2 ^ (n - 1))
        (by apply Nat.two_pow_pred_lt_two_pow; linarith [i.2])
        (by simp)
    exfalso
    apply gen_ord
    exact alg
  · assumption

def lift_to_subgroup {x : Fˣ} {H : Subgroup Fˣ} (h : x ∈ H) : H := ⟨x, h⟩

example : evalDomain gen (Fin.last n) = ⊥ := by
  unfold evalDomain
  rw [Fin.val_last, Subgroup.zpowers_eq_bot, ←(@Fact.out _ gen_ord), pow_orderOf_eq_one]

instance {i : Fin (n + 1)} : OfNat (evalDomain gen i) 1 where
  ofNat := ⟨1, one_in_doms gen i⟩

instance domain_neg_inst {i : Fin n} : Neg (evalDomain gen i.castSucc) where
  neg := fun x => (lift_to_subgroup (minus_one_in_doms gen i)) * x

end Domain

end Fri
