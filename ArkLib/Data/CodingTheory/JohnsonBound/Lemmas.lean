/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov 
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Module.LinearMap.Defs

import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.JohnsonBound.Choose2
import ArkLib.Data.CodingTheory.JohnsonBound.Expectations

namespace JohnsonBound

section 

variable {n : ℕ}
variable {F : Type*} [Fintype F] [DecidableEq F]
         {B : Finset (Fin n → F)} {i : Fin n}

private def Fi (B : Finset (Fin n → F)) (i : Fin n) (α : F) : Finset (Fin n → F) :=
  { x | x ∈ B ∧ x i = α } 

private abbrev K (B : Finset (Fin n → F)) (i : Fin n) (α : F) : ℕ :=
  (Fi B i α).card

private lemma Fis_cover_B : B = Finset.univ.biUnion (Fi B i) := by
  aesop (add simp [Fi])

private lemma Fis_pairwise_disjoint : Set.PairwiseDisjoint Set.univ (Fi B i) := by
  unfold Fi
  rintro x - y - h₁ _ h₂ h₃ _ contra
  specialize h₂ contra
  specialize h₃ contra
  aesop

private lemma sum_K_eq_card : ∑ (α : F), K B i α = B.card := by
  rw (occs := [2]) [Fis_cover_B (B := B) (i := i)]
  rw [Finset.card_biUnion (by simp [Fis_pairwise_disjoint])]

private lemma K_eq_sum {α : F} : K B i α = ∑ (x : B), if x.1 i = α then 1 else 0 := by
  simp [K, Fi]
  simp_rw [Finset.card_filter, Finset.sum_attach_eq_sum_dite]
  apply Finset.sum_congr <;> aesop

@[simp]
private lemma K_le_card {α : F} : K B i α ≤ B.card := by
  simp [K, Fi]
  exact Finset.card_le_card fun _ ha ↦ by simp at ha; exact ha.1

open Finset in
private lemma sum_choose_K' [Zero F]
  (h_card : 2 ≤ (Fintype.card F))
  : 
  (Fintype.card (α := F) - 1) * choose_2 ((B.card - K B i 0) / (Fintype.card (α := F) - 1)) ≤
  ∑ (α : F) with α ≠ 0, choose_2 (K B i α) := by
  rw [←sum_K_eq_card (i := i), Nat.cast_sum]
  set X₁ : ℚ := Fintype.card F - 1
  have X₁h : X₁ ≠ 0 := by simp [X₁, sub_eq_zero]; omega
  set X₂ := K B i
  suffices X₁ * choose_2 (∑ x with x ≠ 0, (fun _ ↦ X₁⁻¹) x • (Nat.cast (R := ℚ) ∘ X₂) x) ≤
           ∑ α with α ≠ 0, choose_2 ↑(X₂ α) by
    simp at this
    convert this
    rw [sum_eq_sum_diff_singleton_add (i := 0) (by simp)]
    ring_nf
    rw [sum_mul]
    apply sum_congr (ext _) <;> field_simp
  apply le_trans
  · rewrite [mul_le_mul_left (by aesop)]
    apply ConvexOn.map_sum_le choose_2_convex
            (by aesop (add safe (by omega)))
            (by simp [X₁]; rw [Field.mul_inv_cancel _ X₁h])
            (by simp)
  · rw [mul_sum]; field_simp

private def sum_choose_K (B : Finset (Fin n → F)) (i : Fin n) : ℚ :=
  ∑ (α : F), choose_2 (K B i α)

private lemma le_sum_choose_K [Zero F]
  (h_card : 2 ≤ (Fintype.card F)) : 
  choose_2 (K B i 0) + (Fintype.card (α := F) - 1) *
  choose_2 ((B.card - K B i 0) / (Fintype.card (α := F) - 1)) ≤ sum_choose_K B i := by 
  unfold sum_choose_K  
  rw [show Finset.univ = {0} ∪ {x : F | x ≠ 0}.toFinset by ext; simp; tauto]
  simp [Finset.sum_union, sum_choose_K' h_card]

private def k [Zero F] (B : Finset (Fin n → F)) : ℚ := 
  (1 : ℚ) / n * ∑ i, K B i 0

omit [Fintype F] in
private lemma hamming_weight_eq_sum [Zero F] {x : Fin n → F}
  : 
  ‖x‖₀ = ∑ i, if x i = 0 then 0 else 1 := by simp [hammingNorm, Finset.sum_ite]

private lemma sum_hamming_weight_sum [Zero F]
  :
  ∑ x ∈ B, (‖x‖₀ : ℚ) = n * B.card - ∑ i, K B i 0 := by 
  simp only [hamming_weight_eq_sum, Nat.cast_sum, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
    K_eq_sum, Finset.sum_boole, Nat.cast_id]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, eq_sub_iff_add_eq]
  simp_rw [Nat.cast_sum, Nat.cast_ite]
  conv in Finset.sum _ _ => arg 2; ext; arg 2; ext; rw [←ite_not]
  simp_rw [Finset.univ_eq_attach, Finset.sum_attach_eq_sum_dite]
  simp only [Nat.cast_one, CharP.cast_eq_zero, dite_eq_ite, Finset.sum_ite_mem, Finset.univ_inter]
  rw [←Finset.sum_add_distrib]
  simp_rw [←Finset.sum_filter, add_comm, Finset.sum_filter_add_sum_filter_not]
  simp

private lemma k_and_e [Zero F]
  (h_n : n ≠ 0)
  (h_B : B.card ≠ 0)
  :
  k B = B.card * (n - e B 0) / n := by
  simp [e, k, sum_hamming_weight_sum]
  field_simp

private lemma k_and_e' [Zero F]
  (h_n : n ≠ 0)
  (h_B : B.card ≠ 0)
  :
  k B / B.card = (n - e B 0) / n := by
  rw [k_and_e h_n h_B]
  field_simp
  ring

private lemma k_choose_2 [Zero F] {B : Finset (Fin n → F)} 
  (h_n : n ≠ 0)
  (h_B : B.card ≠ 0)
  :
  n * choose_2 (k B) ≤ ∑ i, choose_2 (K B i 0) := by
  suffices choose_2 (∑ i, (fun _ ↦ (1:ℚ) / n) i • (fun i ↦ K B i 0) i) * n ≤
           ∑ i, choose_2 (K B i 0) by
    rw [mul_comm]; convert this
    simp [k, Finset.mul_sum]
  transitivity
  apply (mul_le_mul_right (by simp; omega)).2
          (ConvexOn.map_sum_le
            choose_2_convex
            (by simp)
            (by field_simp)
            (by simp))
  rw [Finset.sum_mul]
  field_simp

private def aux_frac (B : Finset (Fin n → F)) (x : ℚ) : ℚ := 
  (B.card - x) / (Fintype.card F - 1)

private lemma sum_1_over_n_aux_frac_k_i [Zero F] 
  (h_n : 0 < n) : ∑ i, 1/n * aux_frac B (K B i 0) = aux_frac B (k B) := by
  simp [aux_frac]
  suffices (n : ℚ)⁻¹ * (↑n * B.card - ∑ x, JohnsonBound.K B x 0) = B.card - k B by
    rw [←Finset.mul_sum, ←Finset.sum_div, ←this]
    field_simp
  field_simp [k]; ac_rfl

private lemma aux_sum [Zero F]
  (h_n : 0 < n)
  : n * choose_2 (aux_frac B (k B)) ≤ ∑ i, choose_2 (aux_frac B (K B i 0)) := by
  suffices choose_2 (∑ i, (fun _ ↦ (1:ℚ)/n) i • (fun x ↦ aux_frac B (K B x 0)) i) * ↑n ≤
           ∑ i, choose_2 (JohnsonBound.aux_frac B (JohnsonBound.K B i 0)) by
    rw [←sum_1_over_n_aux_frac_k_i h_n, mul_comm]
    convert this
  transitivity
  apply (mul_le_mul_right (by simp; omega)).2
          (ConvexOn.map_sum_le
             choose_2_convex
             (by simp)
             (by field_simp )
             (by simp))
  rw [Finset.sum_mul]
  field_simp

private lemma le_sum_sum_choose_K [Zero F]
  (h_n : 0 < n)
  (h_B : B.card ≠ 0)
  (h_card : 2 ≤ Fintype.card F)
  : 
  n * (choose_2 (k B) + (Fintype.card (α := F) - 1) 
    * choose_2 ((B.card - k B) / ((Fintype.card (α := F) - 1))))
  ≤ ∑ i, sum_choose_K B i := by 
  rw [mul_add]
  transitivity
  apply add_le_add_right (k_choose_2 (n := n) (by omega) h_B)
  transitivity
  apply add_le_add_left (by 
    rewrite [←mul_assoc, mul_comm (n : ℚ), mul_assoc]
    transitivity
    apply (mul_le_mul_left (by simp; omega)).2 (aux_sum h_n)
    rfl
  )
  rw [Finset.mul_sum, ←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ ↦ le_sum_choose_K h_card

private def F2i (B : Finset (Fin n → F)) (i : Fin n) (α : F) : Finset ((Fin n → F) × (Fin n → F)) :=
  { x | x ∈ B ×ˢ B ∧ x.1 i = α ∧ x.2 i = α ∧ x.1 ≠ x.2 } 

private def Bi (B : Finset (Fin n → F)) (i : Fin n) : Finset ((Fin n → F) × (Fin n → F)) :=
  { x | x ∈ B ×ˢ B ∧ x.1 i = x.2 i ∧ x.1 ≠ x.2 }

private lemma Bi_biUnion_F2i :
  Bi B i = Finset.univ.biUnion (F2i B i) := by aesop (add simp [Bi, F2i])

@[simp]
private lemma F2i_disjoint :
  Set.PairwiseDisjoint Set.univ (F2i B i) := by 
  simp 
    [Set.PairwiseDisjoint
    , Set.Pairwise
    , Disjoint
    , F2i
    , Finset.Nonempty
    , Finset.subset_iff
    ] 
  intro _ _ _ _ h1 h2 x₁ x₂ contr 
  specialize h1 x₁ x₂ contr
  specialize h2 x₁ x₂ contr
  aesop

private lemma F2i_card {α : F} :
  (F2i B i α).card = 2 * choose_2 (K B i α) := by
  simp [F2i]
  letI Tα := (Fin n → F) × (Fin n → F)
  let S₁ : Finset Tα := {x | (x.1 ∈ B ∧ x.2 ∈ B) ∧ x.1 i = α ∧ x.2 i = α}
  let S₂ : Finset _ := {x | x ∈ S₁ ∧ x.1 ≠ x.2}
  set A := Fi B i α with eqA
  suffices S₂.card = 2 * choose_2 (K B i α) by simp [S₂, S₁, ←this]; congr; ext; tauto
  rw [
    show S₂ = S₁ \ ({x | x ∈ S₁ ∧ x.1 = x.2} : Finset _) by aesop,
    Finset.card_sdiff fun _ _ ↦ by aesop,
    show S₁ = A ×ˢ A by ext; rw [Finset.mem_product]; simp [S₁, Fi, A]; tauto,
    Finset.filter_and
  ]
  simp; rw [Finset.card_prod_self_eq (s := A), Finset.card_product]
  simp [choose_2, K, eqA.symm]
  have : A.card ≤ A.card * A.card := Nat.le_mul_self _
  field_simp [this]; ring

open Finset in
private lemma sum_of_not_equals :
  ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0) 
  = 
  2 * choose_2 #B - 2 * ∑ α, choose_2 (K B i α) 
  := by
  generalize eq₁ : {x ∈ B ×ˢ B | x.1 ≠ x.2} = s₁
  suffices ↑(#s₁) - ↑(#(Bi B i)) =
           2 * choose_2 ↑(#B) - 2 * ∑ α, choose_2 ↑(JohnsonBound.K B i α) by
    rw [
      show (∑ x ∈ s₁, if x.1 i ≠ x.2 i then 1 else 0)
         = (∑ x ∈ s₁, ((1 : ℚ) - if x.1 i = x.2 i then 1 else 0)) by congr; aesop
    ]
    simp; convert this
    ext; simp [←eq₁, Bi]; tauto
  rw [
    show #s₁ = 2 * choose_2 #B by
      rw [
        show s₁ = (B ×ˢ B) \ {x ∈ B ×ˢ B | x.1 = x.2} by ext; simp [eq₁.symm]; tauto,
        card_sdiff (by simp)
      ]
      simp [choose_2]
      zify [Nat.le_mul_self #B]
      ring
  ]
  rw [Bi_biUnion_F2i, Finset.card_biUnion (by simp [F2i_disjoint])]
  simp; simp_rw [F2i_card, mul_sum]

private lemma hamming_dist_eq_sum {x y : Fin n → F} :
  ↑Δ₀(x, y) = ∑ i, if x i = y i then 0 else 1 := by
  simp [hammingDist, Finset.sum_ite] 

private lemma d_eq_sum {B : Finset (Fin n → F)} 
  (h_B : 2 ≤ B.card)
  :
  2 * choose_2 B.card * d B = ∑ i, ∑ x ∈ (Finset.product B B) with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0) := by
  simp [d]
  rw [mul_assoc]
  rw [←mul_assoc (choose_2 (↑B.card))]
  rw [←mul_assoc (choose_2 (↑B.card)), Field.mul_inv_cancel _ (by {
    simp [choose_2]
    apply And.intro 
    aesop
    intro contr 
    have h : ↑B.card = (1 : ℚ) := by
      rw [←zero_add (1 : ℚ)]  
      rw [←contr]
      simp
    simp at h
    omega
  })]
  field_simp
  rw [Finset.sum_comm]
  congr 
  ext x 
  rw [hamming_dist_eq_sum]
  simp

private lemma sum_sum_K_i_eq_n_sub_d {B : Finset (Fin n → F)} 
  (h_B : 2 ≤ B.card)
  :
  ∑ i, sum_choose_K B i = choose_2 B.card * (n - d B) := by
  rw [mul_sub]
  have h : choose_2 B.card = ((1 : ℚ)/2) * (2 * choose_2 B.card) := by
    field_simp
  rw [h, mul_assoc (1/2), mul_assoc (1/2), ←mul_sub (1/2)] 
  rw [d_eq_sum h_B]
  conv =>
    rhs 
    congr 
    rfl 
    congr 
    rfl 
    congr 
    rfl
    ext i
    rw [sum_of_not_equals]
    rfl
  simp 
  ring_nf
  simp [sum_choose_K]
  rw [Finset.sum_mul]
  field_simp

private lemma almost_johnson [Zero F] {B : Finset (Fin n → F)} 
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  n * (choose_2 (k B) + ((Finset.univ (α := F)).card - 1 : ℚ) 
    * choose_2 ((B.card - k B)/((Finset.univ (α := F)).card-1)))
  ≤
  choose_2 B.card * (n - d B) := by
  apply le_trans 
  exact le_sum_sum_choose_K h_n (by aesop) h_card 
  rw [sum_sum_K_i_eq_n_sub_d h_B]

private lemma almost_johnson_choose_2_elimed [Zero F] {B : Finset (Fin n → F)} 
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  (k B * (k B - 1)  +  
    (B.card - k B) * ((B.card - k B)/((Finset.univ (α := F)).card-1) - 1))
  ≤
  B.card * (B.card - 1) * (n - d B)/n := by
  have h := almost_johnson h_n h_B h_card 
  have h_den_ne_0 : (↑(Fintype.card F) - (1 : ℚ)) ≠ 0 := by
    intro contr 
    have h : ↑(Fintype.card F) = (1 : ℚ) := by
      rw [←zero_add 1, ← contr]
      simp
    simp at h
    omega
  have h_lhs : 
    n * ((1:ℚ)/2) * ((k B) * (k B - 1) + ((Finset.univ (α := F)).card - 1 : ℚ) 
    * ((B.card - k B)/((Finset.univ (α := F)).card-1)) * ((B.card - k B)/((Finset.univ (α := F)).card-1) - 1))
    =
    n * (choose_2 (k B) + ((Finset.univ (α := F)).card - 1 : ℚ) 
      * choose_2 ((B.card - k B)/((Finset.univ (α := F)).card-1))) := by
    simp [choose_2]
    ring_nf
  rw [←h_lhs] at h
  simp [choose_2] at h 
  have h_rhs : ↑B.card * (↑B.card - 1) / 2 * (↑n - d B)
    = ↑n * 2⁻¹ * (↑n)⁻¹ * ↑B.card * (↑B.card - 1) * (↑n - d B) := by 
    rw [mul_comm (↑n : ℚ)]
    rw [mul_assoc, mul_assoc (2⁻¹)]
    rw [Field.mul_inv_cancel _ (by simp; omega)]
    field_simp
    ring
  rw [h_rhs] at h 
  apply le_of_mul_le_mul_left (a := (↑n : ℚ) * (2⁻¹))
  have h_rhs : ↑n * 2⁻¹ * (↑n)⁻¹ * ↑B.card * (↑B.card - 1) * (↑n - d B)
    = ↑n * 2⁻¹ * (↑B.card * (↑B.card - 1) * (↑n - d B) / ↑n)  := by
    ring
  rw [h_rhs] at h
  apply le_trans' h
  simp 
  conv =>
    rhs 
    congr 
    congr 
    congr 
    rfl 
    rfl 
    congr 
    rfl
    congr 
    rw [Field.div_eq_mul_inv, mul_comm, mul_assoc]
    congr 
    rfl
    rw [mul_comm, Field.mul_inv_cancel _ (by aesop)]
    rfl
    rfl
  simp
  simp
  assumption

private lemma almost_johnson_lhs_div_B_card [Zero F] {B : Finset (Fin n → F)} 
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  :
  (k B * (k B - 1)  +  
    (B.card - k B) * ((B.card - k B)/((Finset.univ (α := F)).card-1) - 1)) / B.card 
  = 
  (1 - e B 0 / n) ^ 2 * B.card + B.card * (e B 0) ^ 2 / ((Fintype.card F - 1) * n^2) - 1 := by
  rw [add_div]
  conv => 
    lhs 
    congr 
    rw [mul_comm, ←mul_div]
    rw [k_and_e' (by omega) (by omega)]
    rw [k_and_e (by omega) (by omega)]
    rfl
    rw [mul_comm, ←mul_div, sub_div (c := (B.card : ℚ))]
    rw [k_and_e' (by omega) (by omega)]
    rw [Field.div_eq_mul_inv _ (B.card : ℚ)]
    rw [Field.mul_inv_cancel _ (by {
      simp
      aesop
    })]
    rw [k_and_e (by omega) (by omega)]
    rfl
  have hn : (↑n : ℚ) / ↑n = 1 := by field_simp
  conv =>
    lhs
    congr 
    rw [sub_mul]
    rw [←mul_div, mul_assoc, ←pow_two, one_mul]
    rw [sub_div, hn]
    rfl
    rw [←mul_div]
    rw [sub_div (c := (↑n : ℚ)), hn]
    simp 
    rw [sub_mul]
    simp
    rw [←mul_one (B.card : ℚ)]
    rw [mul_assoc]
    rw [←mul_sub (B.card : ℚ)]
    simp 
    rw [mul_comm, mul_div, mul_div]
    rfl
  have h : (e B 0 / ↑n * (↑B.card * e B 0 / ↑n) / (↑(Fintype.card F) - 1) - e B 0 / ↑n)
    = ↑B.card * (e B 0)^2/ (↑n^2 *  (↑(Fintype.card F) - 1)) - e B 0 / ↑n:= by
    field_simp
    ring_nf 
  rw [h]
  ring_nf

private lemma johnson_unrefined [Zero F] {B : Finset (Fin n → F)} 
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  (1 - e B 0 / n) ^ 2 * B.card + B.card * (e B 0) ^ 2 / ((Fintype.card F - 1) * n^2) - 1 
  ≤
  (B.card - 1) * (1 - d B/n) := by
  have h : ((1 : ℚ) - d B / ↑n) = (↑n - d B) / ↑n := by
    field_simp
  rw [h]
  rw [←almost_johnson_lhs_div_B_card h_n h_B]
  apply le_of_mul_le_mul_left (a := (B.card : ℚ)) 
  rw [Field.div_eq_mul_inv _ (↑B.card : ℚ)]
  rw [mul_comm]
  rw [mul_assoc, mul_comm _ ((↑B.card) : ℚ), Field.mul_inv_cancel _ (by aesop)]
  simp 
  rw [←mul_assoc]
  apply le_trans 
  apply almost_johnson_choose_2_elimed h_n h_B h_card
  field_simp 
  simp
  rw [Finset.nonempty_iff_ne_empty]
  aesop

private lemma johnson_unrefined_by_M [Zero F] {B : Finset (Fin n → F)} 
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  B.card * ((1 - e B 0 / n) ^ 2  + (e B 0) ^ 2 / ((Fintype.card F - 1) * n^2) - 1 + d B/n)
  ≤
  d B/n := by 
  rw [mul_add, mul_sub]
  rw [sub_add]
  have hh : (↑B.card * 1 - ↑B.card * (d B / ↑n)) = ↑B.card * (1 - (d B/↑n)) := by
    rw [mul_sub]
  rw [hh]
  apply le_of_add_le_add_right (a := -1)
  apply le_of_add_le_add_right (a := ↑B.card * (1 - d B / ↑n))
  have hh : d B / ↑n + -1 + ↑B.card * (1 - d B / ↑n)
    = (↑B.card - 1) * (1 - d B / ↑n) := by ring
  rw [hh]
  apply le_trans' (johnson_unrefined h_n h_B h_card)
  conv =>
    lhs 
    rw [add_comm, ←add_assoc, add_comm, add_sub]
    congr 
    rfl 
    rw [add_comm, ←add_sub]
    simp
    rfl
  simp 
  rw [mul_add, mul_comm, ←mul_div]
  
private lemma johnson_unrefined_by_M' [Zero F] {B : Finset (Fin n → F)} 
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  B.card * ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * ((1 - e B 0 / n) ^ 2  + (e B 0) ^ 2 / ((Fintype.card F - 1) * n^2) - 1 + d B/n)
  ≤
  ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * d B/n := by 
  rw [mul_comm (B.card : ℚ)]
  rw [mul_assoc, ←mul_div]
  apply (mul_le_mul_left (by {
    field_simp
    omega
  })).2
  exact johnson_unrefined_by_M h_n h_B h_card
  
private lemma johnson_denom [Zero F] {B : Finset (Fin n → F)} 
  (h_card : 2 ≤ (Fintype.card F))
  :
  ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * ((1 - e B 0 / n) ^ 2  + (e B 0) ^ 2 / ((Fintype.card F - 1) * n^2) - 1 + d B/n)
  = 
  (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (e B 0 / n)) ^ 2 - (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (d B/n))  := by 
  have h : (((1:ℚ)- e B 0 / (↑n : ℚ)) ^ 2 + e B 0 ^ 2 / ((↑(Fintype.card F) - 1) * ↑n ^ 2) - 1 + d B / ↑n)
    = d B / (↑n : ℚ) - 2 * e B 0 / (↑n : ℚ) + ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (e B 0)^2/n^2 := by 
    have h : e B 0 ^ 2 / ((↑(Fintype.card F) - 1) * ↑n ^ 2) = (((Fintype.card F : ℚ) / (Fintype.card F - 1))- 1) * e B 0 ^ 2 / ↑n ^ 2 := by
     have h : ((Fintype.card F : ℚ) / (↑(Fintype.card F) - 1) - 1) = 1 / (↑(Fintype.card F) - 1) := by
       have h : (Fintype.card F : ℚ) / (Fintype.card F - 1) = ((Fintype.card F : ℚ) - 1 + 1) / (Fintype.card F - 1) := by
         field_simp
       rw [h]
       rw [add_div]
       rw [Field.div_eq_mul_inv]
       rw [Field.mul_inv_cancel _ (by {
          intro contr 
          have h : (Fintype.card F : ℚ) = 1 := by 
            rw [←add_zero 1]
            rw [←contr]
            simp
          simp at h 
          omega
        })]
       field_simp
     rw [h]
     field_simp
    rw [h]
    ring_nf 
  rw [h]
  conv =>
    lhs 
    rw [mul_add, mul_sub, sub_add]
    rfl
  have h : (↑(Fintype.card F) / (↑(Fintype.card F) - 1) * (2 * e B 0 / ↑n) -
    ↑(Fintype.card F) / (↑(Fintype.card F) - 1) *
      (↑(Fintype.card F) / (↑(Fintype.card F) - 1) * e B 0 ^ 2 / ↑n ^ 2)) =
        (1 - (1 - (↑(Fintype.card F) / (↑(Fintype.card F) - 1) * e B 0 / ↑n ))^2) := by 
      ring_nf
  rw [h]
  ring

private lemma johnson_bound₀ [Zero F] {B : Finset (Fin n → F)} 
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  B.card * 
    ((1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (e B 0 / n)) ^ 2 
      - (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (d B/n)))  ≤
  ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * d B/n := by 
  rw [←johnson_denom h_card]
  rw [←mul_assoc]
  exact johnson_unrefined_by_M' h_n h_B h_card


protected lemma johnson_bound_lemma [Field F] {B : Finset (Fin n → F)} {v : Fin n → F}
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  B.card * 
    ((1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (e B v / n)) ^ 2 
      - (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (d B/n)))  ≤
  ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * d B/n := by 
  rw [lin_shift_e (B := B) (by omega)]
  rw [lin_shift_d h_B]
  rw [lin_shift_card (B := B) (v := v)]
  exact johnson_bound₀ h_n (by {
      rw [←lin_shift_card (B := B)]
      assumption
    })
    h_card

protected lemma a_lemma_im_not_proud_of {v a : Fin n → F}     
  (h_card : 2 ≤ Fintype.card F)
  :
  |(1 : ℚ) - ((1 : ℚ) + (1 : ℚ) / ((Fintype.card F : ℚ) - 1)) * ↑Δ₀(v, a) / ↑n|
   ≤ 1 := by
  simp 
  by_cases hn : n = 0 <;> try simp [hn]
  have hn : 0 < n := by omega
  by_cases heq : v = a <;> try simp [heq]
  rw [abs_le]
  apply And.intro 
  · simp 
    rw [←mul_div]
    apply le_trans (b := (2 : ℚ) * (↑Δ₀(v, a) / ↑n))
    rw [mul_comm, mul_comm (2 : ℚ) _, mul_le_mul_left]
    suffices h : ((Fintype.card F : ℚ) - 1)⁻¹ ≤ 1 by { 
      have h' : (2 : ℚ) = 1 + 1 := by ring 
      rw [h'] 
      apply add_le_add
      simp
      assumption
    }
    apply (le_of_mul_le_mul_left (a := (↑(Fintype.card F : ℚ) - 1))) (a0 := by 
      {
        simp
        omega
      })
    rw [Field.mul_inv_cancel _ (by {
      intro contr
      have h : (Fintype.card F : ℚ) = 1 := by
        rw [←zero_add (1 :ℚ)]
        rw [←contr]
        simp
      simp at h 
      omega
    })]
    simp 
    apply le_of_add_le_add_right (a := 1)
    ring_nf
    simp 
    assumption
    field_simp
    assumption 
    ring_nf 
    conv =>
      rhs 
      rw [←mul_one (2 : ℚ)]
      rfl 
    rw [mul_comm]
    apply (mul_le_mul_left (by simp)).2
    have h : (↑Δ₀(v, a) : ℚ) ≤ ↑n := by
      simp [hammingDist]
      apply le_trans
      apply Finset.card_le_univ
      simp
    rw [mul_comm]
    apply le_trans 
    apply (mul_le_mul_left (by simp [hn])).2 h
    rw [mul_comm]
    rw [Field.mul_inv_cancel _ (by {
      simp 
      omega
    })]
  · simp
    rw [←mul_div, mul_nonneg_iff]
    left 
    apply And.intro 
    · apply le_trans (b := 1) (by simp)
      simp
      omega 
    · rw [Field.div_eq_mul_inv]
      rw [mul_nonneg_iff]
      left 
      simp

end

end JohnsonBound
