/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.CodingTheory.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Henselian
import ArkLib.Data.Fin.Basic
import ArkLib.Data.Polynomial.Interface

/-!
  # Reed-Solomon Codes

  TODO: define the Reed-Solomon code, and prove its properties.

  TODO: define the Berkelamp-Welch algorithm for unique decoding, and Guruswami-Sudan algorithm for
  list-decoding.
-/

namespace ReedSolomon

open Polynomial

variable {F : Type*} [Semiring F] {ι : Type*} (domain : ι ↪ F)

/-- The evaluation of a polynomial at a set of points specified by `domain : ι ↪ F`, as a linear
  map. -/
def evalOnPoints : F[X] →ₗ[F] (ι → F) where
  toFun := fun p => fun x => p.eval (domain x)
  map_add' := fun x y => by simp; congr
  map_smul' := fun m x => by simp; congr

/-- The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `domain`.
  -/
def code (deg : ℕ) : Submodule F (ι → F) :=
  (Polynomial.degreeLT F deg).map (evalOnPoints domain)

/-- The generator matrix of the Reed-Solomon code of degree `deg` and evaluation points `domain`. -/
def genMatrix (deg : ℕ) : Matrix (Fin deg) ι F :=
  .of fun i j => domain j ^ (i : ℕ)

/-- The (parity)-check matrix of the Reed-Solomon code, assuming `ι` is finite. -/
def checkMatrix (deg : ℕ) [Fintype ι] : Matrix (Fin (Fintype.card ι - deg)) ι F :=
  sorry

-- theorem code_by_genMatrix (deg : ℕ) :
--     code deg = codeByGenMatrix (genMatrix deg) := by
--   simp [codeByGenMatrix, code]
--   rw [LinearMap.range_eq_map]
--   sorry

open Classical
open Polynomial
open Matrix

variable {F ι ι' : Type*}
         {C : Set (ι → F)}

noncomputable section

namespace Vandermonde

/--
A non-square Vandermonde matrix.
-/
def nonsquare [Semiring F] (ι' : ℕ) (α : ι → F) : Matrix ι (Fin ι') F :=
  Matrix.of fun i j => (α i) ^ j.1

lemma nonsquare_mulVecLin [CommSemiring F] {ι' : ℕ} {α₁ : ι ↪ F} {α₂ : Fin ι' → F} {i : ι} :
  (nonsquare ι' α₁).mulVecLin α₂ i = ∑ x, α₂ x * α₁ i ^ x.1 := by
  simp [nonsquare, mulVecLin_apply, mulVec_eq_sum]

/--
  The transpose of a non-square Vandermonde matrix.
-/
def nonsquareTranspose [Field F] (ι' : ℕ) (α : ι ↪ F) : Matrix (Fin ι') ι F :=
  (Vandermonde.nonsquare ι' α)ᵀ

private lemma todoMoveOut {k : ℕ} : (List.finRange k).dedup = List.finRange k := by
  induction k <;>
  aesop (add simp [List.finRange_succ, List.dedup_map_of_injective, Fin.succ_injective])

section

variable [CommRing F] {m n : ℕ} {α : Fin m → F}

/--
  The maximal upper square submatrix of a Vandermonde matrix is a Vandermonde matrix.
-/
lemma subUpFull_of_vandermonde_is_vandermonde (h : n ≤ m) :
  Matrix.vandermonde (α ∘ Fin.castLE h) =
  Matrix.subUpFull (nonsquare n α) (Fin.castLE h) := by
  ext r c
  simp [Matrix.vandermonde, Matrix.subUpFull, nonsquare]

/--
  The maximal left square submatrix of a Vandermonde matrix is a Vandermonde matrix.
-/
lemma subLeftFull_of_vandermonde_is_vandermonde (h : m ≤ n) :
  Matrix.vandermonde α = Matrix.subLeftFull (nonsquare n α) (Fin.castLE h) := by
  ext r c
  simp [Matrix.vandermonde, Matrix.subLeftFull, nonsquare]

section

variable [IsDomain F]

/--
  The rank of a non-square Vandermonde matrix with more rows than columns is the number of columns.
-/
lemma rank_nonsquare_eq_deg_of_deg_le (inj : Function.Injective α) (h : n ≤ m) :
  (Vandermonde.nonsquare (ι' := n) α).rank = n := by
  rw [
    Matrix.rank_eq_iff_subUpFull_eq h,
    ←subUpFull_of_vandermonde_is_vandermonde,
    Matrix.rank_eq_iff_det_ne_zero,
    Matrix.det_vandermonde_ne_zero_iff
  ]
  apply Function.Injective.comp <;> aesop (add simp Fin.castLE_injective)
  
/--
  The rank of a non-square Vandermonde matrix with more columns than rows is the number of rows.
-/
lemma rank_nonsquare_eq_deg_of_ι_le (inj : Function.Injective α) (h : m ≤ n) :
  (Vandermonde.nonsquare (ι' := n) α).rank = m := by
  rw [
    Matrix.full_row_rank_via_rank_subLeftFull h,
    ← subLeftFull_of_vandermonde_is_vandermonde,
    Matrix.rank_eq_iff_det_ne_zero,
    Matrix.det_vandermonde_ne_zero_iff
  ]
  exact inj

@[simp]
lemma rank_nonsquare_rows_eq_min (inj : Function.Injective α) :
  (Vandermonde.nonsquare (ι' := n) α).rank = min m n := by
  by_cases h : m ≤ n
  · rw [rank_nonsquare_eq_deg_of_ι_le inj h]; simp [h]
  · rw [rank_nonsquare_eq_deg_of_deg_le inj] <;> omega

end

theorem mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
  {n : ℕ} [NeZero n] {v : ι ↪ F} {p : F[X]} (h_deg : p.natDegree < n) :
  (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) =
  fun i => p.eval (v i) := by
  ext i
  simp only [
    nonsquare_mulVecLin, Finset.sum_fin_eq_sum_range, eval_eq_sum
  ]
  refine Eq.symm (Finset.sum_of_injOn (·%n) ?p₁ ?p₂ (fun i _ h ↦ ?p₃) (fun i _ ↦ ?p₄))
  · aesop (add simp [Set.InjOn])
          (add safe forward [le_natDegree_of_mem_supp, lt_of_le_of_lt, Nat.lt_add_one_of_le])
          (add 10% apply (show ∀ {a b c : ℕ}, a < c → b < c → a % c = b % c → a = b from
                                 fun h₁ h₂ ↦ by aesop (add simp Nat.mod_eq_of_lt)))
          (erase simp mem_support_iff)
  · aesop (add simp Set.MapsTo) (add safe apply Nat.mod_lt) (add 1% cases Nat)
  · aesop (add safe (by specialize h i)) (add simp [Nat.mod_eq_of_lt])
  · have : i < n := by aesop (add safe forward le_natDegree_of_mem_supp)
                              (erase simp mem_support_iff)
                              (add safe (by omega))
    aesop (add simp Nat.mod_eq_of_lt) (add safe (by ring))

end

end Vandermonde

namespace ReedSolomonCode

section

variable {deg m n : ℕ} {α : Fin m → F}

section

variable [Semiring F] {p : F[X]}

lemma natDegree_lt_of_mem_degreeLT [NeZero deg] (h : p ∈ degreeLT F deg) : p.natDegree < deg := by
  by_cases p = 0
  · cases deg <;> aesop
  · aesop (add simp [natDegree_lt_iff_degree_lt, mem_degreeLT])

def encode (msg : Fin deg → F) (domain : Fin m ↪ F) : Fin m → F :=
  (polynomialOfCoeffs msg).eval ∘ ⇑domain

lemma encode_mem_ReedSolomon_code [NeZero deg] {msg : Fin deg → F} {domain : Fin m ↪ F} :
  encode msg domain ∈ ReedSolomon.code domain deg :=
  ⟨polynomialOfCoeffs msg, ⟨by simp, by ext i; simp [encode, ReedSolomon.evalOnPoints]⟩⟩

end

def makeZero (ι : ℕ) (F : Type*) [Zero F] : Fin ι → F := fun _ ↦ 0

@[simp]
lemma codewordIsZero_makeZero {ι : ℕ} {F : Type*} [Zero F] :
  makeZero ι F = 0 := by unfold makeZero; ext; rfl

open LinearCode

/--
  The Vandermonde matrix is the generator matrix for an RS code of length `ι` and dimension `deg`.
-/
lemma genMatIsVandermonde [Fintype ι] [Field F] [inst : NeZero m] {α : ι ↪ F} :
  fromColGenMat (Vandermonde.nonsquare (ι' := m) α) = ReedSolomon.code α m := by
  unfold fromColGenMat ReedSolomon.code
  ext x; rw [LinearMap.mem_range, Submodule.mem_map]
  refine ⟨
    fun ⟨coeffs, h⟩ ↦ ⟨polynomialOfCoeffs coeffs, h.symm ▸ ?p₁⟩,
    fun ⟨p, h⟩ ↦ ⟨Fin.liftF' p.coeff, ?p₂⟩
  ⟩
  · rw [
      ←coeff_polynomialOfCoeffs_eq_coeffs (coeffs := coeffs),
      Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials (by simp)
    ]
    simp [ReedSolomon.evalOnPoints]
  · exact h.2 ▸ Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
                  (natDegree_lt_of_mem_degreeLT h.1)

section

variable [Field F]

lemma dim_eq_deg_of_le [NeZero n] (inj : Function.Injective α) (h : n ≤ m) :
  dim (ReedSolomon.code ⟨α, inj⟩ n) = n := by
    rw [
       ← genMatIsVandermonde, ← rank_eq_dim_fromColGenMat, Vandermonde.rank_nonsquare_rows_eq_min
    ] <;> simp [inj, h]

@[simp]
lemma length_eq_domain_size (inj : Function.Injective α) :
  length (ReedSolomon.code ⟨α, inj⟩ deg) = m := by
  simp [length]

lemma rateOfLinearCode_eq_div [NeZero n] (inj : Function.Injective α) (h : n ≤ m) :
  rate (ReedSolomon.code ⟨α, inj⟩ n) = n / m := by
  rwa [rate, dim_eq_deg_of_le, length_eq_domain_size]

@[simp]
lemma dist_le_length (inj : Function.Injective α) : minDist (ReedSolomon.code ⟨α, inj⟩ n) ≤ m := by
  convert minDist_UB
  simp

end

lemma card_le_card_of_count_inj {α β : Type*} {s : Multiset α} {s' : Multiset β}
  {f : α → β} (inj : Function.Injective f) (h : ∀ a : α, s.count a ≤ s'.count (f a)) :
  s.card ≤ s'.card := by
    simp only [←Multiset.toFinset_sum_count_eq]
    apply le_trans (b := ∑ x ∈ s.toFinset, s'.count (f x)) (Finset.sum_le_sum (by aesop))
    rw [←Finset.sum_image (f := s'.count) (by aesop)]
    have : s.toFinset.image f ⊆ s'.toFinset :=
      suffices ∀ x ∈ s, f x ∈ s' by simpa [Finset.image_subset_iff]
      by simp_rw [←Multiset.count_pos]
         exact fun x h' ↦ lt_of_lt_of_le h' (h x)
    exact Finset.sum_le_sum_of_subset_of_nonneg this (by aesop)

section

def constantCode {α : Type*} (x : α) (ι' : Type*) [Fintype ι'] : ι' → α := fun _ ↦ x

variable [Semiring F] {x : F} [Fintype ι] {α : ι ↪ F}

@[simp]
lemma weight_constantCode :
  wt (constantCode x ι) = 0 ↔ IsEmpty ι ∨ x = 0 := by
  by_cases eq : IsEmpty ι <;> aesop (add simp [constantCode, wt_eq_zero_iff])

@[simp]
lemma constantCode_mem_code [NeZero n] :
  constantCode x ι ∈ ReedSolomon.code α n := by
  use C x
  aesop (add simp [ReedSolomon.evalOnPoints, coeff_C, degreeLT])

@[simp]
lemma constantCode_eq_ofNat_zero_iff [Nonempty ι] :
  constantCode x ι = 0 ↔ x = 0 := by
  unfold constantCode
  exact ⟨fun x ↦ Eq.mp (by simp) (congrFun x), (· ▸ rfl)⟩

@[simp]
lemma wt_constantCode [NeZero x] :
  wt (constantCode x ι) = Fintype.card ι := by unfold constantCode wt; aesop

end

open Finset in
/--
  The minimal code distance of an RS code of length `ι` and dimension `deg` is `ι - deg + 1`
-/
theorem minDist [Field F] (inj : Function.Injective α) [NeZero n] (h : n ≤ m) :
  minDist (ReedSolomon.code ⟨α, inj⟩ n) = m - n + 1 := by
  have : NeZero m := by constructor; aesop
  refine le_antisymm ?p₁ ?p₂
  case p₁ =>
    have distUB := singletonBound (LC := ReedSolomon.code ⟨α, inj⟩ n)
    rw [dim_eq_deg_of_le inj h] at distUB
    simp at distUB
    zify [dist_le_length] at distUB
    omega
  case p₂ =>
    rw [minDist_eq_minWtCodewords]
    apply le_csInf (by use m, constantCode 1 _; simp)
    intro b ⟨msg, ⟨p, p_deg, p_eval_on_α_eq_msg⟩, msg_neq_0, wt_c_eq_b⟩
    let zeroes : Finset _ := {i | msg i = 0}
    have eq₁ : zeroes.val.Nodup := by
      aesop (add simp [Multiset.nodup_iff_count_eq_one, Multiset.count_filter])
    have msg_zeros_lt_deg : #zeroes < n := by
      apply lt_of_le_of_lt (b := p.roots.card)
                           (hbc := lt_of_le_of_lt (Polynomial.card_roots' _)
                                                  (natDegree_lt_of_mem_degreeLT p_deg))
      exact card_le_card_of_count_inj inj fun i ↦
        if h : msg i = 0
        then suffices 0 < Multiset.count (α i) p.roots by
                rwa [@Multiset.count_eq_one_of_mem (d := eq₁) (h := by simpa [zeroes])]
              by aesop
        else by simp [zeroes, h]
    have : #zeroes + wt msg = m := by
      rw [wt, filter_card_add_filter_neg_card_eq_card]
      simp
    omega

end

end ReedSolomonCode
end


end ReedSolomon
