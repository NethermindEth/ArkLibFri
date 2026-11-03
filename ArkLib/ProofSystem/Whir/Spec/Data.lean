/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dom Henderson
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Constrained
public import ArkLib.ProofSystem.Fri.Spec.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Spec.General


@[expose]
public section Public

namespace Whir.Spec

open MvPolynomial in
noncomputable def composePolynomials
  {F : Type} [Field F]
  {num_vars : ℕ}
  (f : F⦃≤ 1⦄[X Fin num_vars])
  (w : F⦃≤ 1⦄[X Fin (num_vars + 1)])
:
  F⦃≤2⦄[X Fin num_vars]
:=
  ⟨
    MvPolynomial.eval₂ MvPolynomial.C (Fin.cases f.val MvPolynomial.X) w,
    by
      rw [mem_restrictDegree]
      intros s h i
      simp only [eval₂_eq', MvPolynomial.mem_support_iff, AddMonoidAlgebra.coeff_sum,
        Finsupp.coe_finsetSum, Finset.sum_apply, coeff_C_mul, ne_eq] at h
      have h : ∃ x ∈ w.1.support, w.1.coeff x * (∏ i, ((Fin.cases (f.1 : F[X Fin num_vars]) MvPolynomial.X i) : F[X Fin num_vars] ) ^ x i).coeff s ≠ 0 :=
        Finset.exists_ne_zero_of_sum_ne_zero h
      rcases h with ⟨x, ⟨x_in, h⟩⟩
      simp only [ne_eq, mul_eq_zero, not_or] at h
      have x_le : ∀ i, x i ≤ 1 := by
            have bla := w.2
            rw [mem_restrictDegree] at bla
            exact bla x x_in
      have : x 0 = 0 ∨ x 0 = 1 := by grind
      rcases this with x_eq | x_eq
      · have : ∀ i, s i = x i.succ := by
          intros i
          have h := h.2
          have :
              MvPolynomial.monomial
                ⟨
                  (x.1 \ {0}).image
                    (fun n ↦
                      ⟨n.1 - 1, by rcases num_vars <;> [(exfalso; exact Fin.elim0 i); omega]⟩
                    ),
                  fun (i : Fin num_vars) ↦ x i.succ,
                  by
                    intros a
                    simp only [Finset.mem_image, Finset.mem_sdiff, Finsupp.mem_support_iff, ne_eq,
                      Finset.mem_singleton]
                    apply Iff.intro
                    · rintro ⟨a', h'⟩
                      rw [←h'.2]
                      grind
                    · intros h
                      exists a.succ
                      simpa using h
                ⟩ (1 : F) = ∏ i, X i ^ x i.succ := by
            simp [MvPolynomial.monomial_eq]
          simp only [Fin.prod_univ_succ, Fin.cases_zero, x_eq, pow_zero, Fin.cases_succ,
            one_mul] at h
          rw [←this] at h
          simp only [coeff_monomial, ite_eq_right_iff, one_ne_zero, imp_false,
            Decidable.not_not] at h
          rw [←h]
          simp
        rw [this]
        grind
      · have h := h.2
        simp only [Fin.prod_univ_succ, Fin.cases_zero, x_eq, pow_one, Fin.cases_succ, MvPolynomial.coeff_mul] at h
        have h := Finset.exists_ne_zero_of_sum_ne_zero h
        rcases h with ⟨⟨s₀, s₁⟩, hₛ, h⟩
        simp at hₛ
        simp only [← hₛ, Finsupp.coe_add, Pi.add_apply, ge_iff_le]
        simp only [ne_eq, mul_eq_zero, not_or] at h
        have : s₀ i ≤ 1 := by
          have bla := f.2
          rw [mem_restrictDegree] at bla
          specialize bla s₀
          apply bla
          simpa using h.1
        have : s₁ i ≤ 1 := by
          have : s₁ i = x i.succ := by
            have h := h.2
            have :
                MvPolynomial.monomial
                  ⟨
                    (x.1 \ {0}).image
                      (fun n ↦
                        ⟨n.1 - 1, by rcases num_vars <;> [(exfalso; exact Fin.elim0 i); omega]⟩
                      ),
                    fun (i : Fin num_vars) ↦ x i.succ,
                    by
                      intros a
                      simp only [Finset.mem_image, Finset.mem_sdiff, Finsupp.mem_support_iff, ne_eq,
                        Finset.mem_singleton]
                      apply Iff.intro
                      · rintro ⟨a', h'⟩
                        rw [←h'.2]
                        grind
                      · intros h
                        exists a.succ
                        simpa using h
                  ⟩ (1 : F) = ∏ i, X i ^ x i.succ := by
              simp [MvPolynomial.monomial_eq]
            rw [←this] at h
            simp only [coeff_monomial, ite_eq_right_iff, one_ne_zero, imp_false,
              Decidable.not_not] at h
            rw [←h]
            simp
          grind
        linarith
  ⟩

lemma eval_composePolynomials
  {F : Type} [Field F]
  {num_vars : ℕ}
  {points : Fin num_vars → F}
  {f}
  {w}
:
  MvPolynomial.eval points (composePolynomials f w).val =
  let f_val := MvPolynomial.eval points f.val
  MvPolynomial.eval (Fin.cases f_val points) w.val
:= by
  simp [
    composePolynomials,
    MvPolynomial.eval_eq',
    MvPolynomial.eval₂_eq_eval_map
  ]
  rewrite [MvPolynomial.support_map_of_injective]
  have : ∀ x ∈ w.val.support, ∀ i, x i ≤ 1 := by
    intro x h_x i
    have := w.2
    rewrite [MvPolynomial.mem_restrictDegree] at this
    exact this x h_x i
  . congr
    funext w_support
    simp [MvPolynomial.coeff_map, mul_assoc]
    rewrite [←Finset.mul_sum]
    simp
    set x := w.val.coeff w_support
    have : x = 0 ∨ ¬(x = 0) := by grind
    obtain h_x | h_x := this
    . grind
    . simp [h_x, Fin.prod_univ_succ]
      have : w_support 0 ≤ 1 := by grind
      have : w_support 0 = 0 ∨ w_support 0 = 1 := by grind
      obtain h_w_support | h_w_support := this
      . simp [h_w_support]
        rewrite [MvPolynomial.prod_X_pow]
        simp
        grind
      . simp [
          h_w_support,
          MvPolynomial.prod_X_pow
        ]
        rewrite [←mul_assoc, mul_comm (b := f.val), mul_assoc]
        simp [
          MvPolynomial.C_mul_monomial,
          MvPolynomial.coeff_mul
        ]


        done
    done
  . apply MvPolynomial.C_injective
  grind




section Definitions

open MvPolynomial

structure Statement
  {F : Type} [Field F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
where
  target : F

abbrev OracleIdxPre := Fin 2
abbrev OracleIdxPre.WeightPolynomial : OracleIdxPre := 0
abbrev OracleIdxPre.CodeWord : OracleIdxPre := 1

abbrev OracleIdx := Fin 3
abbrev OracleIdx.WeightPolynomial : OracleIdx := 0
abbrev OracleIdx.CodeWord : OracleIdx := 1
abbrev OracleIdx.CodeWordPolynomial : OracleIdx := 2

--TODO rename
abbrev OracleIdxMid := Fin 5
abbrev OracleIdxMid.WeightPolynomial : OracleIdxMid := 0
abbrev OracleIdxMid.CodeWord : OracleIdxMid := 1
abbrev OracleIdxMid.CodeWordPolynomial : OracleIdxMid := 2
abbrev OracleIdxMid.SumcheckResult : OracleIdxMid := 3
abbrev OracleIdxMid.SumcheckChallenges : OracleIdxMid := 4

@[reducible]
def OracleStatementPre
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ) -- m
  (idx : OracleIdxPre)
: Type
:= match idx with
  | .WeightPolynomial => F⦃≤1⦄[X Fin (num_vars + 1)] -- TODO generalise to higher degree
  | .CodeWord => domain.toFinset → F

@[reducible]
def OracleStatement
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ) -- m
  (idx : OracleIdx)
: Type
:= match idx with
  | .WeightPolynomial => OracleStatementPre domain num_vars .WeightPolynomial
  | .CodeWord => OracleStatementPre domain num_vars .CodeWord
  | .CodeWordPolynomial => F⦃≤1⦄[X Fin num_vars]

open Polynomial in
@[reducible]
def OracleStatementMid
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ) -- m
  (num_sumcheck_rounds : ℕ)
  (idx : OracleIdxMid)
: Type
:= match idx with
    -- ω_hat
  | .WeightPolynomial => OracleStatement domain num_vars .WeightPolynomial
    -- f
  | .CodeWord => OracleStatement domain num_vars .CodeWord
    -- f_hat
  | .CodeWordPolynomial => OracleStatement domain num_vars .CodeWordPolynomial
    -- h_k
  | .SumcheckResult => F⦃≤ 2⦄[X] -- TODO is this the correct degree for h_k
  | .SumcheckChallenges => Fin num_sumcheck_rounds → F

open MvPolynomial in
structure WitnessPreSumcheck
  (F : Type) [Field F]
  (num_vars : ℕ)
where
  -- TODO do we actually restrict the degree here?
  -- Or do we just prove in cases of appropriate degree?
  f_hat : F⦃≤ 1⦄[X Fin num_vars]

open Polynomial MvPolynomial in
structure WitnessPostSumcheck
  (F : Type) [Field F]
  (num_vars : ℕ)
where
  f_hat : F⦃≤ 1⦄[X Fin num_vars]
  h_k_hat : F⦃≤ 2⦄[X] -- this is now in both?

end Definitions


section Helpers

namespace Statement

variable {F : Type} [Field F]
  {log_order : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}
  {num_vars : ℕ}

abbrev domain_order
  (_statement : Statement domain)
: ℕ :=
  2^log_order

end Statement

abbrev code {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}
  {num_vars : ℕ}
  (statement : Statement domain)
  (oracle_statement : OracleStatement domain num_vars .WeightPolynomial)
: Set (Fin (2^log_order) → F) :=
  ReedSolomon.constrainedCode
    domain
    num_vars
    oracle_statement
    statement.target

namespace OracleStatement

abbrev num_weight_poly_vars {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}
  {num_vars : ℕ}
  (_statement : OracleStatement domain num_vars .WeightPolynomial)
: ℕ :=
  num_vars + 1

end OracleStatement

end Helpers


end Whir.Spec

end Public
