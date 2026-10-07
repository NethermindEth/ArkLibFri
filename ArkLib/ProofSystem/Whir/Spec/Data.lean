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
abbrev OracleIdxMid := Fin 4
abbrev OracleIdxMid.WeightPolynomial : OracleIdxMid := 0
abbrev OracleIdxMid.CodeWord : OracleIdxMid := 1
abbrev OracleIdxMid.CodeWordPolynomial : OracleIdxMid := 2
abbrev OracleIdxMid.SumcheckResult : OracleIdxMid := 3

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

open MvPolynomial in
structure Witness
  (F : Type) [Field F]
  (num_vars : ℕ)
where
  -- TODO do we actually restrict the degree here?
  -- Or do we just prove in cases of appropriate degree?
  f_hat : F⦃≤ 1⦄[X Fin num_vars]

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
