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

abbrev OracleIdx := Fin 2
abbrev OracleIdx.WeightPolynomial : OracleIdx := 0
abbrev OracleIdx.CodeWord : OracleIdx := 1

--TODO rename
abbrev OracleIdxMid := Fin 3
abbrev OracleIdxMid.WeightPolynomial : OracleIdxMid := 0
abbrev OracleIdxMid.CodeWord : OracleIdxMid := 1
abbrev OracleIdxMid.Sumcheck : OracleIdxMid := 2

@[reducible]
def OracleStatement
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ) -- m
  (idx : OracleIdx)
: Type
:= match idx with
  | .WeightPolynomial => F⦃≤1⦄[X Fin (num_vars + 1)] -- TODO generalise to higher degree
  | .CodeWord => domain.toFinset → F

@[reducible]
def OracleStatementMid
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ) -- m
  (idx : OracleIdxMid)
: Type
:= match idx with
  | .WeightPolynomial => OracleStatement domain num_vars .WeightPolynomial
  | .CodeWord => OracleStatement domain num_vars .CodeWord
  | .Sumcheck => Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1) ()

open MvPolynomial in
structure Witness
  (F : Type) [Field F]
  (num_vars : ℕ)
where
  f_hat : F[X Fin num_vars]

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
