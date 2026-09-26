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
  (num_vars : ℕ) -- m
where
  weight_polynomial : F⦃≤1⦄[X Fin (num_vars + 1)] -- TODO generalise to higher degree
  target : F

structure OracleStatement
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
where
  codeword : domain.toFinset → F

end Definitions


section Helpers

namespace Statement

variable {F : Type} [Field F]
  {log_order : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}
  {num_vars : ℕ}

abbrev domain_order
  (_statement : Statement domain num_vars)
: ℕ :=
  2^log_order

abbrev code
  (statement : Statement domain num_vars)
: Set (Fin (2^log_order) → F) :=
  ReedSolomon.constrainedCode
    domain
    num_vars
    statement.weight_polynomial
    statement.target

abbrev num_weight_poly_vars
  (_statement : Statement domain num_vars)
: ℕ :=
  num_vars + 1

end Statement

end Helpers


end Whir.Spec

end Public
