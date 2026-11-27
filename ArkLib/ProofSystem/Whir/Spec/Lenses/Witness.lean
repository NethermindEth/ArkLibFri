/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dom Henderson
-/
module

public import ArkLib.ProofSystem.Whir.Spec.Data
public import ArkLib.OracleReduction.LiftContext.Lens
public import ArkLib.ProofSystem.Whir.Spec.Lenses.Statement

@[expose]
public section Public

namespace Whir.Spec.Witness

noncomputable def sumcheckLens
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : (Fin (num_vars + 1)))
: Witness.Lens
  (OuterStmtIn := Statement F num_vars × ((idx : OracleIdxPre) → OracleStatementPre domain idx))
  (InnerStmtOut :=
    Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds ×
    -- TODO potentially increase degree
    (∀ i, Sumcheck.Spec.OracleStatementRound F num_vars (deg := 2) num_sumcheck_rounds i)
  )
  (OuterWitIn := WitnessPreSumcheck F num_vars)
  (InnerWitIn := Sumcheck.Spec.WitnessPoly F num_vars 2)
  (InnerWitOut := Sumcheck.Spec.WitnessPoly F num_vars 2)
  (OuterWitOut := WitnessPreSumcheck F num_vars)
where
  toFunA outerIns := composePolynomials outerIns.2.f_hat outerIns.1.1.weightPolynomial
  toFunB outerIns _ := outerIns.2

end Whir.Spec.Witness

end Public
