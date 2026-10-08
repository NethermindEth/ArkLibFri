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
  (OuterStmtIn := Statement domain × ((idx : OracleIdx) → OracleStatement domain num_vars idx))
  (InnerStmtOut :=
    Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds ×
    -- TODO potentially increase degree
    (∀ i : Unit, Sumcheck.Spec.OracleStatement F num_vars (deg := 2) i)
  )
  (OuterWitIn := WitnessPreSumcheck F num_vars)
  (InnerWitIn := Unit)
  (InnerWitOut := Unit)
  (OuterWitOut := WitnessPostSumcheck F num_vars)
where
  toFunA _ := ()
  toFunB outerIns innerOuts :=
    let outerWitnessIn := outerIns.2
    let outerOracleStatementIn := outerIns.1.2
    let weightPolynomial := outerOracleStatementIn .WeightPolynomial
    let f_hat := outerWitnessIn.f_hat
    let polynomial := composePolynomials f_hat weightPolynomial
    let innerStatementOut := innerOuts.1.1
    let challenges := innerStatementOut.challenges
    -- TODO tighten bound?
    let h_k_hat :=
      if h : num_sumcheck_rounds = num_vars then
        Polynomial.C <| MvPolynomial.eval challenges (cast (by {
          rw! [h]; rfl
        }) polynomial.val)
      else
        Sumcheck.Spec.SingleRound.projectedRoundPolynomial
          (R := F)
          (n := num_vars)
          (deg := 2)
          (D := (domain : Fin (2^log_order) ↪ F))
          (i := ⟨num_sumcheck_rounds.val, by grind⟩)
          (challenges := challenges)
          (poly := polynomial)
    {
      f_hat := f_hat
      h_k_hat := sorry
    }

end Whir.Spec.Witness

end Public
