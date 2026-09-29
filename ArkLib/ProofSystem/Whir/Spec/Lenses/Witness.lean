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

def sumcheckLens
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : (Fin (num_vars + 2))) -- TODO should probably be a tighter bound
: Witness.Lens
  (OuterStmtIn := Statement domain num_vars × (∀ _ : Unit, OracleStatement domain))
  (InnerStmtOut :=
    Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds ×
    (∀ i : Unit, Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1) i)
  )
  (OuterWitIn := Witness)
  (InnerWitIn := Unit)
  (InnerWitOut := Unit)
  (OuterWitOut := Witness)
where
  toFunA _ := ()
  toFunB _ _ := {
    placeholder := ()
  }

end Whir.Spec.Witness

end Public
