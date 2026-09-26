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

namespace Whir.Spec.OracleStatement

def sumcheckLens
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : (Fin (num_vars + 2)))
  [OracleInterface (OracleStatement domain)]
: OracleStatement.Lens
  (OuterStmtIn := Statement domain num_vars)
  (InnerStmtIn := Sumcheck.Spec.StatementRound F (num_vars + 1) 0)
  (InnerStmtOut := Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
  (OuterStmtOut :=
    (Statement domain num_vars) ×
    (Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
  )
  (OuterOStmtIn := fun _ : Unit => OracleStatement domain)
  (InnerOStmtIn := Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1))
  (InnerOStmtOut := Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1))
  (OuterOStmtOut := fun _ : Unit =>
    OracleStatement domain ×
    Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1) ()
  )
where
  toFunA (x : Statement domain num_vars × (∀ _ : Unit, OracleStatement domain)) := ⟨
    (Statement.sumcheckLens domain num_vars num_sumcheck_rounds).proj x.1,
    fun _ => x.1.weight_polynomial
  ⟩

  toFunB
    (x : Statement domain num_vars × (Unit → OracleStatement domain))
    (y: Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds ×
      ((i : Unit) → Sumcheck.Spec.OracleStatement F (num_vars + 1) 1 i))
  := ⟨
    ⟨x.1,  y.1⟩,
    fun _ => ⟨x.2 (), y.2 ()⟩
  ⟩

end Whir.Spec.OracleStatement

end Public
