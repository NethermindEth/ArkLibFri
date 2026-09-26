/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dom Henderson
-/
module

public import ArkLib.ProofSystem.Whir.Spec.Data
public import ArkLib.OracleReduction.LiftContext.Lens

@[expose]
public section Public

namespace Whir.Spec.Statement

def sumcheckLens
  {F : Type} [Field F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : (Fin (num_vars + 2))) -- TODO should probably be a tighter bound
: Statement.Lens
  (OuterStmtIn := Statement domain num_vars)
  (InnerStmtIn := Sumcheck.Spec.StatementRound F (num_vars + 1) 0)
  (InnerStmtOut := Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
  (OuterStmtOut :=
    (Statement domain num_vars) ×
    (Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
  )
where
  toFunA (x : Statement domain num_vars) := {
    target := x.target
    challenges := fun x => nomatch x
    : Sumcheck.Spec.StatementRound F (num_vars + 1) 0
  }
  toFunB x y := ⟨x, y⟩

-- TODO prove maintainance of properties

end Whir.Spec.Statement

end Public
