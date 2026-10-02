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

open MvPolynomial in
instance oracleInterface
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (idx : OracleIdx)
: OracleInterface (OracleStatement domain num_vars idx) where
  Query := match idx with
      | .WeightPolynomial => (Fin (num_vars + 1) → F)
      | .CodeWord => domain.toFinset
  toOC.spec := fun _ => F
  toOC.impl input := do
    let oracle_statement ← read
    match h : idx with
      | .WeightPolynomial =>
        let vals : Fin (num_vars + 1) → F := cast (by aesop) input
        let poly : F⦃≤1⦄[X Fin (num_vars + 1)] := cast (by aesop) oracle_statement
        return MvPolynomial.eval vals poly
      | .CodeWord =>
        let point : domain.toFinset := cast (by {
          rw! [h]
          rfl
        }) input
        let codeword : domain.toFinset → F := cast (by {
          rw! [h]
          rfl
        }) oracle_statement
        return codeword point

open MvPolynomial in
instance oracleInterfaceMid
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (idx : OracleIdxMid)
: OracleInterface (OracleStatementMid domain num_vars idx) where
  Query := match idx with
    | .WeightPolynomial => (oracleInterface domain num_vars .WeightPolynomial).Query
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).Query
    | .Sumcheck => Fin (num_vars + 1) → F
  toOC.spec := match idx with
    | .WeightPolynomial => (oracleInterface domain num_vars .WeightPolynomial).toOC.spec
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).toOC.spec
    | .Sumcheck => (Fin (num_vars + 1) → F) →ₒ F
  toOC.impl input := do
    let data ← read
    match h : idx with
      | .WeightPolynomial =>
        let vals : Fin (num_vars + 1) → F := cast (by aesop) input
        let poly : F⦃≤1⦄[X Fin (num_vars + 1)] := cast (by aesop) data
        return (cast (by {
          rw! (castMode := .all) [h]
          rfl
        }) (MvPolynomial.eval vals poly))
      | .CodeWord =>
        let point : domain.toFinset := cast (by {
          rw! [h]
          rfl
        }) input
        let codeword : domain.toFinset → F := cast (by {
          rw! [h]
          rfl
        }) data
        return (cast (by {
          rw! (castMode := .all) [h]
          rfl
        }) (codeword point))
      | .Sumcheck =>
        let vals : Fin (num_vars + 1) → F := cast (by aesop) input
        let poly : F⦃≤1⦄[X Fin (num_vars + 1)] := cast (by aesop) data
        return (cast (by {
          rw! (castMode := .all) [h]
          rfl
        }) (MvPolynomial.eval vals poly))


def sumcheckLens
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : (Fin (num_vars + 2)))
: OracleStatement.Lens
  (OuterStmtIn := Statement domain)
  (InnerStmtIn := Sumcheck.Spec.StatementRound F (num_vars + 1) 0)
  (InnerStmtOut := Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
  (OuterStmtOut :=
    (Statement domain) ×
    (Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
  )
  (OuterOStmtIn := OracleStatement domain num_vars)
  (InnerOStmtIn := Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1))
  (InnerOStmtOut := Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1))
  (OuterOStmtOut := OracleStatementMid domain num_vars)
where
  toFunA (x : Statement domain × (∀ idx : OracleIdx, OracleStatement domain num_vars idx)) := ⟨
    (Statement.sumcheckLens domain num_vars num_sumcheck_rounds).proj x.1,
    fun _ => (x.2 .WeightPolynomial)
  ⟩

  toFunB x y := ⟨
    ⟨x.1,  y.1⟩,
    fun idx => match idx with
      | .WeightPolynomial => x.2 .WeightPolynomial
      | .CodeWord => x.2 .CodeWord
      | .Sumcheck => y.2 ()
  ⟩

-- def OStmtOut
--   {F : Type} [Field F] [DecidableEq F]
--   {log_order : ℕ}
--   (domain : Domain.SmoothCosetFftDomain log_order F)
--   (num_vars : ℕ)
--   (i : Fin 2)
-- := match i with
--   | 0 => OracleStatement domain num_vars
--   | 1 => Sumcheck.Spec.OracleStatement F (num_vars + 1) 1 ()

-- instance
--   {F : Type} [Field F] [DecidableEq F]
--   {log_order : ℕ}
--   (domain : Domain.SmoothCosetFftDomain log_order F)
--   (num_vars : ℕ)
--   (i : Fin 2)
-- : OracleInterface (OStmtOut domain num_vars i) := match i with
--   | 0 => inferInstanceAs (OracleInterface (OracleStatement domain))
--   | 1 => inferInstanceAs (OracleInterface (Sumcheck.Spec.OracleStatement F (num_vars + 1) 1 ()))

-- instance
--   {F : Type} [Field F] [DecidableEq F]
--   {log_order : ℕ}
--   (domain : Domain.SmoothCosetFftDomain log_order F)
--   (num_vars : ℕ)
--   (i : Fin 2)
-- : OracleInterface (OStmtOut domain num_vars i) where
--   Query := match i with
--     | 0 => (oracleInterface domain num_vars).Query
--     | 1 => Fin (num_vars + 1) → F
--   toOC.spec := match i with
--     | 0 => (oracleInterface domain num_vars).spec
--     | 1 => (Fin (num_vars + 1) → F) →ₒ F
--   toOC.impl := match i with
--     | 0 => (oracleInterface domain num_vars).toOC.impl
--     | 1 => fun points => do return (← read).1.eval points

def sumcheckExecutableLens
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : (Fin (num_vars + 2)))
: OracleStatement.ExecutableLens
  (OuterStmtIn := Statement domain)
  (InnerStmtIn := Sumcheck.Spec.StatementRound F (num_vars + 1) 0)
  (InnerStmtOut := Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
  (OuterStmtOut :=
    (Statement domain) ×
    (Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
  )
  (OuterOStmtIn := OracleStatement domain num_vars)
  (InnerOStmtIn := Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1))
  (InnerOStmtOut := Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1))
  (OuterOStmtOut := OracleStatementMid domain num_vars)
where
  -- Create the sumcheck starting statement from the whir statement
  projStmt whirStatement := {
    target := whirStatement.target
    challenges := !v[]
  }
  -- Create the sumcheck starting oracle statement from the whir statement and oracle statement
  materializeInput whirStatement whirOStatement := fun _ => (whirOStatement .WeightPolynomial)

  -- With access to the whir OStatement, create an implementation for the sumcheck oracle
  --  (the multivariate polynomial)
  -- Would survive the weight polynomial being moved into the oracle statement,
  --  as it can use queryBind to evaluate the whir oracles
  simulateInput whirStatement oracleIdx :=
    OracleComp.queryBind
      (Sigma.mk .WeightPolynomial oracleIdx.2)
      (fun response => do return response)

  simulateInput_eq := by
    intro outerStmt outerOStmt query
    rfl

  liftStmt whirStatementIn sumcheckStatementOut :=
    (whirStatementIn, sumcheckStatementOut)

  materializeOutput whirOracle sumcheckOracle idx := match idx with
    | .WeightPolynomial => whirOracle .WeightPolynomial
    | .CodeWord => whirOracle .CodeWord
    | .Sumcheck => sumcheckOracle ()

  simulateOutput query :=
    let ⟨queryIdx, queryData⟩ := query
    let bindQuery := match queryIdx with
      | .WeightPolynomial => Sum.inl (Sigma.mk .WeightPolynomial queryData)
      | .CodeWord => Sum.inl (Sigma.mk .CodeWord queryData)
      | .Sumcheck => Sum.inr (Sigma.mk () queryData)
    OracleComp.queryBind bindQuery (fun x => do
      return (cast (by {
        rcases eq : bindQuery with a | a
        · have : queryIdx = .WeightPolynomial ∨ queryIdx = .CodeWord := by
            fin_cases queryIdx <;> grind
          obtain this | this := this
          all_goals rw! (castMode := .all) [this]
          all_goals rfl
        · have : queryIdx = .Sumcheck := by
            fin_cases queryIdx <;> grind
          rw! (castMode := .all) [this]
          rfl
      }) x)
    )

  simulateOutput_eq := by
    intro outerOStmt innerOStmt q
    obtain ⟨i, q⟩ := q
    fin_cases i <;> rfl


end Whir.Spec.OracleStatement

end Public
