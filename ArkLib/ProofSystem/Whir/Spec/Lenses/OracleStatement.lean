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
instance oracleInterfacePre
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (idx : OracleIdxPre)
: OracleInterface (OracleStatementPre domain idx) where
  Query := match idx with
      | .CodeWord => domain.toFinset
  toOC.spec := fun _ => F
  toOC.impl input := do
    let oracle_statement ← read
    match h : idx with
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
instance oracleInterface
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (idx : OracleIdx)
: OracleInterface (OracleStatement domain num_vars idx) where
  Query := match idx with
    | .CodeWord => (oracleInterfacePre domain .CodeWord).Query
    | .CodeWordPolynomial => Fin num_vars → F
  toOC.spec := match idx with
    | .CodeWord => (oracleInterfacePre domain .CodeWord).toOC.spec
    | .CodeWordPolynomial => (Fin num_vars → F) →ₒ F
  toOC.impl input := match idx with
    | .CodeWord => (oracleInterfacePre domain .CodeWord).toOC.impl input
    | .CodeWordPolynomial => do
      let data ← read
      let vals : Fin num_vars → F := input
      let poly : F⦃≤1⦄[X Fin num_vars] := data
      return MvPolynomial.eval vals poly

open Polynomial in
instance oracleInterfaceMid
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ)
  (idx : OracleIdxMid)
: OracleInterface (OracleStatementMid domain num_vars num_sumcheck_rounds idx) where
  Query := match idx with
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).Query
    | .CodeWordPolynomial => (oracleInterface domain num_vars .CodeWordPolynomial).Query
    | .SumcheckResult => F
    | .SumcheckChallenges => Fin num_sumcheck_rounds
  toOC.spec := match idx with
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).toOC.spec
    | .CodeWordPolynomial => (oracleInterface domain num_vars .CodeWordPolynomial).toOC.spec
    | .SumcheckResult => F →ₒ F
    | .SumcheckChallenges => fun _ => F
  toOC.impl input := match idx with
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).toOC.impl input
    | .CodeWordPolynomial => (oracleInterface domain num_vars .CodeWordPolynomial).toOC.impl input
    | .SumcheckResult => do
      let vals : F := input
      let poly : F⦃≤2⦄[X] ← read
      return Polynomial.eval vals poly
    | .SumcheckChallenges => do
      let idx : Fin num_sumcheck_rounds := input
      let challenges : Fin num_sumcheck_rounds → F ← read
      return challenges idx

noncomputable def sumcheckExecutableLens
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : (Fin (num_vars + 1)))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
: OracleStatement.ExecutableLens
  (OuterStmtIn := Statement F num_vars)
  (InnerStmtIn := Sumcheck.Spec.StatementRound F num_vars 0)
  (InnerStmtOut := Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
  (OuterStmtOut :=
    (Statement F num_vars) ×
    (Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
  )
  (OuterOStmtIn := OracleStatement domain num_vars)
  (InnerOStmtIn := Sumcheck.Spec.OracleStatementRound F num_vars (deg := 2) 0)
  (InnerOStmtOut := Sumcheck.Spec.OracleStatementRound F num_vars (deg := 2) num_sumcheck_rounds)
  (OuterOStmtOut := OracleStatementMid domain num_vars num_sumcheck_rounds)
where
  -- Create the sumcheck starting statement from the whir statement
  projStmt whirStatement := {
    target := whirStatement.target
    challenges := !v[]
  }
  materializeInput _ _ := fun idx => match idx with
    | .responsePoly => fun x => Fin.elim0 x
    | .challenges => fun x => Fin.elim0 x

  simulateInput _ q := match q with
    | ⟨⟨0, _⟩, data⟩ => Fin.elim0 data.1
    | ⟨⟨1, _⟩, data⟩ => Fin.elim0 data

  simulateInput_eq := by
    intro _ _ q
    obtain ⟨idx, data⟩ := q
    fin_cases idx
    · exact Fin.elim0 data.1
    · exact Fin.elim0 data

  liftStmt whirStatementIn sumcheckStatementOut :=
    (whirStatementIn, sumcheckStatementOut)

  materializeOutput whirOracle sumcheckOracle idx := match idx with
    | .CodeWord => whirOracle .CodeWord
    | .CodeWordPolynomial => whirOracle .CodeWordPolynomial
    | .SumcheckResult => (sumcheckOracle .responsePoly) ⟨num_sumcheck_rounds - 1, by grind⟩
    | .SumcheckChallenges => (sumcheckOracle .challenges)

  simulateOutput query :=
    let ⟨queryIdx, queryData⟩ := query
    let bindQuery := match queryIdx with
      | .CodeWord => Sum.inl (Sigma.mk .CodeWord queryData)
      | .CodeWordPolynomial => Sum.inl (Sigma.mk .CodeWordPolynomial queryData)
      | .SumcheckResult => Sum.inr (Sigma.mk .responsePoly (
          ⟨num_sumcheck_rounds - 1, by grind⟩,
          queryData
        ))
      | .SumcheckChallenges => Sum.inr (Sigma.mk .challenges queryData)
    OracleComp.queryBind bindQuery (fun x => do
      return (cast (by {
        subst bindQuery
        split
        all_goals {
          rfl
        }
      }) x)
    )

  simulateOutput_eq := by
    intro outerOStmt innerOStmt q
    obtain ⟨i, q⟩ := q
    fin_cases i <;> rfl


end Whir.Spec.OracleStatement

end Public
