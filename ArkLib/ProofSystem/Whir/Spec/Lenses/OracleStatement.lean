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
  (num_vars : ℕ)
  (idx : OracleIdxPre)
: OracleInterface (OracleStatementPre domain num_vars idx) where
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
instance oracleInterface
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (idx : OracleIdx)
: OracleInterface (OracleStatement domain num_vars idx) where
  Query := match idx with
    | .WeightPolynomial => (oracleInterfacePre domain num_vars .WeightPolynomial).Query
    | .CodeWord => (oracleInterfacePre domain num_vars .CodeWord).Query
    | .CodeWordPolynomial => Fin num_vars → F
  toOC.spec := match idx with
    | .WeightPolynomial => (oracleInterfacePre domain num_vars .WeightPolynomial).toOC.spec
    | .CodeWord => (oracleInterfacePre domain num_vars .CodeWord).toOC.spec
    | .CodeWordPolynomial => (Fin num_vars → F) →ₒ F
  toOC.impl input := match idx with
    | .WeightPolynomial => (oracleInterfacePre domain num_vars .WeightPolynomial).toOC.impl input
    | .CodeWord => (oracleInterfacePre domain num_vars .CodeWord).toOC.impl input
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
    | .WeightPolynomial => (oracleInterface domain num_vars .WeightPolynomial).Query
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).Query
    | .CodeWordPolynomial => (oracleInterface domain num_vars .CodeWordPolynomial).Query
    | .SumcheckResult => F
    | .SumcheckChallenges => Fin num_sumcheck_rounds
  toOC.spec := match idx with
    | .WeightPolynomial => (oracleInterface domain num_vars .WeightPolynomial).toOC.spec
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).toOC.spec
    | .CodeWordPolynomial => (oracleInterface domain num_vars .CodeWordPolynomial).toOC.spec
    | .SumcheckResult => F →ₒ F
    | .SumcheckChallenges => fun _ => F
  toOC.impl input := match idx with
    | .WeightPolynomial => (oracleInterface domain num_vars .WeightPolynomial).toOC.impl input
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
  (OuterStmtIn := Statement domain)
  (InnerStmtIn := Sumcheck.Spec.StatementRound F num_vars 0)
  (InnerStmtOut := Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
  (OuterStmtOut :=
    (Statement domain) ×
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
  -- Create the sumcheck starting oracle statement from the whir statement and oracle statement
  materializeInput whirStatement whirOStatement := fun idx => match idx with
    | .mvPoly => composePolynomials
      (whirOStatement .CodeWordPolynomial)
      (whirOStatement .WeightPolynomial)
    | .responsePoly => fun x => Fin.elim0 x
    | .challenges => fun x => Fin.elim0 x

  -- With access to the whir OStatement, create an implementation for the sumcheck oracle
  --  (the multivariate polynomial)
  -- Would survive the weight polynomial being moved into the oracle statement,
  --  as it can use queryBind to evaluate the whir oracles
  simulateInput whirStatement oracleIdx :=
    let data : (Fin num_vars → F) := cast (by {
      obtain ⟨a,b⟩ := oracleIdx
      fin_cases a
      · rfl
      · apply Fin.elim0 b.1
      · apply Fin.elim0 b
    }) oracleIdx.2
    OracleComp.queryBind
      (Sigma.mk OracleIdx.CodeWordPolynomial data)
      (fun codeWordEvaluation : F => OracleComp.queryBind
        (Sigma.mk OracleIdx.WeightPolynomial (
          Fin.cases codeWordEvaluation data
        ))
        (fun weightPolyEvaluation : F => do return (cast (by {
          obtain ⟨a,b⟩ := oracleIdx
          fin_cases a
          · rfl
          · apply Fin.elim0 b.1
          · apply Fin.elim0 b
        }) weightPolyEvaluation))
      )

  simulateInput_eq := by
    intro outerStmt outerOStmt query
    obtain ⟨queryIdx, queryData⟩ := query
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.cast_ofNat]
    fin_cases queryIdx
    · simp only [Fin.zero_eta, Fin.isValue, cast_eq]
      change Fin num_vars → F at queryData
      unfold OracleInterface.answer OracleInterface.toOC
      unfold Sumcheck.Spec.instOracleInterfaceOracleStatementRound
      simp only [
        Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.cast_ofNat, Fin.isValue, ReaderT.run,
        OracleInterface.toOC, read, readThe, MonadReaderOf.read, ReaderT.read, bind_pure_comp,
        Functor.map
      ]
      conv_rhs => unfold pure Id.instMonad Applicative.toPure
      simp [eval_composePolynomials]
      rfl
    · exact Fin.elim0 queryData.1
    · exact Fin.elim0 queryData

  liftStmt whirStatementIn sumcheckStatementOut :=
    (whirStatementIn, sumcheckStatementOut)

  materializeOutput whirOracle sumcheckOracle idx := match idx with
    | .WeightPolynomial => whirOracle .WeightPolynomial
    | .CodeWord => whirOracle .CodeWord
    | .CodeWordPolynomial => whirOracle .CodeWordPolynomial
    | .SumcheckResult => (sumcheckOracle .responsePoly) ⟨num_sumcheck_rounds - 1, by grind⟩
    | .SumcheckChallenges => (sumcheckOracle .challenges)

  simulateOutput query :=
    let ⟨queryIdx, queryData⟩ := query
    let bindQuery := match queryIdx with
      | .WeightPolynomial => Sum.inl (Sigma.mk .WeightPolynomial queryData)
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
