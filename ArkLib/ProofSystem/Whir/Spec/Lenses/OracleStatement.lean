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
  (idx : OracleIdxMid)
: OracleInterface (OracleStatementMid domain num_vars idx) where
  Query := match idx with
    | .WeightPolynomial => (oracleInterface domain num_vars .WeightPolynomial).Query
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).Query
    | .CodeWordPolynomial => (oracleInterface domain num_vars .CodeWordPolynomial).Query
    | .SumcheckResult => F
  toOC.spec := match idx with
    | .WeightPolynomial => (oracleInterface domain num_vars .WeightPolynomial).toOC.spec
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).toOC.spec
    | .CodeWordPolynomial => (oracleInterface domain num_vars .CodeWordPolynomial).toOC.spec
    | .SumcheckResult => F →ₒ F
  toOC.impl input := match idx with
    | .WeightPolynomial => (oracleInterface domain num_vars .WeightPolynomial).toOC.impl input
    | .CodeWord => (oracleInterface domain num_vars .CodeWord).toOC.impl input
    | .CodeWordPolynomial => (oracleInterface domain num_vars .CodeWordPolynomial).toOC.impl input
    | .SumcheckResult => do
      let data ← read
      let vals : F := input
      let poly : F⦃≤2⦄[X] := data
      return Polynomial.eval vals poly

open MvPolynomial in
def composePolynomials
  {F : Type} [Field F]
  {num_vars : ℕ}
  (f : F⦃≤ 1⦄[X Fin num_vars])
  (w : F⦃≤ 1⦄[X Fin (num_vars + 1)])
:
  F⦃≤2⦄[X Fin num_vars]
:=
  --λ ..b => w(f(..b), ..b)
  sorry


-- def sumcheckLens
--   {F : Type} [Field F] [DecidableEq F]
--   {log_order : ℕ}
--   (domain : Domain.SmoothCosetFftDomain log_order F)
--   (num_vars : ℕ)
--   (num_sumcheck_rounds : (Fin (num_vars + 1)))
-- : OracleStatement.Lens
--   (OuterStmtIn := Statement domain)
--   (InnerStmtIn := Sumcheck.Spec.StatementRound F num_vars 0)
--   (InnerStmtOut := Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
--   (OuterStmtOut :=
--     (Statement domain) ×
--     (Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
--   )
--   (OuterOStmtIn := OracleStatement domain num_vars)
--   (InnerOStmtIn := Sumcheck.Spec.OracleStatement F num_vars (deg := 2))
--   (InnerOStmtOut := Sumcheck.Spec.OracleStatement F num_vars (deg := 2))
--   (OuterOStmtOut := OracleStatementMid domain num_vars)
-- where
--   toFunA (x : Statement domain × (∀ idx : OracleIdx, OracleStatement domain num_vars idx)) := ⟨
--     (Statement.sumcheckLens domain num_vars num_sumcheck_rounds).proj x.1,
--     fun _ => composePolynomials (x.2 .CodeWordPolynomial) (x.2 .WeightPolynomial)
--   ⟩

--   toFunB x y := ⟨
--     ⟨x.1,  y.1⟩,
--     fun idx => match idx with
--       | .WeightPolynomial => x.2 .WeightPolynomial
--       | .CodeWord => x.2 .CodeWord
--       | .CodeWordPolynomial => x.2 .CodeWordPolynomial
--       | .SumcheckResult => by
--         simp [PFunctor.monomial] at x y
--         done
--   ⟩

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
  (num_sumcheck_rounds : (Fin (num_vars + 1)))
: OracleStatement.ExecutableLens
  (OuterStmtIn := Statement domain)
  (InnerStmtIn := Sumcheck.Spec.StatementRound F num_vars 0)
  (InnerStmtOut := Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
  (OuterStmtOut :=
    (Statement domain) ×
    (Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
  )
  (OuterOStmtIn := OracleStatement domain num_vars)
  (InnerOStmtIn := Sumcheck.Spec.OracleStatement F num_vars (deg := 2))
  (InnerOStmtOut := Sumcheck.Spec.OracleStatement F num_vars (deg := 2))
  (OuterOStmtOut := OracleStatementMid domain num_vars)
where
  -- Create the sumcheck starting statement from the whir statement
  projStmt whirStatement := {
    target := whirStatement.target
    challenges := !v[]
  }
  -- Create the sumcheck starting oracle statement from the whir statement and oracle statement
  materializeInput whirStatement whirOStatement := fun _ => composePolynomials
    (whirOStatement .CodeWordPolynomial)
    (whirOStatement .WeightPolynomial)

  -- With access to the whir OStatement, create an implementation for the sumcheck oracle
  --  (the multivariate polynomial)
  -- Would survive the weight polynomial being moved into the oracle statement,
  --  as it can use queryBind to evaluate the whir oracles
  simulateInput whirStatement oracleIdx :=
    OracleComp.queryBind
      (Sigma.mk OracleIdx.CodeWordPolynomial oracleIdx.2)
      (fun codeWordEvaluation : F => OracleComp.queryBind
        (Sigma.mk OracleIdx.WeightPolynomial (
          Fin.cases codeWordEvaluation oracleIdx.2
        ))
        (fun weightPolyEvaluation : F => do return weightPolyEvaluation)
      )

  -- by
  --   apply OracleComp.queryBind
  --   case t =>
  --     simp [OracleSpec.Domain, OracleInterface.Query]
  --     apply Sigma.mk
  --     case fst =>
  --       exact OracleIdx.CodeWordPolynomial
  --     dsimp
  --     exact oracleIdx.2
  --   intro codeWordEvaluation
  --   simp [OracleSpec.Range] at codeWordEvaluation
  --   simp [OracleInterface.toOracleSpec, OracleInterface.Response, OracleInterface.toOC] at codeWordEvaluation
  --   set x := cast _ _
  --   simp [OracleSpec.Domain] at x
  --   set x_first := x.fst with eq
  --   set x_second := x.snd
  --   rw! (castMode := .all) [←eq] at codeWordEvaluation
  --   have : x.fst = OracleIdx.CodeWordPolynomial := by
  --     subst x
  --     set h := Eq.symm _ with h_eq
  --     set y := @Sigma.mk _ _ OracleIdx.CodeWordPolynomial _
  --     have : y.fst = OracleIdx.CodeWordPolynomial := rfl
  --     rewrite [←this]
  --     congr
  --     funext
  --     simp [OracleInterface.Query]
  --     exact cast_heq h y
  --   rw! (castMode := .all) [eq, this] at codeWordEvaluation
  --   simp [OracleSpec.ofFn] at codeWordEvaluation

  --   apply OracleComp.queryBind
  --   case t =>
  --     apply Sigma.mk
  --     case fst =>
  --       exact OracleIdx.WeightPolynomial
  --     simp [OracleInterface.Query]
  --     apply Fin.cases
  --     . exact codeWordEvaluation
  --     . exact oracleIdx.2
  --     done
  --   intro weightPolyEvaluation
  --   exact do return weightPolyEvaluation

  simulateInput_eq := by
    intro outerStmt outerOStmt query
    -- requires composePolynomials to be defined correctly
    sorry
    -- rfl

  liftStmt whirStatementIn sumcheckStatementOut :=
    (whirStatementIn, sumcheckStatementOut)

  materializeOutput whirOracle sumcheckOracle idx := match idx with
    | .WeightPolynomial => whirOracle .WeightPolynomial
    | .CodeWord => whirOracle .CodeWord
    | .CodeWordPolynomial => whirOracle .CodeWordPolynomial
    | .SumcheckResult => by

      done

  simulateOutput query :=
    let ⟨queryIdx, queryData⟩ := query
    let bindQuery := match queryIdx with
      | .WeightPolynomial => Sum.inl (Sigma.mk .WeightPolynomial queryData)
      | .CodeWord => Sum.inl (Sigma.mk .CodeWord queryData)
      | .CodeWordPolynomial => Sum.inl (Sigma.mk .CodeWordPolynomial queryData)
      | .Sumcheck => Sum.inr (Sigma.mk () queryData)
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
