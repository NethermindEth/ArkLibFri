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
public import ArkLib.ProofSystem.Whir.Spec.Data
public import ArkLib.ProofSystem.Whir.Spec.Lenses.Statement
public import ArkLib.ProofSystem.Whir.Spec.Lenses.OracleStatement
public import ArkLib.ProofSystem.Whir.Spec.Lenses.Witness

@[expose]
public section

namespace Whir

namespace Spec



section ProtocolSpec

namespace pSpec

-- Composing single rounds because the composition in
-- general specifies num variables = num rounds
def sumCheck
    (F : Type) [Field F] [DecidableEq F]
    (num_sumcheck_rounds : ℕ)
: ProtocolSpec (2*num_sumcheck_rounds) := cast
  (by aesop (add simp Fin.vsum_eq_univ_sum) (add safe (by grind)))
  (
    ProtocolSpec.seqCompose (fun (_ : Fin num_sumcheck_rounds) =>
      Sumcheck.Spec.SingleRound.pSpec
        (R := F)
        (deg := 1)
    )
  )

def sendFoldedFunction
    {F : Type} [Field F] [DecidableEq F]
    {n : ℕ}
    (domain : Domain.SmoothCosetFftDomain n F)
: ProtocolSpec 1 :=
    ⟨
        !v[.P_to_V],
        !v[(domain.subdomain 1).toFinset → F]
    ⟩

def outOfDomainSample (F : Type)
: ProtocolSpec 1 :=
    ⟨
        !v[.V_to_P],
        !v[F]
    ⟩

def outOfDomainAnswer (F : Type)
: ProtocolSpec 1 :=
    ⟨
        !v[.P_to_V],
        !v[F]
    ⟩

def shiftQueriesAndCombinationRandomness
    {F : Type} [Field F] [DecidableEq F]
    (num_sumcheck_rounds : ℕ)
    (num_queries : ℕ) --t
    {n}
    (domain : Domain.SmoothCosetFftDomain n F) -- L
: ProtocolSpec 1 :=
    let Zs := (Fin num_queries → (domain.subdomain num_sumcheck_rounds).toFinset)
⟨
    !v[.V_to_P],
    !v[Zs × F]
⟩

end pSpec

open pSpec in
def pspec
    {F : Type} [Field F] [DecidableEq F]
    (num_sumcheck_rounds : ℕ)
    (num_queries : ℕ)
    {log_order : ℕ}
    (domain : Domain.SmoothCosetFftDomain log_order F)
: ProtocolSpec (2*num_sumcheck_rounds + 4) := cast (by grind) (
  (sumCheck F num_sumcheck_rounds) ++ₚ
  (sendFoldedFunction domain) ++ₚ
  (outOfDomainSample F) ++ₚ
  (outOfDomainAnswer F) ++ₚ
  (shiftQueriesAndCombinationRandomness num_sumcheck_rounds num_queries domain)
)

end ProtocolSpec


section Composition

--αs in sumcheck output statement, no need for messages
--hk in oracle statement
--start by constructing trivial versions of missing parts

open MvPolynomial in
def preSumcheckPSpec
  (F : Type) [CommSemiring F]
  (num_vars : ℕ)
: ProtocolSpec 1 := ⟨
  !v[.P_to_V],
  !v[F⦃≤1⦄[X Fin num_vars]]
⟩

structure preSumcheckProverState
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
where
  statement : Statement domain
  oracleStatement : ∀ idx, OracleStatementPre domain num_vars idx
  witness : WitnessPreSumcheck F num_vars

open MvPolynomial in
def preSumcheckProver
  {OSpecIdx : Type} (oSpec : OracleSpec OSpecIdx)
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
: OracleProver
  oSpec
  (Statement domain)
  (OracleStatementPre domain num_vars)
  (WitnessPreSumcheck F num_vars)
  (Statement domain)
  (OracleStatement domain num_vars)
  (WitnessPreSumcheck F num_vars)
  (preSumcheckPSpec F num_vars)
where
  PrvState _ := preSumcheckProverState domain num_vars
  input ins := {
    statement := ins.1.1
    oracleStatement := ins.1.2
    witness := ins.2
  }
  sendMessage idx state := match idx with
    | ⟨0, _⟩ => do
      return (state.witness.f_hat,state)
  receiveChallenge idx _state := match idx with
    | ⟨0, h⟩ => nomatch h
  output state := do
    return (
      (
        state.statement,
        fun idx => match idx with
          | .WeightPolynomial => state.oracleStatement .WeightPolynomial
          | .CodeWord => state.oracleStatement .CodeWord
          | .CodeWordPolynomial => state.witness.f_hat
      ),
      state.witness
    )

open MvPolynomial in
instance
  {F : Type} [Field F]
  (num_vars : ℕ)
  (i : (preSumcheckPSpec F num_vars).MessageIdx)
: OracleInterface ((preSumcheckPSpec F num_vars).Message i) where
  Query := Fin num_vars → F
  toOC.spec := OracleSpec.ofFn fun x ↦ F
  toOC.impl input := do
    let data ← read
    let vals : Fin num_vars → F := input
    let poly : F⦃≤1⦄[X Fin num_vars] := cast (by {
      fin_cases i
      rfl
    }) data
    return MvPolynomial.eval vals poly

def preSumcheckVerifier
  {OSpecIdx : Type} (oSpec : OracleSpec OSpecIdx)
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
: OracleVerifier
    oSpec
    (Statement domain)
    (OracleStatementPre domain num_vars)
    (Statement domain)
    (OracleStatement domain num_vars)
    (preSumcheckPSpec F num_vars)
where
  verify statement _challenges := do
    return statement
  outputOracle := Sum.inl {
    embed := ⟨
      fun idx => match idx with
        | .WeightPolynomial => Sum.inl .WeightPolynomial
        | .CodeWord => Sum.inl .CodeWord
        | .CodeWordPolynomial => Sum.inr ⟨0, rfl⟩,
      by
        aesop (add simp Function.Injective)
    ⟩
    hEq idx := by
      fin_cases idx
      all_goals rfl
    outputInterface_heq idx := by
      fin_cases idx <;> rfl
  }


def preSumcheckReduction
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
: OracleReduction
    oSpec
    (StmtIn := Statement domain)
    (OStmtIn := OracleStatementPre domain num_vars)
    (WitIn := WitnessPreSumcheck F num_vars)
    (StmtOut := Statement domain)
    (OStmtOut := OracleStatement domain num_vars)
    (WitOut := WitnessPreSumcheck F num_vars)
    (preSumcheckPSpec F num_vars)
where
  prover := preSumcheckProver oSpec domain num_vars
  verifier := preSumcheckVerifier oSpec domain num_vars


noncomputable def sumcheckLens
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
: OracleContext.ExecutableLens
    (OuterStmtIn := Statement domain)
    (InnerStmtIn := (Sumcheck.Spec.StatementRound F num_vars 0))
    (InnerStmtOut := (Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds))
    (OuterStmtOut :=
      (Statement domain) ×
      (Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
    )
    (OuterOStmtIn := OracleStatement domain num_vars)
    (InnerOStmtIn := Sumcheck.Spec.OracleStatement F num_vars (deg := 2))
    (InnerOStmtOut := Sumcheck.Spec.OracleStatement F num_vars (deg := 2))
    (OuterOStmtOut := OracleStatement domain num_vars)
    (OuterWitIn := WitnessPreSumcheck F num_vars)
    (InnerWitIn := Unit)
    (InnerWitOut := Unit)
    (OuterWitOut := WitnessPostSumcheck F num_vars)
where
  stmt := OracleStatement.sumcheckExecutableLens
    domain num_vars num_sumcheck_rounds
  wit := Witness.sumcheckLens
    domain num_vars num_sumcheck_rounds

def output
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h : num_sumcheck_rounds > 0)
: OracleVerifier.LiftContextOutput
  (sumcheckLens domain num_vars num_sumcheck_rounds).stmt
  (
    Sumcheck.Spec.partialOracleVerifier
      (R := F)
      (deg := 2)
      (m := 2^log_order)
      ↑domain
      (n := num_vars)
      oSpec
      num_sumcheck_rounds
  )
where
  outputOracle := Sum.inl {
    embed := ⟨
      fun idx => Sum.inl idx,
      by simp [Function.Injective]
    ⟩
    hEq := by
      intro i; fin_cases i <;> rfl
    outputInterface_heq := by
      intro i
      fin_cases i
      all_goals rfl
  }

  materialize_eq := by
    intro outerStatement challenges outerOracleStatement messages
    simp only [OracleVerifier.materializeOutputOracle, ProtocolSpec.MessageIdx,
      Function.Embedding.coeFn_mk]
    simp only [sumcheckLens, OracleStatement.sumcheckExecutableLens, PFunctor.FreeM.liftBind_eq,
      OracleSpec.ofPFunctor_toPFunctor, PFunctor.FreeM.bind_eq_bind, bind_pure_comp]
    funext idx
    fin_cases idx
    all_goals rfl






  -- Can't do an embedding because it's not an injection
  -- outputOracle := Sum.inr {
  --   materializeOutput := by
  --     intro challenges oracles messages idx
  --     match idx with
  --       | .WeightPolynomial => exact oracles .WeightPolynomial
  --       | .CodeWord => exact oracles .CodeWord
  --       | .Sumcheck => exact oracles .WeightPolynomial
  --   simulateOutputQuery challenges idx :=
  --     OracleComp.queryBind (
  --       let ⟨idx, data⟩ := idx
  --       match idx with
  --       | .WeightPolynomial => (Sum.inr (Sum.inl ⟨.WeightPolynomial, data⟩))
  --       | .CodeWord => (Sum.inr (Sum.inl ⟨.CodeWord, data⟩))
  --       | .Sumcheck => (Sum.inr (Sum.inl ⟨.WeightPolynomial, data⟩))
  --     ) (fun response => do return (cast (by {
  --       obtain ⟨idx, data⟩ := idx
  --       fin_cases idx <;> rfl
  --     }) response))
  --   simulateOutputQuery_eq := by
  --     intro challenges whirOracles messages query
  --     aesop
  -- }

  -- materialize_eq := by
  --   intro outerStatement challenges outerOracleStatement messages
  --   unfold sumcheckLens OracleStatement.sumcheckExecutableLens OracleVerifier.materializeOutputOracle
  --   dsimp
  --   funext idx
  --   fin_cases idx
  --   . rfl
  --   . rfl
  --   . done


noncomputable def sumcheckReduction
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
: OracleReduction
    oSpec
    (StmtIn := Statement domain)
    (OStmtIn := OracleStatement domain num_vars)
    (WitIn := WitnessPreSumcheck F num_vars)
    (StmtOut := (Statement domain) ×
      (Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
    )
    (OStmtOut := OracleStatement domain num_vars)
    (WitOut := WitnessPostSumcheck F num_vars)
    (Sumcheck.Spec.pSpec F (deg := 2) num_sumcheck_rounds)
:= (
  Sumcheck.Spec.partialOracleReduction
    (R := F)
    (deg := 2)
    (m := 2^log_order)
    ↑domain
    (n := num_vars)
    oSpec
    num_sumcheck_rounds
  ).liftContext (
    sumcheckLens
      domain num_vars num_sumcheck_rounds
  ) (
    output
      oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds
  )

def restPSpec
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  {num_vars : ℕ}
  (num_sumcheck_rounds : Fin (num_vars + 2))
  (num_queries : ℕ)
:=
  (pSpec.sendFoldedFunction domain) ++ₚ
  (pSpec.outOfDomainSample F) ++ₚ
  (pSpec.outOfDomainAnswer F) ++ₚ
  (pSpec.shiftQueriesAndCombinationRandomness num_sumcheck_rounds num_queries domain)

instance
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  {num_vars : ℕ}
  (num_sumcheck_rounds : Fin (num_vars + 2))
  (num_queries : ℕ)
  (i : (restPSpec domain num_sumcheck_rounds num_queries).MessageIdx)
: OracleInterface
    ((restPSpec domain num_sumcheck_rounds num_queries).Message i)
where
  Query := sorry
  toOC := sorry

open Polynomial MvPolynomial in
structure ProverStateRound0
  {F : Type} [Field F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_sumcheck_rounds : ℕ)
  (num_vars : ℕ)
where
  α : Fin num_sumcheck_rounds → F
  f_hat : F[X Fin num_vars]
  h_hat_k : F⦃≤ 2⦄[X]

open Polynomial MvPolynomial in
structure ProverStateRound1
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_sumcheck_rounds : ℕ)
  (num_vars : ℕ)
where
  α : Fin num_sumcheck_rounds → F
  f_hat : F[X Fin num_vars]
  g : (domain.subdomain 1) → F
  h_hat_k : F⦃≤ 2⦄[X]

open Polynomial MvPolynomial in
structure ProverStateRound2
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_sumcheck_rounds : ℕ)
  (num_vars : ℕ)
where
  α : Fin num_sumcheck_rounds → F
  f_hat : F[X Fin num_vars]
  g : (domain.subdomain 1) → F
  h_hat_k : F⦃≤ 2⦄[X]
  z0 : List F

open Polynomial MvPolynomial in
structure ProverStateRound3
  {F : Type} [Field F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_sumcheck_rounds : ℕ)
  (num_vars : ℕ)
where
  α : Fin num_sumcheck_rounds → F
  f_hat : F[X Fin num_vars]
  h_hat_k : F⦃≤ 2⦄[X]
  y : F

open Polynomial MvPolynomial in
structure ProverStateRound4
  {F : Type} [Field F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_sumcheck_rounds : ℕ)
  (num_vars : ℕ)
where
  α : Fin num_sumcheck_rounds → F
  f_hat : F[X Fin num_vars]
  h_hat_k : F⦃≤ 2⦄[X]
  y : F
  γ : F


def restProver
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 2))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
  (num_queries : ℕ)
:
  OracleProver
    oSpec
    (Statement domain × Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
    (OracleStatement domain num_vars)
    (WitnessPostSumcheck F num_vars)
    (Statement (Domain.CosetFftDomain.subdomain domain 1))
    (OracleStatement (Domain.CosetFftDomain.subdomain domain 1) num_vars)
    (WitnessPostSumcheck F num_vars) -- TODO does num vars change here
    (restPSpec domain num_sumcheck_rounds num_queries)
where
  PrvState (round : Fin 5) := match round with
    | 0 => ProverStateRound0 domain num_sumcheck_rounds num_vars
    | 1 => ProverStateRound1 domain num_sumcheck_rounds num_vars
    | 2 => ProverStateRound2 domain num_sumcheck_rounds num_vars
    | 3 => ProverStateRound3 domain num_sumcheck_rounds num_vars
    | 4 => ProverStateRound4 domain num_sumcheck_rounds num_vars

  input ins :=
    let whir_statement := ins.1.1.1
    let sumcheck_statement := ins.1.1.2
    let oracle_statement := ins.1.2
    let witness := ins.2
    {
      α := sumcheck_statement.challenges
      f_hat := witness.f_hat
      h_hat_k := sorry -- TODO get sumcheck target polynomial
    }

  sendMessage msgIdx state := match msgIdx with
    | ⟨0, h⟩ => do -- send folded function
      let alpha := state.α -- Fin num_sumcheck_rounds → F
                         -- challenges from sumcheck
      let f_hat := sorry -- codeword polynomial (from witness?)
      let g_hat := sorry -- g_hat(x) = f_hat(...alpha,x)
      let g : domain.subdomain 1 → F := fun x => sorry -- g_hat.eval x
      let msg := g
      let newState := {
        α := state.α
        g := g
        h_hat_k := state.h_hat_k
      }
      return (msg, newState)
    | ⟨1, h⟩ => nomatch h
    | ⟨2, h⟩ => do -- out of domain answer
      let g := state.g
      let z0 := state.z0 -- this is supposed to be a tuple, yet g takes only one input?
      let y0 : F := g z0
      let msg : F := sorry
      let newState := {
        α := state.α
        h_hat_k := state.h_hat_k
        y := y0
      }
      return (msg, newState)
    | ⟨3, h⟩ => nomatch h

  receiveChallenge msgIdx state := match msgIdx with
    | ⟨0, h⟩ => nomatch h
    | ⟨1, h⟩ => do -- receive out of domain sample
      return fun challenge => (
        let z0 : List F := (List.range (
            num_vars - num_sumcheck_rounds
          )).foldl (init := [challenge]) (fun acc idx =>
            let prev := acc[idx]!
            acc.concat (prev*prev)
          )
        let newState := {
          α := state.α
          g := state.g
          h_hat_k := state.h_hat_k
          z0 := z0
        }
        newState
      )
    | ⟨2, h⟩ => nomatch h
    | ⟨3, h⟩ => do
      return fun challenge => (
        let zs := challenge.1
        let γ := challenge.2
        let newState := {
          y := state.y
          γ := γ
          α := state.α
          h_hat_k := state.h_hat_k
        }
        newState -- set up for next round
      )

  output state := do
    let ys : Vector F (num_queries + 1) := Vector.cast (by grind) (
      #v[state.y] ++
      Vector.replicate num_queries (sorry : F) -- FOLD
    )
    let γ : F := state.γ
    let α_k : F := state.α ⟨num_sumcheck_rounds.val - 1, by grind⟩
    let h_hat_k := state.h_hat_k.val

    let sum := (ys.mapIdx (fun idx y =>
      let pow := (List.replicate (idx + 1) γ).prod
      pow * y
    )).sum
    let newTarget := MvPolynomial.eval (fun _ => α_k) h_hat_k + sum

    let newWeightPolynomial := _
    let newCodeWord := _
    let statement := {
      target := newTarget
    }
    let oracleStatement := fun idx => match idx with
      | .WeightPolynomial => newWeightPolynomial
      | .CodeWord => newCodeWord
    let witness := {
      placeholder := ()
    }
    return ((statement, oracleStatement), witness)

def restVerifier
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 2))
  (num_queries : ℕ)
:
  OracleVerifier
    oSpec
    (Statement domain × Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
    (OracleStatement domain num_vars)
    (Statement (Domain.CosetFftDomain.subdomain domain 1))
    (OracleStatement (Domain.CosetFftDomain.subdomain domain 1) num_vars)
    (restPSpec domain num_sumcheck_rounds num_queries)
where
  verify := sorry
  outputOracle := sorry

def restReduction
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 2))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
  (num_queries : ℕ)
: OracleReduction
    oSpec
    (StmtIn := (Statement domain) ×
      (Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
    )
    (OStmtIn := (OracleStatement domain num_vars))
    (WitIn := WitnessPostSumcheck F num_vars)
    (StmtOut := (Statement (domain.subdomain 1)))
    --TODO does num_vars remain the same?
    (OStmtOut := (OracleStatement (domain.subdomain 1) num_vars))
    (WitOut := Witness) -- TODO, we need a proper witness here
    (pSpec := restPSpec domain num_sumcheck_rounds num_queries)
where
  prover := restProver oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds num_queries
  verifier := restVerifier oSpec domain num_vars num_sumcheck_rounds num_queries

noncomputable def oracleReduction
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 2))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
  (num_queries : ℕ)
:= OracleReduction.append
  (sumcheckReduction oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds)
  (restReduction oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds num_queries)


end Composition




section Prover

def proverState
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  {num_sumcheck_rounds : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
: ProverState (2*num_sumcheck_rounds + 4) where
  PrvState := fun _round => (Statement domain) × (OracleStatement domain)

def prover
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_sumcheck_rounds : ℕ)
  (num_queries : ℕ)
:
  OracleProver []ₒ
  (Statement domain) (fun _ : Unit => OracleStatement domain) Unit
  (Statement (domain.subdomain 1)) (fun _ : Unit => OracleStatement (domain.subdomain 1)) Unit
  (pspec num_sumcheck_rounds num_queries domain)
where
  PrvState := (proverState domain).PrvState
  input := fun ⟨⟨a, b⟩, c⟩ => (a, b ())


  sendMessage round state := do
    let ⟨round, h_send⟩ := round
    if _ : round < 2*num_sumcheck_rounds then
      -- we know we are in a send round
      return ⟨LinearMvExtension.linearMvExtension state.1.weight_polynomial, state⟩
    else if _ : round == 2*num_sumcheck_rounds then
      let g_hat := _
      return ⟨g_hat, state⟩
    else if _ : round == 2*num_sumcheck_rounds + 2 then
      let y := _
      return ⟨y, state⟩
    else





end Prover





end Spec

end Whir

end
