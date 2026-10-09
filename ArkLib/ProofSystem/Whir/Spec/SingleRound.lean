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
        !v[domain.subdomain 1 → F]
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
instance preSumcheckPSpecInterface
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
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
: OracleContext.ExecutableLens
    (OuterStmtIn := Statement domain)
    (InnerStmtIn := (Sumcheck.Spec.StatementRound F num_vars 0))
    (InnerStmtOut := (Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds))
    (OuterStmtOut :=
      (Statement domain) ×
      (Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
    )
    (OuterOStmtIn := OracleStatement domain num_vars)
    (InnerOStmtIn := Sumcheck.Spec.OracleStatementRound F num_vars (deg := 2) 0)
    (InnerOStmtOut := Sumcheck.Spec.OracleStatementRound F num_vars (deg := 2) num_sumcheck_rounds)
    (OuterOStmtOut := OracleStatementMid domain num_vars)
    (OuterWitIn := WitnessPreSumcheck F num_vars)
    (InnerWitIn := Unit)
    (InnerWitOut := Unit)
    (OuterWitOut := WitnessPostSumcheck F num_vars)
where
  stmt := OracleStatement.sumcheckExecutableLens
    domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds
  wit := Witness.sumcheckLens
    domain num_vars num_sumcheck_rounds

def output
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
: OracleVerifier.LiftContextOutput
  (sumcheckLens domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds).stmt
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
      fun idx => match idx with
        | .WeightPolynomial => Sum.inl .WeightPolynomial
        | .CodeWord => Sum.inl .CodeWord
        | .CodeWordPolynomial => Sum.inl .CodeWordPolynomial
        | .SumcheckResult => Sum.inr ⟨
          ⟨2*(num_sumcheck_rounds.val - 1), by simp [Fin.vsum_eq_univ_sum]; grind⟩,
          by
            set x := num_sumcheck_rounds.val - 1 with eq
            have : num_sumcheck_rounds.val = x + 1 := by grind
            rw! [←eq, this]
            simp
            sorry -- I believe this is correct
        ⟩,
      by
        simp [Function.Injective]
        intro a1 a2
        fin_cases a1 <;> fin_cases a2 <;> dsimp
        <;> intro h_eq
        all_goals try rfl
        all_goals exfalso; grind

    ⟩
    hEq := by
      intro i; fin_cases i <;> try rfl
      simp
      sorry -- same proof as above
    outputInterface_heq := by
      intro i
      fin_cases i
      all_goals try rfl
      sorry -- fundamentally the same thing going on here
  }

  materialize_eq :=
    sorry
    -- intro outerStatement challenges outerOracleStatement messages
    -- simp only [OracleVerifier.materializeOutputOracle, ProtocolSpec.MessageIdx,
    --   Function.Embedding.coeFn_mk]
    -- simp only [sumcheckLens, OracleStatement.sumcheckExecutableLens, PFunctor.FreeM.liftBind_eq,
    --   OracleSpec.ofPFunctor_toPFunctor, PFunctor.FreeM.bind_eq_bind, bind_pure_comp]
    -- funext idx
    -- fin_cases idx
    -- all_goals rfl






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
    (OStmtOut := OracleStatementMid domain num_vars)
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
      domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds
  ) (
    output
      oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds
  )

def restPSpec
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  {num_vars : ℕ}
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (num_queries : ℕ)
:=
  (pSpec.sendFoldedFunction domain) ++ₚ
  (pSpec.outOfDomainSample F) ++ₚ
  (pSpec.outOfDomainAnswer F) ++ₚ
  (pSpec.shiftQueriesAndCombinationRandomness num_sumcheck_rounds num_queries domain)

instance restPSpecInstance
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  {num_vars : ℕ}
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (num_queries : ℕ)
  (idx : (restPSpec domain num_sumcheck_rounds num_queries).MessageIdx)
: OracleInterface ((restPSpec domain num_sumcheck_rounds num_queries).Message idx)
where
  Query := match idx with
    | ⟨0, _⟩ =>  domain.subdomain 1
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => Unit
    | ⟨3, h⟩ => nomatch h
  toOC.spec := match idx with
    | ⟨0, _⟩ =>  fun _ => F
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => fun _ => F
    | ⟨3, h⟩ => nomatch h
  toOC.impl := match idx with
    | ⟨0, _⟩ => fun point => do
      let folded_function ← read
      return (folded_function point)
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => fun _ => do
      let answer ← read
      return answer
    | ⟨3, h⟩ => nomatch h

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
  ω_hat : F⦃≤ 1⦄[X Fin (num_vars + 1)]

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
  g_hat : F⦃≤ 1⦄[X Fin (num_vars - num_sumcheck_rounds)]
  ω_hat : F⦃≤ 1⦄[X Fin (num_vars + 1)]
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
  g_hat : F⦃≤ 1⦄[X Fin (num_vars - num_sumcheck_rounds)]
  h_hat_k : F⦃≤ 2⦄[X]
  ω_hat : F⦃≤ 1⦄[X Fin (num_vars + 1)]
  z0 : Fin (num_vars - num_sumcheck_rounds) → F

open Polynomial MvPolynomial in
structure ProverStateRound3
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_sumcheck_rounds : ℕ)
  (num_vars : ℕ)
where
  α : Fin num_sumcheck_rounds → F
  f_hat : F[X Fin num_vars]
  g : (domain.subdomain 1) → F
  g_hat : F⦃≤ 1⦄[X Fin (num_vars - num_sumcheck_rounds)]
  h_hat_k : F⦃≤ 2⦄[X]
  ω_hat : F⦃≤ 1⦄[X Fin (num_vars + 1)]
  y : F
  z0 : Fin (num_vars - num_sumcheck_rounds) → F

open Polynomial MvPolynomial in
structure ProverStateRound4
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_sumcheck_rounds : ℕ)
  (num_vars : ℕ)
  (num_queries : ℕ)
where
  α : Fin num_sumcheck_rounds → F
  f_hat : F[X Fin num_vars]
  g : (domain.subdomain 1) → F
  g_hat : F⦃≤ 1⦄[X Fin (num_vars - num_sumcheck_rounds)]
  γ : F
  h_hat_k : F⦃≤ 2⦄[X]
  ω_hat : F⦃≤ 1⦄[X Fin (num_vars + 1)]
  y : F
  zs : Fin (num_queries + 1) → Fin (num_vars - num_sumcheck_rounds) → F


def restProver
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
  (num_queries : ℕ)
:
  OracleProver
    oSpec
    (Statement domain × Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
    (OracleStatementMid domain num_vars)
    (WitnessPostSumcheck F num_vars)
    (Statement (Domain.CosetFftDomain.subdomain domain 1))
    (OracleStatementPre (Domain.CosetFftDomain.subdomain domain 1) (num_vars - num_sumcheck_rounds))
    (WitnessPreSumcheck F (num_vars - num_sumcheck_rounds))
    (restPSpec domain num_sumcheck_rounds num_queries)
where
  PrvState (round : Fin 5) := match round with
    | 0 => ProverStateRound0 domain num_sumcheck_rounds num_vars
    | 1 => ProverStateRound1 domain num_sumcheck_rounds num_vars
    | 2 => ProverStateRound2 domain num_sumcheck_rounds num_vars
    | 3 => ProverStateRound3 domain num_sumcheck_rounds num_vars
    | 4 => ProverStateRound4 domain num_sumcheck_rounds num_vars num_queries

  input ins :=
    let whir_statement := ins.1.1.1
    let sumcheck_statement := ins.1.1.2
    let oracle_statement := ins.1.2
    let witness := ins.2
    {
      α := sumcheck_statement.challenges
      f_hat := witness.f_hat
      h_hat_k := oracle_statement .SumcheckResult --can also use the witness, it's in both currently. TODO, remove from witness?
      ω_hat := oracle_statement .WeightPolynomial
    }

  sendMessage msgIdx state := match msgIdx with
    | ⟨0, h⟩ => do -- send folded function
      let alpha := state.α -- Fin num_sumcheck_rounds → F
                         -- challenges from sumcheck
      let f_hat := state.f_hat
      let g_hat := sorry -- g_hat(x) = f_hat(...alpha,x)
      let g : domain.subdomain 1 → F := fun x => sorry -- g_hat.eval x
      let msg := g
      let newState := {
        α := state.α
        f_hat := f_hat
        g := g
        g_hat := g_hat
        h_hat_k := state.h_hat_k
        ω_hat := state.ω_hat
      }
      return (msg, newState)
    | ⟨1, h⟩ => nomatch h
    | ⟨2, h⟩ => do -- out of domain answer
      let g_hat := state.g_hat
      let z0 := state.z0
      let y0 : F := MvPolynomial.eval z0 g_hat
      let msg : F := sorry
      let newState := {
        α := state.α
        f_hat := state.f_hat
        g := state.g
        g_hat := state.g_hat
        h_hat_k := state.h_hat_k
        ω_hat := state.ω_hat
        y := y0
        z0 := state.z0
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
          f_hat := state.f_hat
          g := state.g
          g_hat := state.g_hat
          h_hat_k := state.h_hat_k
          ω_hat := state.ω_hat
          z0 := z0
        }
        newState
      )
    | ⟨2, h⟩ => nomatch h
    | ⟨3, h⟩ => do
      return fun challenge => (
        let zs := challenge.1
        let zs := _ -- TODO calculate exponentiations for each zs i
        let γ := challenge.2
        let newState := {
          α := state.α
          γ := γ
          f_hat := state.f_hat
          g := state.g
          g_hat := state.g_hat
          h_hat_k := state.h_hat_k
          ω_hat := state.ω_hat
          y := state.y
          zs := Fin.cases state.z0 zs
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
    let newTarget := Polynomial.eval α_k h_hat_k + sum

    let zs := state.zs
    let specialisedWeightPolynomial := _ -- fun inputs => state.ω_hat (inputs 0) ..state.α (inputs 1..)
    let eq := _
    let sum := _ -- fun inputs => (inputs 0) * ∑ i ≤ num_queries, γ^(i+1)*eq (zi, (inputs 1..))

    let newWeightPolynomial := _ -- fun inputs => specializeWeightPolynomial inputs + sum inputs
    let newCodeWord := state.g
    let newCodeWordPolynomial := state.g_hat
    let statement := {
      target := newTarget
    }
    let oracleStatement := fun idx => match idx with
      | .WeightPolynomial => newWeightPolynomial
      | .CodeWord => newCodeWord
    let witness := {
      f_hat := state.g_hat
    }
    return ((statement, oracleStatement), witness)

def restVerifier
  {OSpecIdx : Type} (oSpec : OracleSpec OSpecIdx)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (num_queries : ℕ)
:
  OracleVerifier
    oSpec
    (Statement domain × Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
    (OracleStatementMid domain num_vars)
    (Statement (Domain.CosetFftDomain.subdomain domain 1))
    (OracleStatementPre (Domain.CosetFftDomain.subdomain domain 1) (num_vars - num_sumcheck_rounds))
    (restPSpec domain num_sumcheck_rounds num_queries)
where
  verify statement challenges := do
    let newTarget : F := _
    return {
      target := newTarget
    }
  outputOracle := Sum.inl {
    embed := _
    hEq := _
    outputInterface_heq := _
  }

def restReduction
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
  (num_queries : ℕ)
: OracleReduction
    oSpec
    (StmtIn := (Statement domain) ×
      (Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
    )
    (OStmtIn := (OracleStatementMid domain num_vars))
    (WitIn := WitnessPostSumcheck F num_vars)
    (StmtOut := (Statement (domain.subdomain 1)))
    (OStmtOut := (OracleStatementPre (domain.subdomain 1) (num_vars - num_sumcheck_rounds)))
    (WitOut := WitnessPreSumcheck F (num_vars - num_sumcheck_rounds))
    (pSpec := restPSpec domain num_sumcheck_rounds num_queries)
where
  prover := restProver oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds num_queries
  verifier := restVerifier oSpec domain num_vars num_sumcheck_rounds num_queries

-- instance appendInterface
--   {n1 n2 : ℕ}
--   (pSpec1 : ProtocolSpec n1)
--   (pSpec2 : ProtocolSpec n2)
--   (idx : (pSpec1 ++ₚ pSpec2).MessageIdx)
--   [inst1 : (idx : pSpec1.MessageIdx) → OracleInterface (pSpec1.Message idx)]
--   [inst2 : (idx : pSpec2.MessageIdx) → OracleInterface (pSpec2.Message idx)]
-- : OracleInterface
--     ((pSpec1 ++ₚ pSpec2).Message idx)
-- := by
--   if h : idx < n1 then
--     constructor
--     case Query =>
--       apply (inst1 _).Query
--       constructor
--       case val => exact ⟨idx.val.val, by grind⟩
--       simp at idx
--       rewrite [←Fin.vappend_left (u := pSpec1.dir) (v := pSpec2.dir)]
--       convert idx.2
--       rfl
--     case toOC =>
--       convert (inst1 _).toOC using 2
--       unfold ProtocolSpec.Message
--       rewrite [←Fin.vappend_left (u := pSpec1.Type) (v := pSpec2.Type)]
--       rfl
--     done
--   else
--     constructor
--     case Query =>
--       apply (inst2 _).Query
--       constructor
--       case val => exact ⟨idx.val.val - n1, by grind⟩
--       simp at idx
--       rewrite [←Fin.vappend_right (u := pSpec1.dir) (v := pSpec2.dir)]
--       convert idx.2
--       grind
--     case toOC =>
--       convert (inst2 _).toOC using 2
--       unfold ProtocolSpec.Message
--       rewrite [
--         ←Fin.vappend_right (u := pSpec1.Type) (v := pSpec2.Type),
--         show (pSpec1 ++ₚ pSpec2).Type = (pSpec1.Type ++ᵛ pSpec2.Type) by rfl
--       ]
--       congr
--       grind
--     done

-- instance
--   {F : Type} [Field F] [DecidableEq F]
--   {log_order : ℕ}
--   (domain : Domain.SmoothCosetFftDomain log_order F)
--   (num_vars : ℕ)
--   (num_sumcheck_rounds : Fin (num_vars + 1))
--   (num_queries : ℕ)
--   (i :
--     (preSumcheckPSpec F num_vars ++ₚ Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds ++ₚ
--       restPSpec domain num_sumcheck_rounds num_queries).MessageIdx)
-- : OracleInterface
--     ((preSumcheckPSpec F num_vars ++ₚ Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds ++ₚ
--       restPSpec domain num_sumcheck_rounds num_queries).Message
--     i)
-- := by
--   apply @appendInterface _ _ _ _ _ (inferInstance) (inferInstance)

-- TODO why does this need declaring manually?
instance
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (num_queries : ℕ)
  (i :
    (preSumcheckPSpec F num_vars ++ₚ Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds ++ₚ
      restPSpec domain num_sumcheck_rounds num_queries).MessageIdx)
: OracleInterface
    ((preSumcheckPSpec F num_vars ++ₚ Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds ++ₚ
      restPSpec domain num_sumcheck_rounds num_queries).Message
    i)
:= ProtocolSpec.instOracleInterfaceMessageAppend i


noncomputable def oracleReduction
  {ι : Type} (oSpec : OracleSpec ι)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
  (num_queries : ℕ)
: OracleReduction
    oSpec
    (StmtIn := Statement domain)
    (OStmtIn := OracleStatementPre domain num_vars)
    (WitIn := WitnessPreSumcheck F num_vars)
    (StmtOut := Statement (domain.subdomain 1))
    (OStmtOut := OracleStatementPre (domain.subdomain 1) (num_vars - num_sumcheck_rounds))
    (WitOut := WitnessPreSumcheck F (num_vars - num_sumcheck_rounds))
    (pSpec :=
      preSumcheckPSpec F num_vars ++ₚ
      Sumcheck.Spec.pSpec F (deg := 2) num_sumcheck_rounds ++ₚ
      restPSpec domain num_sumcheck_rounds num_queries
    )
:= OracleReduction.append
    (OracleReduction.append
      (preSumcheckReduction oSpec domain num_vars)
      (sumcheckReduction oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds)
    )
  (restReduction oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds num_queries)


end Composition



end Spec

end Whir

end
