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

def StatementIn : Type := sorry
def OStatementIn (idx : Type) : idx → Type := sorry
def WitnessIn : Type := sorry

def StatementMid : Type := sorry
def OStatementMid (idx : Type) : idx → Type := sorry
def WitnessMid : Type := sorry

def StatementOut : Type := sorry
def OStatementOut (idx : Type) : idx → Type := sorry
def WitnessOut : Type := sorry

def sumcheckPSpec : ProtocolSpec 42 := sorry
def restPSpec : ProtocolSpec 47 := sorry


def sumcheckLens
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 2))
  [OracleInterface (OracleStatement domain)]
: OracleContext.ExecutableLens
    (OuterStmtIn := Statement domain num_vars)
    (InnerStmtIn := (Sumcheck.Spec.StatementRound F (num_vars + 1) 0))
    (InnerStmtOut := (Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds))
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
    (OuterWitIn := Witness)
    (InnerWitIn := Unit)
    (InnerWitOut := Unit)
    (OuterWitOut := Witness)
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
  (num_sumcheck_rounds : Fin (num_vars + 2))
  [OracleInterface (OracleStatement domain)]
: OracleVerifier.LiftContextOutput
  (sumcheckLens domain num_vars num_sumcheck_rounds).stmt
  (
    Sumcheck.Spec.partialOracleVerifier
      (R := F)
      (deg := 1)
      (m := 2^log_order)
      ↑domain
      (n := num_vars + 1)
      oSpec
      num_sumcheck_rounds
  )
where
  outputOracle := Sum.inl {
    embed := ⟨
      fun _ => Sum.inl (),
      by simp [Function.Injective]
    ⟩
    hEq := by
      intro i
    outputInterface_heq := sorry
  }

  materialize_eq := sorry

-- TODO change OStmtOut type to not be over unit, but Fin 2, one for OracleStatement, and one for the sumcheck oracle statement

noncomputable def sumcheckReduction
  {ι : Type} (oSpec : OracleSpec ι) (Idx1 Idx2 : Type)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 2))
  [(i : Idx1) → OracleInterface (OStatementIn Idx1 i)]
  [(i : sumcheckPSpec.MessageIdx) → OracleInterface (sumcheckPSpec.Message i)]
  [(i : Idx2) → OracleInterface (OStatementMid Idx2 i)]
  [OracleInterface (OracleStatement domain)]
: OracleReduction
    oSpec
    (Statement domain num_vars)
    (fun _ : Unit => OracleStatement domain)
    Witness
    ((Statement domain num_vars) ×
      (Sumcheck.Spec.StatementRound F (num_vars + 1) num_sumcheck_rounds)
    )
    (fun _ : Unit =>
      OracleStatement domain ×
      Sumcheck.Spec.OracleStatement F (num_vars + 1) (deg := 1) ()
    )
    Witness
    (Sumcheck.Spec.pSpec F 1 num_sumcheck_rounds)
:= (
  Sumcheck.Spec.partialOracleReduction
    (R := F)
    (deg := 1)
    (m := 2^log_order)
    ↑domain
    (n := num_vars + 1)
    oSpec
    num_sumcheck_rounds
  ).liftContext (
    sumcheckLens
      domain num_vars num_sumcheck_rounds
  ) (
    output
      oSpec domain num_vars num_sumcheck_rounds
  )



def restReduction
  {ι : Type} (oSpec : OracleSpec ι) (Idx1 Idx2 : Type)
: OracleReduction
    oSpec
    StatementMid (OStatementMid Idx1) WitnessMid
    StatementOut (OStatementOut Idx2) WitnessOut
    restPSpec
:= sorry

def oracleReduction
  {ι : Type} (oSpec : OracleSpec ι) (Idx1 Idx2 Idx3 : Type)
:= OracleReduction.append
  (sumcheckReduction oSpec Idx1 Idx2)
  (restReduction oSpec Idx2 Idx3)


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
