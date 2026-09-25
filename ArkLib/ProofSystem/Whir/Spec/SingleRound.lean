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

namespace Whir

namespace Spec

structure Statement
  {F : Type} [Field F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
where
  log_degree : ℕ
  weight_polynomial : MvPolynomial (Fin (log_degree + 1)) F
  target : F

structure OracleStatement
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
where
  codeword : domain.toFinset → F

namespace Statement

variable {F : Type} [Field F]
  {log_order : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}

abbrev domain_order
  (_statement : Statement domain)
: ℕ :=
  2^log_order

abbrev code
  (statement : Statement domain)
: Set (Fin (2^log_order) → F) :=
  ReedSolomon.constrainedCode
    domain
    statement.log_degree
    statement.weight_polynomial
    statement.target

-- def step
--   (statement : Statement F)
--   (num_sumcheck_rounds : ℕ)
--   (num_steps : ℕ)
-- : Statement F := match num_steps with
--   | 0 => statement
--   | n+1 => step {
--       log_order := statement.log_order - 1
--       domain := statement.domain.subdomain 1
--       log_degree := statement.log_degree - num_sumcheck_rounds

--     } n

end Statement


section Witness

@[reducible]
def Witness (F : Type) :

end Witness


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

def sumcheckReduction
  {ι : Type} (oSpec : OracleSpec ι) (Idx1 Idx2 : Type)
: OracleReduction
    oSpec
    StatementIn (OStatementIn Idx1) WitnessIn
    StatementMid (OStatementMid Idx2) WitnessMid
    sumcheckPSpec
:= sorry

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
