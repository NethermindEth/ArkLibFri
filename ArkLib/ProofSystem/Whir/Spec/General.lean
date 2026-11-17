/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dom Henderson
-/

import ArkLib.ProofSystem.Whir.Spec.SingleRound

namespace Whir

namespace Spec

abbrev StatementRound
  {F : Type} [Field F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  {num_rounds : ℕ}
  (round : Fin num_rounds)
:
  Type
:=
  Statement (domain.subdomain round.val)

lemma statementRound_zero
  {F : Type} [Field F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  {num_rounds : ℕ}
  (h : 0 < num_rounds)
:
  StatementRound domain ⟨0, h⟩ =
  Statement domain
:= by
  unfold StatementRound
  rw [Domain.CosetFftDomain.subdomain_zero_eq_self]

-- TODO statementRound_succ
-- TODO take a look whether subdomain_subdomain_one / a general addition version can be proven without the less than hypothesis
-- alternatively, bring the hypothesis into StatementRound
-- NOTE, need to plan for the last round,
-- there is the case where num_vars is a multiple of num_sumcheck_rounds, then everything 'works' (reduces down to 0 vars)
-- still need to finalise
-- can restrict to that, or can handle a num_vars < num_sumcheck_rounds round separately
-- if this is the case, then ReductionRound may become a Fin.snoc

-- todo
-- oracleStatementRound non-recursive
-- witness round non-recursive
-- reductionround
-- reduction
-- figure out a way to make the reduction instance not break

abbrev OracleStatementRound
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ)
  {num_rounds : ℕ}
  (round : Fin num_rounds)
  (idx : OracleIdxPre)
:
  Type
:=
  OracleStatementPre (domain.subdomain round.val) (num_vars - round.val * num_sumcheck_rounds) idx

abbrev WitnessRound
  (F : Type) [Field F]
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ)
  {num_rounds : ℕ}
  (round : Fin num_rounds)
:
  Type
:=
  WitnessPreSumcheck F (num_vars - round.val * num_sumcheck_rounds)


def ReductionRound
  {OSpecIdx : Type}
  (oSpec : OracleSpec OSpecIdx)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
  (num_queries : ℕ)
  {num_rounds : ℕ}
  (round : Fin num_rounds)
  -- [(i :
  --     (preSumcheckPSpec F (num_vars - ↑round * ↑num_sumcheck_rounds) ++ₚ
  --           Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds ++ₚ
  --         restPSpec (Domain.CosetFftDomain.subdomain domain ↑round) num_sumcheck_rounds num_queries).MessageIdx) →
  --   OracleInterface
  --     ((preSumcheckPSpec F (num_vars - ↑round * ↑num_sumcheck_rounds) ++ₚ
  --             Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds ++ₚ
  --           restPSpec (Domain.CosetFftDomain.subdomain domain ↑round) num_sumcheck_rounds num_queries).Message i)]
: OracleReduction
    (oSpec := oSpec)
    (StmtIn := StatementRound domain round.castSucc)
    (OStmtIn := OracleStatementRound domain num_vars num_sumcheck_rounds round.castSucc)
    (WitIn := WitnessRound F num_vars num_sumcheck_rounds round.castSucc)
    (StmtOut := StatementRound domain round.succ)
    (OStmtOut := OracleStatementRound domain num_vars num_sumcheck_rounds round.succ)
    (WitOut := WitnessRound F num_vars num_sumcheck_rounds round.succ)
    (pSpec :=
      preSumcheckPSpec F (num_vars - round * num_sumcheck_rounds) ++ₚ
      Sumcheck.Spec.pSpec F (deg := 2) num_sumcheck_rounds ++ₚ
      restPSpec (domain.subdomain round) num_sumcheck_rounds num_queries
    )
    (Oₘ := sorry)
:= by convert (oracleReduction
  oSpec
  (domain.subdomain round.val)
  (num_vars - round.val * num_sumcheck_rounds)
  ⟨ num_sumcheck_rounds.val, sorry⟩
  h_num_sumcheck_rounds
  num_queries) using 1 -- TODO remove the convert



def reduction
  {OSpecIdx : Type}
  (oSpec : OracleSpec OSpecIdx)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ)
  {num_rounds : ℕ}
  (round : Fin num_rounds)
:= OracleReduction.seqCompose
  (Stmt := StatementRound domain)
  (OStmt := OracleStatementRound domain num_vars num_sumcheck_rounds)
  (Wit := WitnessRound F num_vars num_sumcheck_rounds)
  (R := ReductionRound oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds num_queries)


end Spec

end Whir
