/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dom Henderson
-/

import ArkLib.ProofSystem.Whir.Spec.SingleRound

namespace Whir

namespace Spec

section RecForDefeq

variable {F : Type} [Field F] {log_order : ℕ}

def subdomainRec_aux (log_order : ℕ) : ℕ → ℕ
  | 0         => log_order
  | round + 1 => subdomainRec_aux log_order round - 1

def subdomainRec
  (domain : Domain.SmoothCosetFftDomain log_order F) :
  (round : ℕ) → Domain.SmoothCosetFftDomain (subdomainRec_aux log_order round) F
  | 0         => domain
  | round + 1 => (subdomainRec domain round).subdomain 1

@[simp, grind =]
lemma subdomainRec_zero {domain : Domain.SmoothCosetFftDomain log_order F} :
   subdomainRec domain 0 = domain := rfl
  
@[simp, grind =]
lemma subdomainRec_succ {domain : Domain.SmoothCosetFftDomain log_order F} {round : ℕ} :
   subdomainRec domain (round + 1) = (subdomainRec domain round).subdomain 1 := rfl

@[simp, grind =]
lemma subdomainRec_aux_eq {log_order round : ℕ} :
  subdomainRec_aux log_order round = log_order - round := by
  induction round <;> grind [subdomainRec_aux]

@[grind _=_]
lemma subdomainRec_heq_subdomain
  {domain : Domain.SmoothCosetFftDomain log_order F} {round : ℕ} :
  subdomainRec domain round ≍ domain.subdomain round := by
  induction round <;> [(simp; rfl); grind]

def numVarsRec (num_vars : ℕ) (k : ℕ → ℕ) : ℕ → ℕ
  | 0         => num_vars
  | round + 1 => numVarsRec num_vars k round - k round

@[simp, grind =]
lemma numVarsRec_zero {num_vars : ℕ} {k : ℕ → ℕ} : numVarsRec num_vars k 0 = num_vars := rfl

@[simp, grind =]
lemma numVarsRec_succ {num_vars : ℕ} {k : ℕ → ℕ} {round : ℕ} :
  numVarsRec num_vars k (round + 1) = numVarsRec num_vars k round - k round := rfl

/-- `mᵢ = num_vars - Σ_{j < i} kⱼ`. -/
lemma numVarsRec_eq {num_vars : ℕ} {k : ℕ → ℕ} {round : ℕ} :
  numVarsRec num_vars k round = num_vars - ∑ j : Fin round, k j := by
  induction round with
  | zero => simp
  | succ round ih =>
    rw [numVarsRec_succ, ih, Fin.sum_univ_castSucc, Nat.sub_sub]
    rfl

@[simp]
lemma numVarsRec_const_eq {num_vars k round : ℕ} :
  numVarsRec num_vars (fun _ ↦ k) round = num_vars - round * k := by
  rw [numVarsRec_eq]
  simp

end RecForDefeq

section Types

variable
  {F : Type} [Field F]
  {log_order : ℕ}
  {num_rounds : ℕ}       

abbrev StatementRound
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (round : Fin num_rounds) : Type :=
  Statement (subdomainRec domain round.val)

abbrev OracleStatementRound
  [DecidableEq F]
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ → ℕ)
  (round : Fin num_rounds)
  (idx : OracleIdxPre) : Type :=
  OracleStatementPre
    (subdomainRec domain round.val)
    (numVarsRec num_vars num_sumcheck_rounds round.val) idx

abbrev WitnessRound
  (F : Type) [Field F]
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ → ℕ)
  (round : Fin num_rounds) : Type :=
  WitnessPreSumcheck F (numVarsRec num_vars num_sumcheck_rounds round.val)

end Types

-- WisDom
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

section DomRoundTypes

abbrev StatementRoundDom
  {F : Type} [Field F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  {num_rounds : ℕ}
  (round : Fin num_rounds)
:
  Type
:=
  Statement (domain.subdomain round.val)

abbrev OracleStatementRoundDom
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

abbrev WitnessRoundDom
  (F : Type) [Field F]
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ)
  {num_rounds : ℕ}
  (round : Fin num_rounds)
:
  Type
:=
  WitnessPreSumcheck F (num_vars - round.val * num_sumcheck_rounds)

variable
  {F : Type} [Field F]
  {log_order : ℕ}
  {num_rounds num_vars : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}
  {round : Fin num_rounds}
  {num_sumcheck_rounds : ℕ}
  {idx : OracleIdxPre}

lemma statementRound_eq_dom :
  StatementRound domain round = StatementRoundDom domain round := by
  unfold StatementRound StatementRoundDom
  rw! [subdomainRec_heq_subdomain]
  grind

lemma oracleStatementRound_eq_dom [DecidableEq F] :
  OracleStatementRound domain num_vars (fun _ ↦ num_sumcheck_rounds) round idx =
  OracleStatementRoundDom domain num_vars num_sumcheck_rounds round idx := by
  unfold OracleStatementRound OracleStatementRoundDom
  rw! (castMode := .all) [subdomainRec_heq_subdomain, subdomainRec_aux_eq, numVarsRec_const_eq]
  rfl

lemma witnessRound_eq_dom :
  WitnessRound F num_vars (fun _ ↦ num_sumcheck_rounds) round =
  WitnessRoundDom F num_vars num_sumcheck_rounds round := by
  change WitnessPreSumcheck F (numVarsRec num_vars (fun _ ↦ num_sumcheck_rounds) round.val) = _
  rw [numVarsRec_const_eq]

end DomRoundTypes

@[grind .]
lemma round_succ_mul_le
  {num_vars : ℕ}
  {num_sumcheck_rounds : Fin (num_vars + 1)}
  {round : Fin (num_vars / num_sumcheck_rounds)}
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0) :
  (round.val + 1) * num_sumcheck_rounds ≤ num_vars
:= (Nat.le_div_iff_mul_le (by grind)).1 round.isLt

@[grind .]
lemma num_sumcheck_rounds_lt_remaining
  {num_vars : ℕ}
  {num_sumcheck_rounds : Fin (num_vars + 1)}
  {round : Fin (num_vars / num_sumcheck_rounds)}
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
:
  num_sumcheck_rounds.val < num_vars - round.val * num_sumcheck_rounds.val + 1
:= by  
  have h := round_succ_mul_le (round := round) h_num_sumcheck_rounds
  grind

-- Either borked or the `oracleReduction` is being mis-called, I can't tell.
noncomputable def ReductionRoundIThinkBorked
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
  /-
    Alright, I have no idea what I am doing, _but_ -
    Looking at Dom's signature, we have `round : Fin num_rounds`.
    We're building this with `oracleReduction`, which wants
    `(num_sumcheck_rounds : Fin (num_vars + 1))`, and we have:
    - `num_sumcheck_rounds.val`
    - `numvars := num_vars - round.val * num_sumcheck_rounds`
    and thus `num_sumcheck_rounds.val < num_vars - round.val * num_sumcheck_rounds.val + 1`.
    This is false in general, see `*the proof`.
  -/
  (round : Fin num_rounds)
: OracleReduction
    (oSpec := oSpec)
    (StmtIn := StatementRound domain round.castSucc)
    (OStmtIn := OracleStatementRound domain num_vars (fun _ ↦ num_sumcheck_rounds) round.castSucc)
    (WitIn := WitnessRound F num_vars (fun _ ↦ num_sumcheck_rounds) round.castSucc)
    (StmtOut := StatementRound domain round.succ)
    (OStmtOut := OracleStatementRound domain num_vars (fun _ ↦ num_sumcheck_rounds) round.succ)
    (WitOut := WitnessRound F num_vars (fun _ ↦ num_sumcheck_rounds) round.succ)
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
  ⟨num_sumcheck_rounds.val, by
    -- `*the proof`
    by_cases h : (round.val + 1) * num_sumcheck_rounds.val ≤ num_vars
    · grind
    · have nope :
        ¬num_sumcheck_rounds.val < num_vars - round.val * num_sumcheck_rounds.val + 1 := by grind
      sorry⟩
  h_num_sumcheck_rounds
  num_queries) using 1 -- TODO remove the convert
      all_goals sorry

section RecSpec

variable {F : Type} [Field F] [DecidableEq F]
         {log_order : ℕ}
         {num_vars : ℕ}
         {num_sumcheck_rounds : Fin (num_vars + 1)}

@[grind .]
lemma num_sumcheck_rounds_lt_numVarsRec
  {round : Fin (num_vars / num_sumcheck_rounds)}
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0) :
  num_sumcheck_rounds.val < numVarsRec num_vars (fun _ ↦ num_sumcheck_rounds) round + 1 := by
  rw [numVarsRec_const_eq]
  exact num_sumcheck_rounds_lt_remaining h_num_sumcheck_rounds

@[grind .]
lemma lt_numVarsRec_add_one_of_sum {num_vars M : ℕ} {k : ℕ → ℕ} {i : Fin M}
  (h : ∑ j : Fin M, k j ≤ num_vars) : k i < numVarsRec num_vars k i + 1 := by
  rw [numVarsRec_eq, Fin.sum_univ_eq_sum_range k i]
  rw [Fin.sum_univ_eq_sum_range k M] at h
  have h_prefix : ∑ j ∈ Finset.range (i.val + 1), k j ≤ ∑ j ∈ Finset.range M, k j :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr i.isLt)
  rw [Finset.sum_range_succ] at h_prefix
  omega

/--
The statement is like this to ensure good defeq behaviour and typeclass inference.
-/
abbrev pSpecDefeqViable
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ → ℕ)
  (num_queries : ℕ)
  (round : ℕ)
  (h : num_sumcheck_rounds round < numVarsRec num_vars num_sumcheck_rounds round + 1) :=
  let r : Fin (numVarsRec num_vars num_sumcheck_rounds round + 1) :=
    ⟨num_sumcheck_rounds round, h⟩
  preSumcheckPSpec F (numVarsRec num_vars num_sumcheck_rounds round) ++ₚ
  Sumcheck.Spec.pSpec F (deg := 2) r ++ₚ
  restPSpec (subdomainRec domain round) r num_queries

end RecSpec

section FoldingParams

structure FoldingParams (num_vars : ℕ) where
  num_whir_rounds : ℕ
  num_sumcheck_rounds : ℕ → ℕ
  num_sumcheck_rounds_pos : ∀ i < num_whir_rounds, 0 < num_sumcheck_rounds i
  sum_num_sumcheck_rounds_le : ∑ j : Fin num_whir_rounds, num_sumcheck_rounds j ≤ num_vars

namespace FoldingParams

variable {num_vars : ℕ}

@[grind .]
lemma num_sumcheck_rounds_lt
  {sched : FoldingParams num_vars} {round : Fin sched.num_whir_rounds} :
  sched.num_sumcheck_rounds round < numVarsRec num_vars sched.num_sumcheck_rounds round + 1 :=
  lt_numVarsRec_add_one_of_sum sched.sum_num_sumcheck_rounds_le

end FoldingParams

end FoldingParams

noncomputable def ReductionRound
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {OSpecIdx : Type}
  {log_order : ℕ}
  {num_vars : ℕ}
  (oSpec : OracleSpec OSpecIdx)
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (params : FoldingParams num_vars)
  (num_queries : ℕ)
  (round : Fin params.num_whir_rounds) :
  OracleReduction
    (oSpec    := oSpec)
    (StmtIn   := StatementRound domain round.castSucc)
    (OStmtIn  := OracleStatementRound domain num_vars params.num_sumcheck_rounds round.castSucc)
    (WitIn    := WitnessRound F num_vars params.num_sumcheck_rounds round.castSucc)
    (StmtOut  := StatementRound domain round.succ)
    (OStmtOut := OracleStatementRound domain num_vars params.num_sumcheck_rounds round.succ)
    (WitOut   := WitnessRound F num_vars params.num_sumcheck_rounds round.succ)
    (pSpec    := pSpecDefeqViable domain num_vars params.num_sumcheck_rounds num_queries round
                   params.num_sumcheck_rounds_lt) :=
  oracleReduction
    oSpec
    (subdomainRec domain round)
    (numVarsRec num_vars params.num_sumcheck_rounds round)
    ⟨params.num_sumcheck_rounds round, params.num_sumcheck_rounds_lt⟩
    (by simpa [Fin.lt_def] using params.num_sumcheck_rounds_pos round round.isLt)
    num_queries

noncomputable def reduction
  {OSpecIdx : Type}
  (oSpec : OracleSpec OSpecIdx)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order : ℕ}
  {num_vars : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (params : FoldingParams num_vars)
  (num_queries : ℕ) :=
  OracleReduction.seqCompose
    (Stmt  := StatementRound domain)
    (OStmt := OracleStatementRound domain num_vars params.num_sumcheck_rounds)
    (Wit   := WitnessRound F num_vars params.num_sumcheck_rounds)
    (R     := ReductionRound oSpec domain params num_queries)

end Spec

end Whir
