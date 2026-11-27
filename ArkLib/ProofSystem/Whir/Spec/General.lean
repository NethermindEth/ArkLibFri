/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dom Henderson
-/

import ArkLib.ProofSystem.Whir.Spec.SingleRound
import ArkLib.Data.CodingTheory.ProximityGap.Folding

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
  (F : Type) [Field F]
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ → ℕ)
  (round : Fin num_rounds) : Type :=
  Statement F (numVarsRec num_vars num_sumcheck_rounds round.val)

abbrev OracleStatementRound
  [DecidableEq F]
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (round : Fin num_rounds)
  (idx : OracleIdxPre) : Type :=
  OracleStatementPre (subdomainRec domain round.val) idx

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
  (F : Type) [Field F]
  (num_vars : ℕ)
  (num_sumcheck_rounds : ℕ)
  {num_rounds : ℕ}
  (round : Fin num_rounds)
:
  Type
:=
  Statement F (num_vars - round.val * num_sumcheck_rounds)

abbrev OracleStatementRoundDom
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  {num_rounds : ℕ}
  (round : Fin num_rounds)
  (idx : OracleIdxPre)
:
  Type
:=
  OracleStatementPre (domain.subdomain round.val) idx

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
  StatementRound F num_vars (fun _ ↦ num_sumcheck_rounds) round =
  StatementRoundDom F num_vars num_sumcheck_rounds round := by
  unfold StatementRound StatementRoundDom
  rw [numVarsRec_const_eq]

lemma oracleStatementRound_eq_dom [DecidableEq F] :
  OracleStatementRound domain round idx =
  OracleStatementRoundDom domain round idx := by
  unfold OracleStatementRound OracleStatementRoundDom
  rw! (castMode := .all) [subdomainRec_heq_subdomain, subdomainRec_aux_eq]
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
  Sumcheck.Spec.pSpec F (deg := 2) r ++ₚ
  restPSpec (subdomainRec domain round) r num_queries

end RecSpec

section FoldingParams

@[grind cases]
structure FoldingParams (num_vars : ℕ) where
  num_whir_rounds : ℕ
  num_sumcheck_rounds : ℕ → ℕ
  num_sumcheck_rounds_pos : ∀ i ≤ num_whir_rounds, 0 < num_sumcheck_rounds i
  -- `Σ_{i = 0}^{M - 1} kᵢ ≤ m`
  sum_num_sumcheck_rounds_le : ∑ j : Fin (num_whir_rounds + 1), num_sumcheck_rounds j ≤ num_vars

namespace FoldingParams

variable {num_vars : ℕ}

@[grind .]
lemma num_sumcheck_rounds_lt
  {params : FoldingParams num_vars} {round : Fin (params.num_whir_rounds + 1)} :
  params.num_sumcheck_rounds round < numVarsRec num_vars params.num_sumcheck_rounds round + 1 :=
  lt_numVarsRec_add_one_of_sum params.sum_num_sumcheck_rounds_le

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
    (StmtIn   := StatementRound F num_vars params.num_sumcheck_rounds round.castSucc)
    (OStmtIn  := OracleStatementRound domain round.castSucc)
    (WitIn    := WitnessRound F num_vars params.num_sumcheck_rounds round.castSucc)
    (StmtOut  := StatementRound F num_vars params.num_sumcheck_rounds round.succ)
    (OStmtOut := OracleStatementRound domain round.succ)
    (WitOut   := WitnessRound F num_vars params.num_sumcheck_rounds round.succ)
    (pSpec    := pSpecDefeqViable domain num_vars params.num_sumcheck_rounds num_queries round
                   (params.num_sumcheck_rounds_lt (round := round.castSucc))) := by
  convert (oracleReduction
    oSpec
    (subdomainRec domain round)
    (numVarsRec num_vars params.num_sumcheck_rounds round)
    ⟨params.num_sumcheck_rounds round, params.num_sumcheck_rounds_lt (round := round.castSucc)⟩
    (by simpa [Fin.lt_def] using params.num_sumcheck_rounds_pos round round.isLt.le)
    num_queries) using 1
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
    rfl
  · rfl
  · rfl
  · rfl


noncomputable def lastRound
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {OSpecIdx : Type}
  {log_order : ℕ}
  {num_vars : ℕ}
  (oSpec : OracleSpec OSpecIdx)
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (params : FoldingParams num_vars) :
  letI round := params.num_whir_rounds
  letI remaining_vars := numVarsRec num_vars params.num_sumcheck_rounds round
  letI last_num_sumcheck_rounds : Fin (remaining_vars + 1) :=
    ⟨
      params.num_sumcheck_rounds round,
      params.num_sumcheck_rounds_lt (round := Fin.last _)
    ⟩
  OracleReduction
    (oSpec    := oSpec)
    (StmtIn   := StatementRound F num_vars params.num_sumcheck_rounds (Fin.last round))
    (OStmtIn  := OracleStatementPre (subdomainRec domain round))
    (WitIn    := WitnessPreSumcheck F remaining_vars)
    (StmtOut  := StatementRound F num_vars params.num_sumcheck_rounds (Fin.last round) ×
                 Sumcheck.Spec.StatementRound F remaining_vars last_num_sumcheck_rounds)
    (OStmtOut := OracleStatementMid (subdomainRec domain round))
    (WitOut   := WitnessPreSumcheck F remaining_vars)
    (pSpec    := Sumcheck.Spec.pSpec F 2 last_num_sumcheck_rounds) :=
  letI ω := subdomainRec domain params.num_whir_rounds
  letI remaining_vars := numVarsRec num_vars params.num_sumcheck_rounds params.num_whir_rounds
  letI last_num_sumcheck_rounds : Fin (remaining_vars + 1) :=
    ⟨
      params.num_sumcheck_rounds params.num_whir_rounds,
      (params.num_sumcheck_rounds_lt (round := Fin.last _))
    ⟩
  sumcheckReduction
    oSpec
    ω
    remaining_vars
    last_num_sumcheck_rounds
    (by grind)

-- I think we just want the second part of this.
-- /-- The final folding round of the FRI protocol begins with the verifier sending a random field
--   element as the challenge to the prover, then in contrast to the previous folding rounds simply
--   sends the folded polynomial to the verifier. -/
-- @[reducible]
-- def pSpec (F : Type) [Semiring F] [BEq F] [LawfulBEq F] : ProtocolSpec 2 :=
--   ⟨!v[.V_to_P, .P_to_V], !v[F, CompPoly.CPolynomial F]⟩

-- open MvPolynomial in
-- def preSumcheckPSpec
--   (F : Type) [CommSemiring F]
--   (num_vars : ℕ)
-- : ProtocolSpec 1 := ⟨
--   !v[.P_to_V],
--   !v[F⦃≤1⦄[X Fin num_vars]]
-- ⟩

open MvPolynomial in
/--
p. 33 - 3. + 4.
-/
abbrev pSpecFinal
         (F : Type) [Field F] [DecidableEq F]
         (num_vars : ℕ)
         {log_order : ℕ}
         (repetition_param : ℕ)
         (final_folding_parameter : ℕ)
         (domain : Domain.SmoothCosetFftDomain log_order F) : ProtocolSpec 2 :=
  ⟨
    !v[.P_to_V, .V_to_P],
    !v[
      F⦃≤1⦄[X Fin num_vars],
      Fin repetition_param → domain.subdomain final_folding_parameter
      -- L_{M-1}^{2^{k_{M-1}}}
      --         _____________ this does this bit, so we need to pass `L_{M-1}`
    ]
  ⟩

instance {F} [Field F] [DecidableEq F] {num_vars} {repetition_param log_order : ℕ}
         {final_folding_parameter : ℕ}
         {domain : Domain.SmoothCosetFftDomain log_order F} :
  ∀ j,
    OracleInterface (
      (pSpecFinal F num_vars repetition_param
                  final_folding_parameter domain).Message j)
  | _ => OracleInterface.instDefault

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
    (Stmt  := StatementRound F num_vars params.num_sumcheck_rounds)
    (OStmt := OracleStatementRound domain)
    (Wit   := WitnessRound F num_vars params.num_sumcheck_rounds)
    (R     := ReductionRound oSpec domain params num_queries)

noncomputable def reductionWithLastRound
  {OSpecIdx : Type}
  (oSpec : OracleSpec OSpecIdx)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {log_order num_vars : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (params : FoldingParams num_vars)
  (num_queries : ℕ)
:=
  OracleReduction.append
    (reduction oSpec domain params num_queries)
    (lastRound oSpec domain params)

--------------------

open MvPolynomial in
theorem eval₂_vappend_C_X_mem_restrictDegree_one {F : Type} [Field F] {n k m : ℕ}
    (h : n = k + m) (c : Fin k → MvPolynomial (Fin m) F) (hc : ∀ i, ∃ a, c i = C a)
    (p : MvPolynomial (Fin n) F) (hp : p ∈ restrictDegree (Fin n) F 1) :
    eval₂ C (fun i => Fin.vappend c (fun j : Fin m => MvPolynomial.X j) (Fin.cast h i)) p
      ∈ restrictDegree (Fin m) F 1 := by
  have key : ∀ (v : Fin m) (j : Fin (k + m)),
      degreeOf v (Fin.vappend c (fun j : Fin m => MvPolynomial.X j) j) ≠ 0 → j = Fin.natAdd k v := by
    intro v j hj
    induction j using Fin.addCases with
    | left j =>
      obtain ⟨a, ha⟩ := hc j
      simp [ha] at hj
    | right j =>
      simp only [Fin.vappend_right, degreeOf_X] at hj
      split_ifs at hj with hvj
      · rw [hvj]
      · exact absurd rfl hj
  refine eval₂_C_mem_restrictDegree_one p hp _ (fun i v => ?_) (fun v i j hi hj => ?_)
  · generalize Fin.cast h i = j
    induction j using Fin.addCases with
    | left j =>
      obtain ⟨a, ha⟩ := hc j
      simp [ha]
    | right j =>
      simp only [Fin.vappend_right, degreeOf_X]
      split <;> omega
  · exact Fin.cast_injective h ((key v _ hi).trans (key v _ hj).symm)

noncomputable def proverFinal
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {OSpecIdx : Type}
  {log_order : ℕ}
  {num_vars : ℕ}
  (oSpec : OracleSpec OSpecIdx)
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (params : FoldingParams num_vars)
  (num_queries : ℕ)
  (repetition_param : ℕ) :
  letI lastRound := Fin.last params.num_whir_rounds
  letI remaining_vars := numVarsRec num_vars params.num_sumcheck_rounds params.num_whir_rounds
  letI last_num_sumcheck_rounds : Fin (remaining_vars + 1) :=
    ⟨params.num_sumcheck_rounds params.num_whir_rounds,
      params.num_sumcheck_rounds_lt (round := lastRound)⟩
  OracleProver
    (oSpec := oSpec)
    (StmtIn :=
      StatementRound F num_vars params.num_sumcheck_rounds lastRound ×
      Sumcheck.Spec.StatementRound F remaining_vars last_num_sumcheck_rounds)
    (OStmtIn :=
      OracleStatementMid
        (subdomainRec domain params.num_whir_rounds)
    )
    (WitIn := WitnessPreSumcheck F remaining_vars)
    (StmtOut :=
      StatementRound F num_vars params.num_sumcheck_rounds lastRound ×
      Sumcheck.Spec.StatementRound F remaining_vars last_num_sumcheck_rounds)
    (OStmtOut :=
      OracleStatementMid
        (subdomainRec domain params.num_whir_rounds))
    (WitOut := WitnessPreSumcheck F remaining_vars)
    (pSpec :=
      pSpecFinal
        F
        (remaining_vars - last_num_sumcheck_rounds)
        repetition_param
        last_num_sumcheck_rounds
        (subdomainRec domain params.num_whir_rounds)
    ) :=
    letI lastRound := Fin.last params.num_whir_rounds
    let remaining_vars := numVarsRec num_vars params.num_sumcheck_rounds params.num_whir_rounds
    letI last_num_sumcheck_rounds : Fin (remaining_vars + 1) :=
      ⟨params.num_sumcheck_rounds params.num_whir_rounds,
        params.num_sumcheck_rounds_lt (round := lastRound)⟩
    {
    PrvState := fun _ ↦
      (
        (StatementRound F num_vars params.num_sumcheck_rounds lastRound ×
          Sumcheck.Spec.StatementRound F remaining_vars last_num_sumcheck_rounds) ×
        (∀ j, OracleStatementMid (subdomainRec domain params.num_whir_rounds) j)
      ) ×
      WitnessPreSumcheck F remaining_vars

    input := id
    sendMessage := fun i state ↦
      match i with
      | ⟨0, _⟩ =>
        let f_hat := state.2.f_hat.val
        letI num_vars := (numVarsRec num_vars params.num_sumcheck_rounds lastRound.val)
        letI num_args := num_vars - params.num_sumcheck_rounds params.num_whir_rounds
        let challenges := MvPolynomial.C ∘ state.1.1.2.challenges
        let args : Fin num_args → MvPolynomial (Fin num_args) F := fun (i : Fin num_args) ↦ MvPolynomial.X i
        let f_hat_applied := MvPolynomial.eval₂
          MvPolynomial.C
          (fun i =>
            (Fin.vappend challenges args)
            (Fin.cast
              (Nat.add_sub_of_le (Nat.lt_succ_iff.mp last_num_sumcheck_rounds.isLt)).symm i))
          f_hat
        pure ⟨⟨f_hat_applied,
          eval₂_vappend_C_X_mem_restrictDegree_one _ challenges (fun _ => ⟨_, rfl⟩) f_hat
            state.2.f_hat.property⟩, state⟩ -- something from witness
      | ⟨1, h⟩ => nomatch h
    receiveChallenge := fun i s ↦
      match i with
      | ⟨0, h⟩ => nomatch h
      | ⟨1, _⟩ => pure fun _ ↦ s
    output := fun x ↦ pure x
    }

noncomputable def verifierFinal
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {OSpecIdx : Type}
  {log_order : ℕ}
  {num_vars : ℕ}
  (oSpec : OracleSpec OSpecIdx)
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (params : FoldingParams num_vars)
  (num_queries : ℕ)
  (repetition_param : ℕ) :
  letI lastRound := Fin.last params.num_whir_rounds
  letI remaining_vars := numVarsRec num_vars params.num_sumcheck_rounds params.num_whir_rounds
  letI last_num_sumcheck_rounds : Fin (remaining_vars + 1) :=
    ⟨params.num_sumcheck_rounds params.num_whir_rounds,
      params.num_sumcheck_rounds_lt (round := lastRound)⟩
  OracleVerifier
    (oSpec := oSpec)
    (StmtIn :=
      StatementRound F num_vars params.num_sumcheck_rounds lastRound ×
      Sumcheck.Spec.StatementRound F remaining_vars last_num_sumcheck_rounds)
    (OStmtIn :=
      OracleStatementMid
        (subdomainRec domain params.num_whir_rounds))
    (StmtOut :=
      StatementRound F num_vars params.num_sumcheck_rounds lastRound ×
      Sumcheck.Spec.StatementRound F remaining_vars last_num_sumcheck_rounds)
    (OStmtOut :=
      OracleStatementMid
        (subdomainRec domain params.num_whir_rounds))
    (pSpec :=
      pSpecFinal
        F
        (remaining_vars - last_num_sumcheck_rounds)
        repetition_param
        last_num_sumcheck_rounds
        (subdomainRec domain params.num_whir_rounds)) where
  verify s challenges := do
    let remaining_vars := numVarsRec num_vars params.num_sumcheck_rounds params.num_whir_rounds
    let k := params.num_sumcheck_rounds params.num_whir_rounds
    let αs : Fin k → F := s.2.challenges
    let f_hat_M : MvPolynomial.restrictDegree (Fin (remaining_vars - k)) F 1 ←
      OracleComp.queryBind
      (Sum.inr (Sum.inr ⟨⟨0, rfl⟩, ()⟩))
      (fun x => do return (.some x))
    let rs := challenges ⟨1, rfl⟩
    let gs : Vector F repetition_param ←
      (Vector.finRange repetition_param).mapM (fun ℓ => do
        let ω := subdomainRec domain params.num_whir_rounds
        let z := rs ℓ
        let values ← (Vector.finRange (2 ^ subdomainRec_aux log_order params.num_whir_rounds)).mapM
          fun i =>
            if ω i ^ 2 ^ k = z.1
            then OptionT.mk (OracleComp.queryBind
              (Sum.inr (Sum.inl ⟨.CodeWord, ⟨ω i, Domain.CosetFftDomain.mem_toFinset_self⟩⟩))
              (fun y => pure (some y)))
            else pure 0
        return ProximityGap.iteratedFoldWord ω values.get k αs ((ω.subdomain k).log z))
    guard (∀ ℓ : Fin repetition_param,
      MvPolynomial.eval (fun j => ((rs ℓ : F)) ^ (2 ^ j.val)) f_hat_M.val = gs.get ℓ)
    let w_hat_sum : F := ∑ b : Fin (remaining_vars - k) → Fin 2,
      let b : Fin (remaining_vars - k) → F := fun j => ((b j).val : F)
      MvPolynomial.eval
        (Fin.cases (MvPolynomial.eval b f_hat_M.val) (fun v : Fin remaining_vars =>
          if h : v.val < k
          then αs ⟨v.val, h⟩
          else b ⟨v.val - k, by omega⟩))
        s.1.weightPolynomial.val
    guard (w_hat_sum = s.2.target)
    return s
  outputOracle := Sum.inl {
    embed := ⟨Sum.inl, Sum.inl_injective⟩
    hEq _ := rfl
    outputInterface_heq _ := HEq.rfl
  }

noncomputable def reductionFinal
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {OSpecIdx : Type}
  {log_order : ℕ}
  {num_vars : ℕ}
  (oSpec : OracleSpec OSpecIdx)
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (params : FoldingParams num_vars)
  (num_queries : ℕ)
  (repetition_param : ℕ)
:
  letI lastRound := Fin.last params.num_whir_rounds
  letI remaining_vars := numVarsRec num_vars params.num_sumcheck_rounds params.num_whir_rounds
  letI last_num_sumcheck_rounds : Fin (remaining_vars + 1) :=
    ⟨params.num_sumcheck_rounds params.num_whir_rounds,
      params.num_sumcheck_rounds_lt (round := lastRound)⟩
  OracleReduction
    (oSpec := oSpec)
    (StmtIn :=
      StatementRound F num_vars params.num_sumcheck_rounds lastRound ×
      Sumcheck.Spec.StatementRound F remaining_vars last_num_sumcheck_rounds)
    (OStmtIn :=
      OracleStatementMid
        (subdomainRec domain params.num_whir_rounds))
    (StmtOut :=
      StatementRound F num_vars params.num_sumcheck_rounds lastRound ×
      Sumcheck.Spec.StatementRound F remaining_vars last_num_sumcheck_rounds)
    (OStmtOut :=
      OracleStatementMid
        (subdomainRec domain params.num_whir_rounds))
    (WitIn := WitnessPreSumcheck F remaining_vars)
    (WitOut := WitnessPreSumcheck F remaining_vars)
    (pSpec :=
      pSpecFinal
        F
        (remaining_vars - last_num_sumcheck_rounds)
        repetition_param
        last_num_sumcheck_rounds
        (subdomainRec domain params.num_whir_rounds))
where
  prover := proverFinal oSpec domain params num_queries repetition_param
  verifier := verifierFinal oSpec domain params num_queries repetition_param

section

open ProtocolSpec

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
         {dir₁ : Fin m → Direction}
         {dir₂ : Fin n → Direction}
         {τ₁ : Fin m → Type}
         {τ₂ : Fin n → Type}

-- private instance theInstanceinstOracleInterfaceMessageAppend
--   [O₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
--   [O₂ : ∀ i, OracleInterface (pSpec₂.Message i)] :
--   ∀ i, OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message i) := by
--   dsimp [(·++ₚ·)] -- ProtocolSpec.append
--   change
--     (i : { i // (pSpec₁.dir ++ᵛ pSpec₂.dir) i = Direction.P_to_V }) →
--       OracleInterface ((pSpec₁.Type ++ᵛ pSpec₂.Type) ↑i)
--                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^
--   we are matching `OracleInterface ((pSpec₁.Type ++ᵛ pSpec₂.Type) ↑i)`
--   we need to be matching `Fin.vappend`
--   sorry

/--
This should replace the old instance
I just call it here with a different interface, so we should pilfer its body instead.
-/
local instance
  [O₁ : ∀ i : MessageIdx ⟨dir₁, τ₁⟩, OracleInterface (τ₁ i.1)]
  [O₂ : ∀ i : MessageIdx ⟨dir₂, τ₂⟩, OracleInterface (τ₂ i.1)]
  {i : ProtocolSpec.MessageIdx ⟨Fin.vappend dir₁ dir₂, Fin.vappend τ₁ τ₂⟩} :
  OracleInterface (Fin.vappend τ₁ τ₂ i.1) :=
  ProtocolSpec.instOracleInterfaceMessageAppend (pSpec₁ := ⟨dir₁, τ₁⟩) (pSpec₂ := ⟨dir₂, τ₂⟩) _

noncomputable def reductionFinalFull
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {OSpecIdx : Type}
  {log_order : ℕ}
  {num_vars : ℕ}
  (oSpec : OracleSpec OSpecIdx)
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (params : FoldingParams num_vars)
  (num_queries : ℕ)
  (repetition_param : ℕ)
:=
  OracleReduction.append
    (reductionWithLastRound oSpec domain params num_queries)
    (reductionFinal oSpec domain params num_queries repetition_param)

end

theorem nooope
  {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
  {OSpecIdx : Type} (oSpec : OracleSpec OSpecIdx) {log_order num_vars : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (params : Whir.Spec.FoldingParams num_vars) (num_queries repetition_param : ℕ) :
  reductionFinalFull oSpec domain params num_queries repetition_param =
  reductionFinalFull oSpec domain params num_queries repetition_param := rfl

#print axioms nooope -- We have a sorry `:sweat_smile:`


-- NOTE: `preSumcheckReduction` is actually the one we need for the step `p. 33 step 3.`


-- noncomputable def reductionFinal
--   {F : Type} [Field F] [DecidableEq F] [SampleableType F] [Inhabited F]
--   {OSpecIdx : Type}
--   {log_order : ℕ}
--   {num_vars : ℕ}
--   (oSpec : OracleSpec OSpecIdx)
--   (domain : Domain.SmoothCosetFftDomain log_order F)
--   (params : FoldingParams num_vars)
--   (num_queries : ℕ)
--   (repetition_param : ℕ) :
--   letI lastRound := Fin.last params.num_whir_rounds
--   OracleReduction
--     (oSpec    := oSpec)
--     (StmtIn   := StatementRound F num_vars params.num_sumcheck_rounds lastRound)
--     (OStmtIn  := OracleStatementRound domain (lastRound))
--     (WitIn    := WitnessRound F num_vars params.num_sumcheck_rounds (lastRound))
--     (StmtOut  := StatementRound F num_vars params.num_sumcheck_rounds lastRound)
--     (OStmtOut := OracleStatementRound domain lastRound)
--     (WitOut   := WitnessRound F num_vars params.num_sumcheck_rounds lastRound)
--     (pSpec    := pSpecFinal F num_vars repetition_param log_order
--                             (params.num_sumcheck_rounds params.num_whir_rounds) domain) where
--     prover := proverFinal oSpec domain params num_queries repetition_param
--     verifier := verifierFinal oSpec domain params num_queries repetition_param
  -- oracleReduction
  --   oSpec
  --   (subdomainRec domain round)
  --   (numVarsRec num_vars params.num_sumcheck_rounds round)
  --   ⟨params.num_sumcheck_rounds round, params.num_sumcheck_rounds_lt⟩
  --   (by simpa [Fin.lt_def] using params.num_sumcheck_rounds_pos round round.isLt)
  --   num_queries

-- /- Oracle reduction of the FRI protocol. -/
-- @[reducible]
-- def reduction :
--     OracleReduction []ₒ
--     (Statement F (0 : Fin (k + 1))) (OracleStatement s ω (0 : Fin (k + 1)))
--       (Witness F s d (0 : Fin (k + 2)))
--     (FinalStatement F k) (FinalOracleStatement s ω) (Witness F s d (Fin.last (k + 1)))
--     (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ QueryRound.pSpec l (ω := ω)) :=
--   OracleReduction.append (reductionFold k s d)
--     (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l)

end Spec

end Whir
