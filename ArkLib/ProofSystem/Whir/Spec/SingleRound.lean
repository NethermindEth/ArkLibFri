/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dom Henderson, Julian Sutherland
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

public import Mathlib.Tactic

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


universe v in
/-- Heterogeneous congruence for applying heterogeneously equal functions to proof arguments.
Both arguments are proofs, so they are automatically heterogeneously equal. -/
theorem heq_app_prop {p q : Prop} {γ δ : Sort v} (hγδ : γ = δ)
    {f : p → γ} {g : q → δ} (hf : HEq f g) (hp : p) (hq : q) : HEq (f hp) (g hq) := by
  subst hγδ
  have hpq : p = q := propext ⟨fun _ => hq, fun _ => hp⟩
  subst hpq
  have hfg : f = g := eq_of_heq hf
  subst hfg
  exact heq_of_eq (congrArg f (proof_irrel hp hq))

/-- The final sum-check round, as an index into the `num_sumcheck_rounds` rounds. -/
def lastSumcheckRound
  {num_vars : ℕ}
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
: Fin num_sumcheck_rounds.val :=
  ⟨num_sumcheck_rounds.val - 1, by have := Fin.lt_def.mp h_num_sumcheck_rounds; omega⟩

/-- The prover message carrying `h_k`, the response polynomial of the final sum-check round.
Since each sum-check round contributes one prover message followed by one challenge, this sits
at flat index `2 * (num_sumcheck_rounds - 1)` of the composed sum-check protocol. -/
def sumcheckResultIdx
  (F : Type) [Field F]
  {num_vars : ℕ}
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
: (Sumcheck.Spec.pSpec F (deg := 2) num_sumcheck_rounds).MessageIdx :=
  ProtocolSpec.sigmaMessageIdxToSeqCompose
    (lastSumcheckRound num_sumcheck_rounds h_num_sumcheck_rounds)
    (⟨0, rfl⟩ : (Sumcheck.Spec.SingleRound.pSpec F 2).MessageIdx)

section

universe u v w in
theorem _root_.Fin.fflatten₂_eq_splitSum
  {A : Sort u} {B : Sort v}
  {F : A → B → Sort w}
  {m : ℕ} {n : Fin m → ℕ}
  {α : (i : Fin m) → (j : Fin (n i)) → A}
  {β : (i : Fin m) → (j : Fin (n i)) → B}
  {v : (i : Fin m) → (j : Fin (n i)) → F (α i j) (β i j)}
  {k : Fin (Fin.vsum n)}
:
  Fin.fflatten₂ v k =
  cast (by {
    congr
    all_goals {
      conv_rhs=>rw! (castMode := .all) [←Fin.embedSum_splitSum k]
      rw [Fin.vflatten_embedSum]
    }
  }) (v k.splitSum.fst k.splitSum.snd)
:= by
  conv_lhs =>
    rw! (castMode := .all) [←Fin.embedSum_splitSum k]
  rw [Fin.fflatten₂_embedSum]
  grind

universe u v w in
theorem _root_.Fin.fflatten₂_heq_splitSum
  {A : Sort u} {B : Sort v}
  {F : A → B → Sort w}
  {m : ℕ} {n : Fin m → ℕ}
  {α : (i : Fin m) → (j : Fin (n i)) → A}
  {β : (i : Fin m) → (j : Fin (n i)) → B}
  {v : (i : Fin m) → (j : Fin (n i)) → F (α i j) (β i j)}
  {k : Fin (Fin.vsum n)}
:
  Fin.fflatten₂ v k ≍
  (v k.splitSum.fst k.splitSum.snd)
:= by
  simp [Fin.fflatten₂_eq_splitSum]

end

theorem _root_.ProtocolSpec.seqCompose_message_eq
  {m : ℕ}
  {n : Fin m → ℕ}
  {pSpec : ∀ i, ProtocolSpec (n i)}
  (i : (ProtocolSpec.seqCompose pSpec).MessageIdx)
:
  (ProtocolSpec.seqCompose pSpec).Message i =
  (pSpec (ProtocolSpec.seqComposeMessageIdxToSigma i).1).Message
    (ProtocolSpec.seqComposeMessageIdxToSigma i).2 := by
  unfold ProtocolSpec.Message ProtocolSpec.seqComposeMessageIdxToSigma
  simp only [ProtocolSpec.seqCompose_type]
  conv_lhs => rw [← Fin.embedSum_splitSum i.1]
  rw [Fin.vflatten_embedSum]

lemma app_cast_fun
  {A B C D}
  {f : A → B}
  {h_fun : (A → B) = (C → D)}
  {arg : C}
  (h_arg : C = A)
  (h_result : B = D)
:
  (cast h_fun f) arg =
  (cast h_result (f (cast h_arg arg)))
:= by
  aesop

lemma christina
  {F} [CommSemiring F]
  {num_sumcheck_rounds : ℕ}
  (idx : Fin (Fin.vsum fun (_ : Fin num_sumcheck_rounds) ↦ 2))
  {h_idx}
:
  (
    (fun h' ↦ Sumcheck.Spec.SingleRound.instOracleInterfaceMessagePSpec F 2 ⟨idx.splitSum.snd, h'⟩)
    h_idx
  ).1 = F
:= by
  set x := idx.splitSum.snd with x_eq
  obtain ⟨idx_val, h_idx_val⟩ := x
  rw! [←x_eq]
  by_cases h_x : idx_val = 0
  · subst h_x
    rfl
  · have : idx_val = 1 := by grind
    rw! [this] at h_idx
    simp only [
      Nat.reduceAdd, Nat.add_zero,
      Fin.vcons_fin_zero, Fin.vappend_zero, Fin.mk_one,
      Fin.isValue
    ] at h_idx
    rewrite [Fin.vappend_right_of_not_lt] at h_idx
    · simp at h_idx
    · grind

section EqualByParts

variable
  {m : ℕ}
  {n : Fin m → ℕ}
  {pSpec : ∀ i, ProtocolSpec (n i)}
  [inst : ∀ i j, OracleInterface ((pSpec i).Message j)]
  {i : Fin m}
  {j : (pSpec i).MessageIdx}

open ProtocolSpec

/-
A few notes:
The `heq_apply` bit is just `dcongr_heq` in Mathlib (it also has a redundant `hα` hypothesis, ehh)

The trick is to talk about the instance in isolation `seqCompose_message_inst`, and handwave
the definitional type mismatch with `heq` at an abstract level, then immediately prove it in
`seqCompose_message_type`. The `heq` proofs don't make you want to strangle baby seals
if they're in a small abstract context without any detail.
-/

/--
Composition preserves oracle interfaces of messages.
-/
@[simp, grind =]
theorem seqCompose_message_inst
:
  ProtocolSpec.instOracleInterfaceMessageSeqCompose (sigmaMessageIdxToSeqCompose i j) ≍
  inst i j
:= by
  cbv
  simp only [Fin.fflatten₂_embedSum]
  exact dcongr_heq (by simp) (by simp) (fun _ _ => cast_heq _ _)

omit inst in
/--
Composition preserves types of messages.
-/
@[simp, grind =]
theorem seqCompose_message_type
:
  (seqCompose pSpec).Message (sigmaMessageIdxToSeqCompose i j) = (pSpec i).Message j
:= by
  simp [sigmaMessageIdxToSeqCompose]

open ProtocolSpec in
/--
Composition preserves types of queries.
-/
@[simp]
theorem seqCompose_query_eq
:
  OracleInterface.Query ((seqCompose pSpec).Message (sigmaMessageIdxToSeqCompose i j)) =
  OracleInterface.Query ((pSpec i).Message j)
:= by
  grind

end EqualByParts

lemma sumcheckResultMessageType
  (F) [Field F]
  {num_vars : ℕ}
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
:
  OracleInterface.Query
    ((Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds).Message
      (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds)) =
  F
:=
  seqCompose_query_eq

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
    (OuterOStmtOut := OracleStatementMid domain num_vars num_sumcheck_rounds)
    (OuterWitIn := WitnessPreSumcheck F num_vars)
    (InnerWitIn := Unit)
    (InnerWitOut := Unit)
    (OuterWitOut := WitnessPostSumcheck F num_vars)
where
  stmt := OracleStatement.sumcheckExecutableLens
    domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds
  wit := Witness.sumcheckLens
    domain num_vars num_sumcheck_rounds

def sumcheckChallengeIdx
  (F : Type) [CommSemiring F]
  (num_sumcheck_rounds : ℕ)
:
  Fin num_sumcheck_rounds → (Sumcheck.Spec.pSpec F 2 num_sumcheck_rounds).ChallengeIdx
:= fun round =>
  ProtocolSpec.sigmaChallengeIdxToSeqCompose round ⟨1, rfl⟩

def sumcheckChallenge
  {F : Type} [CommSemiring F]
  {num_sumcheck_rounds : ℕ}
  (round : Fin num_sumcheck_rounds)
  (challenges : (Sumcheck.Spec.pSpec F 2 num_sumcheck_rounds).Challenges)
:
  F
:=
  cast (by {
    aesop (add simp [sumcheckChallengeIdx, ProtocolSpec.sigmaChallengeIdxToSeqCompose])
  }) (challenges (sumcheckChallengeIdx F num_sumcheck_rounds round))

lemma snd_heq_inr
  {pSpecLength1 pSpecLength2}
  {pSpec1 : ProtocolSpec pSpecLength1}
  {pSpec2 : ProtocolSpec pSpecLength2}
  (challenges : (pSpec1 ++ₚ pSpec2).Challenges)
  (idx)
:
  challenges.snd idx ≍
  challenges (ProtocolSpec.ChallengeIdx.inr idx)
:= by
  apply heq_of_eq_cast
  rfl

lemma snd_eq_cast_inr
  {pSpecLength1 pSpecLength2}
  {pSpec1 : ProtocolSpec pSpecLength1}
  {pSpec2 : ProtocolSpec pSpecLength2}
  (challenges : (pSpec1 ++ₚ pSpec2).Challenges)
  (idx)
:
  challenges.snd idx =
  cast (ProtocolSpec.challenge_append_inr idx) (challenges (ProtocolSpec.ChallengeIdx.inr idx))
:= by
  rfl

-- example
--   {pSpecLength1 pSpecLength2}
--   {pSpec1 : ProtocolSpec pSpecLength1}
--   {pSpec2 : ProtocolSpec pSpecLength2}
--   {idx : ProtocolSpec.ChallengeIdx pSpec2}
--   {inr_round}
--   (h)
-- :
--   (ProtocolSpec.sigmaChallengeIdxToSeqCompose inr_round idx).inr =
--   sorry
-- := by
--   ext
--   exact h


lemma sumcheckChallenge_succ
  {F : Type} [CommSemiring F]
  {num_sumcheck_rounds : ℕ}
  (round : Fin (num_sumcheck_rounds + 1))
  (challenges :
    (Sumcheck.Spec.SingleRound.pSpec F 2 ++ₚ
     Sumcheck.Spec.pSpec F 2 num_sumcheck_rounds).Challenges)
:
  sumcheckChallenge round challenges =
  letI chal : F := challenges.fst ⟨1, rfl⟩
  ((fun (_ : Fin 1) ↦ chal) ++ᵛ (sumcheckChallenge · challenges.snd)) (round.cast (by grind))
:= by
  obtain _ | round := round
  · rewrite [Fin.vappend_left_of_lt]
    · rfl
    · grind
  · rewrite [Fin.vappend_right_of_not_lt]
    · simp only [
        sumcheckChallenge, Fin.vsum_succ, sumcheckChallengeIdx, Nat.reduceAdd, Nat.add_zero,
        Fin.vcons_fin_zero, Nat.cast_ofNat, Fin.vappend_zero, Fin.isValue, ProtocolSpec.Challenge,
        Fin.cast_mk, Nat.add_one_sub_one
      ]
      rewrite [snd_eq_cast_inr]
      apply cast_eq_iff_heq.mpr
      · symm
        apply (cast_heq_iff_heq _ _ _).mpr
        · apply (cast_heq_iff_heq _ _ _).mpr
          · congr
          · grind



-- lemma sumcheckChallenge_eq
--   {F : Type} [CommSemiring F]
--   {num_sumcheck_rounds : ℕ}
--   (round : Fin num_sumcheck_rounds)
--   (challenges : (Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds).Challenges)
-- :
--   sumcheckChallenge round challenges =
--   sorry
-- := by
--   simp [Sumcheck.Spec.pSpec] at challenges
--   simp [sumcheckChallenge]
--   done

section ByPartsAgain

/-
A few notes:

Once again, don't deal with `heq` 'concretely', wrap in lemmas a'la the old `heq_apply` but not bad.

I still dislike 'this' indentation, just so you know.
-/

variable {α β : Type}
         {Oracle₁ : OracleInterface α} {Oracle₂ : OracleInterface β}
         {query₁ : Oracle₁.Query} {query₂ : Oracle₂.Query}
         {message₁ : α} {message₂ : β}

/--
Response congruence.
-/
@[grind .]
theorem responose_congr (h₁ : α = β) (h₂ : Oracle₁ ≍ Oracle₂) (h₃ : query₁ ≍ query₂)
:
  Oracle₁.Response query₁ = Oracle₂.Response query₂
:= by grind

/--
Answer congruence.
-/
@[grind .]
theorem answer_congr (h₁ : α = β) (h₂ : Oracle₁ ≍ Oracle₂)
                     (h₃ : message₁ ≍ message₂) (h₄ : query₁ ≍ query₂)
:
  Oracle₁.answer message₁ query₁ ≍ Oracle₂.answer message₂ query₂
:= by grind

end ByPartsAgain

lemma answer_cast
  (F : Type) [Field F] [DecidableEq F]
  (log_order : ℕ)
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
  (messages : (i : (Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds).MessageIdx) →
    (Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds).Message i)
  (queryData : F)
  (h : (Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds).Message (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds) =
    OracleStatementMid domain num_vars (↑num_sumcheck_rounds) OracleIdxMid.SumcheckResult)
:
  @OracleInterface.answer
    (OracleStatementMid domain num_vars (↑num_sumcheck_rounds) 3)
    (OracleStatement.oracleInterfaceMid domain num_vars ↑num_sumcheck_rounds ⟨3, by trivial⟩)
    (cast h (messages (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds)))
    queryData =
  cast
    (by exact responose_congr h seqCompose_message_inst (cast_heq _ _)) -- `by exact` is on purpose
    (@OracleInterface.answer
    ((Sumcheck.Spec.pSpec F 2 ↑num_sumcheck_rounds).Message (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds))
    _
    (messages (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds))
    (cast (by {
      symm
      convert sumcheckResultMessageType _ _ _
    }) queryData)
  ) -- (OracleInterface.answer (messages (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds) (cast (by sorry) queryData)))
:= by
  rewrite [←heq_iff_eq, heq_cast_iff_heq]
  exact (answer_congr h seqCompose_message_inst (by grind) (by grind)).symm

universe u v in
lemma pure_cast
  (A B)
  (a : A)
  (h : A = B)
  {monad : Type u → Type v}
  [inst : Pure monad]
:
  @pure monad inst B (cast h a) =
  cast (by rw [h]) (@pure monad inst A a)
:= by
  grind only

-- example
--   {OSpecIdx : Type}
--   {oSpec : OracleSpec OSpecIdx}
--   {num_verifiers : ℕ}
--   {OStmtIdx : Fin (num_verifiers + 1) → Type}
--   {Stmt : Fin (num_verifiers + 1) → Type}
--   {OStmt : (i : Fin (num_verifiers + 1)) → OStmtIdx i → Type}
--   [(i : Fin (num_verifiers + 1)) → (j : OStmtIdx i) → OracleInterface (OStmt i j)]
--   {pSpec_lengths : Fin num_verifiers → ℕ}
--   {pSpec : (i : Fin num_verifiers) → ProtocolSpec (pSpec_lengths i)}
--   [(i : Fin (num_verifiers)) → (i_1 : (pSpec i).MessageIdx) → OracleInterface ((pSpec i).Message i_1)]
--   {verifiers :
--     (i : Fin num_verifiers) →
--     OracleVerifier
--       oSpec
--       (Stmt i.castSucc)
--       (OStmt i.castSucc)
--       (Stmt i.succ)
--       (OStmt i.succ)
--       (pSpec i)
--   }
-- :
--   (OracleVerifier.seqCompose Stmt OStmt verifiers).outputOracle =
--   sorry
-- := by
--   unfold OracleVerifier.seqCompose OracleVerifier.seqCompose'
--   split
--   · done
--   · unfold OracleVerifier.append appendOutputSimulation
--     dsimp
--     done

--   done

-- example
--   {OSpecIdx : Type}
--   {oSpec : OracleSpec OSpecIdx}
--   {num_verifiers : ℕ}
--   {OStmtIdx : Fin (num_verifiers + 1) → Type}
--   {Stmt : Fin (num_verifiers + 1) → Type}
--   {OStmt : (i : Fin (num_verifiers + 1)) → OStmtIdx i → Type}
--   [(i : Fin (num_verifiers + 1)) → (j : OStmtIdx i) → OracleInterface (OStmt i j)]
--   {pSpec_lengths : Fin num_verifiers → ℕ}
--   {pSpec : (i : Fin num_verifiers) → ProtocolSpec (pSpec_lengths i)}
--   [(i : Fin (num_verifiers)) → (i_1 : (pSpec i).MessageIdx) → OracleInterface ((pSpec i).Message i_1)]
--   {verifiers :
--     (i : Fin num_verifiers) →
--     OracleVerifier
--       oSpec
--       (Stmt i.castSucc)
--       (OStmt i.castSucc)
--       (Stmt i.succ)
--       (OStmt i.succ)
--       (pSpec i)
--   }
-- :
--   (OracleVerifier.seqCompose Stmt OStmt verifiers).materializeOutput =
--   fun challenges oStmt messages => sorry
-- := by
--   unfold OracleVerifier.materializeOutput
--   funext challenges oStmt messages
--   unfold OracleVerifier.materializeOutputOracle

--   done

@[simp, grind =]
lemma OracleVerifier.append_materializeOutput
  {OSpecIdx1}
  {oSpec1 : OracleSpec OSpecIdx1}
  {StmtIn1 : Type}
  {OStmtInIdx1 : Type}
  {OStmtIn1 : OStmtInIdx1 → Type}
  {StmtOut1 : Type}
  {OStmtOutIdx1 : Type}
  {OStmtOut1 : OStmtOutIdx1 → Type}
  {pSpecLength1}
  {pSpec1 : ProtocolSpec pSpecLength1}
  [(i : OStmtInIdx1) → OracleInterface (OStmtIn1 i)]
  [(i : OStmtOutIdx1) → OracleInterface (OStmtOut1 i)]
  [(i : pSpec1.MessageIdx) → OracleInterface (pSpec1.Message i)]
  {StmtOut2 : Type}
  {OStmtOutIdx2 : Type}
  {OStmtOut2 : OStmtOutIdx2 → Type}
  {pSpecLength2}
  {pSpec2 : ProtocolSpec pSpecLength2}
  [(i : OStmtOutIdx2) → OracleInterface (OStmtOut2 i)]
  [(i : pSpec2.MessageIdx) → OracleInterface (pSpec2.Message i)]
  (verifier1 : OracleVerifier oSpec1 StmtIn1 OStmtIn1 StmtOut1 OStmtOut1 pSpec1)
  (verifier2 : OracleVerifier oSpec1 StmtOut1 OStmtOut1 StmtOut2 OStmtOut2 pSpec2)
  {challenges oStmt messages i}
:
  (OracleVerifier.append verifier1 verifier2).materializeOutput challenges oStmt messages i =
  verifier2.materializeOutput
    challenges.snd
    (verifier1.materializeOutput challenges.fst oStmt messages.fst)
    messages.snd
    i
:= rfl

lemma materializeOutput_append
  {OSpecIdx : Type} {oSpec : OracleSpec OSpecIdx}
  {m : ℕ}
  {Stmt : Fin (m + 2) → Type}
  {ιₛ : Fin (m + 2) → Type} {OStmt : (i : Fin (m + 2)) → ιₛ i → Type}
  (Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j))
  {arity : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (arity i)}
  (Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j))
  (V : (i : Fin (m + 1)) → OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc)
    (Stmt i.succ) (OStmt i.succ) (pSpec i))
  (challenges : (pSpec 0 ++ₚ ProtocolSpec.seqCompose (fun i => pSpec i.succ)).Challenges)
  (oStmt : ∀ j, OStmt 0 j)
  (messages : (pSpec 0 ++ₚ ProtocolSpec.seqCompose (fun i => pSpec i.succ)).Messages)
:
  (OracleVerifier.append
    (V 0)
    (OracleVerifier.seqCompose
      (Stmt ∘ Fin.succ)
      (fun i => OStmt (Fin.succ i))
      (Oₛ := fun i => Oₛ (Fin.succ i))
      (Oₘ := fun i => Oₘ (Fin.succ i))
      (fun i => V (Fin.succ i))
    )
  ).materializeOutput
    challenges
    oStmt
    messages =
  (OracleVerifier.seqCompose
    (Oₛ := fun i => Oₛ i.succ)
    (Oₘ := fun i => Oₘ i.succ)
    (Stmt ∘ Fin.succ)
    (fun i => OStmt i.succ)
    (fun i => V i.succ)
  ).materializeOutput
    challenges.snd
    ((V 0).materializeOutput (Oₛᵢ := Oₛ 0) (Oₘ := Oₘ 0) (Oₛₒ := Oₛ 1)
      challenges.fst oStmt messages.fst)
  messages.snd
:= rfl

lemma materializeOutput_append_fixed
  {OSpecIdx : Type} {oSpec : OracleSpec OSpecIdx}
  {num_rounds : ℕ}
  {Stmt : Fin (num_rounds + 2) → Type}
  {OStmtIdx : Fin (num_rounds + 2) → Type}
  {OStmt : (round : Fin (num_rounds + 2)) → OStmtIdx round → Type}
  (OStmtInterface : ∀ round, ∀ idx, OracleInterface (OStmt round idx))
  {pSpecLength : ℕ}
  {pSpec : ProtocolSpec pSpecLength}
  (msgInterface : ∀ j, OracleInterface (pSpec.Message j))
  (V :
    (round : Fin (num_rounds + 1)) →
    OracleVerifier
      oSpec
      (Stmt round.castSucc)
      (OStmt round.castSucc)
      (Stmt round.succ)
      (OStmt round.succ)
      pSpec)
  (challenges : (pSpec ++ₚ ProtocolSpec.seqCompose (fun _ => pSpec)).Challenges)
  (oStmt : ∀ idx, OStmt 0 idx)
  (messages : (pSpec ++ₚ ProtocolSpec.seqCompose (fun _ => pSpec)).Messages)
:
  (OracleVerifier.append
    (V 0)
    (OracleVerifier.seqCompose
      (Stmt ∘ Fin.succ)
      (fun i => OStmt (Fin.succ i))
      (Oₛ := fun i => OStmtInterface (Fin.succ i))
      (Oₘ := fun _ => msgInterface)
      (fun i => V (Fin.succ i))
    )
  ).materializeOutput
    challenges
    oStmt
    messages =
  (OracleVerifier.seqCompose
    (Oₛ := fun i => OStmtInterface i.succ)
    (Oₘ := fun _ => msgInterface)
    (Stmt ∘ Fin.succ)
    (fun i => OStmt i.succ)
    (fun i => V i.succ)
  ).materializeOutput
    challenges.snd
    ((V 0).materializeOutput (Oₛᵢ := OStmtInterface 0) (Oₘ := msgInterface) (Oₛₒ := OStmtInterface 1)
      challenges.fst oStmt messages.fst)
  messages.snd
:= rfl


/-
Questions:
- Why is the degree fixed to 2?
-/

section

open Sumcheck.Spec

structure MultiRoundData (F : Type) [CommSemiring F] (n k : ℕ) (round : Fin (n + 1)) where
  oracleState : ∀ j, OracleStatementRound F n 2 round j
  challenges  : (Sumcheck.Spec.pSpec F 2 k).Challenges
  messages    : (Sumcheck.Spec.pSpec F 2 k).Messages

abbrev SingleRoundData (F : Type) [CommSemiring F] (n : ℕ) (round : Fin (n + 1)) :=
  MultiRoundData F n 1 round

variable {F : Type} [CommSemiring F]
         {m n : ℕ} {i : Fin n} {data : SingleRoundData F n i.castSucc}
         {D : Fin m ↪ F}
         {ι : Type} {oSpec : OracleSpec ι}
         {StmtIn StmtOut : Type}
         {roundIn roundOut : Fin (n + 1)}
         {round : Fin (n + 1)}
         {data : MultiRoundData F n m round}
         {dataSingle : SingleRoundData F n i.castSucc}

abbrev SumcheckVerifier
  (oSpec : OracleSpec ι)
  (F : Type) [CommSemiring F]
  (n : ℕ)
  (StmtIn : Type)
  (roundIn : Fin (n + 1)) (StmtOut : Type) (roundOut : Fin (n + 1))
:=
  OracleVerifier
    oSpec
    StmtIn
    (OracleStatementRound F n 2 roundIn)
    StmtOut
    (OracleStatementRound F n 2 roundOut)
    (SingleRound.pSpec F 2)

abbrev SumcheckVerifiers
  (oSpec : OracleSpec ι)
  (F : Type) [CommSemiring F]
  (n : ℕ)
  (Stmt : Fin (m + 1) → Type)
  (round : Fin (m + 1) → Fin (n + 1))
:=
  ∀ i : Fin m,
    SumcheckVerifier oSpec F n (Stmt i.castSucc) (round i.castSucc) (Stmt i.succ) (round i.succ)

def MultiRoundData.appendedChallenges
  (data : MultiRoundData F n m round) : Fin (round.val + m) → F
:= data.oracleState .challenges ++ᵛ (sumcheckChallenge · data.challenges)

@[simp low, grind =]
lemma MultiRoundData.appendedChallenges_castAdd {r : Fin round.val}
:
  data.appendedChallenges (.castAdd m r) = data.oracleState .challenges r
:= Fin.vappend_left _ _ r

@[simp low, grind =]
lemma MultiRoundData.appendedChallenges_natAdd {r : Fin m}
:
  data.appendedChallenges (.natAdd round.val r) = sumcheckChallenge r data.challenges
:= Fin.vappend_right _ _ r

@[grind =]
lemma MultiRoundData.appendedChallenges_of_lt {r : Fin (round.val + m)}
  (h : r.val < round.val)
:
  data.appendedChallenges r = data.oracleState .challenges ⟨r.val, h⟩
:= Fin.vappend_left_of_lt _ _ r h

@[grind =]
lemma SingleRoundData.appendedChallenges_eq_snoc :
  dataSingle.appendedChallenges =
  Fin.snoc
    (α := fun _ ↦ F)
    (dataSingle.oracleState OracleIdx.challenges)
    (sumcheckChallenge 0 dataSingle.challenges)
:= Fin.vconcat_eq_snoc _ _

noncomputable def _root_.OracleVerifier.materializeChallenges
  (verifier :
    OracleVerifier oSpec
      StmtIn (OracleStatementRound F n 2 roundIn)
      StmtOut (OracleStatementRound F n 2 roundOut)
      (Sumcheck.Spec.pSpec F 2 m))
  (data : MultiRoundData F n m roundIn)
:
  Fin roundOut.val → F
:=
  verifier.materializeOutput
    data.challenges data.oracleState data.messages OracleIdx.challenges

@[grind =]
def _root_.OracleVerifier.AppendsChallengesSingleRound
  (verifier : SumcheckVerifier oSpec F n StmtIn roundIn StmtOut roundOut)
:
  Prop
:=
  ∃ h : roundOut.val = roundIn.val + 1, -- This is just a funny looking 'dependent' `∧`
    ∀ data : SingleRoundData F n roundIn,
      verifier.materializeChallenges data = data.appendedChallenges ∘ Fin.cast h

def MultiRoundData.head (data : MultiRoundData F n (m + 1) round) : SingleRoundData F n round :=
  ⟨
    data.oracleState,
    ProtocolSpec.Challenges.fst (pSpec₂ := Sumcheck.Spec.pSpec ..) data.challenges,
    ProtocolSpec.Messages.fst (pSpec₂ := Sumcheck.Spec.pSpec ..) data.messages
  ⟩

section

variable {mid : Fin (n + 1)} {StmtMid : Type} {data : MultiRoundData F n (m + 1) roundIn}

noncomputable def MultiRoundData.tail
  (data : MultiRoundData F n (m + 1) roundIn)
  (head : SumcheckVerifier oSpec F n StmtIn roundIn StmtMid mid)
:
  MultiRoundData F n m mid
:=
  ⟨
    head.materializeOutput data.head.challenges data.head.oracleState data.head.messages,
    ProtocolSpec.Challenges.snd (pSpec₂ := Sumcheck.Spec.pSpec ..) data.challenges,
    ProtocolSpec.Messages.snd (pSpec₂ := Sumcheck.Spec.pSpec ..) data.messages
  ⟩

@[simp, grind =]
lemma materializeChallenges_append
  {head : SumcheckVerifier oSpec F n StmtIn roundIn StmtMid mid}
  {tail : OracleVerifier (StmtOut := StmtOut) (OStmtOut := OracleStatementRound F n 2 roundOut) ..}
  {data}
:
  OracleVerifier.materializeChallenges (m := m + 1) (head.append tail) data =
  tail.materializeChallenges (data.tail head)
:= rfl

end

@[grind =]
lemma materializeChallenges_of_lt
  {verifier : SumcheckVerifier oSpec F n StmtIn roundIn StmtOut roundOut}
  (h₁ : verifier.AppendsChallengesSingleRound)
  {data : SingleRoundData _ _ roundIn}
  {r : Fin roundOut.val}
  (h₂ : r.val < roundIn.val)
:
  verifier.materializeChallenges data r = data.oracleState .challenges ⟨r.val, h₂⟩
:= by
  rcases h₁ with ⟨_, head⟩; specialize head data
  rw [head]
  grind

variable [DecidableEq F] [SampleableType F]

@[grind =]
private lemma materializeChallenges_oracleVerifier_eq_snoc :
  (SingleRound.oracleVerifier F n 2 D oSpec i).materializeChallenges dataSingle =
  Fin.snoc
    (α := fun _ ↦ F)
    (dataSingle.oracleState OracleIdx.challenges)
    (sumcheckChallenge 0 dataSingle.challenges) := rfl

attribute [local grind =]
  Vector.get_mk Fin.snoc_last Fin.vappend_right_of_not_lt Fin.vappend_left_of_lt Fin.snoc_castSucc

@[simp, grind =]
lemma materializeChallenges_oracleVerifier :
  (SingleRound.oracleVerifier F n 2 D oSpec i).materializeChallenges dataSingle =
  dataSingle.appendedChallenges := by grind

@[simp, grind! .]
lemma singleRound_appendsChallenge :
  (SingleRound.oracleVerifier F n 2 D oSpec i).AppendsChallengesSingleRound :=
  ⟨rfl, fun _ ↦ materializeChallenges_oracleVerifier⟩

section

omit [DecidableEq F] [SampleableType F]

variable {round : Fin (m + 1) → Fin (n + 1)} {Stmt : Fin (m + 1) → Type}
         {verifiers : SumcheckVerifiers oSpec F n Stmt round}

lemma sizeAgrees
  (h : ∀ i : Fin m, (verifiers i).AppendsChallengesSingleRound)
:
  (round (Fin.last m)).val = (round 0).val + m
:= by
  have h {i : Fin (m + 1)} : (round i).val = (round 0).val + i.val := by
    induction i using Fin.induction <;> grind
  grind

/--
Note:
  - round's _type_ is also generalised
-/
lemma materializeChallenges_seqCompose
  {data : MultiRoundData F n m (round 0)}
  (h : ∀ i : Fin m, (verifiers i).AppendsChallengesSingleRound)
:
  (OracleVerifier.seqCompose
    Stmt
    (fun i j ↦ OracleStatementRound F n 2 (round i) j) verifiers).materializeChallenges data =
  data.appendedChallenges ∘ Fin.cast (sizeAgrees h)
:= by
  induction' m with m ih
  · rfl
  · funext r
    let lhsLength := (round 0).val -- The ones already in end here
    by_cases eq : r.val < lhsLength
    · simp
      rw [MultiRoundData.appendedChallenges_of_lt (by grind)]
      erw [materializeChallenges_append, ih (by grind)]
      simp
      rw [MultiRoundData.appendedChallenges_of_lt sorry]
      apply materializeChallenges_of_lt (h 0)      
    · sorry

end

end

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
  outputOracle := Sum.inr {
    materializeOutput challenges oracleStatement messages oracleIdx := match oracleIdx with
      | .WeightPolynomial => oracleStatement .WeightPolynomial
      | .CodeWord => oracleStatement .CodeWord
      | .CodeWordPolynomial => oracleStatement .CodeWordPolynomial
      | .SumcheckResult =>
        cast (by {
          aesop (add simp [sumcheckResultIdx, ProtocolSpec.sigmaMessageIdxToSeqCompose]) -- TODO encapsulate
        }) (messages (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds))
      | .SumcheckChallenges => fun round => sumcheckChallenge round challenges
    simulateOutputQuery challenges query :=
      let ⟨queryIdx, queryData⟩ := query
      match queryIdx with
        | .WeightPolynomial => OracleComp.queryBind (Sum.inr (Sum.inl ⟨.WeightPolynomial, queryData⟩)) (pure ·)
        | .CodeWord => OracleComp.queryBind (Sum.inr (Sum.inl ⟨.CodeWord, queryData⟩)) (pure ·)
        | .CodeWordPolynomial => OracleComp.queryBind (Sum.inr (Sum.inl ⟨.CodeWordPolynomial, queryData⟩)) (pure ·)
        | .SumcheckResult => OracleComp.queryBind (Sum.inr (Sum.inr
            ⟨sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds, cast (by {
              rewrite [sumcheckResultMessageType]
              rfl
            }) queryData⟩
          )) (fun data => do return (cast (by {
            simp [OracleInterface.toOracleSpec]
            have : (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds).val.splitSum.snd = 0 := by
              obtain ⟨idx, h_idx⟩ := sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds
              by_contra
              have h_one : idx.splitSum.snd = 1 := by grind
              simp at h_idx
              rewrite [←idx.embedSum_splitSum, Fin.vflatten_embedSum, h_one] at h_idx
              reduce at h_idx
              simp at h_idx

            congr
            . simp [OracleStatementMid]
              rewrite [
                ←Fin.embedSum_splitSum (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds).val,
                this,
                Fin.vflatten_embedSum
              ]
              rfl
            . simp [
                ProtocolSpec.instOracleInterfaceMessageSeqCompose,
                Fin.fflatten₂_eq_splitSum
              ]
              rw! [this]
              simp [
                Sumcheck.Spec.SingleRound.instOracleInterfaceMessagePSpec,
                ProtocolSpec.instOracleInterfaceMessageAppend,
                Sumcheck.Spec.SingleRound.instOI₂,
                Fin.fconcat₂,
                Sumcheck.Spec.SingleRound.instOI₁,
                ProtocolSpec.instOracleInterfaceMessageMkVconsDirectionP_to_VVempty,
                OracleInterface.instPolynomialDegreeLE
              ]
              have {Y Z} (y : Y) (z : Z) : (fun x => y) z = y := rfl

              rewrite [←this (OracleStatement.oracleInterfaceMid _ _ _ _) (sumcheckResultIdx F num_sumcheck_rounds h_num_sumcheck_rounds).2]
              clear this
              set lhs_fun := fun h' ↦ {
                Query := F
                toOC := _
                : OracleInterface _
              }
              set lhs_fun_cast := cast _ lhs_fun
              set rhs_fun := fun x ↦ OracleStatement.oracleInterfaceMid domain _ _ _
              apply heq_apply
              · rfl
              · congr
                simp
                rewrite [←Fin.embedSum_splitSum (sumcheckResultIdx _ _ _).val, Fin.vflatten_embedSum]
                rewrite [this]
                reduce
                rfl
              · subst lhs_fun_cast
                apply (cast_heq_iff_heq _ _ _).mpr
                subst lhs_fun
                subst rhs_fun
                apply heq_funext
                simp
                rewrite [←Fin.embedSum_splitSum (sumcheckResultIdx _ _ _).val, Fin.vflatten_embedSum]
                . simp [this]
                . rfl
                . intro h h' heq
                  rfl
              · rfl
            . apply (cast_heq_iff_heq (a := queryData) _ _).mpr
              rfl
          }) data))
        | .SumcheckChallenges => do return sumcheckChallenge (F := F) queryData challenges
    simulateOutputQuery_eq challenges oStmt messages q := by
      obtain ⟨queryIdx, queryData⟩ := q
      fin_cases queryIdx
      . rfl
      . rfl
      . dsimp
        rfl
      .
        simp [-bind_pure_comp]
        rewrite [answer_cast, pure_cast]
        cbv
        simp
        convert pure_cast _ _ _ _
        . simp [cast]
          rfl



        -- unfold OracleInterface.answer
        -- conv_lhs => unfold Functor.map

        -- unfold pure

        -- rewrite [←OracleInterface.answer.eq_def]
        -- change F at queryData

        -- rw! (castMode := .all) [this]

        -- unfold OracleInterface.answer OracleInterface.toOC OracleStatement.oracleInterfaceMid
        -- dsimp
        -- simp







        -- unfold OracleInterface.answer ReaderT.run OracleInterface.toOC
        -- simp [
        --   OracleStatement.oracleInterfaceMid
        -- ]
        -- conv_rhs =>
        --   unfold Functor.map ReaderT.instMonad
        --   dsimp [Applicative.toFunctor, ReaderT.instApplicativeOfMonad, ReaderT.instFunctorOfMonad, read, readThe, MonadReaderOf.read, ReaderT.read, Functor.map]
        -- unfold simulateQ PFunctor.FreeM.liftM PFunctor.FreeM.lift
        -- dsimp
        -- unfold PFunctor.FreeM.lift
        -- simp
        -- unfold PFunctor.FreeM.lift
        -- split
        -- · exfalso
        --   grind
        -- next x a cont heq =>
        --   simp only [
        --     OracleSpec.ofPFunctor_toPFunctor, OracleSpec.add_apply_inr, PFunctor.FreeM.liftBind_eq,
        --     PFunctor.FreeM.bind_pure, PFunctor.FreeM.bind_eq_bind, Fin.isValue, map_bind
        --   ] at heq ⊢
        --   unfold_projs
        --   rewrite [
        --     ←PFunctor.FreeM.map_bind
        --   ]
        --   dsimp
        --   sorry
        --   done


        -- rfl

        -- -- cbv
        -- -- congr
        -- -- dsimp

      . rfl
  }

  materialize_eq := by
    intro _outerStatement challenges outerOracleStatement messages
    funext idx
    fin_cases idx
    · rfl
    · rfl
    · rfl
    · have := Sumcheck.Spec.partialOracleVerifier_materializeOutput_responsePoly_last
      apply eq_of_heq
      apply HEq.trans _ (this _ _ _ _ _ _ _ _ _ _).symm
      · grind
      · simp [OracleVerifier.materializeOutputOracle]
        rfl
    · simp [
        OracleVerifier.materializeOutputOracle,
        sumcheckLens,
        OracleStatement.sumcheckExecutableLens,
        Sumcheck.Spec.partialOracleVerifier,
        Sumcheck.Spec.OracleIdx.challenges
      ]
      obtain ⟨num_sumcheck_rounds, h_num_sumcheck_rounds'⟩ := num_sumcheck_rounds
      set f := fun (idx : Sumcheck.Spec.OracleIdx) ↦ _
      have :
        (fun round ↦ sumcheckChallenge round challenges) =
        (fun round : Fin (Fin.mk num_sumcheck_rounds h_num_sumcheck_rounds').val ↦ (
          (f 2) ++ᵛ
          (fun round ↦ sumcheckChallenge round challenges)
        ) (round.cast (by grind)))
      := by
        subst f
        simp
        rfl
      rewrite [this]
      -- PICK UP
      -- the idea is to generalize f to be for any round
      -- prove that the verifier materialize output (for this verifier specifically)
      -- appends on to f, leaving anything handled by it
      -- this will likely require another induction
      -- then when doing this induction, we can wrap the SingleRound materializeOutput as f in the induction hypothesis
      -- and use sumcheckChallenge_succ to split off the first round, and move it onto the other side of the append
      have :=
        materializeChallenges_seqCompose
          (m := num_sumcheck_rounds)
          (round := fun i ↦ i.castLE (by grind))
          (Stmt := fun i ↦ Sumcheck.Spec.StatementRound F num_vars (i.castLE (by grind)))
          (verifiers := fun i ↦ Sumcheck.Spec.SingleRound.oracleVerifier F num_vars 2
            (domain : Fin (2 ^ log_order) ↪ F) oSpec (i.castLE (by omega)))
          (data := ⟨f, challenges, messages⟩)
          fun i ↦ singleRound_appendsChallenge
            (D := (domain : Fin (2 ^ log_order) ↪ F))
            (oSpec := oSpec)
            (i := i.castLE (by grind))
      exact this.symm

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
    (OStmtOut := OracleStatementMid domain num_vars num_sumcheck_rounds)
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
: ProtocolSpec 4 :=
  (pSpec.sendFoldedFunction domain) ++ₚ
  (pSpec.outOfDomainSample F) ++ₚ
  (pSpec.outOfDomainAnswer F) ++ₚ
  (pSpec.shiftQueriesAndCombinationRandomness num_sumcheck_rounds num_queries domain)

def restPSpec.foldedFunction
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}
  {num_vars : ℕ}
  {num_sumcheck_rounds : Fin (num_vars + 1)}
  {num_queries : ℕ}
: (restPSpec domain num_sumcheck_rounds num_queries).MessageIdx := ⟨0, rfl⟩
def restPSpec.outOfDomainSample
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}
  {num_vars : ℕ}
  {num_sumcheck_rounds : Fin (num_vars + 1)}
  {num_queries : ℕ}
: (restPSpec domain num_sumcheck_rounds num_queries).ChallengeIdx := ⟨1, rfl⟩
def restPSpec.outOfDomainAnswer
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}
  {num_vars : ℕ}
  {num_sumcheck_rounds : Fin (num_vars + 1)}
  {num_queries : ℕ}
: (restPSpec domain num_sumcheck_rounds num_queries).MessageIdx := ⟨2, rfl⟩
def restPSpec.shiftQueriesAndCombinationRandomness
  {F : Type} [Field F] [DecidableEq F]
  {log_order : ℕ}
  {domain : Domain.SmoothCosetFftDomain log_order F}
  {num_vars : ℕ}
  {num_sumcheck_rounds : Fin (num_vars + 1)}
  {num_queries : ℕ}
: (restPSpec domain num_sumcheck_rounds num_queries).ChallengeIdx := ⟨3, rfl⟩


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
    (OracleStatementMid domain num_vars num_sumcheck_rounds)
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
      α := oracle_statement .SumcheckChallenges
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

open MvPolynomial in
example
  {F : Type} [Field F]
  {deg : ℕ}
  {num_vars1 num_vars2 : ℕ}
  {poly : F⦃≤ deg⦄[X Fin num_vars1]}
  {varIdx : Fin num_vars2}
  {vars : Fin num_vars1 → F⦃≤ 1⦄[X Fin num_vars2]}
:
  degreeOf varIdx (MvPolynomial.eval₂ MvPolynomial.C (fun x => (vars x).val) poly.val) ≤ 1
:= by
  obtain ⟨poly, h_poly⟩ := poly
  simp [eval₂, Finsupp.sum]
  induction num_vars1
  . simp
    apply le_trans (MvPolynomial.degreeOf_sum_le _ _ _)
    simp
  case succ num_vars1 ih =>

    done



open Polynomial MvPolynomial in
def restVerifier
  {OSpecIdx : Type} (oSpec : OracleSpec OSpecIdx)
  {F : Type} [Field F] [DecidableEq F] [SampleableType F]
  {log_order : ℕ}
  (domain : Domain.SmoothCosetFftDomain log_order F)
  (num_vars : ℕ)
  (num_sumcheck_rounds : Fin (num_vars + 1))
  (h_num_sumcheck_rounds : num_sumcheck_rounds > 0)
  (num_queries : ℕ)
:
  OracleVerifier
    oSpec
    (Statement domain × Sumcheck.Spec.StatementRound F num_vars num_sumcheck_rounds)
    (OracleStatementMid domain num_vars num_sumcheck_rounds)
    (Statement (Domain.CosetFftDomain.subdomain domain 1))
    (OracleStatementPre (Domain.CosetFftDomain.subdomain domain 1) (num_vars - num_sumcheck_rounds))
    (restPSpec domain num_sumcheck_rounds num_queries)
where
  verify statement challenges := do
    let sumcheck_statement := statement.2
    let alpha_k : F := sumcheck_statement.challenges ⟨num_sumcheck_rounds - 1, by grind⟩
    let h_hat_k_of_alpha_k : F ← OracleComp.queryBind
      (Sum.inr (Sum.inl (Sigma.mk OracleIdxMid.SumcheckResult alpha_k)))
      (fun x => do return (.some x))

    let γ : F := (challenges ⟨3, rfl⟩).2

    let y0 : F ← OracleComp.queryBind
      (Sum.inr (Sum.inr (Sigma.mk ⟨2, rfl⟩ ())))
      (fun x => do return (.some x))

    let y_one_plus : Fin num_queries → F := _ -- folds

    let ys : Fin (num_queries + 1) → F := Fin.cases y0 y_one_plus
    let gamma_y_sum : F := ∑ i, γ^(i.val+1) * (ys i)
    let newTarget : F := h_hat_k_of_alpha_k + gamma_y_sum
    return {
      target := newTarget
    }
  outputOracle := Sum.inr {
    materializeOutput challenges oracles messages oracleIdx := match oracleIdx with
      | .WeightPolynomial =>
        let num_x := num_vars - num_sumcheck_rounds
        let αs : Fin num_sumcheck_rounds → F := _
        let αs_poly : Fin num_sumcheck_rounds → F[X Fin (num_vars - num_sumcheck_rounds + 1)] := _
        let w_hat_vars : Fin (num_vars + 1) → _ := Fin.cases
          (MvPolynomial.X 0)
          (fun (x : Fin num_vars) => if h: x.val < num_sumcheck_rounds
            then αs_poly ⟨x.val, h⟩
            else  MvPolynomial.X (Fin.mk (x.val - num_sumcheck_rounds + 1) (by grind))
          )
        let w_hat : F[X Fin (num_vars - num_sumcheck_rounds + 1)] := MvPolynomial.eval₂ MvPolynomial.C w_hat_vars (oracles .WeightPolynomial).val
        let z0 := challenges restPSpec.outOfDomainSample
        let ⟨zs, γ⟩ := challenges restPSpec.shiftQueriesAndCombinationRandomness
        let zs : Fin (num_queries + 1) → F := Fin.cases z0 (zs ·)
        let γ_poly : F[X Fin (num_vars - num_sumcheck_rounds + 1)] := MvPolynomial.C γ

        let eq
          : Fin (num_queries + 1 ) → F[X Fin (num_vars - num_sumcheck_rounds + 1)]
        := fun i =>
          ∏ (j : Fin (num_vars - num_sumcheck_rounds)), (
            let b := (MvPolynomial.C ((zs i)^(2^j.val)))
            let z := (MvPolynomial.X j.succ)
            b*z + (1 - b) * (1 - z)
          )

        let sum : F[X Fin (num_vars - num_sumcheck_rounds + 1)] :=
          ∑ (i: Fin (num_queries + 1)), γ_poly^(i.val + 1) * eq i
        let w_hat' : F[X Fin (num_vars - num_sumcheck_rounds + 1)] := w_hat + MvPolynomial.X 0 * sum
        ⟨
          w_hat',
          by {
            simp [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
            intro varIdx
            subst w_hat'
            have : degreeOf varIdx w_hat ≤ 1 := by
              subst w_hat
              have ⟨w_hat, h_w_hat⟩ := (oracles .WeightPolynomial)

              done
            have : degreeOf varIdx (MvPolynomial.X 0 * sum) ≤ 1 := sorry
            apply le_trans (MvPolynomial.degreeOf_add_le _ _ _)
            grind
          }
        ⟩

        -- fun (args : Fin (num_vars - num_sumcheck_rounds + 1) → F) =>
        -- let Z : F := args ⟨0, by grind⟩
        -- let X : Fin (num_vars - num_sumcheck_rounds) → F := fun i => args i.succ

        -- let prev : F⦃≤1⦄[X Fin (num_vars + 1)] := oracles .WeightPolynomial
        -- let αs : Fin num_sumcheck_rounds → F := _ -- in the statement, not accessible here
        -- let αs_append_X : Fin num_vars → F := fun idx => (Fin.append αs X) (idx.cast (by grind))
        -- let prev_eval : F := MvPolynomial.eval (Fin.cases Z αs_append_X) prev

        -- let γ : F := (challenges ⟨3, rfl⟩).2
        -- let z0 : F := (challenges ⟨1, rfl⟩) -- note that these are the non-bold zs
        -- let z_one_plus : Fin (num_queries) → F := ((challenges ⟨3, rfl⟩).1 ·)
        -- let zs : Fin (num_queries + 1) → F := Fin.cases z0 z_one_plus

        -- let new_num_vars : ℕ:= num_vars - num_sumcheck_rounds
        -- let bold_zs : Fin (num_queries + 1) → Fin (new_num_vars) → F := fun x y =>
        --   (zs x)^(2^y.val)
        -- let eq := fun (b z : Fin new_num_vars → F) =>
        --   ∏ (i : Fin new_num_vars), ((b i * z i) + (1 - b i)*(1 - z i))
        -- let sum := ∑ (i : Fin (num_queries + 1)), γ^(i.val + 1)*eq (bold_zs i) X
        -- prev_eval + Z*sum
      | .CodeWord => messages ⟨0, rfl⟩
    simulateOutputQuery challenges query := match query with
      | ⟨.WeightPolynomial, args⟩ => do
        let Z : F := args ⟨0, by grind⟩
        let X : Fin (num_vars - num_sumcheck_rounds) → F := fun i => args i.succ

        let αs : Vector F num_sumcheck_rounds ← (Vector.finRange num_sumcheck_rounds).mapM (fun idx =>
          OracleComp.queryBind
            (Sum.inr (Sum.inl ⟨.SumcheckChallenges, idx⟩))
            (fun result => do return result)
        )
        let αs : Fin num_sumcheck_rounds → F := (αs[·])

        let αs_append_X : Fin num_vars → F := fun idx => (Fin.append αs X) (idx.cast (by grind))
        let prev_eval : F ← OracleComp.queryBind
          (Sum.inr (Sum.inl ⟨.WeightPolynomial, (Fin.cases Z αs_append_X)⟩))
          (fun result => do return result)

        let γ : F := (challenges ⟨3, rfl⟩).2
        let z0 : F := (challenges ⟨1, rfl⟩) -- note that these are the non-bold zs
        let z_one_plus : Fin (num_queries) → F := ((challenges ⟨3, rfl⟩).1 ·)
        let zs : Fin (num_queries + 1) → F := Fin.cases z0 z_one_plus

        let new_num_vars : ℕ:= num_vars - num_sumcheck_rounds
        let bold_zs : Fin (num_queries + 1) → Fin (new_num_vars) → F := fun x y =>
          (zs x)^(2^y.val)
        let eq := fun (b z : Fin new_num_vars → F) =>
          ∏ (i : Fin new_num_vars), ((b i * z i) + (1 - b i)*(1 - z i))
        let sum := ∑ (i : Fin (num_queries + 1)), γ^(i.val + 1)*eq (bold_zs i) X
        return prev_eval + Z*sum
      | ⟨.CodeWord, x⟩ => OracleComp.queryBind
        (Sum.inr (Sum.inr ⟨⟨0, rfl⟩, x⟩))
        (fun result => do return result)
    simulateOutputQuery_eq := _
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
    (OStmtIn := (OracleStatementMid domain num_vars num_sumcheck_rounds))
    (WitIn := WitnessPostSumcheck F num_vars)
    (StmtOut := (Statement (domain.subdomain 1)))
    (OStmtOut := (OracleStatementPre (domain.subdomain 1) (num_vars - num_sumcheck_rounds)))
    (WitOut := WitnessPreSumcheck F (num_vars - num_sumcheck_rounds))
    (pSpec := restPSpec domain num_sumcheck_rounds num_queries)
where
  prover := restProver oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds num_queries
  verifier := restVerifier oSpec domain num_vars num_sumcheck_rounds h_num_sumcheck_rounds num_queries

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
