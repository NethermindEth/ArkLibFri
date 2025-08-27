

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.ProtocolSpec
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ProofSystem.Fri.Domain

/-!
# The FRI protocol

We describe the FRI oracle reduction as a composition of many single rounds, and a final
(zero-interaction) query round where the oracle verifier makes all queries to all received oracle
codewords. f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`. -/

/-- The (default) oracle interface for a function `α → β`. -/
instance {α β : Type*} : OracleInterface (α → β) :=
  {
    Query := α
    Response := β
    oracle := id
  }

namespace Fri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Domain

namespace Spec

variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicC D] [DSmooth : Smooth2 n D]
variable {k : ℕ} (k_le_n : k ≤ n) (i : Fin k)


/-- For the `i`-th round of the protocol, the input statement is equal to the challenges sent from
    rounds `0` to `i - 1`. After the `i`-th round, we append the `i`-th challenge to the statement.
-/
@[reducible]
def Statement (F : Type) (i : Fin (k + 1)) : Type := Fin i.val → F

/-- For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the
  beginning purported codeword, and `i` more for each of the rounds `0` to `i - 1`. After the `i`-th
  round, we append the `i`-th message sent by the prover to the oracle statement. -/
@[reducible]
def OracleStatement (i : Fin (k + 1)) : Fin i.1 → Type :=
  fun j => evalDomain D j.1 → F

/-- The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in
  the oracle statement. -/
@[reducible]
def Witness (F : Type) [Semiring F] := F[X]

-- Might want to refine the witness each round to `F⦃< 2^(n - i)⦄[X]`

def oSpec : OracleSpec Unit :=
  fun _ ↦ (Unit, evalDomain D 0)

namespace FoldPhase

/-- The oracle interface for the `j`-th oracle statement of the `i`-th round of the FRI protocol.

Since everything are functions right now, we just use the default oracle interface for functions. -/
instance {i : Fin (k + 1)} : ∀ j, OracleInterface (OracleStatement D i j) :=
  fun _ => instOracleInterfaceForall

/-- This is missing the relationship between the oracle statement and the witness. Need to define a
  proximity parameter here. Completeness will be for proximity param `0`, while soundness will have
  non-zero proximity param. -/
def inputRelation :
    Set ((Statement F i.castSucc × (∀ j, OracleStatement D i.castSucc j)) × Witness F) :=
  {⟨⟨_, _⟩, p⟩ | Polynomial.natDegree p < 2 ^ (k - i.val)}

/-- Same with the above comment about input relation. -/
def outputRelation :
    Set ((Statement F i.succ × (∀ j, OracleStatement D i.succ j)) × Witness F) :=
  {⟨⟨_, _⟩, p⟩ | Polynomial.natDegree p < 2 ^ (k - (i.val + 1))}

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending a codeword (of the desired length) to
  the verifier. -/
@[reducible]
def pSpec : ProtocolSpec 2 := ![(.V_to_P, F), (.P_to_V, (evalDomain D i.1) → F)]

instance {i : Fin k} : ∀ j, OracleInterface ((pSpec D i).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => instOracleInterfaceForall

/-- The prover for the `i`-th round of the FRI protocol. It first receives the challenge -/
noncomputable def prover :
  OracleProver (oSpec D) (Statement F i.castSucc) (OracleStatement D i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement D i.succ) (Witness F) (pSpec D i) where
  -- This may be difficult to reason about, given that the degree does get divided by 2 each round.
  -- Might want to bake that into the type.
  -- Also need to return all the prior oracle statements and prior challenges
  PrvState
  | 0 => (Fin i.castSucc → F) × F[X] × (∀ j : Fin i, OracleStatement D i.castSucc j)
  | 1 => (Fin i.succ → F) × F[X] × (∀ j : Fin i, OracleStatement D i.castSucc j)
  | 2 => (Fin i.succ → F) × F[X] × (∀ j : Fin i, OracleStatement D i.castSucc j)

  input := fun x =>
    ⟨
      x.1.1,
      x.2,
      by simpa only [Fin.coe_castSucc] using x.1.2
    ⟩

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨chals, p, o⟩ => do
    pure ⟨fun x => p.eval x.1.1, chals, p, o⟩

  receiveChallenge
  | ⟨0, _⟩ => fun (⟨chals, p, o⟩) (α : F) =>
    ⟨Fin.append chals (fun (_ : Fin 1) => α), foldα p α, o⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨chals, p, o⟩ =>
    ⟨
      ⟨
        chals,
        fun j =>
          if h : j.1 < i.1
          then by
            simpa [OracleStatement, evalDomain] using o ⟨j.1, h⟩
          else fun x => p.eval x.1.1
      ⟩,
      p
    ⟩

/-- The oracle verifier for the `i`-th round of the FRI protocol. -/
noncomputable def verifier :
  OracleVerifier (oSpec D)
    (Statement F i.castSucc) (OracleStatement D i.castSucc)
    (Statement F i.succ) (OracleStatement D i.succ)
    (pSpec D i) where
  verify := fun prevChallenges roundChallenge => do
    pure (Fin.append prevChallenges (fun _ => roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j =>
        if h : j.val = i.val
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl ⟨j.val, by have := Nat.eq_or_lt_of_le (Nat.le_of_lt_succ j.2); aesop⟩,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    aesop

/-- The oracle reduction that is the `i`-th round of the FRI protocol. -/
noncomputable def oracleReduction :
  OracleReduction (oSpec D)
    (Statement F i.castSucc) (OracleStatement D i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement D i.succ) (Witness F)
    (pSpec D i) where
  prover := prover D i
  verifier := verifier D i

end FoldPhase

namespace QueryRound

variable (l : ℕ)

@[reducible]
def pSpec (F : Type) : ProtocolSpec 1 := ![(.P_to_V, Unit → F)]

instance : ∀ j, OracleInterface ((pSpec F).Message j) := fun j =>
  by
    simp only [Message, Matrix.cons_val_fin_one]
    exact instOracleInterfaceForall

noncomputable def proverFinal :
  OracleProver
    (oSpec D)
    (Statement F (Fin.last k)) (OracleStatement D (Fin.last k)) (Witness F)
    (Statement F (Fin.last k)) (OracleStatement D (Fin.last k)) (Witness F)
    (pSpec F) where
  PrvState
  | 0 => (Fin k → F) × F[X] × (∀ j : Fin k, OracleStatement D (Fin.last k) j)
  | 1 => (Fin k → F) × F[X] × (∀ j : Fin k, OracleStatement D (Fin.last k) j)

  input := fun x =>
    ⟨
      x.1.1,
      x.2,
      by simpa only [Fin.coe_castSucc] using x.1.2
    ⟩

  sendMessage
  | ⟨0, h⟩ => fun ⟨chals, p, o⟩ => do
      pure ⟨fun _ => p.coeff 0, chals, p, o⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h

  output := fun ⟨chals, p, o⟩ => ⟨⟨chals, o⟩, p⟩

def getChallenge :
    OracleComp (oSpec D) (evalDomain D 0) :=
  OracleComp.lift (OracleSpec.query () ())

def sampleCodeword (i : Fin k) (x : evalDomain D i.1) :
    OracleComp [OracleStatement D (Fin.last k)]ₒ F :=
  OracleComp.lift (OracleSpec.query i x)

@[simp]
lemma pSpec_domain {F : Type} :
    [(pSpec F).Message]ₒ.domain ⟨0, Eq.refl (pSpec F 0).1⟩ = Unit := by rfl

@[simp]
lemma pSpec_range {F : Type} :
    [(pSpec F).Message]ₒ.range ⟨0, Eq.refl (pSpec F 0).1⟩ = F := by rfl

def getConst :
    OracleComp
      [(pSpec F).Message]ₒ
      F := OracleComp.lift
        (by
          simpa using
            OracleSpec.query
              (spec := [(pSpec F).Message]ₒ)
              ⟨0, by rfl⟩
              (by simpa using ())
        )

noncomputable def verifierFinal [DecidableEq F] :
  OracleVerifier (oSpec D)
    (Statement F (Fin.last k))
    (OracleStatement D (Fin.last k))
    (Statement F (Fin.last k)) (OracleStatement D (Fin.last k))
    (pSpec F) where
  verify := fun prevChallenges roundChallenge => do
    for _ in [0:l] do
      let s₀ ← getChallenge D;
      let _ ← (List.finRange k).mapM
              (fun (i : Fin k) =>
                do
                  let x₀ := prevChallenges i;
                  have h : s₀.1 ^ (2 ^ i.1) ∈ evalDomain D ↑i := by
                    apply pow_2_pow_i_mem_Di_of_mem_D
                    convert s₀.2
                    simp [D_def]
                  let s₀ : evalDomain D i.1 := ⟨_, h⟩;
                  let i' : Fin n := ⟨i.1, by omega⟩
                  let s₁ := (domain_neg_inst (i := i') D).neg s₀;
                  let α₀ ← sampleCodeword D i s₀;
                  let α₁ ← sampleCodeword D i s₁;
                  let h' := sqr_mem_D_succ_i_of_mem_D_i D s₀.2;
                  if h : i.1 < k - 1
                  then
                    let β  ← sampleCodeword D (⟨i.1.succ, by omega⟩ : Fin k) ⟨_, h'⟩;
                    guard (consistency_check x₀ s₀.1.1 s₁.1.1 α₀ α₁ β)
                  else
                    let β  ← @getConst F
                    guard (consistency_check x₀ s₀.1.1 s₁.1.1 α₀ α₁ β)
              )
    pure prevChallenges
  embed :=
    ⟨
      fun (j : Fin k) =>
        Sum.inl <| by simpa using j,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    aesop


noncomputable def oracleReductionFinal [DecidableEq F] :
  OracleReduction (oSpec D)
    (Statement F (Fin.last k))
    (OracleStatement D (Fin.last k))
    (Witness F)
    (Statement F (Fin.last k))
    (OracleStatement D (Fin.last k))
    (Witness F)
    (pSpec F) where
  prover := proverFinal D
  verifier := verifierFinal D k_le_n l

end QueryRound

end Spec

end Fri
