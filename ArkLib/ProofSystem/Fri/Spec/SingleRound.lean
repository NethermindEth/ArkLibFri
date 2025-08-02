

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.ProtocolSpec
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ProofSystem.Fri.Domain

/-!
# The FRI protocol

We describe the FRI oracle reduction as a composition of many single rounds, and a final
(zero-interaction) query round where the oracle verifier makes all queries to all received oracle
codewords.
-/

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
variable (gen : Fˣ) {n : ℕ} [n_nezero : NeZero n] (i : Fin n)


/-- For the `i`-th round of the protocol, the input statement is equal to the challenges sent from
    rounds `0` to `i - 1`. After the `i`-th round, we append the `i`-th challenge to the statement.
-/
@[reducible]
def Statement (F : Type) (i : Fin (n + 1)) : Type := Fin i.val → F

/-- For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the
  beginning purported codeword, and `i` more for each of the rounds `0` to `i - 1`. After the `i`-th
  round, we append the `i`-th message sent by the prover to the oracle statement. -/
@[reducible]
def OracleStatement (i : Fin (n + 1)) : Fin (i + 1) → Type :=
  fun j => evalDomain gen j → F

/-- The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in
  the oracle statement. -/
@[reducible]
def Witness (F : Type) [Semiring F] := F[X]

-- Might want to refine the witness each round to `F⦃< 2^(n - i)⦄[X]`

namespace SingleRound

/-- The oracle interface for the `j`-th oracle statement of the `i`-th round of the FRI protocol.

Since everything are functions right now, we just use the default oracle interface for functions. -/
instance {i : Fin (n + 1)} : ∀ j, OracleInterface (OracleStatement gen i j) := fun j => by
  unfold OracleStatement
  exact instOracleInterfaceForall

/-- This is missing the relationship between the oracle statement and the witness. Need to define a
  proximity parameter here. Completeness will be for proximity param `0`, while soundness will have
  non-zero proximity param. -/
def inputRelation :
    Set ((Statement F i.castSucc × (∀ j, OracleStatement gen i.castSucc j)) × Witness F) :=
  {⟨⟨_, _⟩, p⟩ | Polynomial.natDegree p < 2 ^ (n - i.val)}

/-- Same with the above comment about input relation. -/
def outputRelation :
    Set ((Statement F i.castSucc × (∀ j, OracleStatement gen i.castSucc j)) × Witness F) :=
  {⟨⟨_, _⟩, p⟩ | Polynomial.natDegree p < 2 ^ (n - (i.val + 1))}

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending a codeword (of the desired length) to
  the verifier. -/
@[reducible]
def pSpec (i : Fin (n + 1)) : ProtocolSpec 2 := ![(.V_to_P, F), (.P_to_V, (evalDomain gen i) → F)]

instance {i : Fin (n + 1)} : ∀ j, OracleInterface ((pSpec gen i).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => instOracleInterfaceForall

def oSpec {F : Type} [NonBinaryField F] (gen : Fˣ) (n : ℕ) : OracleSpec (Fin n) :=
fun i ↦ (Unit, evalDomain gen i.castSucc)

/-- The prover for the `i`-th round of the FRI protocol. It first receives the challenge -/
noncomputable def prover :
  OracleProver (oSpec gen n) (Statement F i.castSucc) (OracleStatement gen i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement gen i.succ) (Witness F) (pSpec gen i.succ) where
  -- This may be difficult to reason about, given that the degree does get divided by 2 each round.
  -- Might want to bake that into the type.
  -- Also need to return all the prior oracle statements and prior challenges
  PrvState
  | 0 => (Fin i.castSucc → F) × F[X] × (∀ j : Fin (i + 1), OracleStatement gen i.castSucc j)
  | 1 => (Fin i.succ → F) × F[X] × (∀ j : Fin (i + 1), OracleStatement gen i.castSucc j)
  | 2 => (Fin i.succ → F) × F[X] × (∀ j : Fin (i + 1), OracleStatement gen i.castSucc j)
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
    ⟨Fin.append chals (fun (_ : Fin 1) => α), by simpa using @foldα F _ p α, o⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨chals, p, o⟩ =>
    ⟨
      ⟨
        chals,
        fun j =>
          if h : j.1 < i.1 + 1
          then by
            simpa [OracleStatement, evalDomain] using o ⟨j.1, h⟩
          else fun x => p.eval x.1.1
      ⟩,
      p
    ⟩

variable [gen_ord : Fact (orderOf gen = (2 ^ n))]

/-- The oracle verifier for the `i`-th round of the FRI protocol. -/
noncomputable def oracleVerifier [DecidableEq F] (i : Fin (n - 1)) :
  OracleVerifier (oSpec gen n)
    (Statement F i.castSucc.castSucc) (OracleStatement gen i.castSucc.castSucc)
    (Statement F i.castSucc.succ) (OracleStatement gen i.castSucc.succ)
    (pSpec gen i.castSucc.succ) where
  verify := fun prevChallenges roundChallenge => do
    pure (Fin.append prevChallenges (fun _ => roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j =>
        if h : j.val = i.val + 1
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl ⟨j.val, by have := Nat.eq_or_lt_of_le (Nat.le_of_lt_succ j.2); aesop⟩,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    aesop

/-- The oracle reduction that is the `i`-th round of the FRI protocol. -/
noncomputable def oracleReduction [DecidableEq F] (i : Fin (n - 1)) :
  OracleReduction (oSpec gen n)
    (Statement F i.castSucc.castSucc) (OracleStatement gen i.castSucc.castSucc) (Witness F)
    (Statement F i.castSucc.succ) (OracleStatement gen i.castSucc.succ) (Witness F)
    (pSpec gen i.castSucc.succ) where
  prover := by
    have : (n - 1) + 1 = n := Nat.succ_pred_eq_of_ne_zero n_nezero.out
    have x := prover gen i.castSucc
    convert x <;> exact this.symm
  verifier := oracleVerifier gen i

-- TODO: need to define the final query step of the FRI protocol.

def getSample (i : Fin n) :
    OracleComp (oSpec gen n) (evalDomain gen i.castSucc) :=
  OracleComp.lift (OracleSpec.query i ())

def sampleCodeword (i : Fin n) (x : evalDomain gen i.castSucc) :
    OracleComp
      (ι := Fin (n - 1 + 1))
      [OracleStatement gen ⟨n - 1, Nat.sub_lt_succ _ _⟩]ₒ
      F :=
  OracleComp.lift
    (
      OracleSpec.query
        (spec := [OracleStatement gen ⟨n - 1, Nat.sub_lt_succ _ _⟩]ₒ)
        ⟨i.1, by dsimp; omega⟩
        x
    )

def getConst :
    OracleComp
      (ι := (pSpec gen (Fin.last n)).MessageIdx)
      [(pSpec gen (Fin.last n)).Message]ₒ
      F := OracleComp.lift
        (
          OracleSpec.query
            (spec := [(pSpec gen (Fin.last n)).Message]ₒ)
            ⟨1, by simp⟩
            ⟨1, ⟨0, by simp⟩⟩
        )

noncomputable def oracleVerifierFinal [DecidableEq F] :
  OracleVerifier (oSpec gen n)
    (Statement F (⟨n - 1, Nat.sub_lt_succ _ _⟩ : Fin (n + 1)))
    (OracleStatement gen (⟨n - 1, Nat.sub_lt_succ _ _⟩ : Fin (n + 1)))
    (Statement F (Fin.last n)) (OracleStatement gen (Fin.last n))
    (pSpec gen (Fin.last n)) where
  verify := fun prevChallenges roundChallenge => do
    let _ ← (List.finRange (n - 1)).mapM
              (fun (i : Fin (n - 1)) =>
                do
                  let x₀ := prevChallenges i;
                  let i' : Fin n := ⟨i.1.succ, by omega⟩;
                  let i : Fin n := ⟨i.1, by omega⟩;
                  let s₀ ← getSample (n := n) gen i;
                  let s₁ := (domain_neg_inst (i := i) gen).neg s₀;
                  let α₀ ← sampleCodeword gen i s₀;
                  let α₁ ← sampleCodeword gen i s₁;
                  let h' := sqr_mem_D_succ_i_of_mem_D_i s₀.2;
                  let β  ← sampleCodeword gen i' (lift_to_subgroup h');
                  guard (consistency_check x₀ s₀.1.1 s₁.1.1 α₀ α₁ β)
              )
    let x₀ : F := roundChallenge ⟨0, by simp⟩;
    let α₀ ← sampleCodeword gen i 1;
    let α₁ ← sampleCodeword gen i (-1);
    let β  ← getConst (n := n) gen;
    guard (consistency_check x₀ 1 (-1) α₀ α₁ β)
    pure
      (
        Nat.succ_pred_eq_of_ne_zero n_nezero.out ▸
          Fin.append prevChallenges (fun (_ : Fin 1) => roundChallenge ⟨0, by simp⟩)
      )
  embed :=
    ⟨
      fun j =>
        if h : j.val = n
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl <| by
          simpa using
            ⟨
              j.val,
              by
                have : n - 1 + 1 = n := Nat.succ_pred_eq_of_ne_zero n_nezero.out
                rw [this]
                rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ j.2) <;> aesop
            ⟩,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    aesop

noncomputable def oracleReductionFinal [DecidableEq F] :
  OracleReduction (oSpec gen n)
    (Statement F (⟨n - 1, Nat.sub_lt_succ _ _⟩ : Fin (n + 1)))
    (OracleStatement gen (⟨n - 1, Nat.sub_lt_succ _ _⟩ : Fin (n + 1)))
    (Witness F)
    (Statement F (Fin.last n))
    (OracleStatement gen (Fin.last n))
    (Witness F)
    (pSpec gen  (Fin.last n)) where
  prover :=  Nat.succ_pred_eq_of_ne_zero n_nezero.out ▸ prover gen (Fin.last (n - 1))
  verifier := oracleVerifierFinal gen 0

end SingleRound

end Spec

end Fri
