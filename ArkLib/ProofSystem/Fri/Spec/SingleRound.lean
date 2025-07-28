

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.ProtocolSpec
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ProofSystem.Fri.Domain
import ArkLib.ProofSystem.Fri.Spec.Oracle

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
variable (gen : Fˣ) {n : ℕ} (i : Fin n)


/-- For the `i`-th round of the protocol, the input statement is equal to the challenges sent from
    rounds `0` to `i - 1`. After the `i`-th round, we append the `i`-th challenge to the statement.
-/
@[reducible]
def Statement (F : Type) (i : Fin (n + 1)) : Type := Fin i → F

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
  {⟨⟨_, o⟩, p⟩ | Polynomial.natDegree p < 2 ^ (n - i.val)}

/-- Same with the above comment about input relation. -/
def outputRelation :
    Set ((Statement F i.castSucc × (∀ j, OracleStatement gen i.castSucc j)) × Witness F) :=
  {⟨⟨_, o⟩, p⟩ | Polynomial.natDegree p < 2 ^ (n - (i.val + 1))}

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending a codeword (of the desired length) to
  the verifier. -/
@[reducible]
def pSpec : ProtocolSpec 2 := ![(.V_to_P, F), (.P_to_V, (evalDomain gen i.succ) → F)]

instance {i : Fin (n + 1)} : ∀ j, OracleInterface ((pSpec gen i).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => instOracleInterfaceForall

-- def getChallengeQ (i : Fin n) :
--     OracleComp ![] (evalDomain gen i.castSucc) :=
--   OracleComp.lift
--     (OracleSpec.query (spec := oSpec gen n) i ())

/-- The prover for the `i`-th round of the FRI protocol. It first receives the challenge -/
noncomputable def prover (i : Fin n) :
  OracleProver []ₒ (Statement F i.castSucc) (OracleStatement gen i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement gen i.succ) (Witness F) (pSpec gen i) where
  -- This may be difficult to reason about, given that the degree does get divided by 2 each round.
  -- Might want to bake that into the type.
  -- Also need to return all the prior oracle statements and prior challenges
  PrvState := fun _ => F[X]

  input := fun ⟨_, p⟩ => p

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun p => do
    pure ⟨fun x => p.eval x.1.1, p⟩

  receiveChallenge
  | ⟨0, _⟩ => fun (p : F[X]) (α : F) => by
    simpa using @foldα F _ p α
  | ⟨1, h⟩ => nomatch h

  output := sorry
  -- fun p => ⟨⟨(), fun _ x => p.eval x.1.1⟩, p⟩

variable [gen_ord : Fact (orderOf gen = (2 ^ n))]

-- Don't know why instance synthesization for OracleInterface of the messages is not working.

/-- The oracle verifier for the `i`-th round of the FRI protocol. -/
noncomputable def oracleVerifier [DecidableEq F] :
  OracleVerifier []ₒ
    (Statement F i.castSucc) (OracleStatement gen i.castSucc)
    (Statement F i.succ) (OracleStatement gen i.succ)
    (pSpec gen i) where
  verify := fun prevChallenges roundChallenge => pure (Fin.append prevChallenges (roundChallenge 0))
    -- sorry
    -- let (s₀ : evalDomain gen i.castSucc) ← @getChallengeQ F _ gen n i;
    -- let α₀ := o () s₀;
    -- let α₁ := o () (-s₀);
    -- let h' := sqr_mem_D_succ_i_of_mem_D_i s₀.2;
    -- let β  := (transcript 1) (lift_to_subgroup h')
    -- guard (consistency_check (F := F) (transcript 0) s₀.1.1 (-s₀).1.1 α₀ α₁ β)
    -- pure ((), fun _ => transcript 1)
  embed := sorry
  hEq := sorry

/-- The oracle reduction that is the `i`-th round of the FRI protocol. -/
noncomputable def oracleReduction [DecidableEq F] :
  OracleReduction []ₒ
    (Statement F i.castSucc) (OracleStatement gen i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement gen i.succ) (Witness F)
    (pSpec gen i) where
  prover := prover gen i
  verifier := oracleVerifier gen i

end SingleRound

-- TODO: need to define the final query step of the FRI protocol.

end Spec

end Fri
