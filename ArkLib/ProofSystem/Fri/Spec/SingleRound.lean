

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ProofSystem.Fri.Domain

/-!
# The FRI protocol

We describe the FRI oracle reduction as a composition of many single rounds, and a final
(zero-interaction) query round where the oracle verifier makes all queries to all received oracle
codewords. f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`. -/

namespace Fri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset CosetDomain

namespace Spec

variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (d : ℕ) (k_le_n : k ≤ n) (i : Fin k)


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
  fun j => evalDomain D x j.1 → F

/-- The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in
  the oracle statement. -/
@[reducible]
def Witness (F : Type) [Semiring F] := F[X]

-- Might want to refine the witness each round to `F⦃< 2^(n - i)⦄[X]`

namespace FoldPhase

/-- The oracle interface for the `j`-th oracle statement of the `i`-th round of the FRI protocol.

Since everything are functions right now, we just use the default oracle interface for functions. -/
instance {i : Fin (k + 1)} : ∀ j, OracleInterface (OracleStatement D x i j) :=
  fun _ => inferInstance

/-- This is missing the relationship between the oracle statement and the witness. Need to define a
  proximity parameter here. Completeness will be for proximity param `0`, while soundness will have
  non-zero proximity param. -/
def inputRelation :
    Set ((Statement F i.castSucc × (∀ j, OracleStatement D x i.castSucc j)) × Witness F) :=
  {⟨⟨_, _⟩, p⟩ | Polynomial.natDegree p < 2 ^ (k - i.val) * d}

/-- Same with the above comment about input relation. -/
def outputRelation :
    Set ((Statement F i.succ × (∀ j, OracleStatement D x i.succ j)) × Witness F) :=
  {⟨⟨_, _⟩, p⟩ | Polynomial.natDegree p < 2 ^ (k - (i.val + 1)) * d}

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending a codeword (of the desired length) to
  the verifier. -/
@[reducible]
def pSpec : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[F, (evalDomain D x i.1) → F]⟩

instance {i : Fin k} : ∀ j, OracleInterface ((pSpec D x i).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      infer_instance



/-- The prover for the `i`-th round of the FRI protocol. It first receives the challenge -/
noncomputable def foldProver :
  OracleProver []ₒ (Statement F i.castSucc) (OracleStatement D x i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement D x i.succ) (Witness F) (pSpec D x i) where
  -- This may be difficult to reason about, given that the degree does get divided by 2 each round.
  -- Might want to bake that into the type.
  -- Also need to return all the prior oracle statements and prior challenges
  PrvState
  | 0 =>
    (Statement F i.castSucc × ((j : Fin ↑i.castSucc) → OracleStatement D x i.castSucc j)) ×
      Witness F
  | _ =>
    (Statement F i.succ × ((j : Fin ↑i.castSucc) → OracleStatement D x i.castSucc j)) × Witness F

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ =>
    pure ⟨fun x => p.eval x.1.1, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => pure <|
    fun (α : F) =>
      ⟨⟨Fin.append chals (fun (_ : Fin 1) => α), o⟩, foldα p α⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ => pure <|
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
noncomputable def foldVerifier :
  OracleVerifier []ₒ
    (Statement F i.castSucc) (OracleStatement D x i.castSucc)
    (Statement F i.succ) (OracleStatement D x i.succ)
    (pSpec D x i) where
  verify := fun prevChallenges roundChallenge =>
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
    intros j
    simp only [Fin.val_succ, Fin.coe_castSucc, Fin.vcons_fin_zero,
      Nat.reduceAdd, MessageIdx, Fin.isValue, Function.Embedding.coeFn_mk,
      Message]
    split_ifs with h
    · simp [h]
    · rfl

/-- The oracle reduction that is the `i`-th round of the FRI protocol. -/
noncomputable def foldOracleReduction :
  OracleReduction []ₒ
    (Statement F i.castSucc) (OracleStatement D x i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement D x i.succ) (Witness F)
    (pSpec D x i) where
  prover := foldProver D x i
  verifier := foldVerifier D x i

end FoldPhase

namespace QueryRound

variable (l : ℕ)

@[reducible]
def pSpec : ProtocolSpec 2 :=
  ⟨!v[.P_to_V, .V_to_P], !v[Unit → F[X], Fin l → evalDomain D x 0]⟩

instance : ∀ j, OracleInterface ((pSpec D x l).Message j) := fun j =>
  match j with
  | ⟨0, h⟩ => by
    simp
    exact OracleInterface.instFunction
  | ⟨1, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec D x l).Challenge j) := fun j =>
  match j with
  | ⟨0, h⟩ => nomatch h
  | ⟨1, h⟩ => by
    simp
    infer_instance

noncomputable def queryProver :
  OracleProver
    []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x (Fin.last k)) (Witness F)
    (Statement F (Fin.last k)) (OracleStatement D x (Fin.last k)) (Witness F)
    (pSpec D x l) where
  PrvState
  | _ =>
    (Statement F (Fin.last k) × ((i : Fin ↑(Fin.last k)) → OracleStatement D x (Fin.last k) i)) ×
      Witness F

  input := id

  sendMessage
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => do
      pure ⟨fun _ => p, ⟨⟨chals, o⟩, p⟩⟩
  | ⟨1, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun x => pure <| fun _ => x

  output := pure

def sampleCodeword {F : Type} [NonBinaryField F] {D : Subgroup Fˣ} [DIsCyclicC : IsCyclicWithGen ↥D]
  {x : Fˣ} {k : ℕ} {i : Fin k} (d : evalDomain D x i.1) :
    OracleComp [OracleStatement D x (Fin.last k)]ₒ F :=
  OracleComp.lift (OracleSpec.query i d)

def getConst : OracleComp [(pSpec D x l).Message]ₒ F[X] :=
  OracleComp.lift
    (by simpa using
          OracleSpec.query
            (spec := [(pSpec D x l).Message]ₒ)
            ⟨0, by rfl⟩
            (by simpa using ())
    )

noncomputable def queryVerifier [DecidableEq F] :
  OracleVerifier []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x (Fin.last k))
    (Statement F (Fin.last k)) (OracleStatement D x (Fin.last k))
    (pSpec D x l) where
  verify := fun prevChallenges roundChallenge => do
    for m in (List.finRange l) do
      let s₀ := roundChallenge ⟨1, by aesop⟩ m
      let p ← getConst D x l
      guard (p.natDegree < d)
      discard <|
        (List.finRange k).mapM
              (fun (i : Fin k) =>
                do
                  let x₀ := prevChallenges i
                  let s₀ : evalDomain D x i.1 := ⟨_, pow_2_pow_i_mem_Di_of_mem_D i s₀.2⟩
                  let s₁ : evalDomain D x i.1 :=
                    (domain_neg_inst (n := n) (i := ⟨i.1, by omega⟩)).neg s₀
                  let α₀ ← sampleCodeword s₀
                  let α₁ ← sampleCodeword s₁
                  let β ←
                    if h : i.1 < k - 1
                    then
                      sampleCodeword (k := k) (i := ⟨i.1.succ, by omega⟩)
                        ⟨_, sqr_mem_D_succ_i_of_mem_D_i D x s₀.2⟩
                    else pure (p.eval s₀.1.1)
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


noncomputable def queryOracleReduction [DecidableEq F] :
  OracleReduction []ₒ
    (Statement F (Fin.last k))
    (OracleStatement D x (Fin.last k))
    (Witness F)
    (Statement F (Fin.last k))
    (OracleStatement D x (Fin.last k))
    (Witness F)
    (pSpec D x l) where
  prover := queryProver D x l
  verifier := queryVerifier D x d k_le_n l

end QueryRound

end Spec

end Fri
