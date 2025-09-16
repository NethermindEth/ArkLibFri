

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.Fri.Domain
import ArkLib.ProofSystem.Fri.RoundConsistency


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
variable {k : ℕ} (s d : ℕ) [s_nz : NeZero s] [d_nz : NeZero d]
variable (k_le_n : 2 ^ ((k + 1) * s) * d ≤ 2 ^ n) (i : Fin k)

omit s_nz in
lemma k_le_n' (k_le_n : 2 ^ ((k + 1) * s) * d ≤ 2 ^ n) : (k + 1) * s ≤ n := by
  have : 0 < d := by
    have := d_nz.out
    omega
  have : 2 ^ ((k + 1) * s) ≤ 2 ^ n := by
    exact le_of_mul_le_of_one_le_left k_le_n this
  rw [Nat.pow_le_pow_iff_right (by decide)] at this
  exact this


/-- For the `i`-th round of the protocol, the input statement is equal to the challenges sent from
    rounds `0` to `i - 1`. After the `i`-th round, we append the `i`-th challenge to the statement.
-/
@[reducible]
def Statement (F : Type) (i : Fin (k + 1)) : Type := Fin i.val → F

@[reducible]
def FinalStatement (F : Type) (k : ℕ) : Type := Fin (k + 1) → F

/-- For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the
  beginning purported codeword, and `i` more for each of the rounds `0` to `i - 1`. After the `i`-th
  round, we append the `i`-th message sent by the prover to the oracle statement. -/
@[reducible]
def OracleStatement (i : Fin (k + 1)) : Fin (i.val + 1) → Type :=
  fun j => evalDomain D x (s * j.1) → F

@[reducible]
def FinalOracleStatement (k : ℕ) : Fin (k + 2) → Type :=
  fun j =>
    if j.1 = k + 1
    then (Unit → F[X])
    else (evalDomain D x (s * j.1) → F)

/-- The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in
  the oracle statement. -/
@[reducible]
def Witness (F : Type) [Semiring F] := F[X]

-- Might want to refine the witness each round to `F⦃< 2^(n - i)⦄[X]`

instance {i : Fin (k + 1)} : ∀ j, OracleInterface (OracleStatement D x s i j) :=
  fun _ => inferInstance

instance : ∀ j, OracleInterface (FinalOracleStatement D x s k j) :=
  fun j =>
    match j with
    | ⟨j, hj⟩ =>
      if h : j = k + 1
      then h ▸ by
                unfold FinalOracleStatement
                simp
                exact OracleInterface.instFunction
      else by
            unfold FinalOracleStatement
            simp only [h, ↓reduceIte]
            exact OracleInterface.instFunction

      -- split_ifs
      -- · exact OracleInterface.instFunction
      -- · exact OracleInterface.instFunction

/-- The oracle interface for the `j`-th oracle statement of
    the `i`-th round of the FRI protocol. --/
def statementConsistent
      (stmt : Statement F i.castSucc)
      (ostmt : ∀ j, OracleStatement D x s i.castSucc j) : Prop :=

  sorry

namespace FoldPhase

/-- This is missing the relationship between the oracle statement and the witness. Need to define a
  proximity parameter here. Completeness will be for proximity param `0`, while soundness will have
  non-zero proximity param. -/
def inputRelation :
    Set ((Statement F i.castSucc × (∀ j, OracleStatement D x s i.castSucc j)) × Witness F) :=
  {⟨⟨stmt, ostmt⟩, p⟩ | Polynomial.natDegree p < (2 ^ (s * (k - i.val))) * d}

/-- Same with the above comment about input relation. -/
def outputRelation :
    Set ((Statement F i.succ × (∀ j, OracleStatement D x s i.succ j)) × Witness F) :=
  {⟨⟨_, _⟩, p⟩ | Polynomial.natDegree p < (2 ^ (s * (k - (i.val + 1)))) * d}

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending a codeword (of the desired length) to
  the verifier. -/
@[reducible]
def pSpec : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[F, (evalDomain D x (s * (i.1 + 1))) → F]⟩

instance {i : Fin k} : ∀ j, OracleInterface ((pSpec D x s i).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      infer_instance



/-- The prover for the `i`-th round of the FRI protocol. It first receives the challenge -/
noncomputable def foldProver :
  OracleProver []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement D x s i.succ) (Witness F)
    (pSpec D x s i) where
  -- This may be difficult to reason about, given that the degree does get divided by 2 each round.
  -- Might want to bake that into the type.
  -- Also need to return all the prior oracle statements and prior challenges
  PrvState
  | 0 =>
    (Statement F i.castSucc × ((j : Fin (↑i.castSucc + 1)) → OracleStatement D x s i.castSucc j)) ×
      Witness F
  | _ =>
    (Statement F i.succ × ((j : Fin (↑i.castSucc + 1)) → OracleStatement D x s i.castSucc j)) ×
      Witness F

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ =>
    pure ⟨fun x => p.eval x.1.1, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => pure <|
    fun (α : F) =>
      ⟨⟨Fin.append chals (fun (_ : Fin 1) => α), o⟩, RoundConsistency.foldα (2 ^ s) p α⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ => pure <|
    ⟨
      ⟨
        chals,
        fun j =>
          if h : j.1 < i.1
          then by
            simpa [OracleStatement, evalDomain] using o ⟨j.1, by
              rw [Fin.coe_castSucc]
              exact Nat.lt_add_right 1 h
            ⟩
          else fun x => p.eval x.1.1
      ⟩,
      p
    ⟩


/-- The oracle verifier for the `i`-th round of the FRI protocol. -/
noncomputable def foldVerifier :
  OracleVerifier []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc)
    (Statement F i.succ) (OracleStatement D x s i.succ)
    (pSpec D x s i) where
  verify := fun prevChallenges roundChallenge =>
    pure (Fin.append prevChallenges (fun _ => roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j =>
        if h : j.val = (i.val + 1)
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl ⟨j.val, by have := Nat.lt_succ_iff_lt_or_eq.mp j.2; aesop⟩,
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
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement D x s i.succ) (Witness F)
    (pSpec D x s i) where
  prover := foldProver D x s i
  verifier := foldVerifier D x s i

end FoldPhase

namespace FinalFoldPhase

-- /-- This is missing the relationship between the oracle statement and the witness. Need to define a
--   proximity parameter here. Completeness will be for proximity param `0`, while soundness will have
--   non-zero proximity param. -/
-- def inputRelation :
--     Set ((Statement F i.castSucc × (∀ j, OracleStatement D x s i.castSucc j)) × Witness F) :=
--   {⟨⟨stmt, ostmt⟩, p⟩ | Polynomial.natDegree p < (2 ^ (s * (k - i.val))) * d}

-- /-- Same with the above comment about input relation. -/
-- def outputRelation :
--     Set ((Statement F i.succ × (∀ j, OracleStatement D x s i.succ j)) × Witness F) :=
--   {⟨⟨_, _⟩, p⟩ | Polynomial.natDegree p < (2 ^ (s * (k - (i.val + 1)))) * d}

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending a codeword (of the desired length) to
  the verifier. -/
@[reducible]
def pSpec (F : Type) [Semiring F] : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[F, Unit → F[X]]⟩

instance : ∀ j, OracleInterface ((pSpec F).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      exact OracleInterface.instFunction


omit d in
noncomputable def finalFoldProver :
  OracleProver []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k)) (Witness F)
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (pSpec F) where
  -- This may be difficult to reason about, given that the degree does get divided by 2 each round.
  -- Might want to bake that into the type.
  -- Also need to return all the prior oracle statements and prior challenges
  PrvState
  | 0 =>
    (Statement F (Fin.last k) × ((j : Fin (k + 1)) → OracleStatement D x s (Fin.last k) j)) ×
      Witness F
  | _ =>
    (FinalStatement F k × ((j : Fin (k + 1)) → OracleStatement D x s (Fin.last k) j)) ×
      Witness F

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ =>
    pure ⟨fun x => p, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => pure <|
    fun (α : F) =>
      ⟨⟨Fin.append chals (fun (_ : Fin 1) => α), o⟩, RoundConsistency.foldα (2 ^ s) p α⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ => pure <|
    ⟨
      ⟨
        chals,
        fun j => by
          unfold FinalOracleStatement
          if h : j.1 = k + 1
          then
            simpa [h] using fun x => p
          else
          simpa [h, ↓reduceIte, OracleStatement, evalDomain] using
            o ⟨j.1, by omega⟩
      ⟩,
      p
    ⟩

def getConst (F : Type) [NonBinaryField F] : OracleComp [(pSpec F).Message]ₒ F[X] :=
  OracleComp.lift
    (by exact
          OracleSpec.query
            (spec := [(pSpec F).Message]ₒ)
            ⟨1, by rfl⟩
            (by simpa using ())
    )

/-- The oracle verifier for the `i`-th round of the FRI protocol. -/
noncomputable def finalFoldVerifier :
  OracleVerifier []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k))
    (FinalStatement F k) (FinalOracleStatement D x s k)
    (pSpec F)  where
  verify := fun prevChallenges roundChallenge => do
    let p ← getConst F
    guard (p.natDegree < d)
    pure (Fin.append prevChallenges (fun _ => roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j =>
        if h : j.val = (k + 1)
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl ⟨j.val, by have := Nat.lt_succ_iff_lt_or_eq.mp j.2; aesop⟩,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    intros j
    simp only [
      Fin.vcons_fin_zero, Nat.reduceAdd, MessageIdx, Fin.isValue,
      Function.Embedding.coeFn_mk, Message
    ]
    split_ifs with h
    · simp
    · rfl

/-- The oracle reduction that is the `i`-th round of the FRI protocol. -/
noncomputable def finalFoldOracleReduction :
  OracleReduction []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k)) (Witness F)
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (pSpec F) where
  prover := finalFoldProver (n := n) (k := k) D x s d
  verifier := finalFoldVerifier (k := k) D x s d

end FinalFoldPhase

namespace QueryRound

variable (l : ℕ)

@[reducible]
def pSpec : ProtocolSpec 1 :=
  ⟨!v[.V_to_P], !v[Fin l → evalDomain D x 0]⟩

instance : ∀ j, OracleInterface ((pSpec D x l).Message j) := fun j =>
  match j with
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec D x l).Challenge j) := fun j =>
  by
    unfold Challenge
    have : j.1 = 0 := by omega
    rw [this]
    exact OracleInterface.instFunction

noncomputable def queryProver :
  OracleProver []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (pSpec D x l) where
  PrvState
  | _ =>
    (FinalStatement F k × ((i : Fin (k + 2)) → FinalOracleStatement D x s k i)) ×
      Witness F

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨1, _⟩ => fun x => pure <| fun _ => x

  output := pure

@[simp]
lemma range_lem {i : Fin (k + 1)} : [FinalOracleStatement D x s k]ₒ.range ⟨i.1, by omega⟩ = F := by
  sorry

#check Eq.mpr

set_option pp.proofs true

@[simp]
lemma domain_lem {F : Type} [NonBinaryField F] (D : Subgroup Fˣ)
  [DIsCyclicC : IsCyclicWithGen D] (x : Fˣ) {k : ℕ} (s : ℕ) {i : Fin (k + 1)} :
  [FinalOracleStatement D x s k]ₒ.domain ⟨i.1, by omega⟩ = evalDomain D x (s * i.1) := by
  unfold OracleSpec.domain FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  have : i.val ≠ k + 1 := by omega
  simp only [this, ↓reduceDIte, id_eq]
  unfold OracleInterface.instFunction
  generalize_proofs h
  split at h
  · aesop
  · aesop





  sorry

def queryCodeword {i : Fin (k + 1)} (w : evalDomain D x (s * i.1)) :
    OracleComp [FinalOracleStatement D x s k]ₒ F := OracleComp.lift <| by
  have := @OracleSpec.query (Fin (k + 2)) [FinalOracleStatement D x s k]ₒ ⟨i.1, by omega⟩
  have bla := @range_lem F _ _ D n _ _ x k s d _ _ i
  rw [bla] at this
  apply this
  have := @domain_lem n k s d _ _ F _ D _ x k s i
  rw [this]
  exact w


def getConst : OracleComp [FinalOracleStatement D x s k]ₒ F[X] :=
  OracleComp.lift
    (by convert
          OracleSpec.query
            (spec := [FinalOracleStatement D x s k]ₒ)
            (Fin.last (k + 1))
            (by convert (); sorry)
        sorry
    )

noncomputable def queryVerifier [DecidableEq F] :
  OracleVerifier []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s k)
    (FinalStatement F k) (FinalOracleStatement D x s k)
    (pSpec D x l) where
  verify := fun prevChallenges roundChallenge => do
    let (p : F[X]) ← getConst (k := k) D x s
    guard (p.natDegree < d)
    for m in (List.finRange l) do
      have : 0 < s := by
        have := s_nz.out
        omega
      let s₀ := roundChallenge ⟨1, by aesop⟩ m
      discard <|
        (List.finRange (k + 1)).mapM
              (fun i =>
                do
                  let x₀ := prevChallenges i
                  have : s * i.val ≤ n - s := by
                    apply Nat.le_sub_of_add_le
                    have := k_le_n' _ _ k_le_n
                    nlinarith [i.2]
                  let s₀ : evalDomain D x (s * i.1) :=
                    ⟨_, pow_2_pow_i_mem_Di_of_mem_D (s * i.1) s₀.2⟩
                  let queries : List (evalDomain D x (s * i.1)) :=
                    List.map (fun r => ⟨_, CosetDomain.mul_root_of_unity D this s₀.2 r.2⟩)
                      (Domain.rootsOfUnity D n s)
                  let (pts : List (F × F)) ←
                    List.mapM (fun q => queryCodeword s q >>= fun v => pure (q.1.1, v)) queries
                  let β ←
                    if h : i.1 < k
                    then
                      queryCodeword s (k := k) (i := ⟨i.1.succ, by omega⟩)
                        ⟨_, CosetDomain.pow_lift D x s s₀.2⟩
                    else pure (p.eval (s₀.1.1 ^ (2 ^ s)))
                  guard (RoundConsistency.round_consistency_check x₀ pts β)
              )
    pure prevChallenges
  embed :=
    ⟨
      fun j =>
        Sum.inl <| by simpa using j,
      by intros _; aesop
    ⟩
  hEq := by
    unfold FinalOracleStatement pSpec
    aesop


noncomputable def queryOracleReduction [DecidableEq F] :
  OracleReduction []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (pSpec D x l) where
  prover := queryProver D x s l
  verifier := queryVerifier D x s d k_le_n l

end QueryRound

end Spec

end Fri
