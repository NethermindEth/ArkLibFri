import ArkLib.OracleReduction.Basic
import ArkLib.ProofSystem.Fri.Domain
import ArkLib.ProofSystem.Fri.RoundConsistency

/-!
# The FRI protocol

  We describe the FRI oracle reduction as a composition of many single rounds, and a final
  (zero-interaction) query round where the oracle verifier makes all queries to all received oracle
  codewords.

  This formalisation tries to encompass all of the generalisations of the FRI
  low-degree test covered in the "A summary on the {FRI} low degree test" paper
  by Ulrich Haböck (Cryptology ePrint Archive, Paper 2022/1216), see:
  https://eprint.iacr.org/2022/1216

 -/

namespace Fri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset CosetDomain NNReal

namespace Spec

/- FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree", for `s = 1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `domain_size_cond`, a proof that the initial evaluation domain is large enough to test
      for proximity of a polynomial of appropriate degree.
  - `i` the index of the current folding round.
-/
variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s d : ℕ) [s_nz : NeZero s] [d_nz : NeZero d]
variable (domain_size_cond : 2 ^ ((k + 1) * s) * d ≤ 2 ^ n) (i : Fin k)

omit s_nz in
lemma round_bound {n k s d : ℕ} [d_nz : NeZero d]
  (domain_size_cond : 2 ^ ((k + 1) * s) * d ≤ 2 ^ n) : (k + 1) * s ≤ n := by
  have : 2 ^ ((k + 1) * s) ≤ 2 ^ n := by
    exact le_of_mul_le_of_one_le_left domain_size_cond (Nat.zero_lt_of_ne_zero d_nz.out)
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
def Witness (F : Type) [Semiring F] {k : ℕ} (s d : ℕ) (i : Fin (k + 2)) :=
  F⦃< 2^(((k + 1) - i.1) * s) * d⦄[X]

omit [Finite F] s_nz d_nz in
private lemma witness_lift {F : Type} [NonBinaryField F]
      {k s d : ℕ} [NeZero s] {p : F[X]} {α : F} {i : Fin (k + 1)} :
    p ∈ Witness F s d i.castSucc →
      p.foldNth (2 ^ s) α ∈ Witness F s d i.succ := by
  intro deg_bound
  unfold Witness at deg_bound ⊢
  rw [Polynomial.mem_degreeLT] at deg_bound ⊢
  simp only [Fin.coe_castSucc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Fin.val_succ] at deg_bound ⊢
  by_cases h : p = 0
  · have arith : 2 ^ ((k - i.1) * s) * ↑d = WithBot.some (2 ^ ((k - i.1) * s) * d) := by rfl
    rw [h, foldNth_zero, degree_zero, Nat.add_sub_add_right, arith]
    exact WithBot.bot_lt_coe _
  · have arith : 2 ^ ((k + 1 - ↑i) * s) * ↑d = WithBot.some (2 ^ ((k + 1 - ↑i) * s) * d) := by rfl
    have cast_lemma {a} : @Nat.cast (WithBot ℕ) _ a = WithBot.some a := rfl
    rw [Polynomial.degree_eq_natDegree h, arith, cast_lemma, WithBot.coe_lt_coe] at deg_bound
    have h' :=
      lt_of_le_of_lt
        (foldNth_degree_le' (n := 2 ^ s) (f := p) (α := α))
        deg_bound
    have : 2 ^ ((k + 1 - i.1) * s) * d = 2 ^ s * (2 ^ ((k + 1 - (i.1 + 1)) * s) * d) := by
      have : k + 1 - i.1 = ((k + 1) - (i.1 + 1)) + 1 := by
        refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
        exact Nat.le_sub_of_add_le' (by omega)
      rw [this, Nat.add_mul, one_mul, pow_add]
      grind
    rw [this] at h'
    have h' := Nat.lt_of_mul_lt_mul_left h'
    have arith' :
      2 ^ ((k + 1 - (↑i + 1)) * s) * ↑d =
        WithBot.some (2 ^ ((k + 1 - (↑i + 1)) * s) * d) := rfl
    rw [arith']
    by_cases h'' : p.foldNth (2 ^ s) α = 0
    · rw [h'', degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_eq_natDegree h'', cast_lemma, WithBot.coe_lt_coe]
      exact h'

instance {i : Fin (k + 1)} : ∀ j, OracleInterface (OracleStatement D x s i j) :=
  fun _ => inferInstance

instance : ∀ j, OracleInterface (FinalOracleStatement D x s k j) :=
  fun j =>
    if h : j = k + 1
    then {
           Query := Unit
           Response := F[X]
           answer := cast (by simp [h, FinalOracleStatement])
                          (id (α := Unit → F[X]))
         }
    else {
           Query := ↑(evalDomain D x (s * ↑j))
           Response := F
           answer := cast (by simp [h, FinalOracleStatement])
                          (id (α := ↑(evalDomain D x (s * ↑j)) → F))
         }

@[simp]
lemma range_lem₁ {F : Type} [NonBinaryField F] {D : Subgroup Fˣ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {s k : ℕ} {i : Fin (k + 1)} :
    [FinalOracleStatement D x s k]ₒ.range ⟨i.1, Nat.lt_succ_of_lt i.2⟩ = F := by
  unfold OracleSpec.range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp [Nat.ne_of_lt i.2]

@[simp]
lemma domain_lem₁ {F : Type} [NonBinaryField F] {D : Subgroup Fˣ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : ℕ} {i : Fin (k + 1)} :
    [FinalOracleStatement D x s k]ₒ.domain ⟨i.1, Nat.lt_succ_of_lt i.2⟩ =
      evalDomain D x (s * i.1) := by
  unfold OracleSpec.domain FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp [Nat.ne_of_lt i.2]

@[simp]
lemma range_lem₂ {F : Type} [NonBinaryField F] {D : Subgroup Fˣ} [DIsCyclicC : IsCyclicWithGen ↥D]
  {x : Fˣ} {s k : ℕ} : [FinalOracleStatement D x s k]ₒ.range (Fin.last (k + 1)) = F[X] := by
  unfold OracleSpec.range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp

@[simp]
lemma domain_lem₂ {F : Type} [NonBinaryField F] (D : Subgroup Fˣ)
  [DIsCyclicC : IsCyclicWithGen D] {x : Fˣ} {s k : ℕ} :
  [FinalOracleStatement D x s k]ₒ.domain (Fin.last (k + 1)) = Unit := by
  unfold OracleSpec.domain FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp

namespace FoldPhase

/- Definition of the non-final folding rounds of the FRI protocol. -/

/- Folding total round consistency predicate, checking of two subsequent code words will pass
   the round consistency at all points. -/
def roundConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : ℕ}
  (cond : (k + 1) * s ≤ n) {i : Fin (k + 1)} [DecidableEq F] {j : Fin i}
    (f : OracleStatement D x s i j.castSucc)
    (f' : OracleStatement D x s i j.succ)
    (x₀ : F) : Prop :=
  ∀ s₀ : evalDomain D x (s * j.1),
      let queries :
          List (evalDomain D x (s * j.1)) :=
            List.map
              (
                fun r =>
                  ⟨
                    _,
                    CosetDomain.mul_root_of_unity
                      D
                      (Nat.le_sub_of_add_le (by nlinarith [cond, j.2, i.2]))
                      s₀.2
                      r.2
                  ⟩
              )
              (Domain.rootsOfUnity D n s);
      let pts := List.map (fun q => (q.1.1, f q)) queries;
      let β := f' ⟨_, CosetDomain.pow_lift D x s s₀.2⟩;
        RoundConsistency.roundConsistencyCheck x₀ pts β

/- Checks for the total Folding round consistency of all rounds up to the current one. -/
def statementConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k s : ℕ} {i : Fin (k + 1)} [DecidableEq F]
      (cond : (k + 1) * s ≤ n)
      (stmt : Statement F i)
      (ostmt : ∀ j, OracleStatement D x s i j) : Prop :=
  ∀ j : Fin i,
    let f  := ostmt j.castSucc;
    let f' := ostmt j.succ;
    let x₀  := stmt j;
    roundConsistent cond f f' x₀

/- The FRI non-final folding round input relation, with proximity parameter `δ`, f
   for the `i`th round. -/
def inputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (Statement F i.castSucc × (∀ j, OracleStatement D x s i.castSucc j)) ×
        Witness F s d i.castSucc.castSucc
      ) := sorry

/- The FRI non-final folding round output relation, with proximity parameter `δ`,
   for the `i`th round. -/
def outputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (Statement F i.succ × (∀ j, OracleStatement D x s i.succ j)) ×
        Witness F s d i.succ.castSucc
      ) := sorry

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending an oracle to
  the verifier, commiting to evaluation of the witness at all points in the appropriate evaluation
  domain. -/
@[reducible]
def pSpec : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[F, (evalDomain D x (s * (i.1 + 1))) → F]⟩

/- `OracleInterface` instance for `pSpec` of the non-final folding rounds. -/
instance {i : Fin k} : ∀ j, OracleInterface ((pSpec D x s i).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      infer_instance

/-- The prover for the `i`-th round of the FRI protocol. It first receives the challenge,
    then does an `s` degree split of this polynomial. Finally, it returns the evaluation of
    this polynomial on the next evaluation domain. -/
noncomputable def foldProver :
  OracleProver []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc) (Witness F s d i.castSucc.castSucc)
    (Statement F i.succ) (OracleStatement D x s i.succ) (Witness F s d i.castSucc.succ)
    (pSpec D x s i) where
  PrvState
  | 0 =>
    (Statement F i.castSucc × ((j : Fin (↑i.castSucc + 1)) → OracleStatement D x s i.castSucc j)) ×
      Witness F s d i.castSucc.castSucc
  | _ =>
    (Statement F i.succ × ((j : Fin (↑i.castSucc + 1)) → OracleStatement D x s i.castSucc j)) ×
      Witness F s d i.castSucc.succ

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ =>
    pure ⟨fun x => p.1.eval x.1.1, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => pure <|
    fun (α : F) =>
      ⟨
        ⟨Fin.append chals (fun (_ : Fin 1) => α), o⟩,
        ⟨p.1.foldNth (2 ^ s) α, witness_lift p.2⟩
      ⟩
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
          else fun x => p.1.eval x.1.1
      ⟩,
      p
    ⟩

/-- The oracle verifier for the `i`-th non-final folding round of the FRI protocol. -/
noncomputable def foldVerifier :
  OracleVerifier []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc)
    (Statement F i.succ) (OracleStatement D x s i.succ)
    (pSpec D x s i) where
  verify := fun prevChallenges roundChallenge =>
    pure (Fin.vappend prevChallenges (fun _ => roundChallenge ⟨0, by simp⟩))
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
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc) (Witness F s d i.castSucc.castSucc)
    (Statement F i.succ) (OracleStatement D x s i.succ) (Witness F s d i.succ.castSucc)
    (pSpec D x s i) where
  prover := foldProver D x s d i
  verifier := foldVerifier D x s i

end FoldPhase

namespace FinalFoldPhase

/- Definition of the final folding round of the FRI protocol. -/

/- Folding total round consistency predicate, for the final round. -/
def roundConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : ℕ}
  (cond : (k + 1) * s ≤ n) [DecidableEq F]
    (f : FinalOracleStatement D x s k (Fin.last k).castSucc)
    (f' : FinalOracleStatement D x s k (Fin.last (k + 1)))
    (x₀ : F) : Prop :=
  let f : evalDomain D x (s * k) → F := by
    unfold FinalOracleStatement at f
    simp only [Fin.coe_castSucc, Fin.val_last, Nat.left_eq_add, one_ne_zero, ↓reduceIte] at f
    exact f
  let f' : F[X] := by
    unfold FinalOracleStatement at f'
    simp only [Fin.val_last, ↓reduceIte] at f'
    exact f' ()
  ∀ s₀ : evalDomain D x (s * k),
      let queries :
          List (evalDomain D x (s * k)) :=
            List.map
              (
                fun r =>
                  ⟨
                    _,
                    CosetDomain.mul_root_of_unity
                      D
                      (Nat.le_sub_of_add_le
                        (by
                          rw [Nat.add_mul, one_mul, mul_comm] at cond
                          exact cond
                        )
                      )
                      s₀.2
                      r.2
                  ⟩
              )
              (Domain.rootsOfUnity D n s);
      let pts := List.map (fun q => (q.1.1, f q)) queries;
      let β := f'.eval (s₀.1.1 ^ (2 ^ s));
        RoundConsistency.roundConsistencyCheck x₀ pts β

/- Input relation for the final folding round. This is currently sorried out, to be filled in later.
-/
def inputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (
          Statement F (Fin.last k) ×
          (∀ j, OracleStatement D x s (Fin.last k) j)
        ) ×
        Witness F s d (Fin.last k).castSucc
      ) := sorry

/- Output relation for the final folding round. This is currently sorried out, to be filled in
later. -/
def outputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement D x s k j) ×
        Witness F s d (Fin.last (k + 1))
      ) := sorry

/-- The final folding round of the FRI protocol begins with the verifier sending a random field
  element as the challenge to the prover, then in contrast to the previous folding rounds simply
  sends the folded polynomial to the verifier. -/
@[reducible]
def pSpec (F : Type) [Semiring F] : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[F, Unit → F[X]]⟩

/- `OracleInterface` instance for the `pSpec` of the final folding round of the FRI protocol. -/
instance : ∀ j, OracleInterface ((pSpec F).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      exact OracleInterface.instFunction

/- Prover for the final folding round of the FRI protocol. -/
noncomputable def finalFoldProver :
  OracleProver []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k))
      (Witness F s d (Fin.last k).castSucc)
    (FinalStatement F k) (FinalOracleStatement D x s k)
      (Witness F s d (Fin.last (k + 1)))
    (pSpec F) where
  PrvState
  | 0 =>
    (Statement F (Fin.last k) × ((j : Fin (k + 1)) → OracleStatement D x s (Fin.last k) j)) ×
      Witness F s d (Fin.last k).castSucc
  | _ =>
    (FinalStatement F k × ((j : Fin (k + 1)) → OracleStatement D x s (Fin.last k) j)) ×
      Witness F s d (Fin.last (k + 1))

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ =>
    pure ⟨fun x => p.1, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => pure <|
    fun (α : F) =>
      ⟨
        ⟨Fin.vappend chals !v[α], o⟩,
        ⟨
          p.1.foldNth (2 ^ s) α,
          by
            simpa only [(rfl : (Fin.last k).succ = (Fin.last (k + 1)))] using
              witness_lift p.2
        ⟩
      ⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ => pure <|
    ⟨
      ⟨
        chals,
        fun j => by
          unfold FinalOracleStatement
          if h : j.1 = k + 1
          then
            simpa [h] using fun x => p.1
          else
          simpa [h, ↓reduceIte, OracleStatement, evalDomain] using
            o ⟨j.1, Nat.lt_of_le_of_ne (Fin.is_le j) h⟩
      ⟩,
      p
    ⟩

/- Used to fetch the polynomial sent by the prover. -/
def getConst (F : Type) [NonBinaryField F] : OracleComp [(pSpec F).Message]ₒ F[X] :=
  OracleComp.lift
    (by exact
          OracleSpec.query
            (spec := [(pSpec F).Message]ₒ)
            ⟨1, by rfl⟩
            (by simpa using ())
    )

/-- The oracle verifier for the final folding round of the FRI protocol.
    Checks if the returned polynomial has degree less than `d`. -/
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

/-- The oracle reduction that is the final folding round of the FRI protocol. -/
noncomputable def finalFoldOracleReduction :
  OracleReduction []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k))
      (Witness F s d (Fin.last k).castSucc)
    (FinalStatement F k) (FinalOracleStatement D x s k)
      (Witness F s d (Fin.last (k + 1)))
    (pSpec F) where
  prover := finalFoldProver D x s d
  verifier := finalFoldVerifier D x s d

end FinalFoldPhase

namespace QueryRound

/- Definition of the query round of the FRI protocol. -/

/-  Parameter for the number of round consistency checks to be
    run by the query round. -/
variable (l : ℕ) [NeZero l]

/- Input/Output relations for the query round of the FRI protocol -/
def inputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement D x s k j) ×
        Witness F s d (Fin.last (k + 1))
      )
  := FinalFoldPhase.outputRelation D x s d cond δ

def outputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement D x s k j) ×
        Witness F s d (Fin.last (k + 1))
      )
  := FinalFoldPhase.outputRelation D x s d cond δ

/- The query round consistens of the verifier sending `l` elements of the
   the first evaluation domain, which will be used as a basis for the round
   consistency checks. This makes this implementation a public-coin protocol.
-/
@[reducible]
def pSpec : ProtocolSpec 1 :=
  ⟨!v[.V_to_P], !v[Fin l → evalDomain D x 0]⟩

/- `OracleInterface` instances for the query round `pSpec`. -/
instance : ∀ j, OracleInterface ((pSpec D x l).Message j) := fun j =>
  match j with
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec D x l).Challenge j) := fun j =>
  by
    unfold Challenge
    rw [Fin.fin_one_eq_zero j.1]
    exact OracleInterface.instFunction

/- Query round prover, does nothing. After BCS transform is applied to
   construct the non-interactive FRI protocol, it will have to respond with
   appropriate Merkle proofs against the commitments sent in the non final folding
   rounds. -/
noncomputable def queryProver :
  OracleProver []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F s d (Fin.last (k + 1)))
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F s d (Fin.last (k + 1)))
    (pSpec D x l) where
  PrvState
  | _ =>
    (FinalStatement F k × ((i : Fin (k + 2)) → FinalOracleStatement D x s k i)) ×
      Witness F s d (Fin.last (k + 1))

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨1, _⟩ => fun x => pure <| fun _ => x

  output := pure

/- Used by the verified to query the `i`th oracle at `w`, a point of the
   appropriate evaluation domain. -/
def queryCodeword {s : ℕ} (k : ℕ) {i : Fin (k + 1)} (w : evalDomain D x (s * i.1)) :
    OracleComp [FinalOracleStatement D x s k]ₒ F :=
      OracleComp.lift <| by
        simpa using
          OracleSpec.query
            (spec := [FinalOracleStatement D x s k]ₒ)
            ⟨i.1, Nat.lt_succ_of_lt i.2⟩
            (by simpa using w)

/- Used by the verifier to fetch the polynomial sent in final folding round. -/
def getConst (k : ℕ) (s : ℕ) : OracleComp [FinalOracleStatement D x s k]ₒ F[X] :=
  OracleComp.lift
    (by
        simpa using
          OracleSpec.query
            (spec := [FinalOracleStatement D x s k]ₒ)
            (Fin.last (k + 1))
            (by simpa using ())
    )

/- Verifier for query round of the FRI protocol. Runs `l` checks on uniformly
   sampled points in the first evaluation domain against the oracles sent during
   every folding round. -/
noncomputable def queryVerifier (k_le_n : (k + 1) * s ≤ n) (l : ℕ) [DecidableEq F] :
  OracleVerifier []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s k)
    (FinalStatement F k) (FinalOracleStatement D x s k)
    (pSpec D x l) where
  verify := fun prevChallenges roundChallenge => do
    let (p : F[X]) ← getConst D x k s
    for m in (List.finRange l) do
      let s₀ := roundChallenge ⟨1, by aesop⟩ m
      discard <|
        (List.finRange (k + 1)).mapM
              (fun i =>
                do
                  let x₀ := prevChallenges i
                  have h : s * i.val ≤ n - s :=
                    Nat.le_sub_of_add_le (by nlinarith [i.2])
                  let s₀ : evalDomain D x (s * i.1) :=
                    ⟨_, pow_2_pow_i_mem_Di_of_mem_D (s * i.1) s₀.2⟩
                  let queries : List (evalDomain D x (s * i.1)) :=
                    List.map (fun r => ⟨_, CosetDomain.mul_root_of_unity D h s₀.2 r.2⟩)
                      (Domain.rootsOfUnity D n s)
                  let (pts : List (F × F)) ←
                    List.mapM
                      (fun q => queryCodeword D x k q >>= fun v => pure (q.1.1, v))
                      queries
                  let β ←
                    if h : i.1 < k
                    then
                      queryCodeword D x k (i := ⟨i.1.succ, Order.lt_add_one_iff.mpr h⟩)
                        ⟨_, CosetDomain.pow_lift D x s s₀.2⟩
                    else
                      pure (p.eval (s₀.1.1 ^ (2 ^ s)))
                  guard (RoundConsistency.roundConsistencyCheck x₀ pts β)
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

/- Query round oracle reduction. -/
noncomputable def queryOracleReduction [DecidableEq F] :
  OracleReduction []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F s d (Fin.last (k + 1)))
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F s d (Fin.last (k + 1)))
    (pSpec D x l) where
  prover := queryProver D x s d l
  verifier := queryVerifier D x s (round_bound domain_size_cond) l

end QueryRound

end Spec

end Fri
