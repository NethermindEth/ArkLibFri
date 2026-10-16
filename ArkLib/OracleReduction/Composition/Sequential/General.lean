/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
  # Sequential Composition of Many Oracle Reductions

  This file defines the sequential composition of an arbitrary `m + 1` number of oracle reductions.
  This is defined by iterating the composition of two reductions, as defined in `Append.lean`.

  The soundness and knowledge-soundness claims inherit the admitted binary security contracts.
  The false fixed-init completeness contracts have been removed. Proved completeness interfaces
  live in `Sequential/Completeness.lean`, `Sequential/GuardedNary.lean`, and
  `Sequential/OracleCompleteness.lean`, with explicit shared-state hypotheses.
-/

@[expose] public section

open ProtocolSpec OracleComp

universe u v

variable {ι : Type} {oSpec : OracleSpec ι}

section Composition

namespace Prover

/-- Sequential composition of provers, defined via iteration of the composition (append) of two
  provers. Specifically, we have the following definitional equalities:
- `seqCompose (m := 0) P = Prover.id`
- `seqCompose (m := m + 1) P = append (P 0) (seqCompose (m := m) P)`

TODO: improve efficiency, this might be `O(m^2)`
-/
@[inline]
def seqCompose
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin m) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
      Prover oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) :=
  match m with
  | 0 => Prover.id
  | _ + 1 => append (P 0) (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => P (Fin.succ i)))

@[simp]
lemma seqCompose_zero
    (Stmt : Fin 1 → Type) (Wit : Fin 1 → Type) {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin 0) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit P = Prover.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin (m + 1)) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit P =
      append (P 0) (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => P (Fin.succ i))) := rfl

end Prover

namespace Verifier

/-- Sequential composition of verifiers, defined via iteration of the composition (append) of
two verifiers. Specifically, we have the following definitional equalities:
- `seqCompose (m := 0) V = Verifier.id`
- `seqCompose (m := m + 1) V = append (V 0) (seqCompose (m := m) V)`

TODO: improve efficiency, this might be `O(m^2)`
-/
@[inline]
def seqCompose {m : ℕ} (Stmt : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    Verifier oSpec (Stmt 0) (Stmt (Fin.last m)) (seqCompose pSpec) := match m with
  | 0 => Verifier.id
  | _ + 1 => append (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i)))

@[simp]
lemma seqCompose_zero (Stmt : Fin 1 → Type)
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin 0) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    seqCompose Stmt V = Verifier.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ} (Stmt : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin (m + 1)) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    seqCompose Stmt V = append (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i))) := rfl

end Verifier

namespace Reduction

/-- Sequential composition of reductions, defined via sequential composition of provers and
  verifiers (or equivalently, folding over the append of reductions).

TODO: improve efficiency, this might be `O(m^2)`
-/
@[inline]
def seqCompose {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    Reduction oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) where
  prover := Prover.seqCompose Stmt Wit (fun i => (R i).prover)
  verifier := Verifier.seqCompose Stmt (fun i => (R i).verifier)

@[simp]
lemma seqCompose_zero (Stmt : Fin 1 → Type) (Wit : Fin 1 → Type)
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (R : (i : Fin 0) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit R = Reduction.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (R : (i : Fin (m + 1)) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit R =
      append (R 0) (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))) := rfl

end Reduction

namespace OracleProver

/-- Sequential composition of provers in oracle reductions, defined via sequential composition of
  provers in non-oracle reductions. -/
@[inline]
def seqCompose {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin m) →
      OracleProver oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    OracleProver oSpec (Stmt 0) (OStmt 0) (Wit 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (Wit (Fin.last m)) (seqCompose pSpec) :=
  Prover.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit P

@[simp]
lemma seqCompose_def {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin m) →
      OracleProver oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt OStmt Wit P = Prover.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit P :=
  rfl

end OracleProver

namespace OracleVerifier

/-- Sequential composition of verifiers in oracle reductions.

This is the auxiliary version that has instance parameters as implicit parameters, so that matching
on `m` can properly specialize those parameters.

TODO: have to fix instance diamonds to make this work -/
def seqCompose' {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j))
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i)) :
    OracleVerifier oSpec (Stmt 0) (OStmt 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (seqCompose pSpec) := match m with
  | 0 => @OracleVerifier.id ι oSpec (Stmt 0) (ιₛ 0) (OStmt 0) (Oₛ := Oₛ 0)
  | _ + 1 => append (V 0) (seqCompose' (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
      (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i)))

/-- Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the
  composition (append) of two oracle verifiers. -/
def seqCompose {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i)) :
    OracleVerifier oSpec (Stmt 0) (OStmt 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (seqCompose pSpec) :=
  seqCompose' Stmt OStmt Oₛ Oₘ V

@[simp]
lemma seqCompose_zero
    (Stmt : Fin 1 → Type)
    {ιₛ : Fin 1 → Type} (OStmt : (i : Fin 1) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin 0) → OracleVerifier oSpec
      (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ) (pSpec i)) :
    seqCompose Stmt OStmt V = OracleVerifier.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type)
    {ιₛ : Fin (m + 2) → Type} (OStmt : (i : Fin (m + 2)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin (m + 1)) → OracleVerifier oSpec
      (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ) (pSpec i)) :
    seqCompose Stmt OStmt V =
      append (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
        (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i))
          (fun i => V (Fin.succ i))) := rfl

/-- Reading a round-local value out of the materialized output of a sequential composition.

If every component verifier exposes, in its output oracles, the message it indexes with `msg`
(hypothesis `hf`, phrased via the read-out `f`), then the composed verifier's materialized output
exposes the *last* component's message. This is the fact needed to relate an output-oracle
embedding that points at a late prover message to the composed verifier's semantics. -/
theorem seqCompose_materializeOutput_last :
    ∀ {m : ℕ}
      {Stmt : Fin (m + 2) → Type}
      {ιₛ : Fin (m + 2) → Type} {OStmt : (i : Fin (m + 2)) → ιₛ i → Type}
      (Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j))
      {arity : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (arity i)}
      (Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j))
      (V : (i : Fin (m + 1)) → OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (pSpec i))
      {T : Type} (f : (i : Fin (m + 1)) → (∀ j, OStmt i.succ j) → T)
      (msg : (i : Fin (m + 1)) → (pSpec i).MessageIdx)
      (_hf : ∀ (i : Fin (m + 1)) ch oS ms,
        HEq (f i ((V i).materializeOutput (Oₛᵢ := Oₛ i.castSucc) (Oₘ := Oₘ i)
          (Oₛₒ := Oₛ i.succ) ch oS ms)) (ms (msg i)))
      (challenges : (ProtocolSpec.seqCompose pSpec).Challenges)
      (oStmt : ∀ j, OStmt 0 j)
      (messages : (ProtocolSpec.seqCompose pSpec).Messages),
      HEq (f (Fin.last m)
            ((seqCompose (Oₛ := Oₛ) (Oₘ := Oₘ) Stmt OStmt V).materializeOutput
              challenges oStmt messages))
        (messages (sigmaMessageIdxToSeqCompose (Fin.last m) (msg (Fin.last m)))) := by
  intro m
  induction m with
  | zero =>
    intro Stmt ιₛ OStmt Oₛ arity pSpec Oₘ V T f msg hf challenges oStmt messages
    have h1 : (seqCompose (Oₛ := Oₛ) (Oₘ := Oₘ) Stmt OStmt V).materializeOutput
          challenges oStmt messages
        = (V 0).materializeOutput (Oₛᵢ := Oₛ 0) (Oₘ := Oₘ 0) (Oₛₒ := Oₛ 1)
            (challenges.fst : (pSpec 0).Challenges) oStmt
            (messages.fst : (pSpec 0).Messages) := rfl
    rw [h1]
    exact HEq.trans (hf 0 _ _ _) (Messages.fst_heq messages (msg 0))
  | succ m ih =>
    intro Stmt ιₛ OStmt Oₛ arity pSpec Oₘ V T f msg hf challenges oStmt messages
    change (pSpec 0 ++ₚ ProtocolSpec.seqCompose (fun i => pSpec i.succ)).Challenges at challenges
    change (pSpec 0 ++ₚ ProtocolSpec.seqCompose (fun i => pSpec i.succ)).Messages at messages
    have h1 : (seqCompose (Oₛ := Oₛ) (Oₘ := Oₘ) Stmt OStmt V).materializeOutput
          challenges oStmt messages
        = (seqCompose (Oₛ := fun i => Oₛ i.succ) (Oₘ := fun i => Oₘ i.succ)
              (Stmt ∘ Fin.succ) (fun i => OStmt i.succ) (fun i => V i.succ)).materializeOutput
            challenges.snd
            ((V 0).materializeOutput (Oₛᵢ := Oₛ 0) (Oₘ := Oₘ 0) (Oₛₒ := Oₛ 1)
              challenges.fst oStmt messages.fst)
            messages.snd := rfl
    rw [h1]
    refine HEq.trans
      (ih (Stmt := Stmt ∘ Fin.succ) (ιₛ := fun i => ιₛ i.succ) (OStmt := fun i => OStmt i.succ)
        (arity := fun i => arity i.succ) (pSpec := fun i => pSpec i.succ)
        (fun i => Oₛ i.succ) (fun i => Oₘ i.succ) (fun i => V i.succ)
        (fun i => f i.succ) (fun i => msg i.succ)
        (fun i ch oS ms => hf i.succ ch oS ms) _ _ _) ?_
    exact Messages.snd_heq messages _

@[simp]
lemma seqCompose_toVerifier {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i)) :
    (seqCompose Stmt OStmt V).toVerifier =
      Verifier.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier) := by
  induction m with
  | zero =>
    simp only [Fin.isValue, Fin.reduceLast, Fin.vsum_zero, seqCompose_zero, Nat.reduceAdd,
      Verifier.seqCompose_zero]
    exact OracleVerifier.id_toVerifier
  | succ m ih =>
    simp only [seqCompose_succ, Verifier.seqCompose_succ]
    have h1 := OracleVerifier.append_toVerifier (V 0) (seqCompose (Stmt ∘ Fin.succ)
      (fun i => OStmt (Fin.succ i)) (fun i => V (Fin.succ i)))
    exact h1.trans (congrArg ((V 0).toVerifier.append ·)
      (ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (fun i => V (Fin.succ i))))

end OracleVerifier

namespace OracleReduction

/-- Sequential composition of oracle reductions, defined via sequential composition of oracle
  provers and oracle verifiers. -/
def seqCompose {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    OracleReduction oSpec (Stmt 0) (OStmt 0) (Wit 0)
      (Stmt (Fin.last m)) (OStmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) where
  prover := OracleProver.seqCompose Stmt OStmt Wit (fun i => (R i).prover)
  verifier := OracleVerifier.seqCompose Stmt OStmt (fun i => (R i).verifier)

@[simp]
lemma seqCompose_zero
    (Stmt : Fin 1 → Type)
    {ιₛ : Fin 1 → Type} (OStmt : (i : Fin 1) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin 1 → Type)
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin 0) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt OStmt Wit R =
      @OracleReduction.id ι oSpec (Stmt 0) (ιₛ 0) (OStmt 0) (Wit 0) (Oₛ 0) := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type)
    {ιₛ : Fin (m + 2) → Type} (OStmt : (i : Fin (m + 2)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin (m + 1)) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt OStmt Wit R =
      append (R 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ)
        (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i))
          (fun i => R (Fin.succ i))) := rfl

@[simp]
lemma seqCompose_toReduction {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    (seqCompose Stmt OStmt Wit R).toReduction =
      Reduction.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit
        (fun i => (R i).toReduction) := by
  induction m with
  | zero =>
    simp only [Fin.isValue, Fin.reduceLast, Fin.vsum_zero, seqCompose_zero, Nat.reduceAdd,
      Reduction.seqCompose_zero]
    exact OracleReduction.id_toReduction
  | succ m ih =>
    simp only [seqCompose_succ, Reduction.seqCompose_succ]
    have h1 := OracleReduction.append_toReduction (R 0) (seqCompose (Stmt ∘ Fin.succ)
      (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i)))
    exact h1.trans (congrArg ((R 0).toReduction.append ·)
      (ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ)
        (fun i => R (Fin.succ i))))

end OracleReduction

end Composition

variable {m : ℕ}
    {Stmt : Fin (m + 1) → Type}
    {ιₛ : Fin (m + 1) → Type} {OStmt : (i : Fin (m + 1)) → ιₛ i → Type}
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {Wit : Fin (m + 1) → Type}
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

-- section Execution

-- -- Executing .
-- theorem Reduction.run_seqCompose
--     (stmt : Stmt 0) (wit : Wit 0)
--     (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
--       (pSpec i)) :
--       (Reduction.seqCompose R).run stmt wit := by
--   sorry

-- end Execution

section Security

open scoped NNReal

namespace Verifier

/-- If all verifiers in a sequence satisfy soundness with respective soundness errors, then their
    sequential composition also satisfies soundness.
    The soundness error of the seqComposed verifier is the sum of the individual errors. -/
theorem seqCompose_soundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (soundnessError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).soundness init impl (lang i.castSucc) (lang i.succ) (soundnessError i)) :
      (Verifier.seqCompose Stmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i) := by
  induction m with
  | zero =>
    simp only [Fin.isValue, Fin.reduceLast, Fin.vsum_zero, seqCompose_zero,
      Finset.univ_eq_empty, Finset.sum_empty]
    exact Verifier.id_soundness init impl
  | succ m ih =>
    simp only [Fin.vsum_succ, seqCompose_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Function.comp_apply, Fin.succ_last, Nat.succ_eq_add_one]
    have := ih (fun i => lang i.succ) (fun i => V i.succ)
      (fun i => soundnessError i.succ) (fun i => h i.succ)
    simp only [Fin.succ_zero_eq_one, Fin.succ_last, Nat.succ_eq_add_one] at this
    rw [Fin.sum_univ_succ]
    exact append_soundness (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V i.succ))
      (h 0) this

/-- If all verifiers in a sequence satisfy knowledge soundness with respective knowledge errors,
    then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the seqComposed verifier is the sum of the individual errors. -/
theorem seqCompose_knowledgeSoundness
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (knowledgeError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).knowledgeSoundness init impl (rel i.castSucc) (rel i.succ) (knowledgeError i)) :
      (Verifier.seqCompose Stmt V).knowledgeSoundness init impl (rel 0) (rel (Fin.last m))
        (∑ i, knowledgeError i) := by
  induction m with
  | zero =>
    simp only [Fin.isValue, Fin.reduceLast, Fin.vsum_zero, seqCompose_zero,
      Finset.univ_eq_empty, Finset.sum_empty]
    exact Verifier.id_knowledgeSoundness init impl
  | succ m ih =>
    simp only [Fin.vsum_succ, seqCompose_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Function.comp_apply, Fin.succ_last, Nat.succ_eq_add_one]
    have := ih (fun i => rel i.succ) (fun i => V i.succ)
      (fun i => knowledgeError i.succ) (fun i => h i.succ)
    simp only [Fin.succ_zero_eq_one, Fin.succ_last, Nat.succ_eq_add_one] at this
    rw [Fin.sum_univ_succ]
    exact append_knowledgeSoundness (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V i.succ))
      (h 0) this

/-- If all verifiers in a sequence satisfy round-by-round soundness with respective RBR soundness
    errors, then their sequential composition also satisfies round-by-round soundness. -/
theorem seqCompose_rbrSoundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (rbrSoundnessError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrSoundness init impl (lang i.castSucc) (lang i.succ) (rbrSoundnessError i)) :
      (Verifier.seqCompose Stmt V).rbrSoundness init impl (lang 0) (lang (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) := by
  induction m with
  | zero =>
    have herr : (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2) = 0 := by
      funext i
      exact Fin.elim0 i.val
    rw [herr]
    rw [Verifier.seqCompose_zero]
    exact Verifier.id_rbrSoundness init impl
  | succ m ih =>
    simp only [Fin.vsum_succ, seqCompose_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Function.comp_apply, Fin.succ_last, Nat.succ_eq_add_one, ChallengeIdx]
    have := ih (fun i => lang i.succ) (fun i => V i.succ)
      (fun i => rbrSoundnessError i.succ) (fun i => h i.succ)
    simp only [Fin.succ_zero_eq_one, Fin.succ_last, Nat.succ_eq_add_one, ChallengeIdx] at this
    convert append_rbrSoundness (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V i.succ))
      (h 0) this;
    sorry

/-- If all verifiers in a sequence satisfy round-by-round knowledge soundness with respective RBR
    knowledge errors, then their sequential composition also satisfies round-by-round knowledge
    soundness. -/
theorem seqCompose_rbrKnowledgeSoundness
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (rbrKnowledgeError i)) :
      (Verifier.seqCompose Stmt V).rbrKnowledgeSoundness init impl (rel 0) (rel (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrKnowledgeError ij.1 ij.2) := by
  induction m with
  | zero =>
    have herr : (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        rbrKnowledgeError ij.1 ij.2) = 0 := by
      funext i
      exact Fin.elim0 i.val
    rw [herr]
    rw [Verifier.seqCompose_zero]
    exact Verifier.id_rbrKnowledgeSoundness init impl
  | succ m ih =>
    simp only [Fin.vsum_succ, seqCompose_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Function.comp_apply, Fin.succ_last, Nat.succ_eq_add_one, ChallengeIdx]
    have := ih (fun i => rel i.succ) (fun i => V i.succ)
      (fun i => rbrKnowledgeError i.succ) (fun i => h i.succ)
    simp only [Fin.succ_zero_eq_one, Fin.succ_last, Nat.succ_eq_add_one, ChallengeIdx] at this
    convert append_rbrKnowledgeSoundness (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V i.succ))
      (h 0) this;
    sorry

end Verifier

namespace OracleVerifier

/-- If all verifiers in a sequence satisfy soundness with respective soundness errors, then their
  sequential composition also satisfies soundness.
  The soundness error of the sequentially composed oracle verifier is the sum of the individual
  errors. -/
theorem seqCompose_soundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i × ∀ j, OStmt i j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (soundnessError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).soundness init impl (lang i.castSucc) (lang i.succ) (soundnessError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i) := by
  unfold OracleVerifier.soundness
  convert Verifier.seqCompose_soundness lang (fun i => (V i).toVerifier) soundnessError h
  simp only [seqCompose_toVerifier]

/-- If all verifiers in a sequence satisfy knowledge soundness with respective knowledge errors,
    then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the sequentially composed oracle verifier is the sum of the individual
    errors. -/
theorem seqCompose_knowledgeSoundness
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (knowledgeError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).knowledgeSoundness init impl (rel i.castSucc) (rel i.succ) (knowledgeError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).knowledgeSoundness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, knowledgeError i) := by
  unfold OracleVerifier.knowledgeSoundness
  convert Verifier.seqCompose_knowledgeSoundness rel (fun i => (V i).toVerifier) knowledgeError h
  simp only [seqCompose_toVerifier]

/-- If all verifiers in a sequence satisfy round-by-round soundness with respective RBR soundness
    errors, then their sequential composition also satisfies round-by-round soundness. -/
theorem seqCompose_rbrSoundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i × ∀ j, OStmt i j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (rbrSoundnessError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrSoundness init impl (lang i.castSucc) (lang i.succ) (rbrSoundnessError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).rbrSoundness
        init impl (lang 0) (lang (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) := by
  unfold OracleVerifier.rbrSoundness
  convert Verifier.seqCompose_rbrSoundness lang (fun i => (V i).toVerifier)
    rbrSoundnessError h
  simp only [seqCompose_toVerifier]

/-- If all verifiers in a sequence satisfy round-by-round knowledge soundness with respective RBR
    knowledge errors, then their sequential composition also satisfies round-by-round knowledge
    soundness. -/
theorem seqCompose_rbrKnowledgeSoundness
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : (i : Fin m) → OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (pSpec i))
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (rbrKnowledgeError i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).rbrKnowledgeSoundness
        init impl (rel 0) (rel (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrKnowledgeError ij.1 ij.2) := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  convert Verifier.seqCompose_rbrKnowledgeSoundness rel (fun i => (V i).toVerifier)
    rbrKnowledgeError h
  simp only [seqCompose_toVerifier]

end OracleVerifier

end Security
