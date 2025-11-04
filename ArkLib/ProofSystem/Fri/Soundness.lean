/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Fri.Domain
import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.ProofSystem.Fri.Spec.SingleRound
import ArkLib.OracleReduction.Security.Basic
import ToMathlib.Control.OptionT

namespace Fri
section Fri

open OracleComp OracleSpec ProtocolSpec
open NNReal Finset Function ProbabilityTheory

universe u
variable {k n : ℕ}
variable {F : Type} [NonBinaryField F] [Finite F]
variable [DecidableEq F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]

def pows (z : F) (ℓ : ℕ) : Matrix Unit (Fin ℓ) F :=
  Matrix.of <| fun _ j => z ^ j.val

noncomputable def Mg {i : ℕ} (g : Domain.evalDomain D (i + 1))
  (f : Fin (2 ^ (n - i)) → F)
  :
  Matrix Unit (Fin (2 ^ (n - i))) F
  :=
  let poly := Lagrange.interpolate (F := F)
    (@Finset.univ _ (sorry))
    (fun x => (CosetDomain.domain D g n i x).val) f
  Matrix.of <| fun _ j => poly.coeff j

lemma Mg_invertible {i : ℕ} {g : Domain.evalDomain D (i + 1)}
  :
  ∃ Mg_inv, Function.LeftInverse (Mg (n := n) D g) Mg_inv
    ∧ Function.RightInverse (Mg D g) Mg_inv := by sorry

noncomputable def Mg_inv {i : ℕ} (g : Domain.evalDomain D (i + 1))
  :
  Matrix Unit (Fin (2 ^ (n - i))) F
  →
  (Fin (2 ^ (n - i))) → F
  := Classical.choose (Mg_invertible D (n := n) (g := g) (DSmooth := DSmooth))

noncomputable def f_succ {i : ℕ}
  (f : Fin (2 ^ (n - i)) → F)
  (z : F)
  (x : Fin (2 ^ (n - (i + 1))))
  :
  F
  :=
  ((pows z (2^(n - i))) * (Matrix.transpose
    <| Mg D (n := n) (Domain.domain D n (i + 1) x) f)).diag 0

lemma claim_8_1
  {i : ℕ}
  (f : ReedSolomon.code
     (F := F)
     (ι := Fin (2 ^ (n - i)))
     ⟨fun x => (Domain.domain D n i x).val, sorry⟩ (2 ^ (n - i)))
  (hk : ∃ k', k + 1 = 2 ^ k')
  (z : F)
  :
  f_succ D f.val z ∈ (ReedSolomon.code
    (F := F)
    (ι := Fin (2 ^ (n - (i + 1))))
    ⟨fun x => (Domain.domain D n (i + 1) x).val, sorry⟩ (2 ^ (n - (i + 1)))).carrier
  := by sorry

/-- Affine space: {g | ∃ x : Fin t.succ → F, x 0 = 1 ∧ g = ∑ i, x i • f i  }
-/
def Fₛ {t : ℕ} (f : Fin t.succ → (Fin (2 ^ n) → F)) : AffineSubspace F (Fin (2 ^ n) → F) :=
  f 0 +ᵥ affineSpan F (Finset.univ.image (f ∘ Fin.succ))

def correlated_agreement_density (Fₛ : AffineSubspace F (Fin (2 ^ n) → F))
  (V : Submodule F ((Fin (2 ^ n)) → F)) : ℝ := sorry

noncomputable def εC [Fintype F]
  {r : ℕ}
  (ℓ : Fin r → ℕ) (ρ : ℝ) (m : ℕ) : ℝ :=
  (m + (1 : ℚ)/2)^7 * (2^n)^2
    / (2 * (Real.sqrt ρ) ^ 3) * (Fintype.card F)
  + (∑ i, ℓ i) * (2 * m + 1) * (2 ^ n + 1) / (Fintype.card F * Real.sqrt ρ)

#check QueryImpl
#check ProbComp
#check OracleSpec
#check OracleQuery
#check PEmpty.elim

open Polynomial

def oracle (g : Fˣ) (l : ℕ) (f : Fin n.succ → (Fin (2 ^ n) → F)) (final : F[X]) :
  QueryImpl
    ([]ₒ ++ₒ ([Spec.FinalOracleStatement D g 1 n]ₒ ++ₒ [(Spec.QueryRound.pSpec D g l).Message]ₒ))
    (OracleComp [(Spec.QueryRound.pSpec D g l).Message]ₒ) where
      impl :=
        λ q ↦
          match q with
          | query (.inl i) _ => PEmpty.elim i
          | query (.inr (.inl i)) _ =>
            if h : i.1 < n + 1
            then sorry
              -- let bla :=  Fri.CosetDomain.domain D g n;
              -- pure (f ∘ Fri.CosetDomain.domain D x <| ⟨i.1, h⟩)
            else pure <| by
              simpa
                [
                  OracleSpec.range, OracleSpec.append, OracleInterface.toOracleSpec, Spec.FinalOracleStatement,
                  OracleInterface.Response, Spec.instOracleInterfaceFinalOracleStatement,
                  show i.1 = n + 1 by grind [cases Fin]
                ] using final
          | query (.inr (.inr i)) _ => _

instance {g : Fˣ} {l : ℕ} : [(Spec.QueryRound.pSpec D g l).Message]ₒ.FiniteRange where
  range_inhabited' := sorry
  range_fintype' := sorry

lemma lemma_8_2
  {l : ℕ}
  {n : ℕ}
  {α : ℝ}
  {f : Fin n.succ → (Fin (2 ^ n) → F)}
  {final : F[X]}
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (F := F)
        (ι := Fin (2 ^ n))
        ⟨fun x => (Domain.domain D n 0 x).val, sorry⟩ (2 ^ n))
    ≤ α)
  {m : ℕ}
  {g : Fˣ}
  :
  let εQ (z : Spec.FinalStatement F n) (x : Fin l → CosetDomain.evalDomain D g 0) :=
    [
      fun _ => True |
      (
        (do
          simulateQ (oracle D g l f final)
            (
              (
                Fri.Spec.QueryRound.queryVerifier D g
                  (n := n + 1) (k := n) (s := 1) (l := l) (by simp)
              ).verify
              z
              (by
                unfold Challenges Spec.QueryRound.pSpec
                simp only [Fin.vcons_fin_zero, Nat.reduceAdd, ChallengeIdx, Challenge]
                rintro ⟨⟨i, h'⟩, h⟩
                have : i = 0 := by omega
                simp only [this]
                exact x
              )
            )
        ) : OracleComp [(Spec.QueryRound.pSpec D g l).Message]ₒ _)
    ];
  True
  -- OptionT.isSome ((Fri.Spec.QueryRound.queryVerifier D x (s := 0) (l := 1)
  --   (by sorry)).verify sorry sorry)
  :=
  by sorry




end Fri
end Fri
