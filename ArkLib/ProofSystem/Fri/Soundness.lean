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

variable {𝔽 : Type} [NonBinaryField 𝔽] [Finite 𝔽] [DecidableEq 𝔽]
variable (D : Subgroup 𝔽ˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (g : 𝔽ˣ)
variable (s : Fin (n + 1) → ℕ+) (d : ℕ+)
variable (domain_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)

noncomputable local instance : Fintype 𝔽 := Fintype.ofFinite _

def pows (z : 𝔽) (ℓ : ℕ) : Matrix Unit (Fin ℓ) 𝔽 :=
  Matrix.of <| fun _ j => z ^ j.val

noncomputable def powsDom (z : 𝔽) (i : ℕ) : Matrix Unit (CosetDomain.evalDomain D g i) 𝔽 :=
  Matrix.of <| fun _ j => z ^ (CosetDomain.domainToFin (n := n) D g j).val

noncomputable def Mg {i : ℕ} (g : Domain.evalDomain D (i + 1))
  (f : Fin (2 ^ (n - i)) → 𝔽)
  :
  Matrix Unit (Fin (2 ^ (n - i))) 𝔽
  :=
  let poly := Lagrange.interpolate
    Finset.univ
    (fun x => (CosetDomain.domain D g n i x).1.1) f
  Matrix.of <| fun _ j => poly.coeff j

noncomputable def MgDom {i : ℕ} {g : 𝔽ˣ}
  (f : CosetDomain.evalDomain D g i → 𝔽)
  :
  Matrix Unit (CosetDomain.evalDomain D g i) 𝔽
  :=
  let poly := Lagrange.interpolate Finset.univ (·.1.1) f
  Matrix.of <| fun _ j => poly.coeff (CosetDomain.domainToFin (n := n) D g j)

lemma Mg_invertible {i : ℕ} {g : Domain.evalDomain D (i + 1)}
  :
  ∃ Mg_inv, Function.LeftInverse (Mg (n := n) D g) Mg_inv
    ∧ Function.RightInverse (Mg D g) Mg_inv := by sorry

noncomputable def Mg_inv {i : ℕ} (g : Domain.evalDomain D (i + 1))
  :
  Matrix Unit (Fin (2 ^ (n - i))) 𝔽
  →
  (Fin (2 ^ (n - i))) → 𝔽
  := Classical.choose (Mg_invertible D (g := g) (DSmooth := DSmooth))

noncomputable def f_succ {i : ℕ}
  (f : Fin (2 ^ (n - i)) → 𝔽)
  (z : 𝔽)
  (x : Fin (2 ^ (n - (i + 1))))
  :
  𝔽
  :=
  ((pows z (2^(n - i))) * (Matrix.transpose
    <| Mg D (Domain.domain D n (i + 1) x) f)).diag 0

open scoped Matrix in
noncomputable def dom_next {i : ℕ}
  (f : CosetDomain.evalDomain D g i → 𝔽)
  (z : 𝔽)
  (x : CosetDomain.evalDomain D g (i + 1))
  :
  𝔽
  :=
  let f : CosetDomain.evalDomain D x (i + 1) → 𝔽 :=
    fun dom ↦ f dom
  powsDom (n := n) D g z i * (MgDom (g := x) (n := n) D f)ᵀ |>.diag 0

lemma claim_8_1
  {i : Fin n}
  (f : ReedSolomon.code
        (CosetDomain.domainEmb (i := i.1) D g)
        (2 ^ (n - i)))
  (z : 𝔽)
  :
  (fun g' ↦ dom_next (n := n) (i := i) D g'.1 f.1 z ) ∈
    (ReedSolomon.code
      (CosetDomain.domainEmb (i := i.1 + 1) D g)
      (2 ^ (n - (i + 1)))
    ).carrier
  := by sorry

lemma claim_8_1'
  {i : Fin n}
  (f : ReedSolomon.code
        ((CosetDomain.domainEnum (n := n) D g i.castSucc).trans CosetDomain.injectF)
        (2 ^ (n - i)))
  (z : 𝔽)
  :
  f_succ D f.val z ∈
    (ReedSolomon.code
      ((CosetDomain.domainEnum (n := n) D g i.succ).trans CosetDomain.injectF)
      (2 ^ (n - (i + 1)))
    ).carrier
  := by sorry

/-- Affine space: {g | ∃ x : Fin t.succ → 𝔽, x 0 = 1 ∧ g = ∑ i, x i • f i  }
-/
def Fₛ {ι : Type} [Fintype ι] {t : ℕ} (f : Fin t.succ → (ι → 𝔽)) : AffineSubspace 𝔽 (ι → 𝔽) :=
  f 0 +ᵥ affineSpan 𝔽 (Finset.univ.image (f ∘ Fin.succ))

noncomputable def correlated_agreement_density {ι : Type} [Fintype ι]
  (Fₛ : AffineSubspace 𝔽 (ι → 𝔽)) (V : Submodule 𝔽 (ι → 𝔽)) : ℝ :=
  let Fc := Fₛ.carrier.toFinset
  let Vc := V.carrier.toFinset
  (Fc ∩ Vc).card / Fc.card

open Polynomial

noncomputable def oracle (l : ℕ) (z : Fin (n + 1) → 𝔽) (f : CosetDomain.evalDomain D g 0 → 𝔽) :
  QueryImpl
    ([]ₒ ++ₒ ([Spec.FinalOracleStatement D g s]ₒ ++ₒ [(Spec.QueryRound.pSpec D g l).Message]ₒ))
    (OracleComp [(Spec.QueryRound.pSpec D g l).Message]ₒ) where
      impl :=
        fun q ↦
          match q with
          | query (.inl i) _ => PEmpty.elim i
          | query (.inr (.inl i)) dom =>
            let f0 := Lagrange.interpolate Finset.univ (fun v => v.1.1) f
            let chals : List (Fin (n + 1) × 𝔽) :=
              ((List.finRange (n + 1)).map (fun i => (i, z i))).take i.1
            let fi : 𝔽[X] := List.foldl (fun f (i, α) => Polynomial.foldNth (s i) f α) f0 chals
            if h : i.1 = n + 1
            then pure <| by
              simp only
                [
                  OracleSpec.range, OracleSpec.append,
                  OracleInterface.toOracleSpec, Spec.FinalOracleStatement
                ]
              unfold OracleInterface.Response Spec.instOracleInterfaceFinalOracleStatement
              simp [h]
              exact fi
            else pure <| by
              simp only
                [
                  OracleSpec.range, OracleSpec.append,
                  OracleInterface.toOracleSpec, Spec.FinalOracleStatement
                ]
              unfold OracleInterface.Response Spec.instOracleInterfaceFinalOracleStatement
              simp [h]
              simp only
                [
                  OracleSpec.domain, OracleSpec.append,
                  OracleInterface.toOracleSpec, Spec.FinalOracleStatement
                ] at dom
              unfold OracleInterface.Query Spec.instOracleInterfaceFinalOracleStatement at dom
              simp only [h, ↓reduceDIte] at dom
              exact fi.eval dom.1.1
          | query (.inr (.inr i)) t => OracleComp.lift (query i t)

instance {g : 𝔽ˣ} {l : ℕ} : [(Spec.QueryRound.pSpec D g l).Message]ₒ.FiniteRange where
  range_inhabited' := by
    intros i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1 = 0 := by omega
    have h := this ▸ i.2
    simp at h
  range_fintype' := by
    intros i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1 = 0 := by omega
    have h := this ▸ i.2
    simp at h

open ENNReal in
lemma lemma_8_2
  {t : ℕ}
  {α : ℝ}
  (f : Fin t.succ → (CosetDomain.evalDomain D g 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code ⟨fun x => x.1.1, fun a b h ↦ by aesop⟩ (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  :
    let ρ_sqrt :=
      ReedSolomonCode.sqrtRate
        (2 ^ n)
        (Embedding.trans (CosetDomain.domainEnum (n := n) D g 0) (CosetDomain.domainEmb D g))
    let α0 : ℝ≥0∞ := ENNReal.ofReal (max α (ρ_sqrt * (1 + 1 / 2 * m)))
    let εC : ℝ≥0∞ := ENNReal.ofReal <|
      (m + (1 : ℚ)/2)^7 * (2^n)^2
        / (2 * ρ_sqrt ^ 3) * (Fintype.card 𝔽)
      + (∑ i, (s i).1) * (2 * m + 1) * (2 ^ n + 1) / (Fintype.card 𝔽 * ρ_sqrt)
    let εQ  (x : Fin t → 𝔽)
            (z : Fin (n + 1) → 𝔽) :=
      Pr_{let samp ←$ᵖ (CosetDomain.evalDomain D g 0)}[
        [
          fun _ => True |
          (
            (do
              simulateQ (oracle D g s 1 z (fun v ↦ f 0 v + ∑ i, x i * f i.succ v))
                (
                  (
                    Fri.Spec.QueryRound.queryVerifier D g
                      (n := n + 1) (k := n) (s := s) (l := 1)
                        (by
                          apply Spec.round_bound (d := d)
                          transitivity
                          · exact domain_size_cond
                          · apply pow_le_pow (by decide) (by decide)
                            simp
                        )
                  ).verify
                  z
                  (fun i => by
                    simpa only
                      [
                        Spec.QueryRound.pSpec, Challenge,
                        show i.1 = 0 by omega, Fin.isValue,
                        Fin.vcons_zero
                      ] using fun _ => samp
                  )
                )
            )
          )
        ] = 1
      ]
    Pr_{let x ←$ᵖ (Fin t → 𝔽); let z ←$ᵖ (Fin (n + 1) → 𝔽)}[ εQ x z ≤ α0 ] ≤ εC
  := by sorry




end Fri
end Fri
