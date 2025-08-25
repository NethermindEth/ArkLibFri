import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Henselian


/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  [BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes".

  ## Main Definitions

-/

namespace ProximityGap

open NNReal Finset Function

open scoped BigOperators

section

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable (C : Submodule F (n → F)) [DecidablePred (· ∈ C)]

/-- The proximity measure of two vectors `u` and `v` from a code `C` at distance `d` is the number
  of vectors at distance at most `d` from the linear combination of `u` and `v` with coefficients
  `r` in `F`. -/
def proximityMeasure (u v : n → F) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀'(r • u + (1 - r) • v, C) ≤ d}

/-- A code `C` exhibits proximity gap at distance `d` and cardinality bound `bound` if for every
      pair of vectors `u` and `v`, whenever the proximity measure for `C u v d` is greater than
      `bound`, then the distance of `[u | v]` from the interleaved code `C ^⊗ 2` is at most `d`. -/
def proximityGap (d : ℕ) (bound : ℕ) : Prop :=
  ∀ u v : n → F, (proximityMeasure C u v d > bound)
    → (Δ₀( u ⋈ v , C ^⋈ Fin 2 ) ≤ d)

/-- A code `C` exhibits `δ`-correlated agreement with respect to a tuple of vectors `W_1, ..., W_k`
  if there exists a set `S` of coordinates such that the size of `S` is at least `(1 - δ) * |n|`,
  and there exists a tuple of codewords `v_1, ..., v_k` such that `v_i` agrees with `W_i` on `S`
  for all `i`. -/
def correlatedAgreement (C : Set (n → F)) (δ : ℝ≥0) {k : ℕ} (W : Fin k → n → F) : Prop :=
  ∃ S : Finset n, #(S) ≥ (1 - δ) * (Fintype.card n) ∧
    ∃ v : Fin k → n → F, ∀ i, v i ∈ C ∧ {j | v i j = W i j} ⊆ S

end

section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*}

/--
  Definition 1.1 in [BCIKS20].
-/
noncomputable def generalProximityGap {α : Type*} [DecidableEq α] [Nonempty α]
  (P : Finset (ι → α)) (C : Set (Finset (ι → α))) (δ ε : ℝ≥0) : Prop :=
  ∀ (S : Finset _) (h : S.Nonempty), S ∈ C → (PMF.uniformOfFinset S h).toOuterMeasure
  {x | Code.relHammingDistToCode x P ≤ δ} = 1
  ∨ (PMF.uniformOfFinset S h).toOuterMeasure {x | Code.relHammingDistToCode x P ≤ δ} ≤ ε
end

section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/--
  The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `ρ` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √ρ)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ [0, (1-√ρ)/2]` and Johnson bound, i.e. `δ ∈ [(1-√ρ)/2 , 1 - √ρ]`.
-/
noncomputable def errorBound (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  letI j := ReedSolomonCode.sqrtRate deg domain
  if δ ≤ 1 - j/2 then Fintype.card ι / Fintype.card F
  else if δ ≥ 1 - j/2 ∧ δ ≤ 1 - j
       then letI m := min (1 - j - δ) (j / 20)
            ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
       else 0

/--
  Theorem 1.2 Proximity Gaps for Reed-Solomon codes in [BCIKS20].
-/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
  (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  generalProximityGap
    (ReedSolomonCode.toFinset domain deg)
    (Affine.AffSpanSetFinsetCol C)
    δ
    (errorBound δ deg domain) := by sorry

/--
  Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].
-/
theorem correlatedAgreement_lines {u : Fin 2 → ι → F} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    (PMF.uniformOfFintype F).toOuterMeasure
      {z | Code.relHammingDistToCode (u 1 + z • u 2) (ReedSolomon.code domain deg) ≤ δ} >
      errorBound δ deg domain) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

/--
  Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].
-/
theorem correlatedAgreement_affine_curves [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    (PMF.uniformOfFintype (Curve.parametrisedCurveFinite u)).toOuterMeasure
      {y | Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ} >
      k * (errorBound δ deg domain)) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

open Affine in
/--
Theorem 1.6 (Correlated agreement over affine spaces) in [BCIKS20].
-/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k] {u : Fin k → ι → F} {deg : ℕ}
  {domain : ι ↪ F} {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    (@PMF.uniformOfFintype (affineSpan F (Affine.finsetOfVectors u).toSet)
      affineSpan_Fintype affineSpan_nonempty').toOuterMeasure
        {y | Code.relHammingDistToCode (ι := ι) (F := F) y (ReedSolomon.code domain deg) ≤ δ} >
        errorBound δ deg domain) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

end

namespace Trivariate
section Trivariate

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]

open Polynomial

opaque eval_on_Z₀ [Field F] [DecidableEq (RatFunc F)] (p : (RatFunc F)[X]) (z : F) : F := 
  sorry 

opaque eval_on_Z₁ [Field F] [DecidableEq (RatFunc F)] (p : (RatFunc F)[X]) (z : F) : F[X] := 
  sorry

opaque eval_on_Z₂ [Field F] [DecidableEq (RatFunc F)] (p : (RatFunc F)[X][X]) (z : F) : F[X][X] := 
  sorry

notation3:max R "[Z][X]" => Polynomial (Polynomial R)

notation3:max R "[Z][X][Y]" => Polynomial (Polynomial (Polynomial (R)))

notation3:max "Y" => Polynomial.X (R := Polynomial _)

notation3:max "Z" => Polynomial.X (R := Polynomial (Polynomial _))

end Trivariate
end Trivariate

section ProximityGapSection5
variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n k m : ℕ}

open Polynomial in
open RatFunc in
lemma proximity_gap_claim_5_4 {ωs u₀ u₁ : Fin n → F} 
  :
  ∃ Q : Polynomial (Polynomial (RatFunc F)) , Q ≠ 0 
    ∧ ∀ i, Bivariate.rootMultiplicity (F := RatFunc F)
      (C (C (RatFunc.mk (C (ωs i)) 1)) 
        : Polynomial (Polynomial (RatFunc F))) 
      (RatFunc.mk (C <| ωs i) 1 : RatFunc F)
      ((RatFunc.mk (C <| u₀ i) 1 + 
        (RatFunc.mk X 1) * 
          (RatFunc.mk (C <| u₁ i) 1)): RatFunc F) ≥ m := by sorry 

open GuruswamiSudan

/-- Lemma 5.3 from the Proximity gap paper -/ 
lemma guruswami_sudan_for_proximity_gap_existence {ωs f : Fin n → F} 
  :
  ∃ Q, GuruswamiSudanCondition k m (proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  sorry

open Polynomial

lemma guruswami_sudan_for_proximity_gap_property 
  {ωs f : Fin n → F} 
  {Q : F[X][X]} {p : F[X]} 
  (h : Δ₀(f, p.eval ∘ f) ≤ proximity_gap_johnson (n := n) k m)
  :
  ((X : F[X][X]) - Polynomial.C p) ∣ Q := by sorry 

noncomputable def D_X (rho : ℚ) (m : ℕ) : ℕ := Nat.floor <| (m + (1 : ℚ)/2) * Real.sqrt rho * n
def D_Y (Q : F[X][X]) : ℕ := Bivariate.degreeY Q 
def D_YZ (Q : F[X][X]) : ℕ := Bivariate.totalDegree Q

def the_S [Field F] (δ : ℚ) (V : LinearCode (ι := Fin n) (F := F)) (u₀ u₁ : Fin n → F) 
  : Finset F := 
    @Set.toFinset _ { z | ∀ v ∈ V.carrier, Δ₀(u₀ + (fun _ => z) * u₁, v) ≤ δ} sorry

opaque C₀ (Q : F[Z][X][Y]) : F[Z][X] := sorry
opaque R₀ (Q : F[Z][X][Y]) : List F[Z][X][Y] := sorry
opaque f₀ (Q : F[Z][X][Y]) : List ℕ := sorry
opaque e₀ (Q : F[Z][X][Y]) : List ℕ := sorry

lemma eq_5_12 {Q : F[Z][X][Y]} : 
  let C := C₀ Q
  let R := R₀ Q
  let f := f₀ Q
  let e := e₀ Q
  R.length = f.length ∧
  f.length = e.length ∧
  ∀ eᵢ∈ e, 1 ≤ eᵢ∧
  ∀ Rᵢ ∈ R, Rᵢ.Separable ∧
  ∀ Rᵢ ∈ R, Irreducible Rᵢ ∧
  Q = (Polynomial.C C) * 
    (List.prod 
      <| List.map 
        (fun ((R, f), e) => (R.comp ((Y : F[Z][X][Y]) ^ f))^e) (List.zip (List.zip R f) e)) 
    := sorry

lemma lemma_5_6
  {Q  : F[Z][X][Y]}
  :
  ∃ x₀,
  ∀ R ∈ R₀ Q,
  Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by sorry

open Trivariate in
lemma lemma_5_7 
  {V : LinearCode (ι := Fin n) F} {δ: ℚ} {x₀ : F} {f u₀ u₁ : Fin n → F} 
  {Q : (RatFunc F)[X][X]} {p : (RatFunc F)[X]} 
  :
  ∃ R H, R ∣ Q ∧ Irreducible H ∧ H ∣ (Bivariate.evalX (RatFunc.mk (Polynomial.C x₀) 1) R) ∧ 
   ({ z ∈ the_S (F := F) δ V u₀ u₁ | 
      (eval_on_Z₂ R z).comp (Polynomial.C (eval_on_Z₁ p z)) = 0
      ∧ (eval_on_Z₁ H z).comp (eval_on_Z₁ p z) = 0 }).card ≥ (the_S (F := F) δ V u₀ u₁).card 
        / (Bivariate.degreeY Q)  
      ∧ (the_S (F := F) δ V u₀ u₁).card 
        / (Bivariate.degreeY Q) > 2 * D_Y Q ^ 2 * (D_X (n := n) (rho := k/n) m) * D_YZ Q
    := by sorry 

end ProximityGapSection5


section ProximityGapSection6
variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n k m : ℕ}

def curve [Field F] (u : List (Fin n → F)) (z : F) : Fin n → F :=
    List.zip u (List.map (fun i => z ^ i) (List.range u.length)) 
    |> List.map (fun (u, z) i => (u i) * z)
    |> List.sum 

def the_S_multi
  [Finite F] (δ : ℚ) (u : List (Fin n → F)) (V : Finset (Fin n → F)) : Finset F :=
  @Set.toFinset _ { z | ∀ v ∈ V, Δ₀(curve u z, v) ≤ δ} sorry

theorem theorem_6_1
  [Field F]
  [Finite F]
  {rho : ℚ}
  {δ : ℚ}
  {V : Finset (Fin n → F)}
  (hδ : δ ≤ (1 - rho) / 2)
  {u : List (Fin n → F)}
  (hS : n * u.length < (the_S_multi δ u V).card)
  :
  the_S_multi δ u V = F ∧
  ∃ (v : List (Fin n → F)) (z : F),
    v.length = u.length ∧
    Δ₀(curve u z, curve v z) ≤ δ ∧
    ({ x : Fin n | 
      List.map (fun el => el x) u 
      ≠ List.map (fun el => el x) v } : Finset _).card ≤ δ * n := sorry

noncomputable def δ₀ (rho : ℚ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

theorem theorem_6_2
  [Field F]
  [Finite F]
  {m : ℕ}
  {rho : ℚ}
  {δ : ℚ}
  (hm : 3 ≤ m)
  {V : Finset (Fin n → F)}
  (hδ : δ ≤ δ₀ rho m)
  {u : List (Fin n → F)}
  (hS : ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.sqrt rho) ^ 3)
    * n ^ 2 * u.length < (the_S_multi δ u V).card)
  :
  ∃ (v : List (Fin n → F)),
  ∀ i ≤ v.length, v.getD (fallback := fun _ => 0) i ∈ V ∧ v.length = u.length ∧
  (1 - δ) * n ≤ ({x : Fin n | ∀ i ≤ u.length, u.getD i (fun _ => 0)
    = v.getD i (fun _ => 0) } : Finset _).card := sorry

section
open NNReal Finset Function

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Uniform in
theorem lemma_6_3 [DecidableEq ι] [DecidableEq F] {k : ℕ} {u : List (ι → F)}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    (PMF.uniformOfFinset (@Set.toFinset _ sorry
      (s := (AffineSubspace.carrier
        <| affineSpan F
          (let set := { x  | ∃ v ∈ (List.tail u), x = u.headD 0 + v };
            set)))) (hs := sorry)).toOuterMeasure
      {y : ι → F | Code.relHammingDistToCode y (ReedSolomon.code domain deg) ≤ δ} >
      (ProximityGap.errorBound δ deg domain)) :
  ∀ x ∈ (AffineSubspace.carrier
  <| affineSpan F 
    (let set := { x  | ∃ v ∈ (List.tail u), x = v }; 
      set
      )), Code.relHammingDistToCode x (ReedSolomon.code domain deg) ≤ δ
  := by sorry

end

end ProximityGapSection6

end ProximityGap
