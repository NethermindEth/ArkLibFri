/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Bivariate
import ArkLib.Data.CodingTheory.ReedSolomonCodes
import Mathlib.Data.Fintype.Defs


open Classical
open Polynomial
open Polynomial.Bivariate

namespace Bivariate

noncomputable section

variable {F : Type} [Semiring F]
         (m n : ℕ)
         (P P₁ P₂ : Finset F) [Nonempty P] [Nonempty P₁] [Nonempty P₁]
         (a : F)
         (f g : F[X][Y])
/--
The vector of coefficients of a bivariate polynomial, where coefficients are interpreted as
polynomials in the first variable `X`.
-/
def coeffsOfBivPolynomial (f : F[X][Y]) : Fin f.natDegree → F[X] :=
fun ⟨y, _⟩ ↦ Polynomial.coeff f y

-- lemma natDegreeBiv_lt_of_lbounded_zero_coeff {f : F[X][Y]} {deg : ℕ} [NeZero deg]
--   (h : ∀ i, deg ≤ i → f.coeff i = 0) : f.natDegree < deg := by
--   aesop (add unsafe [(by by_contra), (by specialize h f.natDegree)])

-- /--
-- Construct a bivariate polynomial in `X` and `Y` from a vector of coefficients,
-- which are polynomials in `X`.
-- -/
-- def polynomialOfCoeffsOfBiv {deg : ℕ} [NeZero deg] (coeffs : Fin deg → F[X]) : F[X][Y] :=
--  ⟨
--     Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
--     fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
--     fun a ↦ by aesop (add safe (by existsi a))
--                      (add simp [Fin.natCast_def, Nat.mod_eq_of_lt])
--   ⟩

-- @[simp]
-- lemma natDegree_polynomialOfCoeffsOfBiv_deg_lt_deg {deg : ℕ} [NeZero deg]
-- (coeffs : Fin deg → F[X]) :
--   (polynomialOfCoeffsOfBiv coeffs).natDegree < deg := by
--   aesop (add simp polynomialOfCoeffsOfBiv)
--         (add safe apply natDegreeBiv_lt_of_lbounded_zero_coeff)

-- @[simp]
-- lemma degree_polynomialOfCoeffsOfBiv_deg_lt_deg
--   {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   (polynomialOfCoeffsOfBiv coeffs).degree < deg := by
--   aesop (add simp [polynomialOfCoeffsOfBiv, degree_lt_iff_coeff_zero])

-- @[simp]
-- lemma coeff_polynomialOfCoeffsOfBiv_eq_coeffs {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   (polynomialOfCoeffsOfBiv coeffs).coeff ∘ Fin.val = coeffs := by -- NOTE TO SELF: `liftF' coeffs`!
--   aesop (add simp polynomialOfCoeffsOfBiv)

-- lemma coeff_polynomialOfCoeffsOfBiv_eq_coeffs' {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   (polynomialOfCoeffsOfBiv coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
--   aesop (add simp polynomialOfCoeffsOfBiv)

-- @[simp]
-- lemma polynomialOfCoeffsOfBiv_mem_degreeLT {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   polynomialOfCoeffsOfBiv coeffs ∈ degreeLT F[X] deg := by
--   aesop (add simp Polynomial.mem_degreeLT)


-- @[simp]
-- lemma polynomialOfCoeffsOfBiv_eq_zero {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F[X]} :
--   polynomialOfCoeffsOfBiv coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
--   simp [polynomialOfCoeffsOfBiv, AddMonoidAlgebra.ext_iff]

-- lemma polynomialOfCoeffsBiv_coeffsOfPolynomialBiv (deg : ℕ) [NeZero deg]
--   {f : F[X][Y]} (h : f.natDegree + 1 = deg)
--   : polynomialOfCoeffsOfBiv (coeffsOfBivPolynomial deg f) = f := by sorry
  -- ext x; symm
  -- aesop (add simp [polynomialOfCoeffsOfBiv, coeffsOfBivPolynomial, coeff_polynomialOfCoeffsOfBiv_eq_coeffs'])
  --       (add safe apply coeff_eq_zero_of_natDegree_lt)
  --       (add safe (by omega))


-- @[simp]
-- lemma coeffsOfBivPolynomial_polynomialOfCoeffsOfBiv {deg : ℕ} [NeZero deg]
--   {coeffs : Fin deg → F[X]} : coeffsOfBivPolynomial deg (polynomialOfCoeffsOfBiv coeffs) = coeffs
--   := by
--   ext x; symm
--   aesop (add simp [
--       polynomialOfCoeffsOfBiv, coeffsOfBivPolynomial, coeff_polynomialOfCoeffsOfBiv_eq_coeffs'
--                    ])
--         (add safe (by omega))

-- @[simp]
-- lemma support_polynomialOfBivCoeffs (deg : ℕ) [NeZero deg] {coeffs : Fin deg → F[X]} :
--   (polynomialOfCoeffsOfBiv coeffs).support =
--   Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl


def evalAtX (a : F) (f : F[X][Y]) : F[X] :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩

lemma evalAtX_deg_le_degY (a : F) (f : F[X][Y]) :
  (evalAtX a f).natDegree ≤ f.natDegree := by
  sorry

/--
Evaluating a bivariate polynomial in the first variable `X` on a set of points resulting in a set of
univariate polynomials in `Y`.
-/
def evalAtXOnASet (P : Finset F) (f : F[X][Y]) : Set (Polynomial F) :=
 {h : Polynomial F | ∃ a ∈ P, evalAtX a f = h}

/--
The evaluation at a point of a bivariate polynomial in the second variable `Y`.
-/
def evalAtY (a : F) (f : F [X][Y]) : Polynomial F :=
  Polynomial.eval (Polynomial.C a) f

/--
Evaluating a bivariate polynomial in the second variable `Y` on a set of points resulting
in a set of univariate polynomials in `X`.
-/
def evalAtYOnASet (P : Finset F) (f : F[X][Y]) : Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalAtY a f = h}


/-the next def, lemmma and def give an alternative def of degreeX. the proof of nonempty
forces the condition of `f ≠ 0`. So this definition is closer to the degree rather than
natdegree one.. mayve still worth keeping?
-/
def degreesXFinset' (f : F[X][Y]) : Finset ℕ :=
  f.toFinsupp.support

lemma degreesXFinset'_nonempty (f : F[X][Y]) (hf : f ≠ 0) : (degreesXFinset' f).Nonempty := by
  rw[degreesXFinset']
  apply Finsupp.support_nonempty_iff.mpr
  intro h
  apply hf
  exact Polynomial.ext (fun n => by rw [← Polynomial.toFinsupp_apply, h]; rfl)


def degreeX' (f : F[X][Y]) (hf : f ≠ 0) : ℕ :=
  f.toFinsupp.support.max' (degreesXFinset'_nonempty f hf)


/--
Julian's deg def
-/
def degreeX (f : F[X][Y]) : ℕ :=
  match f.toFinsupp.support.max with
  | ⊥ => 0
  | .some n => n

/--
The `Y` degree of a bivariate polynomial.
-/
def degreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

/--
The bivariate quotient polynomial.
-/
def quotientPoly : Prop :=
  ∃ q : F[X][Y], g = q * f

/--
The quotient of two non-zero bivariate polynomials is non-zero.
-/
lemma quotientPoly_nezero (q : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) (h_quot_XY : g = q * f)
  : q ≠ 0 := by sorry

/--
The `X` degree of the bivarate quotient is bounded above by the difference of the `X`-degrees of
the divisor and divident.
-/
lemma quotientPoly_degX (q : F[X][Y]) (h_quot_XY : g = q * f) :
  degreeX q ≤ degreeX g - degreeX f
  := by sorry

/--
The `Y` degree of the bivarate quotient is bounded above by the difference of the `Y`-degrees of
the divisor and divident.
-/
lemma quotientPoly_degY (q : F[X][Y]) (h_quot_XY : g = q * f)
  : degreeY q  ≤ degreeY g - degreeY f  := by sorry


/--
The quotient univariate polynomial in `Y` obtained after evaluating bivariate polynomials
`f` and `g` in `X` at a point and dividing in the ring `F[Y]`.
-/
def univQuotientY (a : F) : Prop :=
  ∃ p : Polynomial F, evalAtX a g = p * (evalAtX a f)

/--
Degree bound of the `X`-univariate quotient polynomial (Julian's degree def).
-/
lemma univQuotientY_deg (p : F[X]) :
  evalAtX a g = p * (evalAtX a f) →
    p.natDegree ≤ degreeX g - degreeX f := by
    sorry

/--
Degree bound of the `X`-univariate quotient polynomial.
-/
lemma univQuotientY_deg' (p : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) :
  evalAtX a g = p * (evalAtX a f) →
    p.natDegree ≤ degreeX' g hg - degreeX' f hf := by
    intro h
    sorry
/--
Tighter bound of the `Y`-univariate quotient polynomial.
-/
def univQuotientY_deg_bd (hmn : m ≥ n) : Prop :=
  ∃ p, p.natDegree ≤ m - n ∧ evalAtX a g = p * (evalAtX a f)

/--
Univariate quotients in `Y` obtained after evaluating on a set of points.
-/
def setUnivQuotientY (hmn : m ≥ n) : Prop :=
  ∀ θ ∈ P, univQuotientY_deg_bd m n θ f g hmn

/--
The quotient univariate polynomial in `X` obtained after evaluating bivariate polynomials
`f` and `g` in `Y` at a point and dividing in the ring `F[X]`.
-/
def univQuotientX : Prop :=
  ∃ p : Polynomial F, evalAtY a g = p * (evalAtY a f)


def univQuotientX_deg_bd (hmn : m ≥ n) : Prop :=
  ∃ p : Polynomial F, p.natDegree ≤ m - n ∧ evalAtY a g = p * (evalAtY a f)

/--
Degree bound of the univariate quotient polynomial.
-/
lemma univQuotientX_deg (p : F[X]) :
  evalAtY a g = p * (evalAtY a f) →
    p.natDegree ≤ degreeY g - degreeY f := by
    sorry

/--
Univariate quotients in `X` obtained after evaluating on a set of points.
-/
def setUnivQuotientX (hmn : m ≥ n) : Prop :=
  ∀ θ ∈ P, univQuotientX_deg_bd m n θ f g hmn

end
end Bivariate
