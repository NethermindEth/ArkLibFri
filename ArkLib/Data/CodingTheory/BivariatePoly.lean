/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Bivariate
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

-- def coeffsOfBivPolynomial (f : F[X][Y]) : Fin f.natDegree → F[X] :=
-- fun ⟨y, _⟩ ↦ Polynomial.coeff f y

/---
The `X` polynomial which is a coeff of `Y^n`.
-/
def coeff_Y_n (f : F[X][Y]) : F[X] :=
  f.coeff n

def coeffs (f : F[X][Y]) : Finset F[X] :=
  f.support.image (fun n => f.coeff n)

--Katy new def of degree X
--Katy TO DO: change sup to max' after I write a proof for f.toFinsupp.support.Nonempty
def degreeX'' (f : F[X][Y]) : ℕ :=
  f.toFinsupp.support.sup (fun n => (f.coeff n).natDegree)

lemma degreeX_prod (f g : F[X][Y]) : degreeX'' (f * g) = degreeX'' f + degreeX'' g := by
  unfold degreeX''
  simp only [toFinsupp_mul]
  rw [@mul_eq_sum_sum]
  sorry



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


-- /--
-- Julian's deg def
-- -/
-- def degreeX (f : F[X][Y]) : ℕ :=
--   match f.toFinsupp.support.max with
--   | ⊥ => 0
--   | .some n => n

/--
The `Y` degree of a bivariate polynomial.
-/
def degreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

def leadingCoeffY (f : F[X][Y]) : F[X] := f.coeff (natDegree f)

-- def leadingCoeffY (f : F[X][Y]) : F := leadingCoeff (f.coeff (natDegree f))


lemma degreeY_prod (f g : F[X][Y]) (hf : leadingCoeffY f ≠ 0) (hg : leadingCoeffY g ≠ 0)
  : degreeY (f * g) = degreeY f + degreeY g := by
  unfold degreeY
  sorry

#check Polynomial.monomial

def monomial_y (n : ℕ) : F[X] →ₗ[F[X]] F[X][Y] where
  toFun t := ⟨Finsupp.single n t⟩
  map_add' x y := by rw [Finsupp.single_add]; aesop
  map_smul' r x := by simp; rw[smul_monomial]; aesop


def monomial_xy (n m : ℕ) : F →ₗ[F] F[X][Y] where
  toFun t := ⟨Finsupp.single m ⟨(Finsupp.single n t)⟩⟩
  map_add' x y := by sorry
   --simp only [Finsupp.single_add, ofFinsupp_single]; rw[← monomial ]
  map_smul' x y := by simp; rw[smul_monomial]; sorry

theorem monomial_xy_add (n m : ℕ) (r s : F) :
  monomial_xy n m (r + s) = monomial_xy n m r + monomial_xy n m s :=
  (monomial_xy n m).map_add _ _

theorem monomial_xy_mul_monomial_xy (n m p q : ℕ) (r s : F) :
    monomial_xy n m r * monomial_xy p q s = monomial_xy (n + p) (m + q) (r * s) :=
  toFinsupp_injective <| by
  unfold monomial_xy
  rw [@toFinsupp_mul, @AddMonoidAlgebra.mul_def]
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, toFinsupp_monomial, mul_zero,
    Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]
  rw [@monomial_mul_monomial]


@[simp]
theorem monomial_pow (n m k: ℕ) (r : F) :
  monomial_xy n m r ^ k = monomial_xy (n * k) (m * k) (r ^ k) := by
  unfold monomial_xy
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.monomial_pow]


theorem smul_monomial_xy {S} [SMulZeroClass S F] (a : S) (n m : ℕ) (b : F) :
    a • monomial_xy n m b = monomial_xy n m (a • b) := by
    rw [monomial_xy]
    simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk]
    rw [@Polynomial.smul_monomial, @Polynomial.smul_monomial]


@[simp]
theorem monomial_xy_eq_zero_iff (t : F) (n m : ℕ) : monomial_xy n m t = 0 ↔ t = 0 := by
  rw [monomial_xy]
  simp

theorem monomial_xy_eq_monomial_xy_iff {m n p q : ℕ} {a b : F} :
    monomial_xy n m a = monomial_xy p q b ↔ n = p ∧ m = q ∧ a = b ∨ a = 0 ∧ b = 0 := by
    unfold monomial_xy
    simp
    rw [@monomial_eq_monomial_iff, @monomial_eq_monomial_iff]
    aesop

def totalDegree (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => m + (f.coeff m).natDegree)

lemma monomial_xy_degree (n m : ℕ) (a : F) (ha : a ≠ 0) :
  totalDegree (monomial_xy n m a) = n + m := by
  sorry

theorem totalDegree_prod (f g : F[X][Y]) : totalDegree (f * g) = totalDegree f + totalDegree g := by
  unfold totalDegree
  rw [@mul_eq_sum_sum]
  sorry

def evalAtX (a : F) (f : F[X][Y]) : Polynomial F :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩

-- Katy : Don't want the lemma below anymore. Any objections?
-- lemma evalAtX_deg_le_degY (a : F) (f : F[X][Y]) :
--   (evalAtX a f).natDegree ≤ f.natDegree := by
--   sorry

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


/--
The bivariate quotient polynomial.
-/
def quotientPoly : Prop :=
  ∃ q : F[X][Y], g = q * f

/--
The quotient of two non-zero bivariate polynomials is non-zero.
-/
lemma quotientPoly_nezero (q : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) (h_quot_XY : g = q * f)
  : q ≠ 0 := by
  rw [← @nonempty_support_iff]
  simp only [support_nonempty, ne_eq]
  intro hq
  rw [hq, zero_mul] at h_quot_XY
  tauto

lemma nezero_iff_coeffs_nezero : f ≠ 0 ↔ f.coeff ≠ 0 := by
  apply Iff.intro
  ·
    intro hf
    have f_finsupp : f.toFinsupp ≠ 0 := by aesop
    rw[coeff]
    simp only [ne_eq, Finsupp.coe_eq_zero]
    exact f_finsupp
  ·
    intro f_coeffs
    rw[coeff] at f_coeffs
    aesop


lemma quotientPoly_nezero_iff_coeffs_nezero (q : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0)
  (h_quot_XY : g = q * f) : q.coeff ≠ 0 := by
  apply (nezero_iff_coeffs_nezero q).1
  exact quotientPoly_nezero f g q hf hg h_quot_XY


/--
The `X` degree of the bivarate quotient is bounded above by the difference of the `X`-degrees of
the divisor and divident.
-/
lemma quotientPoly_degX (q : F[X][Y]) (h_quot_XY : g = q * f) :
  degreeX'' q ≤ degreeX'' g - degreeX'' f := by
  rw [h_quot_XY, degreeX_prod q f]
  aesop

/--
The `Y` degree of the bivarate quotient is bounded above by the difference of the `Y`-degrees of
the divisor and divident.
-/
lemma quotientPoly_degY (q : F[X][Y]) (h_quot_XY : g = q * f) (hf : leadingCoeffY f ≠ 0)
 (hg : leadingCoeffY g ≠ 0) : degreeY q  ≤ degreeY g - degreeY f  := by
  rw[h_quot_XY, degreeY_prod q f]
  aesop
  rw[h_quot_XY] at hg
  ·
      have q_coeffs : q.coeff ≠ 0 := by rw [quotientPoly_nezero_iff_coeffs_nezero f g q hf hg h_quot_XY]
      have q_deg : q.natDegree ≠ 0 := sorry
      unfold leadingCoeffY
      aesop

  · exact hf



 --- Katy TODO: continue refining the lemmas below



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








---František's lemmas in the bivariate case

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




end
end Bivariate
