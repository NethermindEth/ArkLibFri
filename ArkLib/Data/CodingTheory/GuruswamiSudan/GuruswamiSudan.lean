/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.Basic

variable {F : Type} [Field F]


open Polynomial

def coeff (p : Polynomial (Polynomial F)) (i j : ℕ) : F := 
  (p.coeff j).coeff i

variable [DecidableEq F]


/- This should be true -/
/- lemma rootMultiplicity₀_some_implies_root {p : Polynomial (Polynomial F)} {x y : F}   -/
/-   (h0 : 0 < p.degree) -/
/-   (h : some 0 < (rootMultiplicity₀ p)) -/
/-   : -/
/-   (p.eval 0).eval 0 = 0 -/
/-   := by -/
/-   sorry -/
  
variable {n : ℕ}

structure GuruswamiSudanCondition (k r D : ℕ) (ωs f : Fin n → F) (Q : Polynomial (Polynomial F)) where 
   Q_deg : weightedDegree Q 1 (k-1) ≤ D 
   Q_roots : ∀ i, (Q.eval (C <| f i)).eval (ωs i) = 0
   Q_multiplicity : ∀ i, r = _root_.rootMultiplicity Q (ωs i) (f i)

opaque decoder (k r D e : ℕ) (ωs f : Fin n → F) : List F[X] := sorry

theorem decoder_mem {k r D e : ℕ} {ωs f : Fin n → F} {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f)
  (h_e : e ≤ n - Real.sqrt (k * n))
  :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by sorry

theorem decoder_empty {k r D e : ℕ} {ωs f : Fin n → F} {p : F[X]}
  (h_nil : decoder k r D e ωs f = [])
  (h_e : e ≤ n - Real.sqrt (k * n))
  :
  ¬∃ (p : F[X]), Δ₀(f, p.eval ∘ ωs) ≤ e := by sorry
