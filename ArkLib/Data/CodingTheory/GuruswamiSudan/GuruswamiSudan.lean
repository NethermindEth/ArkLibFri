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

def weightedDegree (p : Polynomial (Polynomial F)) (u v : ℕ) : Option ℕ := 
  List.max? (List.map (fun n => u * (p.coeff n).natDegree + v * n) (List.range p.natDegree.succ))

open Polynomial
example : weightedDegree (let X := (Polynomial.X : Polynomial F)
  let Y := (Polynomial.X : Polynomial (Polynomial F))
  (C X) * Y + (C (X^2) * Y)) 1 2 = some 4 := by
  unfold weightedDegree
  have h : ((C X * X + C (X ^ 2) * X) : Polynomial (Polynomial F)).natDegree = 1 := by
    rw [←add_mul]
    rw [Polynomial.natDegree_mul (by {
      intro contr 
      rw [←Polynomial.C_add] at contr
      rw [Polynomial.C_eq_zero] at contr 
      rw [pow_two] at contr 
      rw [add_eq_zero_iff_eq_neg] at contr
      have h: (X : Polynomial F).coeff 1 = 0 := by 
        rw [contr]
        simp
      simp at h
    }) (by aesop)]
    simp
  rw [h, List.range_succ]
  simp
  rw [←Polynomial.C_pow, Polynomial.coeff_C]
  simp
  rw [pow_two] 
  have h : (X : F[X]) + X * X = X * (1 + X) := by ring
  rw [h]
  rw [Polynomial.natDegree_mul,]
  rw [add_comm (b := X), ←Polynomial.C_1]
  rw [Polynomial.natDegree_X_add_C]
  simp
  simp
  intro contr 
  rw [add_eq_zero_iff_eq_neg] at contr
  have h : ((- (X : F[X])).coeff 0) = 1 := by 
    rw [←contr]
    simp
  simp at h

def coeff (p : Polynomial (Polynomial F)) (i j : ℕ) : F := 
  (p.coeff j).coeff i

variable [DecidableEq F]

def rootMultiplicity₀ (p : Polynomial (Polynomial F)) : Option ℕ :=
  let deg := weightedDegree p 1 1
  match deg with
  | none => none 
  | some deg => List.max? 
    (List.map 
      (fun x => if _root_.coeff p x.1 x.2 ≠ 0 then x.1 + x.2 else 0) 
      (List.product (List.range deg.succ) (List.range deg.succ)))

noncomputable def rootMultiplicity (p : Polynomial (Polynomial F)) (x y : F) : Option ℕ :=
  let X := (Polynomial.X : Polynomial F)
  let Y := (Polynomial.X : Polynomial (Polynomial F))
  rootMultiplicity₀ ((p.comp (Y + (C (C y)))).map (Polynomial.compRingHom (X + C x)))

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
