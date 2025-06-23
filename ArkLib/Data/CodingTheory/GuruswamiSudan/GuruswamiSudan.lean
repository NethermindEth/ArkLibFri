/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic

import ArkLib.Data.CodingTheory.Basic

variable {F : Type} [Field F]

def WeightedDegree (p : Polynomial (Polynomial F)) (u v : ℕ) : Option ℕ := 
  List.max? (List.map (fun n => u * (p.coeff n).natDegree + v * n) (List.range p.natDegree.succ))

open Polynomial
example : WeightedDegree (let X := (Polynomial.X : Polynomial F)
  let Y := (Polynomial.X : Polynomial (Polynomial F))
  (C X) * Y + (C (X^2) * Y)) 1 2 = some 4 := by
  unfold WeightedDegree
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
