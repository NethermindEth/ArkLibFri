/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Fri.Domain

namespace Fri
section Fri

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

end Fri
end Fri
