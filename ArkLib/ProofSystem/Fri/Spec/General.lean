import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.ProtocolSpec
import ArkLib.ProofSystem.Fri.Spec.SingleRound
import ArkLib.ProofSystem.Fri.Domain

namespace Fri

open OracleSpec OracleComp ProtocolSpec Domain

namespace Spec

variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicC D] [DSmooth : Smooth2 n D]
variable {k : ℕ} (k_le_n : k ≤ n) (i : Fin k)
variable (l : ℕ)

@[reducible]
def pSpecFold : ProtocolSpec (2*k) := by
  convert ProtocolSpec.seqCompose (fun (i : Fin k) => FoldPhase.pSpec D i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

@[reducible]
def pSpec : ProtocolSpec (2*k + 1) :=
  ProtocolSpec.append (pSpecFold (k := k) D) (QueryRound.pSpec D)


-- #check Reduction.seqCompose (oSpec := oSpec D) (Stmt := Statement F) (FoldPhase.foldOracleReduction (k := k) D)

-- @[reducible]
-- def reductionFold : Reduction (oSpec D)
--     (Statement F (0 : Fin (k + 1)) × ∀ r, OracleStatement D (0 : Fin (k + 1)) r) (Witness F)
--     (Statement F (.last k) × ∀ r, OracleStatement D (.last k) r) (Witness F)
--     (pSpecFold (k := k) D) := by
--       have bla := Reduction.seqCompose (oSpec := oSpec D)
--       sorry

-- @[reducible]
-- def reduction : Reduction (oSpec D)
--     (Statement F (0 : Fin (k + 1)) × ∀ r, OracleStatement D (0 : Fin (k + 1)) r) (Witness F)
--     (Statement F (.last k) × ∀ r, OracleStatement D (.last k) r) (Witness F)
--     (pSpec (k := k) D) := sorry
  -- Reduction.seqCompose (oSpec := oSpec)
  --   (Stmt := fun i => Statement R n i × (∀ j, OracleStatement R n deg j))
  --   (Wit := fun _ => Unit)
  --   (pSpec := fun _ => SingleRound.pSpec R deg)
  --   (SingleRound.reduction R n deg D oSpec)


end Spec

end Fri
