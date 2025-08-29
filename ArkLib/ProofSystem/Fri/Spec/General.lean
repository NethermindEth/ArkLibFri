import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.ProofSystem.Fri.Spec.SingleRound
import ArkLib.ProofSystem.Fri.Domain

namespace Fri

open OracleSpec OracleComp ProtocolSpec Domain

namespace Spec

variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicC D] [DSmooth : Smooth2 n D]
variable (k : ℕ) (k_le_n : k ≤ n) (i : Fin k)
variable (l : ℕ)

@[reducible]
def pSpecFold : ProtocolSpec (Fin.vsum fun (_ : Fin k) ↦ 2) :=
  ProtocolSpec.seqCompose (fun (i : Fin k) => FoldPhase.pSpec D i)

instance : ∀ j, OracleInterface ((pSpecFold D k).Message j) :=
  instOracleInterfaceMessageSeqCompose

@[reducible]
noncomputable def reductionFold :
  OracleReduction (oSpec D)
    (Statement F (0 : Fin (k + 1))) (OracleStatement D (0 : Fin (k + 1))) (Witness F)
    (Statement F (.last k)) (OracleStatement D (.last k)) (Witness F)
    (pSpecFold (k := k) D) :=
      OracleReduction.seqCompose _ _ (fun (_ : Fin (k + 1)) => Witness F)
        (FoldPhase.foldOracleReduction D)

@[reducible]
def pSpec : ProtocolSpec ((Fin.vsum fun (_ : Fin k) ↦ 2) + 1) :=
  ProtocolSpec.append (pSpecFold D k) (QueryRound.pSpec D)

@[reducible]
noncomputable def reduction [DecidableEq F] :=
  OracleReduction.append (reductionFold D k)
  (QueryRound.queryOracleReduction (k := k) D k_le_n l)

end Spec

end Fri
