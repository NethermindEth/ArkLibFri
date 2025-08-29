import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.ProofSystem.Fri.Spec.SingleRound
import ArkLib.ProofSystem.Fri.Domain

namespace Fri

open OracleSpec OracleComp ProtocolSpec Domain

namespace Spec

variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicC D] [DSmooth : Smooth2 n D]
variable (x : Fˣ)
variable (k : ℕ) (k_le_n : k ≤ n) (i : Fin k)
variable (l : ℕ)

@[reducible]
def pSpecFold : ProtocolSpec (Fin.vsum fun (_ : Fin k) ↦ 2) :=
  ProtocolSpec.seqCompose (fun (i : Fin k) => FoldPhase.pSpec D x i)

instance : ∀ j, OracleInterface ((pSpecFold D x k).Message j) :=
  instOracleInterfaceMessageSeqCompose

@[reducible]
noncomputable def reductionFold :
  OracleReduction (oSpec D x)
    (Statement F (0 : Fin (k + 1))) (OracleStatement D x (0 : Fin (k + 1))) (Witness F)
    (Statement F (.last k)) (OracleStatement D x (.last k)) (Witness F)
    (pSpecFold (k := k) D x) :=
      OracleReduction.seqCompose _ _ (fun (_ : Fin (k + 1)) => Witness F)
        (FoldPhase.foldOracleReduction D x)

@[reducible]
def pSpec : ProtocolSpec ((Fin.vsum fun (_ : Fin k) ↦ 2) + 1) :=
  ProtocolSpec.append (pSpecFold D x k) (QueryRound.pSpec D)

@[reducible]
noncomputable def reduction [DecidableEq F] :=
  OracleReduction.append (reductionFold D x k)
  (QueryRound.queryOracleReduction (k := k) D x k_le_n l)

end Spec

end Fri
