import VCVio.OracleComp.OracleSpec
import ArkLib.ProofSystem.Fri.Domain

namespace Fri

open OracleSpec Domain

def oSpec {F : Type} [NonBinaryField F] (gen : Fˣ) (n : ℕ) : OracleSpec (Fin n) :=
  fun i ↦ (Unit, evalDomain gen i.castSucc)

end Fri
