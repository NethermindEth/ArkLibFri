import Mathlib.GroupTheory.SpecificGroups.Cyclic

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.ProtocolSpec
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ProofSystem.Fri.Domain

namespace Fri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Domain

namespace Spec

namespace Simple

variable {F : Type} [NonBinaryField F]
variable (gen : Fˣ)
variable {n : ℕ}

variable [Finite F]
variable (i : Fin n)
@[reducible, simp]
def StmtIn (_ : Fin n) : Type := Unit

@[reducible, simp]
def OStmtIn : Unit → Type := fun _ => evalDomain gen i.castSucc → F

def WitIn (F : Type) [Field F] (_ : Fin n) := F[X]

@[reducible, simp]
def StmtOut (_ : Fin n) : Type := Unit

@[reducible, simp]
def OStmtOut : Unit → Type := fun _ => evalDomain gen i.succ → F

def WitOut (F : Type) [Field F] (_ : Fin n) := F[X]

-- def inputRelation : Set ((StmtIn i.castSucc × OStmtIn gen i.castSucc) × WitIn F i.castSucc) :=
--     {⟨⟨_, o⟩, p⟩ | Polynomial.natDegree p < 2 ^ (n - i.val)}

-- def outputRelation : Set ((StmtOut i.castSucc × OStmtOut gen i.castSucc) × WitOut F i.castSucc) :=
--     {⟨⟨_, o⟩, p⟩ | Polynomial.natDegree p < 2 ^ (n - (i.val + 1))}

@[reducible]
def pSpec : ProtocolSpec 2 := ![(.V_to_P, F), (.P_to_V, (evalDomain gen i.succ) → F)]

def oSpec (n : ℕ) : OracleSpec (Fin n) :=
  fun i ↦ (Unit, evalDomain gen i.castSucc)

def getChallengeQ (i : Fin n) :
    OracleComp (oSpec gen n) (evalDomain gen i.castSucc) :=
  OracleComp.lift
    (OracleSpec.query (spec := oSpec gen n) i ())

noncomputable def prover :
  OracleProver
    (oSpec gen n) (StmtIn i) (OStmtIn gen i) (WitIn F i)
    (StmtOut i) (OStmtOut gen i) (WitOut F i) (pSpec gen i) where
  PrvState
    | _ => F[X]

  input := fun ⟨_, p⟩ => p

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun p => do
    pure ⟨fun x => p.eval x.1.1, p⟩

  receiveChallenge
  | ⟨0, _⟩ => fun (p : F[X]) (α : F) => by
    simpa using @foldα F _ p α
  | ⟨1, h⟩ => nomatch h

  output := fun p => ⟨⟨(), fun _ x => p.eval x.1.1⟩, p⟩

variable [gen_ord : Fact (orderOf gen = (2 ^ n))]

noncomputable def verifier [DecidableEq F] :
  Verifier (oSpec gen n)
    (StmtIn i × ∀ r, OStmtIn gen i r) (StmtOut i × ∀ r, OStmtOut gen i r)
    (pSpec gen i) where
  verify := fun ⟨_, o⟩ transcript => do
    let (s₀ : evalDomain gen i.castSucc) ← @getChallengeQ F _ gen n i;
    let α₀ := o () s₀;
    let α₁ := o () (-s₀);
    let h' := sqr_mem_D_succ_i_of_mem_D_i s₀.2;
    let β  := (transcript 1) (lift_to_subgroup h')
    guard (consistency_check (F := F) (transcript 0) s₀.1.1 (-s₀).1.1 α₀ α₁ β)
    pure ((), fun _ => transcript 1)

noncomputable def reduction [DecidableEq F] :
  Reduction (oSpec gen n)
    (StmtIn i × (∀ r, OStmtIn gen i r)) (WitIn F i)
    (StmtOut i × (∀ r, OStmtOut gen i r)) (WitOut F i)
    (pSpec gen i) where
  prover := prover gen i
  verifier := verifier gen i

end Simple

end Spec

end Fri
