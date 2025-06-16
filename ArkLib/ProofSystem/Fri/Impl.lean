/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/
import VCVio

import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ToInit.Data.List.Control

section Defs

variable (F : Type) [Field F]
variable (D : Subgroup Fˣ)
variable (r : ℕ)

def FriCommitSpec : OracleSpec Unit :=
  fun _ ↦ (Unit, F)

inductive Oracle where
  | RO
  | PO : (Fin r) → Oracle

def FriQuerySpec : OracleSpec (Oracle r) :=
  fun i ↦ match i with
  | .RO => (Unit, D)
  | .PO _ => (F, F)

end Defs

variable {F : Type} [NonBinaryField F] [DecidableEq F]
variable {D : Subgroup Fˣ}
variable {r : ℕ} [NeZero r]

def getChallenge : (OracleComp (FriCommitSpec F)) F
  := OracleComp.lift (OracleSpec.query (spec := FriCommitSpec F) () ())

noncomputable def commit (f : Polynomial F)
  : (OracleComp (FriCommitSpec F)) (List (Polynomial F)) :=
  scanlM (fun f _ => getChallenge >>= pure ∘ foldα f) f (List.range r)

def getEval (i : Fin r) (x : F)
  : (OracleComp (FriQuerySpec F D r)) F
  := OracleComp.lift
    (OracleSpec.query (spec := FriQuerySpec F D r) (Oracle.PO i) x)

def getChallengeQ  :
    (OracleComp (FriQuerySpec F D r)) D :=
  OracleComp.lift
    (OracleSpec.query (spec := FriQuerySpec F D r) Oracle.RO ())

noncomputable def query :
    OracleComp (FriQuerySpec F D r) Unit
  := do
    let challenges <- replicateM r <|
      (do
        let c <- getChallengeQ;
        return c.val.val
      )
    mapM_ (fun (i : ℕ) => do
      let x₀ := challenges.getD i 0;
      let s₀ <- getChallengeQ;
      let s₀ := (s₀.val.val ^ (2 ^ i));
      let α₀ <- getEval i s₀;
      let α₁ <- getEval i (-s₀);
      let β <- getEval i.succ (s₀ ^ 2);
      guard (consistency_check x₀ s₀ (-s₀) α₀ α₁ β)
    ) (List.range r)
