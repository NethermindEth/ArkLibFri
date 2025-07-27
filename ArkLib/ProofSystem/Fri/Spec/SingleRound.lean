import Mathlib.GroupTheory.SpecificGroups.Cyclic

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.ProtocolSpec
import ArkLib.ProofSystem.Fri.RoundConsistency


namespace Fri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

variable {F : Type} [NonBinaryField F]
variable (gen : Fˣ)
variable {n : ℕ}
variable (gen_ord : orderOf gen = 2 ^ n)

@[simp]
def evalDomain (i : Fin (n + 1)) : Subgroup Fˣ :=
  Subgroup.zpowers (gen ^ (2 ^ i.val))

@[simp]
def D (n : ℕ) : Subgroup Fˣ := evalDomain gen (0 : Fin (n + 1))

lemma D_def : D gen n = Subgroup.zpowers gen := by unfold D evalDomain; simp

instance : IsCyclic (D gen n) := by
  rw [D_def, Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  exists gen

instance {i : Fin (n + 1)} : IsCyclic (evalDomain gen i) := by
  unfold evalDomain
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  exists ((gen ^ 2 ^ i.1))

lemma pow_2_pow_i_mem_Di_of_mem_D {gen : Fˣ} :
  ∀ {x : Fˣ} (i : Fin (n + 1)),
    x ∈ (D gen n) → x ^ (2 ^ i.val) ∈ evalDomain gen i := by
  intros x i h
  simp only [D, evalDomain, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, pow_one] at h
  simp only [evalDomain]
  rw [Subgroup.mem_zpowers_iff] at h ⊢
  rcases h with ⟨k, h⟩
  exists k
  rw [←h]
  have {x : Fˣ} {n : ℕ} : x ^ n = x ^ (n : ℤ) := by rfl
  rw [this, this, ←zpow_mul, ←zpow_mul]
  ring_nf

lemma sqr_mem_D_succ_i_of_mem_D_i {gen : Fˣ} : ∀ {x : Fˣ} {i : Fin n},
  x ∈ evalDomain gen i.castSucc → x ^ 2 ∈ evalDomain gen i.succ := by
  intros x i h
  simp only [evalDomain, Fin.coe_castSucc] at h
  simp only [evalDomain, Fin.val_succ]
  rw [Subgroup.mem_zpowers_iff] at h ⊢
  rcases h with ⟨k, h⟩
  exists k
  rw [←h]
  have {x : Fˣ} {n : ℕ} : x ^ n = x ^ (n : ℤ) := by rfl
  rw [this, this, this, ←zpow_mul, ←zpow_mul, ←zpow_mul]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [@mul_comm ℤ _ k 2, ←mul_assoc]
  have : (2 : ℤ) ^ (i.val + 1) = 2 ^ i.val * 2 := by
    ring
  rw [this]

example : evalDomain gen (Fin.last n) = ⊥ := by
  unfold evalDomain
  rw [Fin.val_last, Subgroup.zpowers_eq_bot, ←gen_ord, pow_orderOf_eq_one]

namespace Spec

namespace Simple

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

def lift_to_subgroup {x : Fˣ} {H : Subgroup Fˣ} (h : x ∈ H) : H := ⟨x, h⟩

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

noncomputable def verifier [DecidableEq F] :
  Verifier (oSpec gen n)
    (StmtIn i × ∀ r, OStmtIn gen i r) (StmtOut i × ∀ r, OStmtOut gen i r)
    (pSpec gen i) where
  verify := fun ⟨_, o⟩ transcript => do
    let (s₀ : evalDomain gen i.castSucc) ← @getChallengeQ F _ gen n i;
    let α₀ := o () s₀;
    let α₁ := o () (s₀⁻¹);
    let h' := sqr_mem_D_succ_i_of_mem_D_i s₀.2;
    let β  := (transcript 1) (lift_to_subgroup h')
    guard (consistency_check (F := F) (transcript 0) s₀.1.1 (s₀⁻¹).1.1 α₀ α₁ β)
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
