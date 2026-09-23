/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dom Henderson
-/
module

public import ArkLib.ProofSystem.Fri.Spec.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Spec.General

namespace Whir

namespace Spec

end Spec


namespace FoldPhase


section ProtocolSpec

namespace pSpec

-- Composing single rounds because the composition in
-- general specifies num variables = num rounds
def sumCheck
    (F : Type) [Field F] [DecidableEq F]
    (degree : ℕ)
    (num_sumcheck_rounds : ℕ)
:=
    ProtocolSpec.seqCompose (fun (_ : Fin num_sumcheck_rounds) =>
        Sumcheck.Spec.SingleRound.pSpec
            (R := F)
            (deg := degree)
    )

def sendFoldedFunction
    {F : Type} [Field F] [DecidableEq F]
    {n : ℕ}
    (domain : Domain.SmoothCosetFftDomain n F)
: ProtocolSpec 1 :=
    ⟨
        !v[.P_to_V],
        !v[(domain.subdomain 1).toFinset → F]
    ⟩

def outOfDomainSample (F : Type)
: ProtocolSpec 1 :=
    ⟨
        !v[.V_to_P],
        !v[F]
    ⟩

def outOfDomainAnswer (F : Type)
: ProtocolSpec 1 :=
    ⟨
        !v[.P_to_V],
        !v[F]
    ⟩

def shiftQueriesAndCombinationRandomness
    {F : Type} [Field F] [DecidableEq F]
    (num_sumcheck_rounds : ℕ)
    (num_queries : ℕ) --t
    {n}
    (domain : Domain.SmoothCosetFftDomain n F) -- L
: ProtocolSpec 1 :=
    let Zs := (Fin num_queries → (domain.subdomain num_sumcheck_rounds).toFinset)
⟨
    !v[.V_to_P],
    !v[Zs × F]
⟩

end pSpec

open pSpec in
def pspec
    (F : Type) [Field F] [DecidableEq F]
    (degree : ℕ)
    (num_sumcheck_rounds : ℕ)
    (num_queries : ℕ)
    {n : ℕ}
    (domain : Domain.SmoothCosetFftDomain n F)
: ProtocolSpec (2*num_sumcheck_rounds + 4) := cast (by {
    simp [Fin.vsum_eq_univ_sum]
    congr 1
    grind
}) (
    (sumCheck F degree num_sumcheck_rounds) ++ₚ
    (sendFoldedFunction domain) ++ₚ
    (outOfDomainSample F) ++ₚ
    (outOfDomainAnswer F) ++ₚ
    (shiftQueriesAndCombinationRandomness num_sumcheck_rounds num_queries domain)
)

end ProtocolSpec



end FoldPhase

end Whir
