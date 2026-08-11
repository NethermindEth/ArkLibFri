/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Interleaved Reed–Solomon codes are list decodable (Lemma 4.4)
This file formalises the statement
> Let `k ≥ 1` and `C := RS[F, L, m]` be a Reed–Solomon code with rate `ρ`. The `k`-wise
> interleaved code `C^k` is `(1 - √ρ - η, 1/(2η√ρ))`-list decodable for every
> `η ∈ (0, 1 - √ρ)`. -/

open Polynomial
namespace InterleavedListDecoding
open ListDecodable

/-! ## Transfer of list decodability along a bijection of alphabets -/
section Transfer

variable {ι : Type*} [Fintype ι]

/-- Post-composition with a bijection `e` of the alphabets identifies the codewords close to
`e ∘ y` in the image code with the codewords close to `y` in the original code. -/
theorem image_closeCodewordsRel {A B : Type*} [DecidableEq A] [DecidableEq B] (e : A ≃ B)
  (C : Set (ι → A)) (y : ι → A) (r : ℝ) :
  (fun f : ι → A ↦ e ∘ f) '' closeCodewordsRel C y r = 
    closeCodewordsRel ((fun f : ι → A ↦ e ∘ f) '' C) (e ∘ y) r := by
  have := Code.relHammingDist_comp e.injective y
  aesop (add simp [closeCodewordsRel])

/-- List decodability transports along post-composition with a bijection of the alphabets. -/
theorem listDecodable_of_image_equiv {A B : Type*} [DecidableEq A] [DecidableEq B] (e : A ≃ B)
  (C : Set (ι → A)) {δ l : ℝ}
  (h : listDecodable ((fun f : ι → A ↦ e ∘ f) '' C) δ l) : listDecodable C δ l := fun y ↦ by
  have hinj : Function.Injective (fun f : ι → A ↦ e ∘ f) :=
    fun f g hfg ↦ funext fun i ↦ e.injective (congrFun hfg i)
  have := h (e ∘ y)
  have := Set.ncard_image_of_injective (closeCodewordsRel C y δ) hinj
  have := image_closeCodewordsRel e C y δ
  aesop 

end Transfer

/-! ## The reduction to a Reed–Solomon code over a degree-`k` extension -/
section Reduction

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {ι : Type*}

/-- The evaluation domain, viewed inside the extension field `K`. -/
def liftDomain (domain : ι ↪ F) (K : Type*) [Field K] [Algebra F K] : ι ↪ K :=
  domain.trans ⟨algebraMap F K, (algebraMap F K).injective⟩

/-- The `F`-linear bijection `φ : (Fin k → F) ≃ K` attached to a basis `b`. -/
noncomputable def basisEquiv {k : ℕ} (b : Module.Basis (Fin k) F K) : (Fin k → F) ≃ K :=
  b.equivFun.symm.toEquiv

/-- Post-composing an interleaved Reed–Solomon codeword with `φ` yields a codeword of the
Reed–Solomon code over the extension field `K`. -/
theorem image_interleaved_subset_code {k m : ℕ} (domain : ι ↪ F)
  (b : Module.Basis (Fin k) F K) :
  (fun f : ι → (Fin k → F) => (basisEquiv b) ∘ f) ''
      Code.interleavedCodeSet (κ := Fin k) (ReedSolomon.code domain m : Set (ι → F)) ⊆
      (ReedSolomon.code (liftDomain domain K) m : Set (ι → K)) := by
  rintro - ⟨f, hf, rfl⟩
  have hcoord : ∀ j : Fin k, ∃ p : F[X], p.degree < (m : ℕ) ∧ ∀ x, p.eval (domain x) = f x j :=
    fun j => ReedSolomon.mem_code_iff_eval.mp (hf j)
  choose p hpdeg hpval using hcoord
  rw [SetLike.mem_coe, ReedSolomon.mem_code_iff_eval]
  refine ⟨∑ j : Fin k, Polynomial.C (b j) * (p j).map (algebraMap F K), ?_, ?_⟩
  · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (by exact WithBot.bot_lt_coe m)).mpr ?_
    intro j _
    calc (Polynomial.C (b j) * (p j).map (algebraMap F K)).degree
        = ((b j) • (p j).map (algebraMap F K)).degree := by rw [Polynomial.smul_eq_C_mul]
      _ ≤ ((p j).map (algebraMap F K)).degree := Polynomial.degree_smul_le _ _
      _ ≤ (p j).degree := Polynomial.degree_map_le
      _ < (m : ℕ) := hpdeg j
  · intro x
    have hdom : (liftDomain domain K) x = algebraMap F K (domain x) := rfl
    rw [hdom, Polynomial.eval_finsetSum]
    have hterm : ∀ j : Fin k,
        (Polynomial.C (b j) * (p j).map (algebraMap F K)).eval (algebraMap F K (domain x))
          = f x j • b j := by
      intro j
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
        Polynomial.eval₂_at_apply, hpval j x, Algebra.smul_def]
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    simp [basisEquiv, Module.Basis.equivFun_symm_apply]

/-- The interleaved code `C^k` and the Reed–Solomon code `RS[K, domain, m]` over the
degree-`k` extension `K` are equivalent: post-composition with `φ` maps the former *onto*
the latter. -/
theorem image_interleaved_eq_code {k m : ℕ} (domain : ι ↪ F) (b : Module.Basis (Fin k) F K) :
    (fun f : ι → (Fin k → F) => (basisEquiv b) ∘ f) ''
        Code.interleavedCodeSet (κ := Fin k) (ReedSolomon.code domain m : Set (ι → F)) =
      (ReedSolomon.code (liftDomain domain K) m : Set (ι → K)) := by
  refine Set.eq_of_subset_of_subset (image_interleaved_subset_code domain b) ?_
  intro g hg
  rw [SetLike.mem_coe, ReedSolomon.mem_code_iff_eval] at hg
  obtain ⟨P, hPdeg, hPval⟩ := hg
  set p : Fin k → F[X] :=
    fun j => ∑ i ∈ Finset.range m, Polynomial.monomial i (b.repr (P.coeff i) j) with hp
  have hpdeg : ∀ j, (p j).degree < (m : ℕ) := by
    intro j
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (by exact WithBot.bot_lt_coe m)).mpr ?_
    intro i hi
    exact lt_of_le_of_lt (Polynomial.degree_monomial_le _ _)
      (by exact_mod_cast Finset.mem_range.mp hi)
  have hcoeff : ∀ j i, (p j).coeff i = if i < m then b.repr (P.coeff i) j else 0 := by
    intro j i
    simp [hp, Polynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_range]
  have hP : ∑ j : Fin k, Polynomial.C (b j) * (p j).map (algebraMap F K) = P := by
    ext i
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map, hcoeff]
    by_cases hi : i < m
    · simp only [hi, if_true]
      conv_rhs => rw [← Module.Basis.sum_repr b (P.coeff i)]
      exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def]; ring
    · have hzero : P.coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le hPdeg (by exact_mod_cast Nat.not_lt.mp hi))
      simp [hi, hzero]
  refine ⟨fun x j => (p j).eval (domain x), fun j => ?_, ?_⟩
  · exact ReedSolomon.mem_code_iff_eval.mpr ⟨p j, hpdeg j, fun _ => rfl⟩
  · funext x
    have hev : P.eval (algebraMap F K (domain x)) = ∑ j : Fin k, ((p j).eval (domain x)) • b j := by
      rw [← hP, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
        Polynomial.eval₂_at_apply, Algebra.smul_def]
      ring
    have hgx : g x = P.eval (algebraMap F K (domain x)) := (hPval x).symm
    simp [basisEquiv, Module.Basis.equivFun_symm_apply, hgx, hev]

end Reduction

/-! ## Lemma 4.4 -/

/-- **Lemma 4.4.** Let `k ≥ 1` and let `C := RS[F, domain, m]` be a Reed–Solomon code of rate
`ρ`. Then the `k`-wise interleaved code `C^k` is `(1 - √ρ - η, 1/(2η√ρ))`-list decodable for
every `η ∈ (0, 1 - √ρ)`.
The list-decoding bound for Reed–Solomon codes (Theorem 4.3), which is available neither in
`ArkLib` nor in `Mathlib`, is assumed as the hypothesis `hRS`; as in the informal proof it is
applied to the Reed–Solomon code `RS[K, domain, m]` over a degree-`k` extension `K` of `F`,
whose existence is witnessed by the basis `b`. Since the bounds of Theorem 4.3 do not depend
on the size of the field, and since `C^k` has the same rate `ρ` as `C`, the radius and the
list size are expressed throughout in terms of `√ρ = ReedSolomon.sqrtRate m domain`.
The hypotheses `hk : 1 ≤ k` and `η ∈ (0, 1 - √ρ)` are part of the statement of the lemma but
are not needed for the reduction itself (they are needed only for Theorem 4.3, i.e. they are
absorbed into `hRS`). -/
theorem interleaved_listDecodable {F K : Type*} [Field F] [Field K] [Algebra F K]
    [DecidableEq F] [DecidableEq K] {ι : Type*} [Fintype ι]
    (domain : ι ↪ F) (m k : ℕ) (b : Module.Basis (Fin k) F K) (η : ℝ)
    (hRS : listDecodable (ReedSolomon.code (liftDomain domain K) m : Set (ι → K))
      (1 - (ReedSolomon.sqrtRate m domain : ℝ) - η)
      (1 / (2 * η * (ReedSolomon.sqrtRate m domain : ℝ)))) :
    listDecodable
      (Code.interleavedCodeSet (κ := Fin k) (ReedSolomon.code domain m : Set (ι → F)))
      (1 - (ReedSolomon.sqrtRate m domain : ℝ) - η)
      (1 / (2 * η * (ReedSolomon.sqrtRate m domain : ℝ))) := by
  refine listDecodable_of_image_equiv (basisEquiv b) _ ?_
  rw [image_interleaved_eq_code domain b]
  exact hRS

end InterleavedListDecoding
