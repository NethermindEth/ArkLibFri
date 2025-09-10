import Init.Data.Nat.Dvd
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Lagrange

open Polynomial

variable {𝔽 : Type} [CommSemiring 𝔽]

def split (f : 𝔽[X]) (n : ℕ) [inst : NeZero n] : Fin n → 𝔽[X] :=
  fun i =>
    let sup :=
      Finset.filterMap (fun x => if x % n = i.1 then .some (x / n) else .none)
      f.support
      (
        by
          intros a a' b
          simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq, and_imp]
          intros h g h' g'
          rw [Eq.symm (Nat.div_add_mod' a n), Eq.symm (Nat.div_add_mod' a' n)]
          rw [h, g, h', g']
      )
    Polynomial.ofFinsupp
      ⟨
        sup,
        fun e => f.coeff (e * n + i.1),
        by
          intros a
          dsimp [sup]
          simp only [Finset.mem_filterMap, mem_support_iff, ne_eq, Option.ite_none_right_eq_some,
            Option.some.injEq]
          apply Iff.intro
          · rintro ⟨a', g⟩
            have : a' = a * n + i.1 := by
              rw [Eq.symm (Nat.div_add_mod' a' n)]
              rw [g.2.1, g.2.2]
            rw [this.symm]
            exact g.1
          · intros h
            exists (a * n + i.1)
            apply And.intro h
            rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.2]
            apply And.intro rfl
            have {a b : ℕ} : (a * n + b) / n = a + (b / n) := by
              have := inst.out
              have ne_zero : 0 < n := by omega
              rw [Nat.add_div ne_zero, Nat.mul_mod_left, zero_add, Nat.mul_div_cancel a ne_zero]
              have : ¬ (n ≤ b % n) := by
                simp only [not_le]
                exact Nat.mod_lt b ne_zero
              simp [this]
            simp [this]
      ⟩

lemma split_def (n : ℕ) (f : 𝔽[X]) [inst : NeZero n] :
    f =
      ∑ i : Fin n,
        (Polynomial.X ^ i.1) *
          Polynomial.eval₂ Polynomial.C (Polynomial.X ^ n) (split f n i) := by
  ext e
  rw [Polynomial.finset_sum_coeff]
  have h₀ {b e : ℕ} {f : 𝔽[X]} : (X ^ b * f).coeff e = if e < b then 0 else f.coeff (e - b) := by
    rw [Polynomial.coeff_X_pow_mul' f b e]
    aesop
  have h₁ {e : ℕ} {f : 𝔽[X]}  :
    (eval₂ C (X ^ n) f).coeff e =
      if e % n = 0
      then f.coeff (e / n)
      else 0 := by
    rw [Polynomial.eval₂_def, Polynomial.coeff_sum, Polynomial.sum_def]
    conv =>
      lhs
      congr
      · skip
      ext n
      rw [←pow_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases h : e % n = 0 <;> simp [h]
    · rw [Finset.sum_eq_single (e / n)]
      · have : e = n * (e / n) :=
          Nat.eq_mul_of_div_eq_right
            (Nat.dvd_of_mod_eq_zero h) rfl
        rw [if_pos]
        exact this
      · intros b h₀ h₁
        have : ¬ (e = n * b) := by
          intros h'
          apply h₁
          rw [h']
          exact Nat.eq_div_of_mul_eq_right inst.out rfl
        simp [this]
      · intros h'
        split_ifs with h''
        · exact notMem_support_iff.mp h'
        · rfl
    · have {α : Type} {a b : α} : ∀ m, (if e = n * m then a else b) = b := by aesop
      conv =>
        lhs
        congr
        · skip
        ext m
        rw [this m]
      rw [Finset.sum_const_zero]
  conv =>
    rhs
    congr
    · skip
    · ext b
      rw [h₀, h₁]
  unfold split
  simp
  rw [Finset.sum_eq_single ⟨e % n, by refine Nat.mod_lt e (by have := inst.out; omega)⟩]
  · simp only
    have h₁ : ¬ (e < e % n) := by
      by_cases h : e < n
      · rw [Nat.mod_eq_of_lt h]
        simp
      · simp at h ⊢
        exact Nat.mod_le e n
    have h₂ : (e - e % n) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by simp)
    simp only [h₁, h₂, Eq.symm Nat.div_eq_sub_mod_div, Nat.div_add_mod' e n, ↓reduceIte]
  · rintro ⟨b, h⟩ _
    simp only [ne_eq, Fin.mk.injEq, ite_eq_left_iff, not_lt, ite_eq_right_iff]
    intros h₀ h₁ h₂
    exfalso
    apply h₀
    have : e % n = b % n := by
      have h₁' := h₁
      rw [←Nat.div_add_mod' e n, ←Nat.div_add_mod' b n] at h₁ h₂
      by_cases h' : e % n ≥ b % n
      · have : e / n * n + e % n - (b / n * n + b % n) =
                ((e / n - b / n) * n) + (e % n - b % n) := by
          have : e / n * n + e % n - (b / n * n + b % n) =
                  e / n * n + e % n - b / n * n - b % n := by
            omega
          rw [this]
          have : e / n * n + e % n - b / n * n = ((e / n) - (b / n)) * n + e % n := by
            have : e / n * n + e % n - b / n * n = (e / n * n - b / n * n) + e % n :=
              Nat.sub_add_comm (Nat.mul_le_mul (Nat.div_le_div_right h₁') (by rfl))
            rw [this, ←Nat.sub_mul]
          rw [this]
          exact Nat.add_sub_assoc h' ((e / n - b / n) * n)
        rw [
          this, Nat.mul_add_mod_self_right,
          Nat.mod_eq_of_lt (Nat.sub_lt_of_lt (Nat.mod_lt _ (by linarith)))
        ] at h₂
        omega
      · simp only [ge_iff_le, not_le] at h'
        have : e / n * n + e % n - (b / n * n + b % n) =
                ((e / n - b / n - 1) * n) + (n - (b % n - e % n)) := by
          have : e / n * n + e % n - (b / n * n + b % n) =
                  e / n * n + e % n - b / n * n - b % n := by
            omega
          rw [this]
          have : e / n * n + e % n - b / n * n = ((e / n) - (b / n)) * n + e % n := by
            have : e / n * n + e % n - b / n * n = (e / n * n - b / n * n) + e % n :=
              Nat.sub_add_comm (Nat.mul_le_mul (Nat.div_le_div_right h₁') (by rfl))
            rw [this, ←Nat.sub_mul]
          rw [this]
          have : e / n - b / n = (e / n - b / n - 1) + 1 := by
            refine Eq.symm (Nat.sub_add_cancel ?_)
            rw [Nat.one_le_iff_ne_zero]
            intros h
            have h := Nat.le_of_sub_eq_zero h
            nlinarith
          rw (occs := .pos [1]) [this]
          rw
            [
              right_distrib, one_mul, add_assoc,
              Nat.add_sub_assoc (Nat.le_add_right_of_le (Nat.le_of_lt (Nat.mod_lt_of_lt h)))
            ]
          congr 1
          grind
        rw [this, Nat.mul_add_mod_self_right] at h₂

        have {a : ℕ} : (n - a) % n = 0 ∧ a < n → a = 0 := by
          intros h
          rcases exists_eq_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero h.1) with ⟨c, h'⟩
          have : a = (1 - c)*n := by
            have : n = a + c * n := by omega
            have : n - c * n = a := by omega
            rw [←this]
            have : n = 1 * n := by rw [one_mul]
            rewrite (occs := .pos [1]) [this]
            exact Eq.symm (Nat.sub_mul 1 c n)
          have h' := this ▸ h.2
          rw [this]
          have : 1 - c = 0 := by
            have : n = 1 * n := by rw [one_mul]
            rw (occs := .pos [2]) [this] at h'
            have h' := Nat.lt_of_mul_lt_mul_right h'
            linarith
          simp [this]
        exfalso
        have h₂ := this ⟨h₂, by apply Nat.sub_lt_of_lt; apply Nat.mod_lt; linarith⟩
        omega
    rw [this]
    exact Eq.symm (Nat.mod_eq_of_lt h)
  · intros h
    simp at h

noncomputable def foldα (n : ℕ) (f : 𝔽[X]) (α : 𝔽) [inst : NeZero n] : 𝔽[X] :=
  ∑ i : Fin n, Polynomial.C α ^ i.1 * split f n i

noncomputable def consistency_check [Field 𝔽] [DecidableEq 𝔽]
    (γ : 𝔽) (pts : List (𝔽 × 𝔽)) (β : 𝔽) : Bool :=
  let p := Lagrange.interpolate Finset.univ (fun i => (pts.get i).1) (fun i => (pts.get i).2)
  p.eval γ == β

lemma poly_eq_of {p q : 𝔽[X]} {n : ℕ}
      (hp : p.degree < .some n) (hq : q.degree < .some n) (s : Finset 𝔽) :
    s.card ≥ n → (∀ x ∈ s, p.eval x = q.eval x) → p = q := by
  intros h h'
  
  sorry

lemma consistency_check_comp {𝔽 : Type} [inst1 : Field 𝔽] [DecidableEq 𝔽] {f : Polynomial 𝔽}
  {n : ℕ} [inst : NeZero n]
  {γ : 𝔽}
  {s₀ : 𝔽}
  {ω : Fin n ↪ 𝔽}
  (h : ∀ i, (ω i) ^ n = 1)
  (h₁ : s₀ ≠ 0)
  :
    consistency_check
      γ
      (List.map (fun i => (ω i * s₀, f.eval (ω i * s₀))) (List.finRange n))
      ((foldα n f γ).eval (s₀^n)) = true := by
  unfold consistency_check
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
    beq_iff_eq]
  unfold foldα
  conv =>
    left
    rw [split_def n f]
  rw [Polynomial.eval_finset_sum]
  simp only [eval_mul, eval_C, eval_pow]
  have eval_eval₂_pow_eq_eval_pow {s : 𝔽} (i) :
      eval s (eval₂ C (X ^ n) (split f n i)) = (split f n i).eval (s ^ n) := by
    unfold Polynomial.eval
    rw [eval₂_eq_sum, eval₂_eq_sum, eval₂_eq_sum]
    simp only [RingHom.id_apply]
    sorry
  conv =>
    left
    congr
    · skip
    rhs
    ext i
    rw [Polynomial.eval_finset_sum]
    congr
    · skip
    ext j
    rw [eval_mul, eval_pow, eval_X, eval_eval₂_pow_eq_eval_pow]
    rhs
    rw [mul_pow, h, one_mul]
  generalize heq : @Lagrange.interpolate 𝔽 inst1 (Fin _) _ _ _ _ = p'
  have :
    p' = ∑ j, Polynomial.X ^ j.1 * Polynomial.C (eval (s₀ ^ n) (split f n j)) := by
    have p'_deg : p'.degree < .some n := by
      rw [←heq]
      sorry
    have h₂ : (∑ (j : Fin n), X ^ j.1 * C (eval (s₀ ^ n) (split f n j))).degree < .some n := by
      sorry
    let fmul : 𝔽 ↪ 𝔽 := ⟨fun x => x * s₀, by intros _; aesop⟩
    apply poly_eq_of p'_deg h₂ (Finset.map (Function.Embedding.trans ω fmul) Finset.univ) (by simp)
    intros x h'
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at h'
    rcases h' with ⟨a, h'⟩
    simp only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, fmul] at h'
    rw [←h', ←heq]
    simp only [Lagrange.interpolate_apply, map_sum, map_mul, map_pow, X_pow_mul_C]
    rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    conv =>
      lhs
      congr
      · skip
      ext x
      rw [Polynomial.eval_finset_sum]
      lhs
      congr
      · skip
      ext i
      rw [eval_mul, eval_C, eval_pow, eval_mul, eval_C, eval_C]
    have bla :=
      @Finset.sum_eq_single (Fin n) 𝔽 _ Finset.univ
        (fun x => (∑ i, (ω x * s₀) ^ i.1 * eval (s₀ ^ n) (split f n i)) *
      eval (ω a * s₀) (Lagrange.basis Finset.univ (fun (i : Fin n) ↦ ω i * s₀) x)) a
    have blu := @Lagrange.eval_basis_self 𝔽 _ (Fin n) _ Finset.univ (fun i ↦ ω i * s₀) a sorry (Finset.mem_univ a)
    simp only at blu
    rw [blu, mul_one] at bla
    have bla := bla sorry sorry
    conv at bla =>
      rhs
      congr
      · skip
      ext i
      rw [mul_comm]
    rw [←bla]
    have pog :
      (List.map (fun i ↦ (ω i * s₀, eval (ω i * s₀) (∑ i : Fin n, X ^ i.1 * eval₂ C (X ^ n) (split f n i))))
      (List.finRange n)).length = n := by simp
    rw [Finset.sum_fin_eq_sum_range]; conv_rhs => rw [Finset.sum_fin_eq_sum_range]
    congr
    simp
    ext i
    congr
    ext j
    congr 2
    congr 1
    simp
    swap
    congr 1
    simp
    congr 1
    swap
    exact (Fin.heq_fun_iff pog).mpr (congrFun rfl)
    swap
    exact (Fin.heq_ext_iff pog).mpr rfl
    rw [pog]
  rw [this, Polynomial.eval_finset_sum]
  conv =>
    lhs
    congr
    · skip
    ext i
    rw [eval_mul, eval_pow, eval_X, eval_C]
