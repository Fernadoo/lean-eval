/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/

import Mathlib.Probability.Distributions.SetBernoulli
import Submission.Helpers
import ChallengeDeps
/-!
# Main Statement from Thresholds versus fractional expectation-thresholds

We formalise the statement of the main result from K. Frankston, J. Kahn, B. Narayanan, and J. Park,
`Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021.
-/


namespace Submission

open _root_.FractionalExpectationThresholds
set_option autoImplicit false

namespace FractionalExpectationThresholds

open ProbabilityTheory unitInterval Set

open scoped NNReal

section Definitions









end Definitions

/-- The constant `K` in Theorem 1.1. -/
noncomputable def K : ℝ := 192

/--
Statement of Theorem 1.1:

There exists a universal constant `K` such that for any finite set `X` and any increasing
collection of sets `𝓕` such that `l(𝓕)` is at least `2`,

`p_c(𝓕) ≤ K * q_f(𝓕) * log l(𝓕)`.

Note: The assumption that `l(𝓕)` is at least `2` is not explicitly in the paper but is needed
because if `l(𝓕) = 1` then `Real.log (l 𝓕) = 0`, but `p_c 𝓕 ∈ (0,1)` (so the inequality clearly
cannot hold).
-/
theorem theorem_1_1 (X : Type*) [Fintype X] (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕)
    (hl𝓕 : 2 ≤ l 𝓕) : p_c 𝓕 ≤ K * q_f 𝓕 * Real.log (l 𝓕) := by
  have L_count : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (𝓗 : Finset (Finset X)) (M t : ℕ)
      (hM : ∀ H ∈ 𝓗, H.card ≤ M) (Φ : Finset X → Finset (Finset X))
      (hΦ : ∀ W : Finset X, ∀ T ∈ Φ W, Disjoint T W ∧ (∃ H ∈ 𝓗, H ⊆ W ∪ T) ∧
        ∀ H ∈ 𝓗, H ⊆ W ∪ T → T ⊆ H)
      (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1), b ^ t * ∑ W : Finset X, b ^ W.card * (1 - b) ^ (Fintype.card X - W.card) *
          (((Φ W).filter (fun T => T.card = t)).card : ℝ) ≤
        (M.choose t : ℝ) * (1 - b) ^ t :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (𝓗 : Finset (Finset X)) (M t : ℕ)
        (hM : ∀ H ∈ 𝓗, H.card ≤ M) (Φ : Finset X → Finset (Finset X))
        (hΦ : ∀ W : Finset X, ∀ T ∈ Φ W, Disjoint T W ∧ (∃ H ∈ 𝓗, H ⊆ W ∪ T) ∧
          ∀ H ∈ 𝓗, H ⊆ W ∪ T → T ⊆ H)
        (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) => by
      have hb1' : 0 ≤ 1 - b := by linarith
      -- total mass
      have htot : ∑ Z : Finset X, b ^ Z.card * (1 - b) ^ (Fintype.card X - Z.card) = 1 := by
        have h := Finset.sum_pow_mul_eq_add_pow b (1 - b) (Finset.univ : Finset X)
        rw [Finset.powerset_univ, Finset.card_univ] at h
        rw [h, add_sub_cancel, one_pow]
      -- key identity
      have hkey : ∀ W : Finset X, ∀ T ∈ (Φ W).filter (fun T => T.card = t),
          b ^ t * (b ^ W.card * (1 - b) ^ (Fintype.card X - W.card)) =
            b ^ (W ∪ T).card * (1 - b) ^ (Fintype.card X - (W ∪ T).card) * (1 - b) ^ t := by
        intro W T hT
        rw [Finset.mem_filter] at hT
        have hcard : (W ∪ T).card = W.card + t := by
          rw [Finset.card_union_of_disjoint (hΦ W T hT.1).1.symm, hT.2]
        have hle : (W ∪ T).card ≤ Fintype.card X := Finset.card_le_univ _
        rw [hcard] at hle ⊢
        have h2 : Fintype.card X - W.card = (Fintype.card X - (W.card + t)) + t := by omega
        rw [h2, pow_add, pow_add]
        ring
      -- the fibre sets
      have hGcard : ∀ Z : Finset X, ((((Finset.univ : Finset (Finset X)).filter
          (fun T => T.card = t ∧ (∃ H ∈ 𝓗, H ⊆ Z) ∧ ∀ H ∈ 𝓗, H ⊆ Z → T ⊆ H)).card : ℕ) : ℝ) ≤
            (M.choose t : ℝ) := by
        intro Z
        by_cases h : ∃ H ∈ 𝓗, H ⊆ Z
        · obtain ⟨H₀, hH₀, hH₀Z⟩ := h
          have hsub : (Finset.univ : Finset (Finset X)).filter
              (fun T => T.card = t ∧ (∃ H ∈ 𝓗, H ⊆ Z) ∧ ∀ H ∈ 𝓗, H ⊆ Z → T ⊆ H) ⊆
                H₀.powersetCard t := by
            intro T hT
            rw [Finset.mem_filter] at hT
            rw [Finset.mem_powersetCard]
            exact ⟨hT.2.2.2 H₀ hH₀ hH₀Z, hT.2.1⟩
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_powersetCard] at h1
          have h2 := Nat.choose_le_choose t (hM H₀ hH₀)
          exact_mod_cast h1.trans h2
        · rw [Finset.filter_false_of_mem (fun T _ hT => h hT.2.1)]
          simp
      have hmain : ∑ W : Finset X, ∑ T ∈ (Φ W).filter (fun T => T.card = t),
          b ^ (W ∪ T).card * (1 - b) ^ (Fintype.card X - (W ∪ T).card) ≤ (M.choose t : ℝ) := by
        have hinj : Set.InjOn (fun x : (Σ _ : Finset X, Finset X) =>
            (⟨x.1 ∪ x.2, x.2⟩ : Σ _ : Finset X, Finset X))
            ↑((Finset.univ : Finset (Finset X)).sigma
              (fun W => (Φ W).filter (fun T => T.card = t))) := by
          rintro ⟨W₁, T₁⟩ h₁ ⟨W₂, T₂⟩ h₂ heq
          rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter] at h₁ h₂
          simp only [Sigma.mk.injEq, heq_eq_eq] at heq
          obtain ⟨hU, rfl⟩ := heq
          have hd₁ := (hΦ W₁ T₁ h₁.2.1).1
          have hd₂ := (hΦ W₂ T₁ h₂.2.1).1
          have hW : W₁ = W₂ := by
            rw [← Finset.union_sdiff_cancel_right hd₁.symm, hU,
              Finset.union_sdiff_cancel_right hd₂.symm]
          rw [hW]
        have hsub : ((Finset.univ : Finset (Finset X)).sigma
            (fun W => (Φ W).filter (fun T => T.card = t))).image
            (fun x : (Σ _ : Finset X, Finset X) => (⟨x.1 ∪ x.2, x.2⟩ : Σ _ : Finset X, Finset X)) ⊆
            (Finset.univ : Finset (Finset X)).sigma (fun Z => (Finset.univ : Finset (Finset X)).filter
              (fun T => T.card = t ∧ (∃ H ∈ 𝓗, H ⊆ Z) ∧ ∀ H ∈ 𝓗, H ⊆ Z → T ⊆ H)) := by
          intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨⟨W, T⟩, hx, rfl⟩ := hy
          rw [Finset.mem_sigma, Finset.mem_filter] at hx
          obtain ⟨_, hTΦ, hTc⟩ := hx
          obtain ⟨_, hex, hall⟩ := hΦ W T hTΦ
          rw [Finset.mem_sigma, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, Finset.mem_univ _, hTc, hex, hall⟩
        calc ∑ W : Finset X, ∑ T ∈ (Φ W).filter (fun T => T.card = t),
              b ^ (W ∪ T).card * (1 - b) ^ (Fintype.card X - (W ∪ T).card)
            = ∑ x ∈ (Finset.univ : Finset (Finset X)).sigma
                (fun W => (Φ W).filter (fun T => T.card = t)),
                b ^ (x.1 ∪ x.2).card * (1 - b) ^ (Fintype.card X - (x.1 ∪ x.2).card) :=
              Finset.sum_sigma' (Finset.univ : Finset (Finset X))
                (fun W => (Φ W).filter (fun T => T.card = t))
                (fun W T => b ^ (W ∪ T).card * (1 - b) ^ (Fintype.card X - (W ∪ T).card))
          _ = ∑ y ∈ ((Finset.univ : Finset (Finset X)).sigma
                (fun W => (Φ W).filter (fun T => T.card = t))).image
                (fun x : (Σ _ : Finset X, Finset X) => (⟨x.1 ∪ x.2, x.2⟩ : Σ _ : Finset X, Finset X)),
                b ^ y.1.card * (1 - b) ^ (Fintype.card X - y.1.card) :=
              (Finset.sum_image (f := fun y : (Σ _ : Finset X, Finset X) =>
                b ^ y.1.card * (1 - b) ^ (Fintype.card X - y.1.card)) hinj).symm
          _ ≤ ∑ y ∈ (Finset.univ : Finset (Finset X)).sigma
                (fun Z => (Finset.univ : Finset (Finset X)).filter
                  (fun T => T.card = t ∧ (∃ H ∈ 𝓗, H ⊆ Z) ∧ ∀ H ∈ 𝓗, H ⊆ Z → T ⊆ H)),
                b ^ y.1.card * (1 - b) ^ (Fintype.card X - y.1.card) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun y _ _ => mul_nonneg (pow_nonneg hb0 _) (pow_nonneg hb1' _))
          _ = ∑ Z : Finset X, ∑ T ∈ (Finset.univ : Finset (Finset X)).filter
                (fun T => T.card = t ∧ (∃ H ∈ 𝓗, H ⊆ Z) ∧ ∀ H ∈ 𝓗, H ⊆ Z → T ⊆ H),
                b ^ Z.card * (1 - b) ^ (Fintype.card X - Z.card) := Finset.sum_sigma _ _ _
          _ = ∑ Z : Finset X, b ^ Z.card * (1 - b) ^ (Fintype.card X - Z.card) *
                ((((Finset.univ : Finset (Finset X)).filter
                  (fun T => T.card = t ∧ (∃ H ∈ 𝓗, H ⊆ Z) ∧ ∀ H ∈ 𝓗, H ⊆ Z → T ⊆ H)).card : ℕ) :
                  ℝ) := by
              refine Finset.sum_congr rfl (fun Z _ => ?_)
              rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          _ ≤ ∑ Z : Finset X, b ^ Z.card * (1 - b) ^ (Fintype.card X - Z.card) * (M.choose t : ℝ) :=
              Finset.sum_le_sum (fun Z _ => mul_le_mul_of_nonneg_left (hGcard Z)
                (mul_nonneg (pow_nonneg hb0 _) (pow_nonneg hb1' _)))
          _ = (M.choose t : ℝ) := by rw [← Finset.sum_mul, htot, one_mul]
      calc b ^ t * ∑ W : Finset X, b ^ W.card * (1 - b) ^ (Fintype.card X - W.card) *
            (((Φ W).filter (fun T => T.card = t)).card : ℝ)
          = ∑ W : Finset X, ∑ T ∈ (Φ W).filter (fun T => T.card = t),
              b ^ t * (b ^ W.card * (1 - b) ^ (Fintype.card X - W.card)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun W _ => ?_)
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
        _ = ∑ W : Finset X, ∑ T ∈ (Φ W).filter (fun T => T.card = t),
              b ^ (W ∪ T).card * (1 - b) ^ (Fintype.card X - (W ∪ T).card) * (1 - b) ^ t :=
            Finset.sum_congr rfl (fun W _ => Finset.sum_congr rfl (fun T hT => hkey W T hT))
        _ = (∑ W : Finset X, ∑ T ∈ (Φ W).filter (fun T => T.card = t),
              b ^ (W ∪ T).card * (1 - b) ^ (Fintype.card X - (W ∪ T).card)) * (1 - b) ^ t := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun W _ => ?_)
            rw [Finset.sum_mul]
        _ ≤ (M.choose t : ℝ) * (1 - b) ^ t :=
            mul_le_mul_of_nonneg_right hmain (pow_nonneg hb1' _)
  have L_badcost : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (r : ℕ) (𝓗 : Finset (Finset X))
      (h𝓗 : ∀ S ∈ 𝓗, S.card < 2 ^ (r + 1)) (Φ : Finset X → Finset (Finset X))
      (hΦ : ∀ W : Finset X, ∀ T ∈ Φ W, 2 ^ r ≤ T.card ∧ Disjoint T W ∧ (∃ H ∈ 𝓗, H ⊆ W ∪ T) ∧
        ∀ H ∈ 𝓗, H ⊆ W ∪ T → T ⊆ H)
      (b q : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (hq : 0 ≤ q), ∑ W : Finset X, b ^ W.card * (1 - b) ^ (Fintype.card X - W.card) * ∑ T ∈ Φ W, q ^ T.card ≤
        ∑ t ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), (4 * q / b) ^ t :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (r : ℕ) (𝓗 : Finset (Finset X))
        (h𝓗 : ∀ S ∈ 𝓗, S.card < 2 ^ (r + 1)) (Φ : Finset X → Finset (Finset X))
        (hΦ : ∀ W : Finset X, ∀ T ∈ Φ W, 2 ^ r ≤ T.card ∧ Disjoint T W ∧ (∃ H ∈ 𝓗, H ⊆ W ∪ T) ∧
          ∀ H ∈ 𝓗, H ⊆ W ∪ T → T ⊆ H)
        (b q : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (hq : 0 ≤ q) => by
      have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ, mul_comm]
      have hM : ∀ H ∈ 𝓗, H.card ≤ 2 ^ (r + 1) - 1 := fun H hH => by
        have := h𝓗 H hH; omega
      have hΦ' : ∀ W : Finset X, ∀ T ∈ Φ W, Disjoint T W ∧ (∃ H ∈ 𝓗, H ⊆ W ∪ T) ∧
          ∀ H ∈ 𝓗, H ⊆ W ∪ T → T ⊆ H := fun W T hT => (hΦ W T hT).2
      have hmaps : ∀ W : Finset X, ∀ T ∈ Φ W, T.card ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)) := by
        intro W T hT
        obtain ⟨h1, -, ⟨H, hH, hHsub⟩, h4⟩ := hΦ W T hT
        have h5 := Finset.card_le_card (h4 H hH hHsub)
        have h6 := h𝓗 H hH
        exact Finset.mem_Ico.mpr ⟨h1, by omega⟩
      have hsplit : ∀ W : Finset X, ∑ T ∈ Φ W, q ^ T.card =
          ∑ t ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)),
            q ^ t * (((Φ W).filter (fun T => T.card = t)).card : ℝ) := by
        intro W
        rw [← Finset.sum_fiberwise_of_maps_to (hmaps W)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => q ^ t)
          (fun T hT => by rw [(Finset.mem_filter.mp hT).2]), Finset.sum_const, nsmul_eq_mul,
          mul_comm]
      have hswap : ∑ W : Finset X, b ^ W.card * (1 - b) ^ (Fintype.card X - W.card) *
            ∑ T ∈ Φ W, q ^ T.card =
          ∑ t ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), q ^ t * ∑ W : Finset X,
            b ^ W.card * (1 - b) ^ (Fintype.card X - W.card) *
              (((Φ W).filter (fun T => T.card = t)).card : ℝ) := by
        simp_rw [hsplit, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun W _ => by ring
      rw [hswap]
      refine Finset.sum_le_sum fun t ht => ?_
      have ht' := Finset.mem_Ico.mp ht
      have hc := L_count X 𝓗 (2 ^ (r + 1) - 1) t hM Φ hΦ' b hb0.le hb1
      have hchoose : ((2 ^ (r + 1) - 1).choose t : ℝ) ≤ 4 ^ t := by
        have h1 : (2 ^ (r + 1) - 1).choose t ≤ 2 ^ (2 ^ (r + 1) - 1) := Nat.choose_le_two_pow _ t
        have h2 : 2 ^ (2 ^ (r + 1) - 1) ≤ 4 ^ t := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast h1.trans h2
      have h1b : (1 - b) ^ t ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have hbt : 0 < b ^ t := pow_pos hb0 t
      set S := ∑ W : Finset X, b ^ W.card * (1 - b) ^ (Fintype.card X - W.card) *
        (((Φ W).filter (fun T => T.card = t)).card : ℝ) with hS
      have hS0 : b ^ t * S ≤ 4 ^ t := by
        calc b ^ t * S ≤ ((2 ^ (r + 1) - 1).choose t : ℝ) * (1 - b) ^ t := hc
          _ ≤ 4 ^ t * 1 :=
            mul_le_mul hchoose h1b (pow_nonneg (by linarith) t) (by positivity)
          _ = 4 ^ t := mul_one _
      rw [div_pow, mul_pow, le_div_iff₀ hbt]
      calc q ^ t * S * b ^ t = q ^ t * (b ^ t * S) := by ring
        _ ≤ q ^ t * 4 ^ t := mul_le_mul_of_nonneg_left hS0 (pow_nonneg hq t)
        _ = 4 ^ t * q ^ t := mul_comm _ _
  open ProbabilityTheory in
  have L_bridge : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (p : unitInterval) (𝓕 : Set (Set X))
      (𝓗 : Finset (Finset X)) (h𝓗 : ∀ S ∈ 𝓗, ∀ W : Finset X, S ⊆ W → (↑W : Set X) ∈ 𝓕), 1 - ∑ W : Finset X, (if ∃ S ∈ 𝓗, S ⊆ W then 0 else
          (p : ℝ) ^ W.card * (1 - (p : ℝ)) ^ (Fintype.card X - W.card)) ≤
        (setBer((Set.univ : Set X), p)).real 𝓕 :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (p : unitInterval) (𝓕 : Set (Set X))
        (𝓗 : Finset (Finset X)) (h𝓗 : ∀ S ∈ 𝓗, ∀ W : Finset X, S ⊆ W → (↑W : Set X) ∈ 𝓕) => by
      classical
      have hsing : ∀ s : Set X, (setBer((Set.univ : Set X), p)).real {s} =
          (p : ℝ) ^ s.ncard * (1 - (p : ℝ)) ^ (Fintype.card X - s.ncard) := by
        intro s
        have h2 : (Set.univ \ s).ncard = Fintype.card X - s.ncard := by
          rw [Set.ncard_diff (Set.subset_univ s), Set.ncard_univ, Nat.card_eq_fintype_card]
        rw [MeasureTheory.measureReal_def,
          setBernoulli_singleton (Set.univ : Set X) p (Set.subset_univ s) Set.finite_univ, h2,
          ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.coe_toReal,
          ENNReal.coe_toReal, unitInterval.coe_toNNReal, unitInterval.coe_toNNReal,
          unitInterval.coe_symm_eq]
      have hF : (setBer((Set.univ : Set X), p)).real 𝓕 = ∑ W : Finset X, if (↑W : Set X) ∈ 𝓕 then
          (p : ℝ) ^ W.card * (1 - (p : ℝ)) ^ (Fintype.card X - W.card) else 0 := by
        have e1 : (↑(Finset.univ.filter (fun s : Set X => s ∈ 𝓕)) : Set (Set X)) = 𝓕 := by
          ext s; simp
        have e2 := MeasureTheory.sum_measureReal_singleton (μ := setBer((Set.univ : Set X), p))
          (Finset.univ.filter (fun s : Set X => s ∈ 𝓕))
        rw [e1] at e2
        rw [← e2, Finset.sum_filter]
        symm
        apply Fintype.sum_equiv Fintype.finsetEquivSet
        intro W
        rw [Fintype.finsetEquivSet_apply, hsing, Set.ncard_coe_finset]
      have htot : ∑ W : Finset X, (p : ℝ) ^ W.card * (1 - (p : ℝ)) ^ (Fintype.card X - W.card) = 1 := by
        have := Finset.sum_pow_mul_eq_add_pow (p : ℝ) (1 - (p : ℝ)) (Finset.univ : Finset X)
        rw [Finset.powerset_univ, Finset.card_univ] at this
        rw [this, add_sub_cancel, one_pow]
      have hp0 : (0 : ℝ) ≤ p := p.2.1
      have hp1 : (p : ℝ) ≤ 1 := p.2.2
      have hsum : ∑ W : Finset X, ((p : ℝ) ^ W.card * (1 - (p : ℝ)) ^ (Fintype.card X - W.card) -
            (if ∃ S ∈ 𝓗, S ⊆ W then 0 else
              (p : ℝ) ^ W.card * (1 - (p : ℝ)) ^ (Fintype.card X - W.card))) ≤
          ∑ W : Finset X, (if (↑W : Set X) ∈ 𝓕 then
              (p : ℝ) ^ W.card * (1 - (p : ℝ)) ^ (Fintype.card X - W.card) else 0) := by
        apply Finset.sum_le_sum
        intro W _
        have hP : 0 ≤ (p : ℝ) ^ W.card * (1 - (p : ℝ)) ^ (Fintype.card X - W.card) :=
          mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
        by_cases h : ∃ S ∈ 𝓗, S ⊆ W
        · obtain ⟨S, hS, hSW⟩ := h
          have hW : (↑W : Set X) ∈ 𝓕 := h𝓗 S hS W hSW
          rw [if_pos ⟨S, hS, hSW⟩, if_pos hW, sub_zero]
        · rw [if_neg h, sub_self]
          split_ifs <;> linarith
      rw [Finset.sum_sub_distrib, htot] at hsum
      rw [hF]
      exact hsum
  have L_total : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (a : ℝ), ∑ W : Finset X, a ^ W.card * (1 - a) ^ (Fintype.card X - W.card) = 1 :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (a : ℝ) => by
      have h := Finset.sum_pow_mul_eq_add_pow a (1 - a) (Finset.univ : Finset X)
      rw [Finset.powerset_univ, Finset.card_univ] at h
      rw [h, add_sub_cancel, one_pow]
  have L_union_aux1 : ∀ (X : Type u_1) [DecidableEq X] (a b c : ℝ)
      (habc : (1 - a) * (1 - b) = 1 - c) (U : Finset X), ∀ f : Finset X → ℝ, ∑ A ∈ U.powerset, ∑ B ∈ U.powerset,
          (a ^ A.card * (1 - a) ^ (U.card - A.card)) *
            (b ^ B.card * (1 - b) ^ (U.card - B.card)) * f (A ∪ B) =
        ∑ C ∈ U.powerset, c ^ C.card * (1 - c) ^ (U.card - C.card) * f C :=
    fun (X : Type u_1) [DecidableEq X] (a b c : ℝ)
        (habc : (1 - a) * (1 - b) = 1 - c) (U : Finset X) => by
      induction U using Finset.induction_on with
      | empty => intro f; simp
      | insert x U hx ih =>
        intro f
        have hc : (1 - a) * b + a * (1 - b) + a * b = c := by linarith
        have hcard : (insert x U).card = U.card + 1 := Finset.card_insert_of_notMem hx
        have w0 : ∀ (t : ℝ) (A : Finset X), A ∈ U.powerset →
            t ^ A.card * (1 - t) ^ ((insert x U).card - A.card) =
              (1 - t) * (t ^ A.card * (1 - t) ^ (U.card - A.card)) := by
          intro t A hA
          have hle : A.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp hA)
          rw [hcard, show U.card + 1 - A.card = (U.card - A.card) + 1 by omega, pow_succ]
          ring
        have w1 : ∀ (t : ℝ) (A : Finset X), A ∈ U.powerset →
            t ^ (insert x A).card * (1 - t) ^ ((insert x U).card - (insert x A).card) =
              t * (t ^ A.card * (1 - t) ^ (U.card - A.card)) := by
          intro t A hA
          have hxA : x ∉ A := fun h => hx (Finset.mem_powerset.mp hA h)
          rw [hcard, Finset.card_insert_of_notMem hxA,
            show U.card + 1 - (A.card + 1) = U.card - A.card by omega, pow_succ]
          ring
        have key : ∀ (k : ℝ) (g : Finset X → ℝ) (F : Finset X → Finset X → ℝ),
            (∀ A ∈ U.powerset, ∀ B ∈ U.powerset, F A B = k * (a ^ A.card * (1 - a) ^ (U.card - A.card) *
              (b ^ B.card * (1 - b) ^ (U.card - B.card)) * g (A ∪ B))) →
            ∑ A ∈ U.powerset, ∑ B ∈ U.powerset, F A B =
              k * ∑ C ∈ U.powerset, c ^ C.card * (1 - c) ^ (U.card - C.card) * g C := by
          intro k g F h
          rw [← ih g, Finset.mul_sum]
          refine Finset.sum_congr rfl fun A hA => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun B hB => h A hA B hB
        have r1 : ∑ C ∈ U.powerset, c ^ C.card * (1 - c) ^ ((insert x U).card - C.card) * f C =
            (1 - c) * ∑ C ∈ U.powerset, c ^ C.card * (1 - c) ^ (U.card - C.card) * f C := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun C hC => by rw [w0 c C hC]; ring
        have r2 : ∑ C ∈ U.powerset, c ^ (insert x C).card * (1 - c) ^ ((insert x U).card - (insert x C).card) *
              f (insert x C) =
            c * ∑ C ∈ U.powerset, c ^ C.card * (1 - c) ^ (U.card - C.card) * f (insert x C) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun C hC => by rw [w1 c C hC]; ring
        simp only [Finset.sum_powerset_insert hx]
        rw [r1, r2, Finset.sum_add_distrib, Finset.sum_add_distrib,
          key ((1 - a) * (1 - b)) f _ fun A hA B hB => by rw [w0 a A hA, w0 b B hB]; ring,
          key ((1 - a) * b) (fun C => f (insert x C)) _ fun A hA B hB => by
            rw [w0 a A hA, w1 b B hB, Finset.union_insert]; ring,
          key (a * (1 - b)) (fun C => f (insert x C)) _ fun A hA B hB => by
            rw [w1 a A hA, w0 b B hB, Finset.insert_union]; ring,
          key (a * b) (fun C => f (insert x C)) _ fun A hA B hB => by
            rw [w1 a A hA, w1 b B hB, ← Finset.insert_union_distrib]; ring]
        linear_combination (∑ C ∈ U.powerset, c ^ C.card * (1 - c) ^ (U.card - C.card) * f C) * habc +
          (∑ C ∈ U.powerset, c ^ C.card * (1 - c) ^ (U.card - C.card) * f (insert x C)) * hc
  have L_union : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (a b c : ℝ)
      (habc : (1 - a) * (1 - b) = 1 - c) (f : Finset X → ℝ), ∑ A : Finset X, ∑ B : Finset X,
          (a ^ A.card * (1 - a) ^ (Fintype.card X - A.card)) *
            (b ^ B.card * (1 - b) ^ (Fintype.card X - B.card)) * f (A ∪ B) =
        ∑ C : Finset X, c ^ C.card * (1 - c) ^ (Fintype.card X - C.card) * f C :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (a b c : ℝ)
        (habc : (1 - a) * (1 - b) = 1 - c) (f : Finset X → ℝ) => by
      have h := L_union_aux1 X a b c habc Finset.univ f
      rw [Finset.powerset_univ, Finset.card_univ] at h
      exact h
  have L_frag : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (k : ℕ) (𝓗 : Finset (Finset X))
      (W : Finset X), ∃ 𝓗' 𝓑 : Finset (Finset X),
        (∀ T ∈ 𝓗', T.card < k) ∧
        (∀ T ∈ 𝓗', ∃ S ∈ 𝓗, S ⊆ W ∪ T) ∧
        (∀ S ∈ 𝓗, (∃ T ∈ 𝓗', T ⊆ S) ∨ (∃ T ∈ 𝓑, T ⊆ S)) ∧
        (∀ T ∈ 𝓑, k ≤ T.card ∧ Disjoint T W ∧ (∃ H ∈ 𝓗, H ⊆ W ∪ T) ∧
          ∀ H ∈ 𝓗, H ⊆ W ∪ T → T ⊆ H) :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (k : ℕ) (𝓗 : Finset (Finset X))
        (W : Finset X) => by
      have key : ∀ S : Finset X, ∃ S' : Finset X, S ∈ 𝓗 →
          (S' ∈ 𝓗 ∧ S' ⊆ W ∪ S ∧
            ∀ H ∈ 𝓗, H ⊆ W ∪ S → (S' \ W).card ≤ (H \ W).card) := by
        intro S
        by_cases hS : S ∈ 𝓗
        · have hne : (𝓗.filter (fun H => H ⊆ W ∪ S)).Nonempty :=
            ⟨S, Finset.mem_filter.2 ⟨hS, Finset.subset_union_right⟩⟩
          obtain ⟨S', hS'mem, hmin⟩ :=
            Finset.exists_min_image (𝓗.filter (fun H => H ⊆ W ∪ S)) (fun H => (H \ W).card) hne
          rw [Finset.mem_filter] at hS'mem
          refine ⟨S', fun _ => ⟨hS'mem.1, hS'mem.2, fun H hH hHsub => ?_⟩⟩
          exact hmin H (Finset.mem_filter.2 ⟨hH, hHsub⟩)
        · exact ⟨∅, fun h => absurd h hS⟩
      choose f hf using key
      -- f S ⊆ W ∪ (f S \ W)
      have hcov : ∀ S : Finset X, f S ⊆ W ∪ (f S \ W) := by
        intro S x hx
        rw [Finset.mem_union, Finset.mem_sdiff]
        by_cases hxW : x ∈ W
        · exact Or.inl hxW
        · exact Or.inr ⟨hx, hxW⟩
      -- f S \ W ⊆ S for S ∈ 𝓗
      have hTS : ∀ S ∈ 𝓗, f S \ W ⊆ S := by
        intro S hS x hx
        rw [Finset.mem_sdiff] at hx
        have hx' := (hf S hS).2.1 hx.1
        rw [Finset.mem_union] at hx'
        rcases hx' with h | h
        · exact absurd h hx.2
        · exact h
      refine ⟨(𝓗.filter (fun S => (f S \ W).card < k)).image (fun S => f S \ W),
        (𝓗.filter (fun S => k ≤ (f S \ W).card)).image (fun S => f S \ W), ?_, ?_, ?_, ?_⟩
      · intro T hT
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
        exact (Finset.mem_filter.1 hS).2
      · intro T hT
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
        exact ⟨f S, (hf S (Finset.mem_filter.1 hS).1).1, hcov S⟩
      · intro S hS
        rcases lt_or_ge (f S \ W).card k with h | h
        · exact Or.inl ⟨f S \ W, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hS, h⟩), hTS S hS⟩
        · exact Or.inr ⟨f S \ W, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hS, h⟩), hTS S hS⟩
      · intro T hT
        obtain ⟨S₀, hS₀, rfl⟩ := Finset.mem_image.1 hT
        rw [Finset.mem_filter] at hS₀
        refine ⟨hS₀.2, Finset.sdiff_disjoint, ⟨f S₀, (hf S₀ hS₀.1).1, hcov S₀⟩, ?_⟩
        intro H hH hHsub
        have hHS₀ : H ⊆ W ∪ S₀ := by
          intro x hx
          have hx' := hHsub hx
          rw [Finset.mem_union] at hx' ⊢
          rcases hx' with h | h
          · exact Or.inl h
          · exact Or.inr (hTS S₀ hS₀.1 h)
        have hcard : (f S₀ \ W).card ≤ (H \ W).card := (hf S₀ hS₀.1).2.2 H hH hHS₀
        have hsub2 : H \ W ⊆ f S₀ \ W := by
          intro x hx
          rw [Finset.mem_sdiff] at hx
          have hx' := hHsub hx.1
          rw [Finset.mem_union] at hx'
          rcases hx' with h | h
          · exact absurd h hx.2
          · exact h
        have heq : H \ W = f S₀ \ W := Finset.eq_of_subset_of_card_le hsub2 hcard
        rw [← heq]
        exact Finset.sdiff_subset
  have L_core : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (b q : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1)
      (hq : 0 ≤ q) (r : ℕ) (𝓗 : Finset (Finset X)) (h𝓗 : ∀ S ∈ 𝓗, S.card < 2 ^ r) (c : ℝ)
      (hc : ∀ 𝓖 : Finset (Finset X), (∀ S ∈ 𝓗, ∃ G ∈ 𝓖, G ⊆ S) → c ≤ ∑ G ∈ 𝓖, q ^ G.card)
      (a : ℝ) (ha : 1 - a = (1 - b) ^ r), c * ∑ W : Finset X,
          (if ∃ S ∈ 𝓗, S ⊆ W then 0 else a ^ W.card * (1 - a) ^ (Fintype.card X - W.card)) ≤
        ∑ t ∈ Finset.Ico 1 (2 ^ r), (4 * q / b) ^ t :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (b q : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1)
        (hq : 0 ≤ q) (r : ℕ) (𝓗 : Finset (Finset X)) (h𝓗 : ∀ S ∈ 𝓗, S.card < 2 ^ r) (c : ℝ)
        (hc : ∀ 𝓖 : Finset (Finset X), (∀ S ∈ 𝓗, ∃ G ∈ 𝓖, G ⊆ S) → c ≤ ∑ G ∈ 𝓖, q ^ G.card)
        (a : ℝ) (ha : 1 - a = (1 - b) ^ r) => by
      have hP : ∀ (r : ℕ) (a : ℝ), 1 - a = (1 - b) ^ r → ∀ W : Finset X,
          0 ≤ a ^ W.card * (1 - a) ^ (Fintype.card X - W.card) := by
        intro r a ha W
        have h1 : 0 ≤ (1 - b) ^ r := pow_nonneg (by linarith) r
        have h2 : (1 - b) ^ r ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
        have h3 : 0 ≤ a := by linarith
        have h4 : 0 ≤ 1 - a := by linarith
        exact mul_nonneg (pow_nonneg h3 _) (pow_nonneg h4 _)
      have hN : ∀ (r : ℕ) (a : ℝ), 1 - a = (1 - b) ^ r → ∀ 𝓗 : Finset (Finset X),
          0 ≤ ∑ W : Finset X,
            (if ∃ S ∈ 𝓗, S ⊆ W then 0 else a ^ W.card * (1 - a) ^ (Fintype.card X - W.card)) := by
        intro r a ha 𝓗
        refine Finset.sum_nonneg (fun W _ => ?_)
        split_ifs
        · exact le_refl 0
        · exact hP r a ha W
      have hN1 : ∀ (r : ℕ) (a : ℝ), 1 - a = (1 - b) ^ r → ∀ 𝓗 : Finset (Finset X),
          ∑ W : Finset X,
            (if ∃ S ∈ 𝓗, S ⊆ W then 0 else a ^ W.card * (1 - a) ^ (Fintype.card X - W.card)) ≤ 1 := by
        intro r a ha 𝓗
        calc _ ≤ ∑ W : Finset X, a ^ W.card * (1 - a) ^ (Fintype.card X - W.card) := by
              refine Finset.sum_le_sum (fun W _ => ?_)
              split_ifs
              · exact hP r a ha W
              · exact le_refl _
          _ = 1 := L_total X a
      have hRHS : ∀ r : ℕ, 0 ≤ ∑ t ∈ Finset.Ico 1 (2 ^ r), (4 * q / b) ^ t :=
        fun r => Finset.sum_nonneg (fun t _ => pow_nonneg (div_nonneg (by linarith) hb0.le) t)
      induction r generalizing 𝓗 c a with
      | zero =>
        rcases 𝓗.eq_empty_or_nonempty with h | ⟨S, hS⟩
        · have hc0 : c ≤ 0 := by
            have := hc ∅ (by intro S hS; rw [h] at hS; exact absurd hS (Finset.notMem_empty S))
            rwa [Finset.sum_empty] at this
          exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc0 (hN 0 a ha 𝓗)) (hRHS 0)
        · have hS0 : S = ∅ := Finset.card_eq_zero.mp (by have := h𝓗 S hS; rw [pow_zero] at this; omega)
          rw [Finset.sum_eq_zero (fun W _ => if_pos ⟨S, hS, hS0 ▸ Finset.empty_subset W⟩), mul_zero]
          exact hRHS 0
      | succ r ih =>
        rcases le_or_gt c 0 with hc0 | hc0
        · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc0 (hN _ a ha 𝓗)) (hRHS _)
        have ha' : 1 - (1 - (1 - b) ^ r) = (1 - b) ^ r := sub_sub_cancel 1 _
        have habc : (1 - b) * (1 - (1 - (1 - b) ^ r)) = 1 - a := by rw [ha', ha, pow_succ']
        choose 𝓗' 𝓑 h1 h2 h3 h4 using fun A => L_frag X (2 ^ r) 𝓗 A
        have hbad := L_badcost X r 𝓗 h𝓗 𝓑 h4 b q hb0 hb1 hq
        have hU := L_union X b (1 - (1 - b) ^ r) a habc (fun C => if ∃ S ∈ 𝓗, S ⊆ C then 0 else 1)
        have hPb : ∀ A : Finset X, 0 ≤ b ^ A.card * (1 - b) ^ (Fintype.card X - A.card) :=
          hP 1 b (pow_one _).symm
        -- per-A bound from the induction hypothesis
        have key : ∀ A : Finset X, c * ∑ B : Finset X, (if ∃ T ∈ 𝓗' A, T ⊆ B then 0 else
            (1 - (1 - b) ^ r) ^ B.card * (1 - (1 - (1 - b) ^ r)) ^ (Fintype.card X - B.card)) ≤
            (∑ t ∈ Finset.Ico 1 (2 ^ r), (4 * q / b) ^ t) + ∑ T ∈ 𝓑 A, q ^ T.card := by
          intro A
          have hcA : ∀ 𝓖 : Finset (Finset X), (∀ S ∈ 𝓗' A, ∃ G ∈ 𝓖, G ⊆ S) →
              c - ∑ T ∈ 𝓑 A, q ^ T.card ≤ ∑ G ∈ 𝓖, q ^ G.card := by
            intro 𝓖 h𝓖
            have hcov := hc (𝓖 ∪ 𝓑 A) (fun S hS => by
              rcases h3 A S hS with ⟨T, hT, hTS⟩ | ⟨T, hT, hTS⟩
              · obtain ⟨G, hG, hGT⟩ := h𝓖 T hT
                exact ⟨G, Finset.mem_union_left _ hG, hGT.trans hTS⟩
              · exact ⟨T, Finset.mem_union_right _ hT, hTS⟩)
            have h5 := Finset.sum_union_inter (s₁ := 𝓖) (s₂ := 𝓑 A) (f := fun G => q ^ G.card)
            have h6 : 0 ≤ ∑ G ∈ 𝓖 ∩ 𝓑 A, q ^ G.card := Finset.sum_nonneg (fun G _ => pow_nonneg hq _)
            linarith
          have hih := ih (𝓗' A) (h1 A) (c - ∑ T ∈ 𝓑 A, q ^ T.card) hcA _ ha'
          have hN1' := hN1 r _ ha' (𝓗' A)
          have hcost : 0 ≤ ∑ T ∈ 𝓑 A, q ^ T.card := Finset.sum_nonneg (fun T _ => pow_nonneg hq _)
          linarith [mul_nonneg hcost (sub_nonneg.mpr hN1')]
        have hstep : ∀ A B : Finset X,
            b ^ A.card * (1 - b) ^ (Fintype.card X - A.card) *
              ((1 - (1 - b) ^ r) ^ B.card * (1 - (1 - (1 - b) ^ r)) ^ (Fintype.card X - B.card)) *
              (if ∃ S ∈ 𝓗, S ⊆ A ∪ B then (0:ℝ) else 1) ≤
            b ^ A.card * (1 - b) ^ (Fintype.card X - A.card) *
              (if ∃ T ∈ 𝓗' A, T ⊆ B then 0 else
                (1 - (1 - b) ^ r) ^ B.card * (1 - (1 - (1 - b) ^ r)) ^ (Fintype.card X - B.card)) := by
          intro A B
          by_cases hT : ∃ T ∈ 𝓗' A, T ⊆ B
          · obtain ⟨T, hT', hTB⟩ := hT
            obtain ⟨S, hS, hSAT⟩ := h2 A T hT'
            rw [if_pos ⟨S, hS, hSAT.trans (Finset.union_subset_union_right hTB)⟩, if_pos ⟨T, hT', hTB⟩,
              mul_zero, mul_zero]
          · rw [if_neg hT]
            split_ifs
            · rw [mul_zero]; exact mul_nonneg (hPb A) (hP r _ ha' B)
            · rw [mul_one]
        have hmain : ∑ W : Finset X,
            (if ∃ S ∈ 𝓗, S ⊆ W then 0 else a ^ W.card * (1 - a) ^ (Fintype.card X - W.card)) ≤
            ∑ A : Finset X, b ^ A.card * (1 - b) ^ (Fintype.card X - A.card) *
              ∑ B : Finset X, (if ∃ T ∈ 𝓗' A, T ⊆ B then 0 else
                (1 - (1 - b) ^ r) ^ B.card * (1 - (1 - (1 - b) ^ r)) ^ (Fintype.card X - B.card)) := by
          calc _ = ∑ C : Finset X, a ^ C.card * (1 - a) ^ (Fintype.card X - C.card) *
                  (fun C => if ∃ S ∈ 𝓗, S ⊆ C then (0:ℝ) else 1) C := by
                refine Finset.sum_congr rfl (fun W _ => ?_)
                dsimp only
                split_ifs
                · rw [mul_zero]
                · rw [mul_one]
            _ = _ := hU.symm
            _ ≤ _ := by
                refine Finset.sum_le_sum (fun A _ => ?_)
                rw [Finset.mul_sum]
                exact Finset.sum_le_sum (fun B _ => hstep A B)
        calc c * _ ≤ c * ∑ A : Finset X, b ^ A.card * (1 - b) ^ (Fintype.card X - A.card) *
              ∑ B : Finset X, (if ∃ T ∈ 𝓗' A, T ⊆ B then 0 else
                (1 - (1 - b) ^ r) ^ B.card * (1 - (1 - (1 - b) ^ r)) ^ (Fintype.card X - B.card)) :=
              mul_le_mul_of_nonneg_left hmain hc0.le
          _ ≤ ∑ A : Finset X, b ^ A.card * (1 - b) ^ (Fintype.card X - A.card) *
              ((∑ t ∈ Finset.Ico 1 (2 ^ r), (4 * q / b) ^ t) + ∑ T ∈ 𝓑 A, q ^ T.card) := by
              rw [Finset.mul_sum]
              refine Finset.sum_le_sum (fun A _ => ?_)
              exact Eq.trans_le (by ring) (mul_le_mul_of_nonneg_left (key A) (hPb A))
          _ = (∑ t ∈ Finset.Ico 1 (2 ^ r), (4 * q / b) ^ t) +
              ∑ A : Finset X, b ^ A.card * (1 - b) ^ (Fintype.card X - A.card) *
                ∑ T ∈ 𝓑 A, q ^ T.card := by
              simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, L_total X b, one_mul]
          _ ≤ (∑ t ∈ Finset.Ico 1 (2 ^ r), (4 * q / b) ^ t) +
              ∑ t ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), (4 * q / b) ^ t := add_le_add (le_refl _) hbad
          _ = _ := Finset.sum_Ico_consecutive _ Nat.one_le_two_pow
              (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ r))
  have L_cover : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (𝓕 : Set (Set X)) (q : unitInterval)
      (hq : ¬ FractionalExpectationThresholds.IsWeaklySmall q 𝓕) (𝓗 : Finset (Finset X))
      (h𝓗 : ∀ T ∈ 𝓕, ∃ S ∈ 𝓗, (↑S : Set X) ⊆ T) (𝓖 : Finset (Finset X))
      (h𝓖 : ∀ S ∈ 𝓗, ∃ G ∈ 𝓖, G ⊆ S), 2⁻¹ < ∑ G ∈ 𝓖, (q : ℝ) ^ G.card :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (𝓕 : Set (Set X)) (q : unitInterval)
        (hq : ¬ FractionalExpectationThresholds.IsWeaklySmall q 𝓕) (𝓗 : Finset (Finset X))
        (h𝓗 : ∀ T ∈ 𝓕, ∃ S ∈ 𝓗, (↑S : Set X) ⊆ T) (𝓖 : Finset (Finset X))
        (h𝓖 : ∀ S ∈ 𝓗, ∃ G ∈ 𝓖, G ⊆ S) => by
      classical
      by_contra hcon
      push_neg at hcon
      apply hq
      refine ⟨fun A => if A ∈ 𝓖.image (fun G : Finset X => (↑G : Set X)) then 1 else 0, ?_, ?_⟩
      · intro T hT
        obtain ⟨S, hS, hST⟩ := h𝓗 T hT
        obtain ⟨G, hG, hGS⟩ := h𝓖 S hS
        have hGT : (↑G : Set X) ⊆ T := (Finset.coe_subset.mpr hGS).trans hST
        have hmem : (↑G : Set X) ∈ 𝓖.image (fun G : Finset X => (↑G : Set X)) :=
          Finset.mem_image_of_mem _ hG
        refine le_trans ?_ (Finset.single_le_sum (f := fun A : Set X =>
          if A ∈ 𝓖.image (fun G : Finset X => (↑G : Set X)) then (1 : NNReal) else 0)
          (fun _ _ => zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGT⟩))
        simp only [hmem, if_true, le_refl]
      · have h1 : ∀ S : Set X, ((if S ∈ 𝓖.image (fun G : Finset X => (↑G : Set X)) then (1 : NNReal)
            else 0 : NNReal) : ℝ) * (q : ℝ) ^ S.ncard
            = if S ∈ 𝓖.image (fun G : Finset X => (↑G : Set X)) then (q : ℝ) ^ S.ncard else 0 := by
          intro S; split_ifs <;> simp
        simp only [h1]
        rw [Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_image (fun x _ y _ h => Finset.coe_injective h)]
        simpa only [Set.ncard_coe_finset] using hcon
  have L_ell : ∀ (X : Type u_1) [Fintype X] (𝓕 : Set (Set X)) (T : Set X) (hT : T ∈ 𝓕), ∃ S : Finset X, (↑S : Set X) ∈ 𝓕 ∧ (↑S : Set X) ⊆ T ∧
        S.card ≤ FractionalExpectationThresholds.l 𝓕 :=
    fun (X : Type u_1) [Fintype X] (𝓕 : Set (Set X)) (T : Set X) (hT : T ∈ 𝓕) => by
      classical
      obtain ⟨T', hT'⟩ := (Set.toFinite T).exists_finset_coe
      obtain ⟨S₀, hS₀mem, hS₀min⟩ := Finset.exists_min_image
        ((Finset.univ : Finset (Finset X)).filter (fun S : Finset X => (↑S : Set X) ∈ 𝓕 ∧ (↑S : Set X) ⊆ T))
        Finset.card
        ⟨T', Finset.mem_filter.2 ⟨Finset.mem_univ _, hT'.symm ▸ hT, hT'.subset⟩⟩
      obtain ⟨-, hS₀F, hS₀T⟩ := Finset.mem_filter.1 hS₀mem
      refine ⟨S₀, hS₀F, hS₀T, ?_⟩
      have hmin : IsMin (⟨(↑S₀ : Set X), hS₀F⟩ : 𝓕) := by
        rintro ⟨B, hBF⟩ hB
        have hBsub : B ⊆ ↑S₀ := hB
        obtain ⟨B', rfl⟩ := (Set.toFinite B).exists_finset_coe
        have hcard := hS₀min B' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hBF, hBsub.trans hS₀T⟩)
        have heq : B' = S₀ := Finset.eq_of_subset_of_card_le (Finset.coe_subset.1 hBsub) hcard
        subst heq
        exact le_rfl
      calc S₀.card = (↑S₀ : Set X).ncard := (Set.ncard_coe_finset S₀).symm
        _ = ⨆ (_ : IsMin (⟨(↑S₀ : Set X), hS₀F⟩ : 𝓕)),
              ((⟨(↑S₀ : Set X), hS₀F⟩ : 𝓕) : Set X).ncard :=
            (ciSup_pos (f := fun _ => ((⟨(↑S₀ : Set X), hS₀F⟩ : 𝓕) : Set X).ncard) hmin).symm
        _ ≤ FractionalExpectationThresholds.l 𝓕 :=
            le_ciSup (f := fun (A : 𝓕) => ⨆ (_ : IsMin A), (A : Set X).ncard)
              (Set.finite_range _).bddAbove (⟨(↑S₀ : Set X), hS₀F⟩ : 𝓕)
  have L_geom : ∀ (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (N : ℕ), ∑ t ∈ Finset.Ico 1 N, x ^ t ≤ 2 * x :=
    fun (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (N : ℕ) => by
      have hS : 0 ≤ ∑ t ∈ Finset.Ico 1 N, x ^ t :=
        Finset.sum_nonneg (fun t _ => pow_nonneg hx0 t)
      have key : (1 - x) * ∑ t ∈ Finset.Ico 1 N, x ^ t ≤ x := by
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · rw [Finset.Ico_eq_empty_of_le (Nat.zero_le 1), Finset.sum_empty, mul_zero]
          exact hx0
        · have h := geom_sum_Ico_mul x hN
          rw [pow_one] at h
          linarith [pow_nonneg hx0 N]
      linarith [mul_nonneg (sub_nonneg.mpr hx1) hS]
  have L_log : ∀ (ℓ : ℕ) (hℓ : 2 ≤ ℓ), ((Nat.log 2 ℓ : ℕ) : ℝ) + 1 ≤ 3 * Real.log ℓ :=
    fun (ℓ : ℕ) (hℓ : 2 ≤ ℓ) => by
      have hℓ0 : ℓ ≠ 0 := by omega
      have hpow : 2 ^ (Nat.log 2 ℓ) ≤ ℓ := Nat.pow_log_le_self 2 hℓ0
      have hpowR : (2:ℝ) ^ (Nat.log 2 ℓ) ≤ (ℓ:ℝ) := by exact_mod_cast hpow
      have hlog1 : ((Nat.log 2 ℓ : ℕ) : ℝ) * Real.log 2 ≤ Real.log ℓ := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hpowR
      have hℓR : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ
      have hlog2 : Real.log 2 ≤ Real.log ℓ := Real.log_le_log (by norm_num) hℓR
      have hl2 : (2:ℝ) / 3 < Real.log 2 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have hE := Real.exp_bound' (x := (2:ℝ) / 3) (by norm_num) (by norm_num) (n := 3) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at hE
        linarith
      have hk0 : (0:ℝ) ≤ ((Nat.log 2 ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
      have hprod : ((Nat.log 2 ℓ : ℕ) : ℝ) * (2 / 3) ≤ ((Nat.log 2 ℓ : ℕ) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hl2.le hk0
      linarith
  have L_rpow : ∀ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : ℕ) (hr : 1 ≤ r), ∃ b : ℝ, 0 ≤ b ∧ b ≤ 1 ∧ (1 - b) ^ r = 1 - p ∧ p ≤ r * b :=
    fun (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : ℕ) (hr : 1 ≤ r) => by
      have hq0 : (0:ℝ) ≤ 1 - p := by linarith
      have hq1 : 1 - p ≤ (1:ℝ) := by linarith
      have hr0 : r ≠ 0 := by omega
      have hc0 : (0:ℝ) ≤ (1 - p) ^ ((r : ℝ)⁻¹) := Real.rpow_nonneg hq0 _
      have hc1 : (1 - p) ^ ((r : ℝ)⁻¹) ≤ (1:ℝ) :=
        Real.rpow_le_one hq0 hq1 (inv_nonneg.mpr (Nat.cast_nonneg r))
      have hcr : ((1 - p) ^ ((r : ℝ)⁻¹)) ^ r = 1 - p := Real.rpow_inv_natCast_pow hq0 hr0
      refine ⟨1 - (1 - p) ^ ((r : ℝ)⁻¹), by linarith, by linarith, ?_, ?_⟩
      · rw [sub_sub_cancel]
        exact hcr
      · have hb : (-2:ℝ) ≤ -(1 - (1 - p) ^ ((r : ℝ)⁻¹)) := by linarith
        have hB := one_add_mul_le_pow hb r
        have h1 : (1 + -(1 - (1 - p) ^ ((r : ℝ)⁻¹))) = (1 - p) ^ ((r : ℝ)⁻¹) := by ring
        rw [h1, hcr] at hB
        linarith
  classical
  have hK : K = 192 := rfl
  have hl1 : (1 : ℝ) < (l 𝓕 : ℝ) := by exact_mod_cast (show 1 < l 𝓕 by omega)
  have hL : 0 < Real.log (l 𝓕 : ℝ) := Real.log_pos hl1
  have hq0 : (0 : ℝ) ≤ (q_f 𝓕 : ℝ) := (q_f 𝓕).2.1
  have hRHS : (0 : ℝ) ≤ 192 * (q_f 𝓕 : ℝ) * Real.log (l 𝓕 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hq0) hL.le
  by_cases hex : ∃ p, setBer(univ, p).real 𝓕 = 2⁻¹
  swap
  · have h0 : p_c 𝓕 = 0 := by
      unfold p_c
      exact dif_neg hex
    rw [h0, hK]
    exact hRHS
  have hpc' : p_c 𝓕 = Classical.choose hex := by
    unfold p_c
    exact dif_pos hex
  have hpc : setBer(univ, p_c 𝓕).real 𝓕 = 2⁻¹ := by
    rw [hpc']
    exact Classical.choose_spec hex
  by_contra hcon
  push_neg at hcon
  rw [hK] at hcon
  have hp0 : (0 : ℝ) ≤ (p_c 𝓕 : ℝ) := (p_c 𝓕).2.1
  have hp1 : (p_c 𝓕 : ℝ) ≤ 1 := (p_c 𝓕).2.2
  have hppos : 0 < (p_c 𝓕 : ℝ) := lt_of_le_of_lt hRHS hcon
  have hr1 : 1 ≤ Nat.log 2 (l 𝓕) + 1 := by omega
  have hrL : ((Nat.log 2 (l 𝓕) + 1 : ℕ) : ℝ) ≤ 3 * Real.log (l 𝓕 : ℝ) := by
    have h := L_log (l 𝓕) hl𝓕
    push_cast
    linarith
  obtain ⟨b, hb0, hb1, hbr, hpb⟩ := L_rpow (p_c 𝓕 : ℝ) hp0 hp1 (Nat.log 2 (l 𝓕) + 1) hr1
  have hbpos : 0 < b := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hpb
      linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (p_c 𝓕 : ℝ) / (192 * Real.log (l 𝓕 : ℝ)) := ⟨_, rfl⟩
  have h192 : 0 < 192 * Real.log (l 𝓕 : ℝ) := by positivity
  have hqmul : q * (192 * Real.log (l 𝓕 : ℝ)) = (p_c 𝓕 : ℝ) := by
    rw [hq, div_mul_cancel₀ _ h192.ne']
  have hqpos : 0 < q := by
    rw [hq]
    exact div_pos hppos h192
  have hLge : 1 ≤ 3 * Real.log (l 𝓕 : ℝ) := by
    have : (1 : ℝ) ≤ ((Nat.log 2 (l 𝓕) + 1 : ℕ) : ℝ) := by exact_mod_cast hr1
    linarith
  have hq1 : q ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hLge hqpos.le]
  have hqgt : (q_f 𝓕 : ℝ) < q := by
    by_contra h
    push_neg at h
    nlinarith [mul_le_mul_of_nonneg_right h h192.le]
  have hnws : ¬ IsWeaklySmall (⟨q, hqpos.le, hq1⟩ : unitInterval) 𝓕 := by
    intro hws
    have h1 : (⟨q, hqpos.le, hq1⟩ : unitInterval) ≤ q_f 𝓕 := le_sSup hws
    have h2 : q ≤ (q_f 𝓕 : ℝ) := h1
    linarith
  obtain ⟨𝓗, h𝓗⟩ : ∃ 𝓗 : Finset (Finset X),
      𝓗 = Finset.univ.filter (fun S : Finset X => (↑S : Set X) ∈ 𝓕 ∧ S.card ≤ l 𝓕) := ⟨_, rfl⟩
  have h𝓗cov : ∀ T ∈ 𝓕, ∃ S ∈ 𝓗, (↑S : Set X) ⊆ T := by
    intro T hT
    obtain ⟨S, hS𝓕, hST, hScard⟩ := L_ell X 𝓕 T hT
    refine ⟨S, ?_, hST⟩
    rw [h𝓗]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS𝓕, hScard⟩
  have h𝓗up : ∀ S ∈ 𝓗, ∀ W : Finset X, S ⊆ W → (↑W : Set X) ∈ 𝓕 := by
    intro S hS W hSW
    rw [h𝓗] at hS
    exact h𝓕 (Finset.coe_subset.mpr hSW) (Finset.mem_filter.mp hS).2.1
  have h𝓗size : ∀ S ∈ 𝓗, S.card < 2 ^ (Nat.log 2 (l 𝓕) + 1) := by
    intro S hS
    rw [h𝓗] at hS
    exact lt_of_le_of_lt (Finset.mem_filter.mp hS).2.2 (Nat.lt_pow_succ_log_self (by norm_num) _)
  have hcore := L_core X b q hbpos hb1 hqpos.le (Nat.log 2 (l 𝓕) + 1) 𝓗 h𝓗size 2⁻¹
    (fun 𝓖 h𝓖 => (L_cover X 𝓕 ⟨q, hqpos.le, hq1⟩ hnws 𝓗 h𝓗cov 𝓖 h𝓖).le) (p_c 𝓕 : ℝ) hbr.symm
  have h64 : 64 * q ≤ b := by
    have h3 : (p_c 𝓕 : ℝ) ≤ 3 * Real.log (l 𝓕 : ℝ) * b := by
      calc (p_c 𝓕 : ℝ) ≤ ((Nat.log 2 (l 𝓕) + 1 : ℕ) : ℝ) * b := hpb
        _ ≤ 3 * Real.log (l 𝓕 : ℝ) * b := mul_le_mul_of_nonneg_right hrL hb0
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_left h hL]
  have hx : 4 * q / b ≤ 1 / 16 := by
    rw [div_le_iff₀ hbpos]
    linarith
  have hgeom := L_geom (4 * q / b) (by positivity) (by linarith) (2 ^ (Nat.log 2 (l 𝓕) + 1))
  have hbridge := L_bridge X (p_c 𝓕) 𝓕 𝓗 h𝓗up
  rw [hpc] at hbridge
  linarith

end FractionalExpectationThresholds

end Submission
