/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Submission.Helpers
import ChallengeDeps
/-!
# Main Statement from Improved bounds for the sunflower lemma

We formalise the statement of the main result from R. Alweiss, S. Lovett, K. Wu, and J. Zhang,
`Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021.
-/


namespace Submission

open _root_.ImprovedBoundsSunflowerLemma
open _root_.Set
set_option autoImplicit false

namespace Set

variable {X : Type*}





end Set

namespace ImprovedBoundsSunflowerLemma

open Real



/-- The absolute constant `C` in Theorem 1.4. Although not explicitly stated in the paper,
the constant `C` doesn't depend on `r`. -/
noncomputable def C : ℝ := 10000

/--
Statement of Theorem 1.4 (Main theorem, sunflowers):

Let `r ≥ 3`. For some constant `C`, any `w`-set system `F` of size
`|F| ≥ (C * r ^ 3 * log w * log log w) ^ w` contains an `r`-sunflower.

Note: We require `w ≥ 2`, as the paper assumes `log log w > 0`.
-/
theorem theorem_1_4 (r : ℕ) (hr : r ≥ 3) (X : Type*) [Finite X] (ℱ : Set (Set X)) (w : ℕ)
      (hw : w ≥ 2) (hℱ₁ : ℱ.IsSystem w) (hℱ₂ : ℱ.ncard ≥ lowerBound r C w) :
      ∃ S ⊆ ℱ, S.IsSunflower r := by
  have L_colorcount : ∀ (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (c : Fin r) (V : Finset α), (Finset.univ.filter (fun χ : α → Fin r => Finset.univ.filter (fun x => χ x = c) = V)).card
        = (r - 1) ^ (Fintype.card α - V.card) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (c : Fin r) (V : Finset α) => by
      have hset : Finset.univ.filter (fun χ : α → Fin r => Finset.univ.filter (fun x => χ x = c) = V)
          = Fintype.piFinset (fun x => if x ∈ V then ({c} : Finset (Fin r)) else Finset.univ.erase c) := by
        ext χ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        constructor
        · intro h x
          by_cases hx : x ∈ V
          · rw [if_pos hx, Finset.mem_singleton]
            rw [← h] at hx
            simpa using hx
          · rw [if_neg hx, Finset.mem_erase]
            refine ⟨fun hc => hx ?_, Finset.mem_univ _⟩
            rw [← h]
            simpa using hc
        · intro h
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hx := h x
          by_cases hxV : x ∈ V
          · rw [if_pos hxV, Finset.mem_singleton] at hx
            simp [hx, hxV]
          · rw [if_neg hxV, Finset.mem_erase] at hx
            simp [hx.1, hxV]
      rw [hset, Fintype.card_piFinset]
      have hc : ∀ i : α, (if i ∈ V then ({c} : Finset (Fin r)) else Finset.univ.erase c).card
          = if i ∈ V then 1 else r - 1 := by
        intro i
        split_ifs
        · exact Finset.card_singleton c
        · rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      simp only [hc]
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
      congr 1
      have : (Finset.univ.filter (fun x : α => x ∉ V)) = Vᶜ := by
        ext x; simp
      rw [this, Finset.card_compl]
  have L_frag : ∀ (α : Type) [DecidableEq α] (s : ℕ) (J : Finset (Finset α))
      (G : Finset α → Finset α) (W j : Finset α) (hj : j ∈ J)
      (hbad : ∀ j' ∈ J, G j' ⊆ W ∪ G j → s ≤ (G j' \ W).card), ∃ F : Finset α, F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧ (∃ k ∈ J, G k ⊆ W ∪ F) ∧
        (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k) :=
    fun (α : Type) [DecidableEq α] (s : ℕ) (J : Finset (Finset α))
        (G : Finset α → Finset α) (W j : Finset α) (hj : j ∈ J)
        (hbad : ∀ j' ∈ J, G j' ⊆ W ∪ G j → s ≤ (G j' \ W).card) => by
      have hne : (J.filter (fun j' => G j' ⊆ W ∪ G j)).Nonempty :=
        ⟨j, Finset.mem_filter.mpr ⟨hj, Finset.subset_union_right⟩⟩
      obtain ⟨js, hjs, hmin⟩ := Finset.exists_min_image _ (fun j' => (G j' \ W).card) hne
      rw [Finset.mem_filter] at hjs
      have hFj : G js \ W ⊆ G j := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        have := hjs.2 hx.1
        rw [Finset.mem_union] at this
        tauto
      refine ⟨G js \ W, hFj, hbad js hjs.1 hjs.2, Finset.sdiff_disjoint, ⟨js, hjs.1, ?_⟩, ?_⟩
      · intro x hx
        by_cases hxW : x ∈ W
        · exact Finset.mem_union_left _ hxW
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxW⟩)
      · intro k hk hkZ
        have hkcand : G k ⊆ W ∪ G j := hkZ.trans (Finset.union_subset_union (Finset.Subset.refl W) hFj)
        have hle := hmin k (Finset.mem_filter.mpr ⟨hk, hkcand⟩)
        have hsub : G k \ W ⊆ G js \ W := by
          intro x hx
          rw [Finset.mem_sdiff] at hx
          have := hkZ hx.1
          rw [Finset.mem_union] at this
          tauto
        have heq := Finset.eq_of_subset_of_card_le hsub hle
        rw [← heq]
        exact Finset.sdiff_subset
  have L_mass : ∀ (α : Type) [Fintype α] [DecidableEq α] (p : ℝ), ∑ W : Finset α, p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) = 1 :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p : ℝ) => by
      have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ : Finset α)
      rw [Finset.powerset_univ, Finset.card_univ] at h
      rw [h]
      simp
  have L_count_aux1 : ∀ (α : Type) [Fintype α] [DecidableEq α] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
      (W F : Finset α) (hd : Disjoint F W), p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) * p ^ F.card ≤
        p ^ (W ∪ F).card * (1 - p) ^ (Fintype.card α - (W ∪ F).card) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
        (W F : Finset α) (hd : Disjoint F W) => by
      have hcard : (W ∪ F).card = W.card + F.card := Finset.card_union_of_disjoint hd.symm
      have hle : (W ∪ F).card ≤ Fintype.card α := Finset.card_le_univ _
      rw [hcard] at hle ⊢
      have hexp : Fintype.card α - W.card = (Fintype.card α - (W.card + F.card)) + F.card := by omega
      have key : p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) * p ^ F.card =
          (p ^ (W.card + F.card) * (1 - p) ^ (Fintype.card α - (W.card + F.card))) * (1 - p) ^ F.card := by
        rw [hexp, pow_add, pow_add]; ring
      rw [key]
      have h1 : (1 - p) ^ F.card ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have h2 : 0 ≤ p ^ (W.card + F.card) * (1 - p) ^ (Fintype.card α - (W.card + F.card)) :=
        mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
      exact mul_le_of_le_one_right h2 h1
  have L_count_aux0 : ∀ (α : Type) [Fintype α] [DecidableEq α] (s : ℕ)
      (J : Finset (Finset α)) (G : Finset α → Finset α) (W : Finset α), ((J.filter (fun j => ∃ F : Finset α, F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧
              (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k))).card : ℝ) ≤
        ∑ F : Finset α, ((J.filter (fun j => F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧
              (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k))).card : ℝ) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (s : ℕ)
        (J : Finset (Finset α)) (G : Finset α → Finset α) (W : Finset α) => by
      have hsub : J.filter (fun j => ∃ F : Finset α, F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧
                (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k)) ⊆
          (Finset.univ : Finset (Finset α)).biUnion (fun F => J.filter (fun j => F ⊆ G j ∧ s ≤ F.card ∧
                Disjoint F W ∧ (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k))) := by
        intro j hj
        rw [Finset.mem_filter] at hj
        obtain ⟨hjJ, F, hF⟩ := hj
        rw [Finset.mem_biUnion]
        exact ⟨F, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hjJ, hF⟩⟩
      have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      exact_mod_cast this
  have L_count_aux2 : ∀ (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ) (s : ℕ)
      (J : Finset (Finset α)) (G : Finset α → Finset α)
      (hp0 : 0 < p) (hp1 : p ≤ 1) (hκ : 1 ≤ p * κ) (hN : 0 ≤ N)
      (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N)
      (W F : Finset α), p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) *
        ((J.filter (fun j => F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧
              (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k))).card : ℝ) * (p * κ) ^ s ≤
        if Disjoint F W then
          (if (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k) then
            p ^ (W ∪ F).card * (1 - p) ^ (Fintype.card α - (W ∪ F).card) * N else 0)
        else 0 :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ) (s : ℕ)
        (J : Finset (Finset α)) (G : Finset α → Finset α)
        (hp0 : 0 < p) (hp1 : p ≤ 1) (hκ : 1 ≤ p * κ) (hN : 0 ≤ N)
        (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N)
        (W F : Finset α) => by
      have hκ0 : 0 < κ := by
        by_contra h
        push_neg at h
        nlinarith
      have hμ : 0 ≤ p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) :=
        mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (by linarith) _)
      have hμ' : 0 ≤ p ^ (W ∪ F).card * (1 - p) ^ (Fintype.card α - (W ∪ F).card) :=
        mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (by linarith) _)
      rcases Finset.eq_empty_or_nonempty (J.filter (fun j => F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧
                (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k))) with hemp | ⟨j, hj⟩
      · rw [hemp, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul]
        split_ifs
        all_goals first | exact le_refl _ | exact mul_nonneg hμ' hN
      · obtain ⟨_, hs, hd, hex, hall⟩ := (Finset.mem_filter.mp hj).2
        rw [if_pos hd, if_pos ⟨hex, hall⟩]
        have hsub : J.filter (fun j => F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧
                (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k)) ⊆
            J.filter (fun j => F ⊆ G j) := by
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hx.2.1⟩
        have hcard : ((J.filter (fun j => F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧
                (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k))).card : ℝ) ≤
            ((J.filter (fun j => F ⊆ G j)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        have hw := L_count_aux1 α p hp0.le hp1 W F hd
        have hsp := hspread F
        have hpow : (p * κ) ^ s ≤ (p * κ) ^ F.card := pow_le_pow_right₀ hκ hs
        calc _ ≤ p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) *
                ((J.filter (fun j => F ⊆ G j)).card : ℝ) * (p * κ) ^ F.card :=
              mul_le_mul (mul_le_mul_of_nonneg_left hcard hμ) hpow (pow_nonneg (by linarith) _)
                (mul_nonneg hμ (Nat.cast_nonneg _))
          _ = (p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) * p ^ F.card) *
                (((J.filter (fun j => F ⊆ G j)).card : ℝ) * κ ^ F.card) := by
              rw [mul_pow]; ring
          _ ≤ p ^ (W ∪ F).card * (1 - p) ^ (Fintype.card α - (W ∪ F).card) * N :=
              mul_le_mul hw hsp (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hκ0.le _)) hμ'
  have L_count_aux3 : ∀ (α : Type) [Fintype α] [DecidableEq α] (F : Finset α)
      (f : Finset α → ℝ) (hf : ∀ Z, 0 ≤ f Z), ∑ W : Finset α, (if Disjoint F W then f (W ∪ F) else 0) ≤ ∑ Z : Finset α, f Z :=
    fun (α : Type) [Fintype α] [DecidableEq α] (F : Finset α)
        (f : Finset α → ℝ) (hf : ∀ Z, 0 ≤ f Z) => by
      rw [← Finset.sum_filter]
      have hinj : Set.InjOn (fun W : Finset α => W ∪ F)
          ((Finset.univ.filter (fun W : Finset α => Disjoint F W) : Finset (Finset α)) : Set (Finset α)) := by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
        have h1 : (x ∪ F) \ F = x := Finset.union_sdiff_cancel_right hx.symm
        have h2 : (y ∪ F) \ F = y := Finset.union_sdiff_cancel_right hy.symm
        have hxy' : x ∪ F = y ∪ F := hxy
        calc x = (x ∪ F) \ F := h1.symm
          _ = (y ∪ F) \ F := by rw [hxy']
          _ = y := h2
      rw [← Finset.sum_image hinj]
      exact Finset.sum_le_univ_sum_of_nonneg hf
  have L_count_aux4 : ∀ (α : Type) [Fintype α] [DecidableEq α] (m : ℕ)
      (J : Finset (Finset α)) (G : Finset α → Finset α)
      (hm : ∀ j ∈ J, (G j).card ≤ m) (Z : Finset α) (c : ℝ) (hc : 0 ≤ c), ∑ F : Finset α, (if (∃ k ∈ J, G k ⊆ Z) ∧ (∀ k ∈ J, G k ⊆ Z → F ⊆ G k) then c else 0) ≤
        2 ^ m * c :=
    fun (α : Type) [Fintype α] [DecidableEq α] (m : ℕ)
        (J : Finset (Finset α)) (G : Finset α → Finset α)
        (hm : ∀ j ∈ J, (G j).card ≤ m) (Z : Finset α) (c : ℝ) (hc : 0 ≤ c) => by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hc
      by_cases h : ∃ k ∈ J, G k ⊆ Z
      · obtain ⟨k₀, hk₀J, hk₀Z⟩ := h
        have hsub : Finset.univ.filter (fun F : Finset α => (∃ k ∈ J, G k ⊆ Z) ∧
            (∀ k ∈ J, G k ⊆ Z → F ⊆ G k)) ⊆ (G k₀).powerset := by
          intro F hF
          rw [Finset.mem_filter] at hF
          rw [Finset.mem_powerset]
          exact hF.2.2 k₀ hk₀J hk₀Z
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_powerset] at h1
        have h2 : 2 ^ (G k₀).card ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (hm k₀ hk₀J)
        exact_mod_cast h1.trans h2
      · have hemp : Finset.univ.filter (fun F : Finset α => (∃ k ∈ J, G k ⊆ Z) ∧
            (∀ k ∈ J, G k ⊆ Z → F ⊆ G k)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro F _ hF
          exact h hF.1
        rw [hemp, Finset.card_empty, Nat.cast_zero]
        positivity
  have L_count : ∀ (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ) (s m : ℕ)
      (J : Finset (Finset α)) (G : Finset α → Finset α)
      (hp0 : 0 < p) (hp1 : p ≤ 1) (hκ : 1 ≤ p * κ)
      (hm : ∀ j ∈ J, (G j).card ≤ m)
      (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N), ∑ W : Finset α, p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) *
          ((J.filter (fun j => ∃ F : Finset α, F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧
              (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k))).card : ℝ)
        ≤ N * 2 ^ m / (p * κ) ^ s :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ) (s m : ℕ)
        (J : Finset (Finset α)) (G : Finset α → Finset α)
        (hp0 : 0 < p) (hp1 : p ≤ 1) (hκ : 1 ≤ p * κ)
        (hm : ∀ j ∈ J, (G j).card ≤ m)
        (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N) => by
      have hκ0 : 0 < κ := by
        by_contra h
        push_neg at h
        nlinarith
      have hN : 0 ≤ N := by
        have h := hspread ∅
        have h0 : (0:ℝ) ≤ ((J.filter (fun j => (∅ : Finset α) ⊆ G j)).card : ℝ) *
            κ ^ (∅ : Finset α).card := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hκ0.le _)
        linarith
      have hc : 0 < (p * κ) ^ s := pow_pos (by linarith) s
      have hμ : ∀ Z : Finset α, 0 ≤ p ^ Z.card * (1 - p) ^ (Fintype.card α - Z.card) := fun Z =>
        mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (by linarith) _)
      rw [le_div_iff₀ hc, Finset.sum_mul]
      calc _ ≤ ∑ W : Finset α, ∑ F : Finset α, p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) *
              ((J.filter (fun j => F ⊆ G j ∧ s ≤ F.card ∧ Disjoint F W ∧
                (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k))).card : ℝ) * (p * κ) ^ s := by
            apply Finset.sum_le_sum
            intro W _
            rw [← Finset.sum_mul, ← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (L_count_aux0 α s J G W) (hμ W)) hc.le
        _ ≤ ∑ W : Finset α, ∑ F : Finset α, (if Disjoint F W then
              (if (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k) then
                p ^ (W ∪ F).card * (1 - p) ^ (Fintype.card α - (W ∪ F).card) * N else 0)
              else 0) :=
            Finset.sum_le_sum (fun W _ => Finset.sum_le_sum (fun F _ =>
              L_count_aux2 α p κ N s J G hp0 hp1 hκ hN hspread W F))
        _ = ∑ F : Finset α, ∑ W : Finset α, (if Disjoint F W then
              (if (∃ k ∈ J, G k ⊆ W ∪ F) ∧ (∀ k ∈ J, G k ⊆ W ∪ F → F ⊆ G k) then
                p ^ (W ∪ F).card * (1 - p) ^ (Fintype.card α - (W ∪ F).card) * N else 0)
              else 0) := Finset.sum_comm
        _ ≤ ∑ F : Finset α, ∑ Z : Finset α,
              (if (∃ k ∈ J, G k ⊆ Z) ∧ (∀ k ∈ J, G k ⊆ Z → F ⊆ G k) then
                p ^ Z.card * (1 - p) ^ (Fintype.card α - Z.card) * N else 0) := by
            apply Finset.sum_le_sum
            intro F _
            exact L_count_aux3 α F (fun Z => if (∃ k ∈ J, G k ⊆ Z) ∧ (∀ k ∈ J, G k ⊆ Z → F ⊆ G k) then
                p ^ Z.card * (1 - p) ^ (Fintype.card α - Z.card) * N else 0)
              (fun Z => by
                dsimp only
                split_ifs
                · exact mul_nonneg (hμ Z) hN
                · exact le_refl _)
        _ = ∑ Z : Finset α, ∑ F : Finset α,
              (if (∃ k ∈ J, G k ⊆ Z) ∧ (∀ k ∈ J, G k ⊆ Z → F ⊆ G k) then
                p ^ Z.card * (1 - p) ^ (Fintype.card α - Z.card) * N else 0) := Finset.sum_comm
        _ ≤ ∑ Z : Finset α, 2 ^ m * (p ^ Z.card * (1 - p) ^ (Fintype.card α - Z.card) * N) :=
            Finset.sum_le_sum (fun Z _ => L_count_aux4 α m J G hm Z _ (mul_nonneg (hμ Z) hN))
        _ = N * 2 ^ m := by
            rw [← Finset.mul_sum, ← Finset.sum_mul, L_mass]
            ring
  have L_encode : ∀ (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ) (s m : ℕ)
      (J : Finset (Finset α)) (G : Finset α → Finset α)
      (hp0 : 0 < p) (hp1 : p ≤ 1) (hκ : 1 ≤ p * κ)
      (hm : ∀ j ∈ J, (G j).card ≤ m)
      (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N), ∑ W : Finset α, p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) *
          ((J.filter (fun j => ∀ j' ∈ J, G j' ⊆ W ∪ G j → s ≤ (G j' \ W).card)).card : ℝ)
        ≤ N * 2 ^ m / (p * κ) ^ s :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ) (s m : ℕ)
        (J : Finset (Finset α)) (G : Finset α → Finset α)
        (hp0 : 0 < p) (hp1 : p ≤ 1) (hκ : 1 ≤ p * κ)
        (hm : ∀ j ∈ J, (G j).card ≤ m)
        (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N) => by
      refine le_trans ?_ (L_count α p κ N s m J G hp0 hp1 hκ hm hspread)
      apply Finset.sum_le_sum
      intro W _
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast Finset.card_le_card (by
          intro j hj
          rw [Finset.mem_filter] at hj ⊢
          exact ⟨hj.1, L_frag α s J G W j hj.1 hj.2⟩)
      · exact mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (by linarith) _)
  have L_round : ∀ (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ) (m : ℕ)
      (J : Finset (Finset α)) (G : Finset α → Finset α)
      (hp0 : 0 < p) (hp1 : p ≤ 1) (hκ : 1 ≤ p * κ)
      (hm : ∀ j ∈ J, (G j).card ≤ m)
      (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N), ∃ (J' : Finset α → Finset (Finset α)) (G' : Finset α → Finset α → Finset α),
        (∀ W, J' W ⊆ J) ∧
        (∀ W, ∀ j ∈ J' W, G' W j ⊆ G j ∧ (G' W j).card ≤ m / 2 ∧ ∃ j₀ ∈ J, G j₀ ⊆ W ∪ G' W j) ∧
        ∑ W : Finset α, p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) *
            ((J \ J' W).card : ℝ) ≤ N * (4 / (p * κ)) ^ (m / 2 + 1) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ) (m : ℕ)
        (J : Finset (Finset α)) (G : Finset α → Finset α)
        (hp0 : 0 < p) (hp1 : p ≤ 1) (hκ : 1 ≤ p * κ)
        (hm : ∀ j ∈ J, (G j).card ≤ m)
        (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N) => by
      classical
      have hN : 0 ≤ N := by
        have h0 := hspread ∅
        simp only [Finset.empty_subset, Finset.filter_true_of_mem, Finset.card_empty, pow_zero,
          mul_one, implies_true] at h0
        exact le_trans (Nat.cast_nonneg _) h0
      refine ⟨fun W => J.filter (fun j => ∃ j' ∈ J, G j' ⊆ W ∪ G j ∧ (G j' \ W).card ≤ m / 2),
        fun W j => if h : (∃ j' ∈ J, G j' ⊆ W ∪ G j ∧ (G j' \ W).card ≤ m / 2)
          then G (Classical.choose h) \ W else ∅, ?_, ?_, ?_⟩
      · intro W
        exact Finset.filter_subset _ _
      · intro W j hj
        rw [Finset.mem_filter] at hj
        obtain ⟨_, hex⟩ := hj
        simp only [dif_pos hex]
        obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
        refine ⟨?_, h3, Classical.choose hex, h1, ?_⟩
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          have := h2 hx.1
          rw [Finset.mem_union] at this
          tauto
        · intro x hx
          by_cases hxW : x ∈ W
          · exact Finset.mem_union_left _ hxW
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxW⟩)
      · have henc := L_encode α p κ N (m / 2 + 1) m J G hp0 hp1 hκ hm hspread
        have hsd : ∀ W : Finset α,
            J \ J.filter (fun j => ∃ j' ∈ J, G j' ⊆ W ∪ G j ∧ (G j' \ W).card ≤ m / 2)
              = J.filter (fun j => ∀ j' ∈ J, G j' ⊆ W ∪ G j → m / 2 + 1 ≤ (G j' \ W).card) := by
          intro W
          ext j
          simp only [Finset.mem_sdiff, Finset.mem_filter]
          constructor
          · rintro ⟨hj, h⟩
            refine ⟨hj, fun j' hj' hsub => ?_⟩
            by_contra hlt
            exact h ⟨hj, j', hj', hsub, by omega⟩
          · rintro ⟨hj, h⟩
            refine ⟨hj, ?_⟩
            rintro ⟨_, j', hj', hsub, hle⟩
            have := h j' hj' hsub
            omega
        simp only [hsd]
        refine le_trans henc ?_
        have hpk : 0 < p * κ := by linarith
        rw [div_pow, mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ hN
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc (2:ℝ) ^ m ≤ 2 ^ (2 * (m / 2 + 1)) := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 4 ^ (m / 2 + 1) := by rw [pow_mul]; norm_num
  have L_union_aux0 : ∀ (α : Type) [DecidableEq α] (U : Finset α) (a : α) (ha : a ∉ U)
      (g : Finset α → ℝ), ∑ t ∈ (insert a U).powerset, g t
        = ∑ t ∈ U.powerset, g t + ∑ t ∈ U.powerset, g (insert a t) :=
    fun (α : Type) [DecidableEq α] (U : Finset α) (a : α) (ha : a ∉ U)
        (g : Finset α → ℝ) => by
      have hdisj : Disjoint U.powerset (U.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro t ht ht'
        rw [Finset.mem_image] at ht'
        obtain ⟨u, _, rfl⟩ := ht'
        exact ha (Finset.mem_powerset.mp ht (Finset.mem_insert_self a u))
      have hinj : Set.InjOn (insert a) (U.powerset : Set (Finset α)) := by
        intro x hx y hy hxy
        have hx' : a ∉ x := fun h => ha (Finset.mem_powerset.mp (Finset.mem_coe.mp hx) h)
        have hy' : a ∉ y := fun h => ha (Finset.mem_powerset.mp (Finset.mem_coe.mp hy) h)
        rw [← Finset.erase_insert hx', hxy, Finset.erase_insert hy']
      rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj]
  have L_union_aux1 : ∀ (α : Type) [DecidableEq α] (x : ℝ) (U : Finset α) (a : α) (ha : a ∉ U)
      (t : Finset α) (ht : t ∈ U.powerset), x ^ t.card * (1 - x) ^ ((insert a U).card - t.card)
        = (1 - x) * (x ^ t.card * (1 - x) ^ (U.card - t.card)) :=
    fun (α : Type) [DecidableEq α] (x : ℝ) (U : Finset α) (a : α) (ha : a ∉ U)
        (t : Finset α) (ht : t ∈ U.powerset) => by
      have htU : t ⊆ U := Finset.mem_powerset.mp ht
      have hle : t.card ≤ U.card := Finset.card_le_card htU
      rw [Finset.card_insert_of_notMem ha]
      have he : U.card + 1 - t.card = (U.card - t.card) + 1 := by omega
      rw [he, pow_succ]
      ring
  have L_union_aux2 : ∀ (α : Type) [DecidableEq α] (x : ℝ) (U : Finset α) (a : α) (ha : a ∉ U)
      (t : Finset α) (ht : t ∈ U.powerset), x ^ (insert a t).card * (1 - x) ^ ((insert a U).card - (insert a t).card)
        = x * (x ^ t.card * (1 - x) ^ (U.card - t.card)) :=
    fun (α : Type) [DecidableEq α] (x : ℝ) (U : Finset α) (a : α) (ha : a ∉ U)
        (t : Finset α) (ht : t ∈ U.powerset) => by
      have htU : t ⊆ U := Finset.mem_powerset.mp ht
      have hat : a ∉ t := fun h => ha (htU h)
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hat]
      have he : U.card + 1 - (t.card + 1) = U.card - t.card := by omega
      rw [he, pow_succ]
      ring
  have L_union_aux3 : ∀ (α : Type) [DecidableEq α] (p q s : ℝ) (hs : s = p + q - p * q)
      (U : Finset α), ∀ f : Finset α → ℝ,
      ∑ W ∈ U.powerset, ∑ V ∈ U.powerset,
          (p ^ W.card * (1 - p) ^ (U.card - W.card)) *
          (q ^ V.card * (1 - q) ^ (U.card - V.card)) * f (W ∪ V)
        = ∑ Z ∈ U.powerset, (s ^ Z.card * (1 - s) ^ (U.card - Z.card)) * f Z :=
    fun (α : Type) [DecidableEq α] (p q s : ℝ) (hs : s = p + q - p * q)
        (U : Finset α) => by
      induction U using Finset.induction_on with
      | empty => intro f; simp
      | insert a U ha ih =>
        intro f
        have h1 := ih f
        have h2 := ih (fun Z => f (insert a Z))
        calc ∑ W ∈ (insert a U).powerset, ∑ V ∈ (insert a U).powerset,
              (p ^ W.card * (1 - p) ^ ((insert a U).card - W.card)) *
              (q ^ V.card * (1 - q) ^ ((insert a U).card - V.card)) * f (W ∪ V)
            = ∑ W ∈ U.powerset, ∑ V ∈ U.powerset,
              ((1 - s) * ((p ^ W.card * (1 - p) ^ (U.card - W.card)) *
              (q ^ V.card * (1 - q) ^ (U.card - V.card)) * f (W ∪ V)) +
              s * ((p ^ W.card * (1 - p) ^ (U.card - W.card)) *
              (q ^ V.card * (1 - q) ^ (U.card - V.card)) * f (insert a (W ∪ V)))) := by
              rw [L_union_aux0 α U a ha, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun W hW => ?_)
              rw [L_union_aux0 α U a ha, L_union_aux0 α U a ha,
                ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun V hV => ?_)
              rw [L_union_aux1 α p U a ha W hW, L_union_aux1 α q U a ha V hV,
                L_union_aux2 α p U a ha W hW, L_union_aux2 α q U a ha V hV]
              simp only [Finset.union_insert, Finset.insert_union, Finset.insert_idem]
              subst hs
              ring
          _ = (1 - s) * ∑ W ∈ U.powerset, ∑ V ∈ U.powerset,
              (p ^ W.card * (1 - p) ^ (U.card - W.card)) *
              (q ^ V.card * (1 - q) ^ (U.card - V.card)) * f (W ∪ V) +
              s * ∑ W ∈ U.powerset, ∑ V ∈ U.powerset,
              (p ^ W.card * (1 - p) ^ (U.card - W.card)) *
              (q ^ V.card * (1 - q) ^ (U.card - V.card)) * f (insert a (W ∪ V)) := by
              simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          _ = (1 - s) * ∑ Z ∈ U.powerset, (s ^ Z.card * (1 - s) ^ (U.card - Z.card)) * f Z +
              s * ∑ Z ∈ U.powerset, (s ^ Z.card * (1 - s) ^ (U.card - Z.card)) * f (insert a Z) := by
              rw [h1, h2]
          _ = ∑ Z ∈ (insert a U).powerset,
              (s ^ Z.card * (1 - s) ^ ((insert a U).card - Z.card)) * f Z := by
              rw [L_union_aux0 α U a ha, Finset.mul_sum, Finset.mul_sum]
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun Z hZ => ?_)
              rw [L_union_aux1 α s U a ha Z hZ, L_union_aux2 α s U a ha Z hZ]
              ring
  have L_union : ∀ (α : Type) [Fintype α] [DecidableEq α] (p q : ℝ) (f : Finset α → ℝ), ∑ W : Finset α, ∑ V : Finset α,
          (p ^ W.card * (1 - p) ^ (Fintype.card α - W.card)) *
          (q ^ V.card * (1 - q) ^ (Fintype.card α - V.card)) * f (W ∪ V)
        = ∑ Z : Finset α, ((p + q - p * q) ^ Z.card *
            (1 - (p + q - p * q)) ^ (Fintype.card α - Z.card)) * f Z :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p q : ℝ) (f : Finset α → ℝ) => by
      have h := L_union_aux3 α p q (p + q - p * q) rfl Finset.univ f
      rw [Finset.powerset_univ, Finset.card_univ] at h
      exact h
  have L_multi_aux1 : ∀ (α : Type) [Fintype α] [DecidableEq α] (J : Finset (Finset α))
      (G : Finset α → Finset α) (hm : ∀ j ∈ J, (G j).card ≤ 0) (V : Finset α), (if ∃ j ∈ J, G j ⊆ V then (0 : ℝ) else (J.card : ℝ)) = 0 :=
    fun (α : Type) [Fintype α] [DecidableEq α] (J : Finset (Finset α))
        (G : Finset α → Finset α) (hm : ∀ j ∈ J, (G j).card ≤ 0) (V : Finset α) => by
      split_ifs with h
      · rfl
      · have hJ : J = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro j hj
          apply h
          refine ⟨j, hj, ?_⟩
          have h0 := Finset.card_eq_zero.mp (Nat.le_zero.mp (hm j hj))
          rw [h0]
          exact Finset.empty_subset V
        rw [hJ]
        simp
  have L_multi_aux2 : ∀ (α : Type) [Fintype α] [DecidableEq α] (J J' : Finset (Finset α))
      (G G' : Finset α → Finset α) (W V : Finset α)
      (hsub : J' ⊆ J) (hback : ∀ j ∈ J', ∃ j₀ ∈ J, G j₀ ⊆ W ∪ G' j), (if ∃ j ∈ J, G j ⊆ W ∪ V then (0 : ℝ) else (J.card : ℝ)) ≤
        ((J \ J').card : ℝ) + (if ∃ j ∈ J', G' j ⊆ V then (0 : ℝ) else (J'.card : ℝ)) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (J J' : Finset (Finset α))
        (G G' : Finset α → Finset α) (W V : Finset α)
        (hsub : J' ⊆ J) (hback : ∀ j ∈ J', ∃ j₀ ∈ J, G j₀ ⊆ W ∪ G' j) => by
      by_cases h : ∃ j ∈ J', G' j ⊆ V
      · obtain ⟨j, hj, hjV⟩ := h
        obtain ⟨j₀, hj₀, hG⟩ := hback j hj
        have h' : ∃ j ∈ J, G j ⊆ W ∪ V :=
          ⟨j₀, hj₀, hG.trans (Finset.union_subset_union (Finset.Subset.refl W) hjV)⟩
        rw [if_pos h', if_pos ⟨j, hj, hjV⟩]
        simp
      · rw [if_neg h]
        have hc : ((J \ J').card : ℝ) + (J'.card : ℝ) = (J.card : ℝ) := by
          rw [← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hsub]
        rw [hc]
        split_ifs
        · exact Nat.cast_nonneg _
        · exact le_refl _
  have L_multi_aux3 : ∀ (x N : ℝ) (m : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hN : 0 ≤ N)
      (hm : 1 ≤ m), N * x ^ (m / 2 + 1) + N * (2 * x - 2 * x ^ (m / 2 + 1)) ≤ N * (2 * x - 2 * x ^ (m + 1)) :=
    fun (x N : ℝ) (m : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hN : 0 ≤ N)
        (hm : 1 ≤ m) => by
      have hk : m + 1 = (m / 2 + 1) + (m - m / 2) := by omega
      have h1 : x ^ (m - m / 2) ≤ x := by
        calc x ^ (m - m / 2) ≤ x ^ 1 := pow_le_pow_of_le_one hx0 (by linarith) (by omega)
          _ = x := pow_one x
      have h2 : 2 * x ^ (m + 1) ≤ x ^ (m / 2 + 1) := by
        rw [hk, pow_add x (m / 2 + 1) (m - m / 2)]
        have h3 : 0 ≤ x ^ (m / 2 + 1) := pow_nonneg hx0 _
        have h4 : x ^ (m - m / 2) ≤ 1 / 2 := le_trans h1 hx1
        have h5 := mul_le_mul_of_nonneg_left h4 h3
        linarith
      have h6 := mul_le_mul_of_nonneg_left h2 hN
      linarith
  have L_multi_aux4 : ∀ (α : Type) [Fintype α] [DecidableEq α] (p κ N q : ℝ)
      (J : Finset (Finset α)) (G : Finset α → Finset α)
      (hmJ : ∀ j ∈ J, (G j).card ≤ 0), ∑ V : Finset α, q ^ V.card * (1 - q) ^ (Fintype.card α - V.card) *
          (if ∃ j ∈ J, G j ⊆ V then (0 : ℝ) else (J.card : ℝ))
        ≤ N * (2 * (4 / (p * κ)) - 2 * (4 / (p * κ)) ^ (0 + 1)) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p κ N q : ℝ)
        (J : Finset (Finset α)) (G : Finset α → Finset α)
        (hmJ : ∀ j ∈ J, (G j).card ≤ 0) => by
      rw [Finset.sum_eq_zero (fun V _ => by rw [L_multi_aux1 α J G hmJ V, mul_zero])]
      simp
  have L_multi_aux5 : ∀ (α : Type) [Fintype α] (a c B : ℝ) (μ h g : Finset α → ℝ)
      (ha : 0 ≤ a) (hμ : ∀ V, 0 ≤ μ V) (hmass : ∑ V, μ V = 1)
      (hpt : ∀ V, h V ≤ c + g V) (hB : ∑ V, μ V * g V ≤ B), ∑ V, a * μ V * h V ≤ a * c + a * B :=
    fun (α : Type) [Fintype α] (a c B : ℝ) (μ h g : Finset α → ℝ)
        (ha : 0 ≤ a) (hμ : ∀ V, 0 ≤ μ V) (hmass : ∑ V, μ V = 1)
        (hpt : ∀ V, h V ≤ c + g V) (hB : ∑ V, μ V * g V ≤ B) => by
      calc ∑ V, a * μ V * h V ≤ ∑ V, (a * c * μ V + a * (μ V * g V)) := by
            apply Finset.sum_le_sum
            intro V _
            have e : a * c * μ V + a * (μ V * g V) = a * μ V * (c + g V) := by ring
            rw [e]
            exact mul_le_mul_of_nonneg_left (hpt V) (mul_nonneg ha (hμ V))
        _ = a * c * ∑ V, μ V + a * ∑ V, μ V * g V := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ a * c + a * B := by
            rw [hmass]
            have := mul_le_mul_of_nonneg_left hB ha
            linarith
  have L_multi_aux6 : ∀ (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ)
      (hp0 : 0 < p) (hp1 : p < 1) (hκ : 8 ≤ p * κ) (ℓ : ℕ), ∀ (m : ℕ), m < 2 ^ ℓ → ∀ (q : ℝ), 0 ≤ q → q ≤ 1 → 1 - q ≤ (1 - p) ^ ℓ →
      ∀ (J : Finset (Finset α)) (G : Finset α → Finset α),
      (∀ j ∈ J, (G j).card ≤ m) →
      (∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N) →
      ∑ V : Finset α, q ^ V.card * (1 - q) ^ (Fintype.card α - V.card) *
          (if ∃ j ∈ J, G j ⊆ V then (0 : ℝ) else (J.card : ℝ))
        ≤ N * (2 * (4 / (p * κ)) - 2 * (4 / (p * κ)) ^ (m + 1)) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p κ N : ℝ)
        (hp0 : 0 < p) (hp1 : p < 1) (hκ : 8 ≤ p * κ) (ℓ : ℕ) => by
      induction ℓ with
      | zero =>
        intro m hm q _ _ _ J G hmJ _
        have hm0 : m = 0 := by simp at hm; omega
        subst hm0
        exact L_multi_aux4 α p κ N q J G hmJ
      | succ ℓ ih =>
        intro m hm q hq0 hq1 hq J G hmJ hspread
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · subst hm0
          exact L_multi_aux4 α p κ N q J G hmJ
        have hN : 0 ≤ N := by
          have h0 := hspread ∅
          simp only [Finset.empty_subset, Finset.filter_true_of_mem, Finset.card_empty, pow_zero,
            mul_one, implies_true] at h0
          exact le_trans (Nat.cast_nonneg _) h0
        have hκ0 : 0 < κ := by
          by_contra h
          push_neg at h
          nlinarith
        have h1p : 0 < 1 - p := by linarith
        have h1p' : 1 - p ≠ 0 := ne_of_gt h1p
        have hqp : p ≤ q := by
          have h7 : (1 - p) ^ (ℓ + 1) ≤ 1 - p := by
            rw [pow_succ]
            have h8 : (1 - p) ^ ℓ ≤ 1 := pow_le_one₀ h1p.le (by linarith)
            have h9 := mul_le_mul_of_nonneg_right h8 h1p.le
            linarith
          linarith
        obtain ⟨q', hq'0, hq'1, hq'ℓ, hpq⟩ : ∃ q' : ℝ, 0 ≤ q' ∧ q' ≤ 1 ∧ 1 - q' ≤ (1 - p) ^ ℓ ∧
            p + q' - p * q' = q := by
          refine ⟨(q - p) / (1 - p), div_nonneg (by linarith) h1p.le, ?_, ?_, ?_⟩
          · rw [div_le_one h1p]
            linarith
          · have e : 1 - (q - p) / (1 - p) = (1 - q) / (1 - p) := by
              field_simp
              ring
            rw [e, div_le_iff₀ h1p, ← pow_succ]
            exact hq
          · have e : p + (q - p) / (1 - p) - p * ((q - p) / (1 - p))
                = p + (q - p) / (1 - p) * (1 - p) := by ring
            rw [e, div_mul_cancel₀ _ h1p']
            ring
        have hU := L_union α p q' (fun V => if ∃ j ∈ J, G j ⊆ V then (0 : ℝ) else (J.card : ℝ))
        simp only [hpq] at hU
        rw [← hU]
        obtain ⟨J', G', hJ'sub, hG', hround⟩ :=
          L_round α p κ N m J G hp0 hp1.le (by linarith) hmJ hspread
        have hIH : ∀ W : Finset α, ∑ V : Finset α, q' ^ V.card * (1 - q') ^ (Fintype.card α - V.card) *
            (if ∃ j ∈ J' W, G' W j ⊆ V then (0 : ℝ) else ((J' W).card : ℝ))
            ≤ N * (2 * (4 / (p * κ)) - 2 * (4 / (p * κ)) ^ (m / 2 + 1)) := by
          intro W
          apply ih (m / 2) (by rw [pow_succ] at hm; omega) q' hq'0 hq'1 hq'ℓ (J' W) (G' W)
          · intro j hj
            exact (hG' W j hj).2.1
          · intro T
            refine le_trans ?_ (hspread T)
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg hκ0.le _)
            have hsubf : (J' W).filter (fun j => T ⊆ G' W j) ⊆ J.filter (fun j => T ⊆ G j) := by
              intro j hj
              rw [Finset.mem_filter] at hj ⊢
              exact ⟨hJ'sub W hj.1, hj.2.trans (hG' W j hj.1).1⟩
            exact_mod_cast Finset.card_le_card hsubf
        have hW : ∀ W : Finset α, ∑ V : Finset α,
            (p ^ W.card * (1 - p) ^ (Fintype.card α - W.card)) *
            (q' ^ V.card * (1 - q') ^ (Fintype.card α - V.card)) *
            (if ∃ j ∈ J, G j ⊆ W ∪ V then (0 : ℝ) else (J.card : ℝ))
            ≤ p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) * ((J \ J' W).card : ℝ) +
              p ^ W.card * (1 - p) ^ (Fintype.card α - W.card) *
                (N * (2 * (4 / (p * κ)) - 2 * (4 / (p * κ)) ^ (m / 2 + 1))) := by
          intro W
          exact L_multi_aux5 α (p ^ W.card * (1 - p) ^ (Fintype.card α - W.card))
            ((J \ J' W).card : ℝ) (N * (2 * (4 / (p * κ)) - 2 * (4 / (p * κ)) ^ (m / 2 + 1)))
            (fun V => q' ^ V.card * (1 - q') ^ (Fintype.card α - V.card))
            (fun V => if ∃ j ∈ J, G j ⊆ W ∪ V then (0 : ℝ) else (J.card : ℝ))
            (fun V => if ∃ j ∈ J' W, G' W j ⊆ V then (0 : ℝ) else ((J' W).card : ℝ))
            (mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg h1p.le _))
            (fun V => mul_nonneg (pow_nonneg hq'0 _) (pow_nonneg (by linarith) _))
            (L_mass α q')
            (fun V => L_multi_aux2 α J (J' W) G (G' W) W V (hJ'sub W)
              (fun j hj => (hG' W j hj).2.2))
            (hIH W)
        refine le_trans (Finset.sum_le_sum (fun W _ => hW W)) ?_
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, L_mass α p, one_mul]
        have hx0 : 0 ≤ 4 / (p * κ) := div_nonneg (by norm_num) (by linarith)
        have hx1 : 4 / (p * κ) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
        have hfin := L_multi_aux3 (4 / (p * κ)) N m hx0 hx1 hN hmpos
        linarith
  have L_multi : ∀ (α : Type) [Fintype α] [DecidableEq α] (p κ : ℝ)
      (hp0 : 0 < p) (hp1 : p < 1) (hκ : 8 ≤ p * κ) (ℓ m : ℕ) (hmℓ : m < 2 ^ ℓ)
      (q N : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : 1 - q ≤ (1 - p) ^ ℓ)
      (J : Finset (Finset α)) (G : Finset α → Finset α)
      (hm : ∀ j ∈ J, (G j).card ≤ m)
      (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N), ∑ V : Finset α, q ^ V.card * (1 - q) ^ (Fintype.card α - V.card) *
          (if ∃ j ∈ J, G j ⊆ V then (0 : ℝ) else (J.card : ℝ))
        ≤ N * (8 / (p * κ)) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (p κ : ℝ)
        (hp0 : 0 < p) (hp1 : p < 1) (hκ : 8 ≤ p * κ) (ℓ m : ℕ) (hmℓ : m < 2 ^ ℓ)
        (q N : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : 1 - q ≤ (1 - p) ^ ℓ)
        (J : Finset (Finset α)) (G : Finset α → Finset α)
        (hm : ∀ j ∈ J, (G j).card ≤ m)
        (hspread : ∀ T : Finset α, ((J.filter (fun j => T ⊆ G j)).card : ℝ) * κ ^ T.card ≤ N) => by
      have hN : 0 ≤ N := by
        have h0 := hspread ∅
        simp only [Finset.empty_subset, Finset.filter_true_of_mem, Finset.card_empty, pow_zero,
          mul_one, implies_true] at h0
        exact le_trans (Nat.cast_nonneg _) h0
      have h := L_multi_aux6 α p κ N hp0 hp1 hκ ℓ m hmℓ q hq0 hq1 hq J G hm hspread
      have hx0 : 0 ≤ 4 / (p * κ) := div_nonneg (by norm_num) (by linarith)
      have hpow : 0 ≤ (4 / (p * κ)) ^ (m + 1) := pow_nonneg hx0 _
      have e : 8 / (p * κ) = 2 * (4 / (p * κ)) := by ring
      rw [e]
      have h2 := mul_le_mul_of_nonneg_left
        (show 2 * (4 / (p * κ)) - 2 * (4 / (p * κ)) ^ (m + 1) ≤ 2 * (4 / (p * κ)) by linarith) hN
      linarith
  have L_spread : ∀ (α : Type) [Fintype α] [DecidableEq α] (r w : ℕ) (κ : ℝ)
      (F : Finset (Finset α)) (hr : 2 ≤ r)
      (hκ : 16 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1) ≤ κ)
      (hw : ∀ A ∈ F, A.card ≤ w) (hF : F.Nonempty)
      (hspread : ∀ T : Finset α, ((F.filter (fun A => T ⊆ A)).card : ℝ) * κ ^ T.card ≤ F.card), ∑ V : Finset α, (1 / (r : ℝ)) ^ V.card * (1 - 1 / (r : ℝ)) ^ (Fintype.card α - V.card) *
          (if ∃ A ∈ F, A ⊆ V then (0 : ℝ) else 1) < 1 / (r : ℝ) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (r w : ℕ) (κ : ℝ)
        (F : Finset (Finset α)) (hr : 2 ≤ r)
        (hκ : 16 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1) ≤ κ)
        (hw : ∀ A ∈ F, A.card ≤ w) (hF : F.Nonempty)
        (hspread : ∀ T : Finset α, ((F.filter (fun A => T ⊆ A)).card : ℝ) * κ ^ T.card ≤ F.card) => by
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, ℓ = Nat.log 2 w + 1 := ⟨_, rfl⟩
      have hℓR : (ℓ : ℝ) = (Nat.log 2 w : ℝ) + 1 := by rw [hℓ]; exact Nat.cast_succ _
      have hlog0 : (0 : ℝ) ≤ (Nat.log 2 w : ℝ) := Nat.cast_nonneg _
      have hr2 : (2 : ℝ) ≤ r := Nat.ofNat_le_cast.mpr hr
      have hr0 : (0 : ℝ) < r := lt_of_lt_of_le two_pos hr2
      have hℓ1 : (1 : ℝ) ≤ ℓ := by rw [hℓR]; exact le_add_of_nonneg_left hlog0
      have hℓ0' : (ℓ : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hℓ1)
      have hrℓ : (2 : ℝ) ≤ (r : ℝ) * ℓ :=
        le_trans (le_of_eq (mul_one 2).symm) (mul_le_mul hr2 hℓ1 zero_le_one hr0.le)
      have hrℓ0 : (0 : ℝ) < (r : ℝ) * ℓ := mul_pos hr0 (lt_of_lt_of_le one_pos hℓ1)
      -- p := 1/(rℓ)
      obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 1 / ((r : ℝ) * ℓ) := ⟨_, rfl⟩
      have hp0 : 0 < p := hpdef ▸ one_div_pos.mpr hrℓ0
      have hp1 : p < 1 := hpdef ▸ (div_lt_one hrℓ0).mpr (one_lt_two.trans_le hrℓ)
      have hκ16 : 16 * (r : ℝ) ≤ p * κ := by
        rw [hpdef, one_div_mul_eq_div, le_div_iff₀ hrℓ0]
        have e : 16 * (r : ℝ) * ((r : ℝ) * ℓ) = 16 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1) := by
          rw [hℓR]; ring
        rw [e]; exact hκ
      have hpκ : 8 ≤ p * κ := by linarith only [hκ16, hr2]
      have hpκpos : 0 < p * κ := lt_of_lt_of_le (by norm_num) hpκ
      have hwℓ : w < 2 ^ ℓ := by rw [hℓ]; exact Nat.lt_pow_succ_log_self (by norm_num) w
      -- q := 1/r
      obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 / (r : ℝ) := ⟨_, rfl⟩
      have hq0 : 0 ≤ q := hqdef ▸ one_div_nonneg.mpr hr0.le
      have hq1 : q ≤ 1 := hqdef ▸ (div_le_one hr0).mpr (one_le_two.trans hr2)
      have hq : 1 - q ≤ (1 - p) ^ ℓ := by
        have hb := one_add_mul_le_pow (neg_le_neg (hp1.le.trans one_le_two)) ℓ
        have h1 : (ℓ : ℝ) * p = q := by
          rw [hpdef, hqdef, mul_one_div, div_mul_cancel_right₀ hℓ0', one_div]
        rw [mul_neg, h1, ← sub_eq_add_neg, ← sub_eq_add_neg] at hb
        exact hb
      have hmulti : ∑ V : Finset α, q ^ V.card * (1 - q) ^ (Fintype.card α - V.card) *
            (if ∃ A ∈ F, A ⊆ V then (0 : ℝ) else (F.card : ℝ)) ≤ (F.card : ℝ) * (8 / (p * κ)) :=
        L_multi α p κ hp0 hp1 hpκ ℓ w hwℓ q (F.card : ℝ) hq0 hq1 hq F (fun A => A) hw hspread
      have hFpos : (0 : ℝ) < F.card := Nat.cast_pos.mpr hF.card_pos
      have hsum_eq : ∑ V : Finset α, q ^ V.card * (1 - q) ^ (Fintype.card α - V.card) *
            (if ∃ A ∈ F, A ⊆ V then (0 : ℝ) else (F.card : ℝ))
          = (F.card : ℝ) * ∑ V : Finset α, q ^ V.card * (1 - q) ^ (Fintype.card α - V.card) *
            (if ∃ A ∈ F, A ⊆ V then (0 : ℝ) else 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun V _ => ?_)
        split_ifs
        · rw [mul_zero, mul_zero]
        · rw [mul_one, mul_comm]
      have hS : ∑ V : Finset α, q ^ V.card * (1 - q) ^ (Fintype.card α - V.card) *
            (if ∃ A ∈ F, A ⊆ V then (0 : ℝ) else 1) ≤ 8 / (p * κ) := by
        rw [hsum_eq] at hmulti
        exact le_of_mul_le_mul_left hmulti hFpos
      have hfin : 8 / (p * κ) < q := by
        rw [hqdef, div_lt_div_iff₀ hpκpos hr0]
        linarith only [hκ16, hr0]
      rw [← hqdef]
      exact lt_of_le_of_lt hS hfin
  have L_disjoint_aux1 : ∀ (r : ℕ) (hr : 2 ≤ r) (n k : ℕ) (hk : k ≤ n), ((r : ℝ) - 1) ^ (n - k) = (r : ℝ) ^ n * ((1 / (r : ℝ)) ^ k * (1 - 1 / (r : ℝ)) ^ (n - k)) :=
    fun (r : ℕ) (hr : 2 ≤ r) (n k : ℕ) (hk : k ≤ n) => by
      have hr0 : (r : ℝ) ≠ 0 := by
        have : (2 : ℝ) ≤ r := by exact_mod_cast hr
        linarith
      have hn : (r : ℝ) ^ n = (r : ℝ) ^ k * (r : ℝ) ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hk]
      rw [hn]
      have h1 : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
      have h2 : (r : ℝ) * (1 - 1 / (r : ℝ)) = (r : ℝ) - 1 := by field_simp
      calc ((r : ℝ) - 1) ^ (n - k)
            = ((r : ℝ) * (1 / (r : ℝ))) ^ k * ((r : ℝ) * (1 - 1 / (r : ℝ))) ^ (n - k) := by
              rw [h1, h2, one_pow, one_mul]
        _ = (r : ℝ) ^ k * (r : ℝ) ^ (n - k) * ((1 / (r : ℝ)) ^ k * (1 - 1 / (r : ℝ)) ^ (n - k)) := by
              rw [mul_pow, mul_pow]; ring
  have L_disjoint_aux2 : ∀ (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (hr : 2 ≤ r)
      (F : Finset (Finset α)) (c : Fin r), ∑ χ : α → Fin r, (if ∃ A ∈ F, A ⊆ Finset.univ.filter (fun x => χ x = c) then (0 : ℝ) else 1)
        = (r : ℝ) ^ (Fintype.card α) * ∑ V : Finset α, (1 / (r : ℝ)) ^ V.card *
            (1 - 1 / (r : ℝ)) ^ (Fintype.card α - V.card) *
            (if ∃ A ∈ F, A ⊆ V then (0 : ℝ) else 1) :=
    fun (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (hr : 2 ≤ r)
        (F : Finset (Finset α)) (c : Fin r) => by
      rw [← Finset.sum_fiberwise' Finset.univ
        (fun χ : α → Fin r => Finset.univ.filter (fun x => χ x = c))
        (fun V : Finset α => (if ∃ A ∈ F, A ⊆ V then (0 : ℝ) else 1))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun V _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul, L_colorcount]
      rw [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      rw [L_disjoint_aux1 r hr _ _ (Finset.card_le_univ V)]
      ring
  have L_disjoint_aux3 : ∀ (r n : ℕ) (hr : 2 ≤ r) (P : ℝ) (hP : P < 1 / (r : ℝ))
      (hle : (r : ℝ) ^ n ≤ (r : ℝ) * ((r : ℝ) ^ n * P)), False :=
    fun (r n : ℕ) (hr : 2 ≤ r) (P : ℝ) (hP : P < 1 / (r : ℝ))
        (hle : (r : ℝ) ^ n ≤ (r : ℝ) * ((r : ℝ) ^ n * P)) => by
      have hrpos : (0 : ℝ) < r := by
        have : (2 : ℝ) ≤ r := by exact_mod_cast hr
        linarith
      have hrn : (0 : ℝ) < (r : ℝ) ^ n := pow_pos hrpos _
      have hlt : (r : ℝ) * ((r : ℝ) ^ n * P) < (r : ℝ) * ((r : ℝ) ^ n * (1 / (r : ℝ))) := by
        apply mul_lt_mul_of_pos_left _ hrpos
        exact mul_lt_mul_of_pos_left hP hrn
      have heq : (r : ℝ) * ((r : ℝ) ^ n * (1 / (r : ℝ))) = (r : ℝ) ^ n := by
        field_simp
      linarith
  have L_disjoint : ∀ (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (F : Finset (Finset α))
      (hr : 2 ≤ r) (hne : ∀ A ∈ F, A.Nonempty)
      (hprob : ∑ V : Finset α, (1 / (r : ℝ)) ^ V.card * (1 - 1 / (r : ℝ)) ^ (Fintype.card α - V.card) *
          (if ∃ A ∈ F, A ⊆ V then (0 : ℝ) else 1) < 1 / (r : ℝ)), ∃ S ⊆ F, S.card = r ∧ ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint A B :=
    fun (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (F : Finset (Finset α))
        (hr : 2 ≤ r) (hne : ∀ A ∈ F, A.Nonempty)
        (hprob : ∑ V : Finset α, (1 / (r : ℝ)) ^ V.card * (1 - 1 / (r : ℝ)) ^ (Fintype.card α - V.card) *
            (if ∃ A ∈ F, A ⊆ V then (0 : ℝ) else 1) < 1 / (r : ℝ)) => by
      have hgood : ∃ χ : α → Fin r, ∀ c : Fin r, ∃ A ∈ F, A ⊆ Finset.univ.filter (fun x => χ x = c) := by
        by_contra hcon
        have hle : ∑ χ : α → Fin r, (1 : ℝ) ≤ ∑ χ : α → Fin r, ∑ c : Fin r,
            (if ∃ A ∈ F, A ⊆ Finset.univ.filter (fun x => χ x = c) then (0 : ℝ) else 1) := by
          refine Finset.sum_le_sum (fun χ _ => ?_)
          obtain ⟨c, hc⟩ := not_forall.mp (not_exists.mp hcon χ)
          calc (1 : ℝ)
              = (if ∃ A ∈ F, A ⊆ Finset.univ.filter (fun x => χ x = c) then (0 : ℝ) else 1) := by
                rw [if_neg hc]
            _ ≤ ∑ c : Fin r,
                (if ∃ A ∈ F, A ⊆ Finset.univ.filter (fun x => χ x = c) then (0 : ℝ) else 1) := by
                refine Finset.single_le_sum
                  (f := fun c => (if ∃ A ∈ F, A ⊆ Finset.univ.filter (fun x => χ x = c)
                    then (0 : ℝ) else 1)) (fun i _ => ?_) (Finset.mem_univ c)
                dsimp only
                split_ifs <;> norm_num
        rw [Finset.sum_comm] at hle
        simp only [L_disjoint_aux2 α r hr F] at hle
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, mul_one, Nat.cast_pow] at hle
        exact L_disjoint_aux3 r (Fintype.card α) hr _ hprob hle
      obtain ⟨χ, hχ⟩ := hgood
      choose A hAF hAsub using hχ
      have hdisj : ∀ c d : Fin r, c ≠ d → Disjoint (A c) (A d) := by
        intro c d hcd
        rw [Finset.disjoint_left]
        intro x hxc hxd
        have h1 := hAsub c hxc
        have h2 := hAsub d hxd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact hcd (h1.symm.trans h2)
      have hinj : Function.Injective A := by
        intro c d hcd
        by_contra hcd'
        have h := hdisj c d hcd'
        rw [hcd, Finset.disjoint_self_iff_empty] at h
        exact (hne (A d) (hAF d)).ne_empty h
      refine ⟨Finset.univ.image A, ?_, ?_, ?_⟩
      · intro B hB
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hB
        exact hAF c
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      · intro B hB B' hB' hBB'
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hB
        obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hB'
        exact hdisj c d (fun h => hBB' (by rw [h]))
  have L_spreadcase : ∀ (α : Type) [Fintype α] [DecidableEq α] (r w : ℕ) (K : ℝ)
      (F : Finset (Finset α)) (hr : 2 ≤ r)
      (hK : 32 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1) ≤ K)
      (hw : ∀ A ∈ F, A.card ≤ w) (hF : 2 ≤ F.card)
      (hsp : ∀ T : Finset α, T.Nonempty →
        ((F.filter (fun A => T ⊆ A)).card : ℝ) * K ^ T.card ≤ F.card), ∃ S ⊆ F, S.card = r ∧ ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint A B :=
    fun (α : Type) [Fintype α] [DecidableEq α] (r w : ℕ) (K : ℝ)
        (F : Finset (Finset α)) (hr : 2 ≤ r)
        (hK : 32 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1) ≤ K)
        (hw : ∀ A ∈ F, A.card ≤ w) (hF : 2 ≤ F.card)
        (hsp : ∀ T : Finset α, T.Nonempty →
          ((F.filter (fun A => T ⊆ A)).card : ℝ) * K ^ T.card ≤ F.card) => by
      classical
      obtain ⟨G, hGdef⟩ : ∃ G : Finset (Finset α), G = F.erase ∅ := ⟨_, rfl⟩
      have hGF : G ⊆ F := by rw [hGdef]; exact Finset.erase_subset _ _
      have hGcard : F.card ≤ G.card + 1 := by
        have := Finset.pred_card_le_card_erase (s := F) (a := ∅)
        rw [← hGdef] at this
        omega
      have hGpos : 1 ≤ G.card := by omega
      have hGne : G.Nonempty := Finset.card_pos.mp (by omega)
      have hne : ∀ A ∈ G, A.Nonempty := by
        intro A hA
        rw [hGdef, Finset.mem_erase] at hA
        exact Finset.nonempty_iff_ne_empty.mpr hA.1
      have hwG : ∀ A ∈ G, A.card ≤ w := fun A hA => hw A (hGF hA)
      have hKpos : 0 < K := by
        have : (0:ℝ) < 32 * (r:ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1) := by
          have : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
          positivity
        linarith
      have hκ : 16 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1) ≤ K / 2 := by linarith
      have hspG : ∀ T : Finset α,
          ((G.filter (fun A => T ⊆ A)).card : ℝ) * (K / 2) ^ T.card ≤ G.card := by
        intro T
        rcases T.eq_empty_or_nonempty with hT | hT
        · subst hT
          simp
        · have h1 : ((G.filter (fun A => T ⊆ A)).card : ℝ) ≤ (F.filter (fun A => T ⊆ A)).card := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hGF)
          have h2 := hsp T hT
          have h3 : (2:ℝ) ≤ 2 ^ T.card := by
            have : 1 ≤ T.card := Finset.card_pos.mpr hT
            calc (2:ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ T.card := pow_le_pow_right₀ (by norm_num) this
          have hFG : (F.card : ℝ) ≤ 2 * G.card := by
            have h4 : (F.card : ℝ) ≤ G.card + 1 := by exact_mod_cast hGcard
            have h5 : (1:ℝ) ≤ G.card := by exact_mod_cast hGpos
            linarith
          rw [div_pow]
          have h2T : 0 < (2:ℝ) ^ T.card := by positivity
          have hKT : 0 < K ^ T.card := pow_pos hKpos _
          calc ((G.filter (fun A => T ⊆ A)).card : ℝ) * (K ^ T.card / 2 ^ T.card)
              ≤ (F.filter (fun A => T ⊆ A)).card * (K ^ T.card / 2 ^ T.card) := by
                apply mul_le_mul_of_nonneg_right h1; positivity
            _ = ((F.filter (fun A => T ⊆ A)).card * K ^ T.card) / 2 ^ T.card := by ring
            _ ≤ F.card / 2 ^ T.card := by apply div_le_div_of_nonneg_right h2 h2T.le
            _ ≤ F.card / 2 := by apply div_le_div_of_nonneg_left (by positivity) (by norm_num) h3
            _ ≤ G.card := by linarith
      have hprob := L_spread α r w (K / 2) G hr hκ hwG hGne hspG
      obtain ⟨S, hSG, hScard, hSdisj⟩ := L_disjoint α r G hr hne hprob
      exact ⟨S, hSG.trans hGF, hScard, hSdisj⟩
  have L_link_card : ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)) (T : Finset α), ((F.filter (fun A => T ⊆ A)).image (fun A => A \ T)).card
        = (F.filter (fun A => T ⊆ A)).card :=
    fun (α : Type) [DecidableEq α] (F : Finset (Finset α)) (T : Finset α) => by
      apply Finset.card_image_of_injOn
      intro A hA B hB hAB
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hA hB
      have h1 : A = (A \ T) ∪ T := (Finset.sdiff_union_of_subset hA.2).symm
      have h2 : B = (B \ T) ∪ T := (Finset.sdiff_union_of_subset hB.2).symm
      simp only at hAB
      rw [h1, h2, hAB]
  have L_link : ∀ (α : Type) [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) (T : Finset α)
      (S' : Finset (Finset α))
      (hS' : S' ⊆ (F.filter (fun A => T ⊆ A)).image (fun A => A \ T))
      (hcard : S'.card = r)
      (hsf : ∀ A ∈ S', ∀ B ∈ S', A ≠ B → ∀ C ∈ S', ∀ D ∈ S', C ≠ D → A ∩ B = C ∩ D), ∃ S ⊆ F, S.card = r ∧
        ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ C ∈ S, ∀ D ∈ S, C ≠ D → A ∩ B = C ∩ D :=
    fun (α : Type) [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) (T : Finset α)
        (S' : Finset (Finset α))
        (hS' : S' ⊆ (F.filter (fun A => T ⊆ A)).image (fun A => A \ T))
        (hcard : S'.card = r)
        (hsf : ∀ A ∈ S', ∀ B ∈ S', A ≠ B → ∀ C ∈ S', ∀ D ∈ S', C ≠ D → A ∩ B = C ∩ D) => by
      have hdisj : ∀ B ∈ S', Disjoint B T := by
        intro B hB
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (hS' hB)
        exact Finset.sdiff_disjoint
      have hmemF : ∀ B ∈ S', B ∪ T ∈ F := by
        intro B hB
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (hS' hB)
        rw [Finset.mem_filter] at hA
        rw [Finset.sdiff_union_of_subset hA.2]
        exact hA.1
      have hinj : Set.InjOn (fun B => B ∪ T) (S' : Set (Finset α)) := by
        intro B1 hB1 B2 hB2 h
        simp only at h
        have e1 : (B1 ∪ T) \ T = B1 := by
          rw [Finset.union_sdiff_right]; exact (hdisj B1 hB1).sdiff_eq_left
        have e2 : (B2 ∪ T) \ T = B2 := by
          rw [Finset.union_sdiff_right]; exact (hdisj B2 hB2).sdiff_eq_left
        rw [← e1, ← e2, h]
      refine ⟨S'.image (fun B => B ∪ T), ?_, ?_, ?_⟩
      · intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        exact hmemF B hB
      · rw [Finset.card_image_of_injOn hinj, hcard]
      · intro A hA B hB hAB C hC D hD hCD
        obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
        obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hC
        obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hD
        have hAB' : A' ≠ B' := fun h => hAB (h ▸ rfl)
        have hCD' : C' ≠ D' := fun h => hCD (h ▸ rfl)
        rw [← Finset.inter_union_distrib_right, ← Finset.inter_union_distrib_right,
          hsf A' hA' B' hB' hAB' C' hC' D' hD' hCD']
  have L_core_aux1 : ∀ (α : Type) [Fintype α] [DecidableEq α] (r w : ℕ) (hr : 2 ≤ r) (w' : ℕ), w' ≤ w → ∀ F : Finset (Finset α), (∀ A ∈ F, A.card ≤ w') →
        (32 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1)) ^ w' < F.card →
        ∃ S ⊆ F, S.card = r ∧
          ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ C ∈ S, ∀ D ∈ S, C ≠ D → A ∩ B = C ∩ D :=
    fun (α : Type) [Fintype α] [DecidableEq α] (r w : ℕ) (hr : 2 ≤ r) (w' : ℕ) => by
      induction w' using Nat.strong_induction_on with
      | _ w' ih =>
      intro hw'w F hw' hF
      set K : ℝ := 32 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1) with hKdef
      have hr' : (2:ℝ) ≤ r := by exact_mod_cast hr
      have hlog : (0:ℝ) ≤ (Nat.log 2 w : ℝ) := Nat.cast_nonneg _
      have hK1 : 1 ≤ K := by
        have h4 : (4:ℝ) ≤ (r:ℝ) ^ 2 := by nlinarith
        have h1 : (1:ℝ) ≤ (Nat.log 2 w : ℝ) + 1 := by linarith
        have h41 : (4:ℝ) * 1 ≤ (r:ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1) :=
          mul_le_mul h4 h1 (by norm_num) (by positivity)
        have hK' : K = 32 * ((r:ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1)) := by rw [hKdef]; ring
        rw [hK']
        linarith
      by_cases hsp : ∀ T : Finset α, T.Nonempty →
          ((F.filter (fun A => T ⊆ A)).card : ℝ) * K ^ T.card ≤ F.card
      · -- spread 分支
        have hKw' : (1:ℝ) ≤ K ^ w' := one_le_pow₀ hK1
        have h2 : 2 ≤ F.card := by
          have h3 : (1:ℝ) < F.card := lt_of_le_of_lt hKw' hF
          have h4 : 1 < F.card := by exact_mod_cast h3
          omega
        have hK' : 32 * (r : ℝ) ^ 2 * ((Nat.log 2 w' : ℝ) + 1) ≤ K := by
          have hl : Nat.log 2 w' ≤ Nat.log 2 w := Nat.log_mono_right hw'w
          have hl' : (Nat.log 2 w' : ℝ) ≤ (Nat.log 2 w : ℝ) := by exact_mod_cast hl
          have hr2 : (0:ℝ) ≤ 32 * (r:ℝ) ^ 2 := by positivity
          rw [hKdef]
          exact mul_le_mul_of_nonneg_left (by linarith) hr2
        obtain ⟨S, hSF, hScard, hSdisj⟩ := L_spreadcase α r w' K F hr hK' hw' h2 hsp
        refine ⟨S, hSF, hScard, ?_⟩
        intro A hA B hB hAB C hC D hD hCD
        rw [Finset.disjoint_iff_inter_eq_empty.mp (hSdisj A hA B hB hAB),
          Finset.disjoint_iff_inter_eq_empty.mp (hSdisj C hC D hD hCD)]
      · -- link 分支
        push_neg at hsp
        obtain ⟨T, hTne, hT⟩ := hsp
        have hFTne : (F.filter (fun A => T ⊆ A)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.card_empty, Nat.cast_zero, zero_mul] at hT
          exact absurd hT (not_lt.mpr (Nat.cast_nonneg _))
        obtain ⟨A0, hA0⟩ := hFTne
        rw [Finset.mem_filter] at hA0
        have hTw' : T.card ≤ w' := (Finset.card_le_card hA0.2).trans (hw' A0 hA0.1)
        have hT1 : 1 ≤ T.card := Finset.card_pos.mpr hTne
        have hLcard := L_link_card α F T
        have hLw : ∀ B ∈ (F.filter (fun A => T ⊆ A)).image (fun A => A \ T),
            B.card ≤ w' - T.card := by
          intro B hB
          rw [Finset.mem_image] at hB
          obtain ⟨A, hA, rfl⟩ := hB
          rw [Finset.mem_filter] at hA
          rw [Finset.card_sdiff_of_subset hA.2]
          have := hw' A hA.1
          omega
        have hpow : K ^ w' = K ^ (w' - T.card) * K ^ T.card := by
          rw [← pow_add, Nat.sub_add_cancel hTw']
        have hKTpos : 0 < K ^ T.card := pow_pos (by linarith) _
        have hLbig : K ^ (w' - T.card) <
            (((F.filter (fun A => T ⊆ A)).image (fun A => A \ T)).card : ℝ) := by
          rw [hLcard]
          have h1 : K ^ (w' - T.card) * K ^ T.card <
              ((F.filter (fun A => T ⊆ A)).card : ℝ) * K ^ T.card := by
            rw [← hpow]; exact hF.trans hT
          exact lt_of_mul_lt_mul_right h1 hKTpos.le
        have hlt : w' - T.card < w' := by omega
        obtain ⟨S', hS'L, hS'card, hS'sf⟩ :=
          ih (w' - T.card) hlt (by omega) _ hLw hLbig
        exact L_link α r F T S' hS'L hS'card hS'sf
  have L_core : ∀ (α : Type) [Fintype α] [DecidableEq α] (r w : ℕ) (F : Finset (Finset α))
      (hr : 2 ≤ r) (hw : ∀ A ∈ F, A.card ≤ w)
      (hF : (32 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1)) ^ w < F.card), ∃ S ⊆ F, S.card = r ∧
        ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ C ∈ S, ∀ D ∈ S, C ≠ D → A ∩ B = C ∩ D :=
    fun (α : Type) [Fintype α] [DecidableEq α] (r w : ℕ) (F : Finset (Finset α))
        (hr : 2 ≤ r) (hw : ∀ A ∈ F, A.card ≤ w)
        (hF : (32 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1)) ^ w < F.card) => by
      exact L_core_aux1 α r w hr w le_rfl F hw hF
  open Real in
  have L_real_aux1 : ∀ (r A L LL : ℝ) (hr : 3 ≤ r) (hA : A ≤ L) (hL1 : 1 ≤ L)
      (hLL : 10 / 189 ≤ LL), 32 * r ^ 2 * (A + 1) < 10000 * r ^ 3 * L * LL :=
    fun (r A L LL : ℝ) (hr : 3 ≤ r) (hA : A ≤ L) (hL1 : 1 ≤ L)
        (hLL : 10 / 189 ≤ LL) => by
      have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
      have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
      have hP : 0 < r ^ 2 * L := mul_pos (pow_pos hr0 2) hL0
      have h1 : 32 * r ^ 2 * (A + 1) ≤ 32 * r ^ 2 * (L + L) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hL1) (mul_nonneg (by norm_num) (pow_nonneg hr0.le 2))
      have h := mul_le_mul_of_nonneg_left hr hP.le
      have h3 : 10000 * r ^ 3 * L * (10 / 189) ≤ 10000 * r ^ 3 * L * LL :=
        mul_le_mul_of_nonneg_left hLL (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hr0.le 3)) hL0.le)
      linarith only [h1, h, h3, hP]
  open Real in
  have L_real : ∀ (r w : ℕ) (hr : 3 ≤ r) (hw : 2 ≤ w), (32 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1)) ^ w
        < ImprovedBoundsSunflowerLemma.lowerBound r 10000 w :=
    fun (r w : ℕ) (hr : 3 ≤ r) (hw : 2 ≤ w) => by
      have h19 : (0:ℝ) < Real.log 1.9 := Real.log_pos (by norm_num)
      have h19' : Real.log 1.9 ≤ 9 / 10 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      have hd0 : Real.log ((1.9:ℝ) / 2) ≤ -1 / 20 :=
        (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      have hd : Real.log 1.9 - Real.log 2 ≤ -1 / 20 :=
        (Real.log_div (x := 1.9) (y := 2) (by norm_num) two_ne_zero) ▸ hd0
      have hw0 : w ≠ 0 := by omega
      have hwR : (2:ℝ) ≤ (w:ℝ) := Nat.ofNat_le_cast.mpr hw
      have hlogw2 : Real.log 2 ≤ Real.log w := Real.log_le_log two_pos hwR
      have h' : ((2:ℝ) ^ (Nat.log 2 w)) ≤ (w:ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hw0
      have hk : ((Nat.log 2 w : ℕ) : ℝ) * Real.log 2 ≤ Real.log w :=
        (Real.log_pow _ _).symm.le.trans (Real.log_le_log (pow_pos two_pos _) h')
      have hkL : ((Nat.log 2 w : ℕ) : ℝ) ≤ Real.logb 1.9 w := (le_div_iff₀ h19).mpr
        ((mul_le_mul_of_nonneg_left (by linarith only [hd]) (Nat.cast_nonneg _)).trans hk)
      have hL1 : (21:ℝ) / 20 ≤ Real.logb 1.9 w :=
        (le_div_iff₀ h19).mpr (by linarith only [hd, h19', hlogw2])
      have hLpos : 0 < Real.logb 1.9 (w:ℝ) := lt_of_lt_of_le (by norm_num) hL1
      have hinv : (Real.logb 1.9 (w:ℝ))⁻¹ ≤ 20 / 21 := (inv_anti₀ (by norm_num) hL1).trans (by norm_num)
      have hlogL : (1:ℝ) / 21 ≤ Real.log (Real.logb 1.9 (w:ℝ)) := by
        have h1 := Real.one_sub_inv_le_log_of_pos hLpos
        linarith only [h1, hinv]
      have hLL : (10:ℝ) / 189 ≤ Real.logb 1.9 (Real.logb 1.9 (w:ℝ)) :=
        (le_div_iff₀ h19).mpr (by linarith only [h19', hlogL])
      have hr3 : (3:ℝ) ≤ (r:ℝ) := Nat.ofNat_le_cast.mpr hr
      exact pow_lt_pow_left₀ (L_real_aux1 (r:ℝ) _ _ _ hr3 hkL ((by norm_num : (1:ℝ) ≤ 21 / 20).trans hL1) hLL)
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (add_nonneg (Nat.cast_nonneg _) zero_le_one)) hw0
  have L_set : ∀ (n r w : ℕ) (ℱ : Set (Set (Fin n))) (hr : 3 ≤ r) (hw : 2 ≤ w)
      (h1 : ℱ.IsSystem w)
      (h2 : ImprovedBoundsSunflowerLemma.lowerBound r 10000 w ≤ (ℱ.ncard : ℝ)), ∃ S ⊆ ℱ, S.IsSunflower r :=
    fun (n r w : ℕ) (ℱ : Set (Set (Fin n))) (hr : 3 ≤ r) (hw : 2 ≤ w)
        (h1 : ℱ.IsSystem w)
        (h2 : ImprovedBoundsSunflowerLemma.lowerBound r 10000 w ≤ (ℱ.ncard : ℝ)) => by
      classical
      set F : Finset (Finset (Fin n)) :=
        Finset.univ.filter (fun A : Finset (Fin n) => (↑A : Set (Fin n)) ∈ ℱ) with hFdef
      have hmemF : ∀ A : Finset (Fin n), A ∈ F ↔ (↑A : Set (Fin n)) ∈ ℱ := by
        intro A
        rw [hFdef, Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
      have hℱ : ℱ = (fun A : Finset (Fin n) => (↑A : Set (Fin n))) '' (↑F : Set (Finset (Fin n))) := by
        ext X
        constructor
        · intro hX
          refine ⟨X.toFinset, ?_, ?_⟩
          · rw [Finset.mem_coe, hmemF, Set.coe_toFinset]
            exact hX
          · exact Set.coe_toFinset X
        · rintro ⟨A, hA, rfl⟩
          exact (hmemF A).1 (Finset.mem_coe.1 hA)
      have hcard : ℱ.ncard = F.card := by
        rw [hℱ, Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset]
      have hwF : ∀ A ∈ F, A.card ≤ w := by
        intro A hA
        have hle := h1 _ ((hmemF A).1 hA)
        rwa [Set.ncard_coe_finset] at hle
      have hK := L_real r w hr hw
      have hF' : (32 * (r : ℝ) ^ 2 * ((Nat.log 2 w : ℝ) + 1)) ^ w < F.card := by
        rw [← hcard]
        exact lt_of_lt_of_le hK h2
      obtain ⟨S₀, hS₀F, hS₀card, hS₀⟩ := L_core (Fin n) r w F (by omega) hwF hF'
      refine ⟨(fun A : Finset (Fin n) => (↑A : Set (Fin n))) '' (↑S₀ : Set (Finset (Fin n))),
        ?_, ?_, ?_⟩
      · rw [hℱ]
        exact Set.image_mono (Finset.coe_subset.2 hS₀F)
      · rw [Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset, hS₀card]
      · rintro _ ⟨A₀, hA₀, rfl⟩ _ ⟨B₀, hB₀, rfl⟩ hne
        have hA₀' : A₀ ∈ S₀ := Finset.mem_coe.1 hA₀
        have hB₀' : B₀ ∈ S₀ := Finset.mem_coe.1 hB₀
        have hAB : A₀ ≠ B₀ := by
          rintro rfl
          exact hne rfl
        ext x
        constructor
        · rintro ⟨hxA, hxB⟩
          rw [Set.mem_sInter]
          rintro _ ⟨C₀, hC₀, rfl⟩
          have hC₀' : C₀ ∈ S₀ := Finset.mem_coe.1 hC₀
          obtain ⟨D₀, hD₀, hDC⟩ := Finset.exists_mem_ne (by omega : 1 < S₀.card) C₀
          have heq := hS₀ A₀ hA₀' B₀ hB₀' hAB C₀ hC₀' D₀ hD₀ (Ne.symm hDC)
          have hx : x ∈ A₀ ∩ B₀ := Finset.mem_inter.2 ⟨Finset.mem_coe.1 hxA, Finset.mem_coe.1 hxB⟩
          rw [heq] at hx
          exact Finset.mem_coe.2 (Finset.mem_inter.1 hx).1
        · intro hx
          rw [Set.mem_sInter] at hx
          exact ⟨hx _ ⟨A₀, hA₀, rfl⟩, hx _ ⟨B₀, hB₀, rfl⟩⟩
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin X
  have hinj : Function.Injective (Set.image e : Set X → Set (Fin n)) :=
    Set.image_injective.mpr e.injective
  have h1 : ((Set.image e) '' ℱ).IsSystem w := by
    rintro _ ⟨A, hA, rfl⟩
    rw [Set.ncard_image_of_injective _ e.injective]
    exact hℱ₁ A hA
  have h2 : lowerBound r 10000 w ≤ (((Set.image e) '' ℱ).ncard : ℝ) := by
    rw [Set.ncard_image_of_injective _ hinj]
    exact hℱ₂
  obtain ⟨S', hS'sub, hS'card, hS'pw⟩ := L_set n r w ((Set.image e) '' ℱ) hr hw h1 h2
  have hpinj : Function.Injective (Set.preimage e : Set (Fin n) → Set X) :=
    Set.preimage_injective.mpr e.surjective
  refine ⟨(Set.preimage e) '' S', ?_, ?_, ?_⟩
  · rintro _ ⟨A', hA', rfl⟩
    obtain ⟨A, hA, rfl⟩ := hS'sub hA'
    rw [Set.preimage_image_eq A e.injective]
    exact hA
  · rw [Set.ncard_image_of_injective _ hpinj]
    exact hS'card
  · rintro _ ⟨A', hA', rfl⟩ _ ⟨B', hB', rfl⟩ hne
    have hne' : A' ≠ B' := fun h => hne (h ▸ rfl)
    have hAB := hS'pw hA' hB' hne'
    show e ⁻¹' A' ∩ e ⁻¹' B' = ⋂₀ (Set.preimage e '' S')
    rw [← Set.preimage_inter, hAB, Set.sInter_image, Set.preimage_sInter]

end ImprovedBoundsSunflowerLemma

end Submission
