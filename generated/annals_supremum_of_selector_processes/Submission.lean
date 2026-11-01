/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/

import Mathlib.Probability.Distributions.SetBernoulli
import Submission.Helpers
import ChallengeDeps
import Lean
/-!
# Main Statements from On a conjecture of Talagrand on selector processes and a consequence
# on positive empirical processes

We formalise the statements of the main results from J. Park and H. T. Pham,
`On a conjecture of Talagrand on selector processes and a consequence on positive empirical
processes`, Annals of Math, 199 (3) 2024.
-/


namespace Submission

open _root_.SupremumOfSelectorProcesses
set_option autoImplicit false

namespace SupremumOfSelectorProcesses

open MeasureTheory ProbabilityTheory Measure unitInterval Finset

open scoped NNReal ENNReal





/-- The constant `L` of Theorem 1.2. -/
noncomputable def L₂ : ℝ≥0 := 10 ^ 31

/-- The constant of Theorem 1.2 is positive. -/
theorem L₂_pos : L₂ > 0 := by unfold L₂; positivity

open Classical in
/--
Statement of Theorem 1.2:

There exists `L > 0` such that for any `0 < p < 1`, finite type `X`, and set `Λ` of functions from
`X` to `ℝ≥0` such that `0 < 𝔼[sup_{f ∈ Λ} ∑ i ∈ Xp, f i] < ∞`, the collection of sets

`{s ⊆ X | sup_{f ∈ Λ} ∑ i ∈ s, f i ≥ L * 𝔼[sup_{f ∈ Λ} ∑ i ∈ Xp, f i]}`

is `p-small`, where `Xp` is a binomial random subset of `X` with parameter `p`.

Note: The assumption `0 < 𝔼[sup_{f ∈ Λ} ∑ i ∈ Xp, f i] < ∞` is not explicitly stated in the theorem
but used in the last step of the proof where `𝔼 ≥ (L/L') * 𝔼` is a contradiction for `L > L'`.
-/
theorem theorem_1_2 (p : I) (hp₀ : 0 < p) (hp₁ : p < 1) (X : Type*) [Fintype X] (Λ : Set (X → ℝ≥0))
    (hE₀ : 0 < 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p])
    (hE : 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p] < ∞) :
    IsSmall p {s : Set X | ⨆ f ∈ Λ, ∑ i ∈ s, (f i : ℝ≥0∞) ≥
        L₂ * 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p]} := by
  set_option maxRecDepth 100000 in
  run_tac do
    let stx ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "(
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_bern : ∀ (X : Type u_1) [Fintype X] (p : I) (F : Set X → ℝ≥0∞), ∫⁻ s, F s ∂(binomialSetDistribution X p) =
        ∑ s : Finset X, ENNReal.ofReal ((p : ℝ) ^ s.card * (1 - (p : ℝ)) ^ (Fintype.card X - s.card)) *
          F ↑s :=
    fun (X : Type u_1) [Fintype X] (p : I) (F : Set X → ℝ≥0∞) => by
      classical
      unfold binomialSetDistribution
      rw [lintegral_fintype]
      symm
      refine Fintype.sum_bijective (fun s : Finset X => (s : Set X))
        ⟨Finset.coe_injective, fun t => ⟨t.toFinset, by simp⟩⟩ _ _ (fun s => ?_)
      rw [setBernoulli_singleton _ _ (Set.subset_univ _) Set.finite_univ, mul_comm]
      congr 1
      have h1 : (Set.univ \\ (s : Set X)).ncard = Fintype.card X - s.card := by
        rw [← Set.compl_eq_univ_diff, ← Finset.coe_compl, Set.ncard_coe_finset, Finset.card_compl]
      rw [Set.ncard_coe_finset, h1]
      have hp0 : (0 : ℝ) ≤ p := p.2.1
      have hp1 : (0 : ℝ) ≤ 1 - p := by linarith [p.2.2]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hp0, ENNReal.ofReal_pow hp1]
      congr 2
      · rw [ENNReal.ofReal_eq_coe_nnreal hp0]
        rfl
      · rw [ENNReal.ofReal_eq_coe_nnreal hp1]
        rfl
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_thin_marg : ∀ (X : Type u_1) [DecidableEq X] (r : ℝ) (W : Finset X) (i : X) (hi : i ∈ W), ∑ U ∈ W.powerset, (if i ∈ U then r ^ U.card * (1 - r) ^ (W.card - U.card) else 0) = r :=
    fun (X : Type u_1) [DecidableEq X] (r : ℝ) (W : Finset X) (i : X) (hi : i ∈ W) => by
      have hW : W = insert i (W.erase i) := (Finset.insert_erase hi).symm
      rw [hW, Finset.sum_powerset_insert (Finset.notMem_erase i W)]
      have h1 : ∑ t ∈ (W.erase i).powerset, (if i ∈ t then r ^ t.card *
          (1 - r) ^ ((insert i (W.erase i)).card - t.card) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        rw [Finset.mem_powerset] at ht
        have : i ∉ t := fun h => Finset.notMem_erase i W (ht h)
        simp [this]
      rw [h1, zero_add]
      have h2 : ∀ t ∈ (W.erase i).powerset, (if i ∈ insert i t then r ^ (insert i t).card *
          (1 - r) ^ ((insert i (W.erase i)).card - (insert i t).card) else 0) =
          r * (r ^ t.card * (1 - r) ^ ((W.erase i).card - t.card)) := by
        intro t ht
        rw [Finset.mem_powerset] at ht
        have : i ∉ t := fun h => Finset.notMem_erase i W (ht h)
        rw [if_pos (Finset.mem_insert_self i t), Finset.card_insert_of_notMem this,
          Finset.card_insert_of_notMem (Finset.notMem_erase i W), Nat.add_sub_add_right, pow_succ]
        ring
      rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]
      simp
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_thin_sup : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (p q : ℝ) (hq0 : 0 < q)
      (U : Finset X), ∑ W ∈ univ.filter (fun W : Finset X => U ⊆ W), q ^ W.card * (1 - q) ^ (Fintype.card X - W.card) *
        ((p / q) ^ U.card * (1 - p / q) ^ (W.card - U.card)) =
        p ^ U.card * (1 - p) ^ (Fintype.card X - U.card) :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (p q : ℝ) (hq0 : 0 < q)
        (U : Finset X) => by
      have hb : ∑ W ∈ univ.filter (fun W : Finset X => U ⊆ W), q ^ W.card *
          (1 - q) ^ (Fintype.card X - W.card) * ((p / q) ^ U.card * (1 - p / q) ^ (W.card - U.card)) =
          ∑ A ∈ Uᶜ.powerset, p ^ U.card * ((q - p) ^ A.card * (1 - q) ^ (Uᶜ.card - A.card)) := by
        symm
        apply Finset.sum_nbij' (fun A => U ∪ A) (fun W => W \\ U)
        · intro A _; simp
        · intro W _
          rw [Finset.mem_powerset]
          intro x hx
          rw [Finset.mem_compl]
          exact (Finset.mem_sdiff.mp hx).2
        · intro A hA
          rw [Finset.mem_powerset] at hA
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨h | h, h'⟩
            · exact absurd h h'
            · exact h
          · intro h
            exact ⟨Or.inr h, Finset.mem_compl.mp (hA h)⟩
        · intro W hW
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
          exact Finset.union_sdiff_of_subset hW
        · intro A hA
          rw [Finset.mem_powerset] at hA
          have hd : Disjoint U A := by
            rw [Finset.disjoint_left]
            intro x hxU hxA
            exact Finset.mem_compl.mp (hA hxA) hxU
          have hAc : A.card ≤ Uᶜ.card := Finset.card_le_card hA
          rw [Finset.card_union_of_disjoint hd, Finset.card_compl] at *
          rw [Nat.add_sub_cancel_left, show Fintype.card X - (U.card + A.card) =
            Fintype.card X - U.card - A.card by omega]
          have hq : q ≠ 0 := hq0.ne'
          rw [div_pow, pow_add, show (1 : ℝ) - p / q = (q - p) / q by field_simp, div_pow]
          field_simp
      rw [hb, ← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow, Finset.card_compl]
      congr 2
      ring
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_thin : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
      (hq : q ≤ 1) (hq0 : 0 < q) (V : Finset X → X → ℝ) (hV : ∀ W i, 0 ≤ V W i)
      (g : Finset X → ℝ) (hg : ∀ W U : Finset X, U ⊆ W → ∑ i ∈ U, V W i ≤ g U), p / q * ∑ W : Finset X, q ^ W.card * (1 - q) ^ (Fintype.card X - W.card) * ∑ i ∈ W, V W i ≤
        ∑ U : Finset X, p ^ U.card * (1 - p) ^ (Fintype.card X - U.card) * g U :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
        (hq : q ≤ 1) (hq0 : 0 < q) (V : Finset X → X → ℝ) (hV : ∀ W i, 0 ≤ V W i)
        (g : Finset X → ℝ) (hg : ∀ W U : Finset X, U ⊆ W → ∑ i ∈ U, V W i ≤ g U) => by
      set r := p / q with hr
      have hr0 : 0 ≤ r := div_nonneg hp hq0.le
      have hr1 : r ≤ 1 := (div_le_one hq0).mpr hpq
      set c : Finset X → Finset X → ℝ := fun W U => r ^ U.card * (1 - r) ^ (W.card - U.card) with hc
      have hc0 : ∀ W U, 0 ≤ c W U := fun W U => by
        simp only [hc]; exact mul_nonneg (pow_nonneg hr0 _) (pow_nonneg (by linarith) _)
      set μ : Finset X → ℝ := fun W => q ^ W.card * (1 - q) ^ (Fintype.card X - W.card) with hμ
      have hμ0 : ∀ W, 0 ≤ μ W := fun W => by
        simp only [hμ]; exact mul_nonneg (pow_nonneg hq0.le _) (pow_nonneg (by linarith) _)
      -- step (c)
      have hstep : ∀ W : Finset X, r * ∑ i ∈ W, V W i = ∑ U ∈ W.powerset, c W U * ∑ i ∈ U, V W i := by
        intro W
        have e1 : ∀ U ∈ W.powerset, c W U * ∑ i ∈ U, V W i =
            ∑ i ∈ W, V W i * (if i ∈ U then c W U else 0) := by
          intro U hU
          rw [Finset.mem_powerset] at hU
          rw [Finset.mul_sum]
          rw [← Finset.sum_subset hU (f := fun i => V W i * (if i ∈ U then c W U else 0))]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [if_pos hi]; ring
          · intro i _ hi
            rw [if_neg hi, mul_zero]
        rw [Finset.sum_congr rfl e1, Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum, LA_thin_marg X r W i hi, mul_comm]
      calc p / q * ∑ W : Finset X, q ^ W.card * (1 - q) ^ (Fintype.card X - W.card) * ∑ i ∈ W, V W i
          = ∑ W : Finset X, μ W * (r * ∑ i ∈ W, V W i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro W _
            simp only [hμ]; ring
        _ = ∑ W : Finset X, ∑ U ∈ W.powerset, μ W * c W U * ∑ i ∈ U, V W i := by
            apply Finset.sum_congr rfl
            intro W _
            rw [hstep, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro U _; ring
        _ ≤ ∑ W : Finset X, ∑ U ∈ W.powerset, μ W * c W U * g U := by
            apply Finset.sum_le_sum
            intro W _
            apply Finset.sum_le_sum
            intro U hU
            rw [Finset.mem_powerset] at hU
            exact mul_le_mul_of_nonneg_left (hg W U hU) (mul_nonneg (hμ0 W) (hc0 W U))
        _ = ∑ U : Finset X, ∑ W ∈ univ.filter (fun W : Finset X => U ⊆ W), μ W * c W U * g U := by
            apply Finset.sum_comm'
            intro W U
            simp
        _ = ∑ U : Finset X, p ^ U.card * (1 - p) ^ (Fintype.card X - U.card) * g U := by
            apply Finset.sum_congr rfl
            intro U _
            rw [← Finset.sum_mul, ← LA_thin_sup X p q hq0 U]
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_prep_level : ∀ (x : ℝ) (hx : 0 < x), ∃ j : ℕ, (1 / 100 : ℝ) ^ j ≤ x ∧ (1 ≤ x → j = 0) ∧
      (x < 1 → x < 100 * (1 / 100 : ℝ) ^ j) :=
    fun (x : ℝ) (hx : 0 < x) => by
      classical
      by_cases h1 : 1 ≤ x
      · exact ⟨0, by simpa using h1, fun _ => rfl, fun h => absurd h (not_lt.mpr h1)⟩
      · have hex : ∃ j : ℕ, (1 / 100 : ℝ) ^ j ≤ x := by
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1 / 100 : ℝ) < 1)
          exact ⟨n, hn.le⟩
        refine ⟨Nat.find hex, Nat.find_spec hex, fun h => absurd h h1, fun _ => ?_⟩
        have hne : Nat.find hex ≠ 0 := by
          intro h0
          have := Nat.find_spec hex
          rw [h0] at this
          simp at this
          exact h1 this
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
        have hmin := Nat.find_min hex (show m < Nat.find hex by omega)
        rw [hm, pow_succ]
        push_neg at hmin
        linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_prep_sq_sum : ∀ (M : ℕ), ∑ j ∈ Finset.range M, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 - 2 / ((M : ℝ) + 1) :=
    fun (M : ℕ) => by
      induction M with
      | zero => norm_num
      | succ M ih =>
        rw [Finset.sum_range_succ]
        have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        have key : (1 : ℝ) / ((M : ℝ) + 1) ^ 2 ≤ 2 / ((M : ℝ) + 1) - 2 / (((M + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_prep_one : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (S : Finset X) (v : X → ℝ)
      (hv : ∀ i, 0 ≤ v i) (h1 : 1 ≤ ∑ i ∈ S, v i), ∃ S' : Finset X, ∃ ℓ : X → ℕ,
        S' ⊆ S ∧ (∀ i ∈ S', (1 / 100 : ℝ) ^ (ℓ i) ≤ v i) ∧
        (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ S', (1 / 100 : ℝ) ^ (ℓ i) ∧
        ∀ j : ℕ, (S'.filter (fun i => ℓ i = j)).card = 0 ∨
          ((∃ k : ℕ, (S'.filter (fun i => ℓ i = j)).card = 100 ^ k) ∧
            100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * (S'.filter (fun i => ℓ i = j)).card ∧
            (S'.filter (fun i => ℓ i = j)).card < 2 * 100 ^ j) :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (S : Finset X) (v : X → ℝ)
        (hv : ∀ i, 0 ≤ v i) (h1 : 1 ≤ ∑ i ∈ S, v i) => by
      classical
      have hlev : ∀ i, ∃ j : ℕ, 0 < v i → ((1 / 100 : ℝ) ^ j ≤ v i ∧ (1 ≤ v i → j = 0) ∧
          (v i < 1 → v i < 100 * (1 / 100 : ℝ) ^ j)) := by
        intro i
        by_cases h : 0 < v i
        · obtain ⟨j, hj⟩ := LA_prep_level _ h
          exact ⟨j, fun _ => hj⟩
        · exact ⟨0, fun h' => absurd h' h⟩
      choose ℓ hℓ using hlev
      set B : ℕ → Finset X := fun j => S.filter (fun i => 0 < v i ∧ ℓ i = j) with hB
      have hBmem : ∀ j, ∀ i ∈ B j, i ∈ S ∧ 0 < v i ∧ ℓ i = j := by
        intro j i hi
        simp only [hB, Finset.mem_filter] at hi
        exact ⟨hi.1, hi.2.1, hi.2.2⟩
      by_cases hA : ∃ j, 100 ^ j ≤ (B j).card
      · obtain ⟨j, hj⟩ := hA
        obtain ⟨T, hTB, hTc⟩ := Finset.exists_subset_card_eq hj
        have hTmem : ∀ i ∈ T, i ∈ S ∧ 0 < v i ∧ ℓ i = j := fun i hi => hBmem j i (hTB hi)
        refine ⟨T, ℓ, fun i hi => (hTmem i hi).1, fun i hi => (hℓ i (hTmem i hi).2.1).1, ?_, ?_⟩
        · have : ∑ i ∈ T, (1 / 100 : ℝ) ^ (ℓ i) = ∑ i ∈ T, (1 / 100 : ℝ) ^ j :=
            Finset.sum_congr rfl (fun i hi => by rw [(hTmem i hi).2.2])
          rw [this, Finset.sum_const, hTc, nsmul_eq_mul]
          push_cast
          rw [← mul_pow]
          norm_num
        · intro j'
          by_cases hjj : j' = j
          · subst hjj
            have hf : T.filter (fun i => ℓ i = j') = T :=
              Finset.filter_true_of_mem (fun i hi => (hTmem i hi).2.2)
            rw [hf, hTc]
            right
            have hp := pow_pos (show 0 < 100 by norm_num) j'
            refine ⟨⟨j', rfl⟩, Nat.le_mul_of_pos_left _ (by positivity), by omega⟩
          · left
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro i hi
            rw [(hTmem i hi).2.2]
            exact fun h => hjj h.symm
      · push_neg at hA
        have hT : ∀ j, ∃ T ⊆ B j, (T.card = 0 ∧ 100 ^ 4 * (j + 1) ^ 2 * (B j).card < 100 ^ j) ∨
            (100 ^ j ≤ 100 ^ 4 * (j + 1) ^ 2 * (B j).card ∧
              T.card = 100 ^ (Nat.log 100 (B j).card)) := by
          intro j
          by_cases hk : 100 ^ j ≤ 100 ^ 4 * (j + 1) ^ 2 * (B j).card
          · have hpos : (B j).card ≠ 0 := by
              intro h0
              rw [h0] at hk
              have := pow_pos (show 0 < 100 by norm_num) j
              omega
            obtain ⟨T, hTB, hTc⟩ := Finset.exists_subset_card_eq (Nat.pow_log_le_self 100 hpos)
            exact ⟨T, hTB, Or.inr ⟨hk, hTc⟩⟩
          · exact ⟨∅, Finset.empty_subset _, Or.inl ⟨Finset.card_empty, not_le.mp hk⟩⟩
        choose T hTB hTc using hT
        have hTmem : ∀ j, ∀ i ∈ T j, i ∈ S ∧ 0 < v i ∧ ℓ i = j := fun j i hi => hBmem j i (hTB j hi)
        set S' := S.filter (fun i => i ∈ T (ℓ i)) with hS'
        have hfil : ∀ j, S'.filter (fun i => ℓ i = j) = T j := by
          intro j
          ext i
          simp only [hS', Finset.mem_filter]
          constructor
          · rintro ⟨⟨_, h⟩, rfl⟩
            exact h
          · intro h
            obtain ⟨h1, _, h3⟩ := hTmem j i h
            subst h3
            exact ⟨⟨h1, h⟩, rfl⟩
        refine ⟨S', ℓ, Finset.filter_subset _ _, ?_, ?_, ?_⟩
        · intro i hi
          simp only [hS', Finset.mem_filter] at hi
          exact (hℓ i (hTmem _ i hi.2).2.1).1
        · set Idx := S.image ℓ with hI
          have hnew : ∑ i ∈ S', (1 / 100 : ℝ) ^ (ℓ i) = ∑ j ∈ Idx, ((T j).card : ℝ) * (1 / 100 : ℝ) ^ j := by
            rw [← Finset.sum_fiberwise_of_maps_to (s := S') (t := Idx) (g := ℓ)
              (fun i hi => Finset.mem_image_of_mem ℓ (Finset.filter_subset _ _ hi))]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const,
              hfil j, nsmul_eq_mul]
          have hold : ∑ i ∈ S, v i ≤ ∑ j ∈ Idx, ((B j).card : ℝ) * (100 * (1 / 100 : ℝ) ^ j) := by
            have step1 : ∑ i ∈ S, v i ≤ ∑ i ∈ S, (if 0 < v i then 100 * (1 / 100 : ℝ) ^ (ℓ i) else 0) := by
              refine Finset.sum_le_sum (fun i hi => ?_)
              split_ifs with hpos
              · have hne : ℓ i ≠ 0 := by
                  intro h0
                  have hmem : i ∈ B 0 := by
                    simp only [hB, Finset.mem_filter]
                    exact ⟨hi, hpos, h0⟩
                  have h0' := hA 0
                  have hp := Finset.card_pos.mpr ⟨i, hmem⟩
                  rw [pow_zero] at h0'
                  omega
                have hlt1 : v i < 1 := by
                  by_contra hc
                  exact hne ((hℓ i hpos).2.1 (not_lt.mp hc))
                exact ((hℓ i hpos).2.2 hlt1).le
              · exact le_of_eq (le_antisymm (not_lt.mp hpos) (hv i))
            refine step1.trans (le_of_eq ?_)
            rw [← Finset.sum_filter]
            rw [← Finset.sum_fiberwise_of_maps_to (s := S.filter (fun i => 0 < v i)) (t := Idx) (g := ℓ)
              (fun i hi => Finset.mem_image_of_mem ℓ (Finset.filter_subset _ _ hi))]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const,
              nsmul_eq_mul, Finset.filter_filter]
          have hterm : ∀ j ∈ Idx, ((B j).card : ℝ) * (100 * (1 / 100 : ℝ) ^ j) ≤
              10 ^ 4 * (((T j).card : ℝ) * (1 / 100 : ℝ) ^ j) + 100 * (1 / 100 : ℝ) ^ 4 * ((1 : ℝ) / ((j : ℝ) + 1) ^ 2) := by
            intro j _
            have hy : (0 : ℝ) < (1 / 100 : ℝ) ^ j := by positivity
            have hy1 : (1 / 100 : ℝ) ^ j * (100 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
            rcases hTc j with ⟨h0, hd⟩ | ⟨_, hc⟩
            · rw [h0]
              have hc : (100 : ℝ) ^ 4 * ((j : ℝ) + 1) ^ 2 * ((B j).card : ℝ) ≤ (100 : ℝ) ^ j := by
                exact_mod_cast hd.le
              have key : ((B j).card : ℝ) * (1 / 100 : ℝ) ^ j * ((100 : ℝ) ^ 4 * ((j : ℝ) + 1) ^ 2) ≤ 1 := by
                nlinarith
              have hj : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
              simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
              rw [mul_one_div, le_div_iff₀ hj]
              norm_num at key ⊢
              nlinarith
            · have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 100) (B j).card
              rw [pow_succ, ← hc] at hlt
              have hlt' : ((B j).card : ℝ) ≤ ((T j).card : ℝ) * 100 := by exact_mod_cast hlt.le
              have : (0 : ℝ) ≤ 100 * (1 / 100 : ℝ) ^ 4 * ((1 : ℝ) / ((j : ℝ) + 1) ^ 2) := by positivity
              nlinarith
          have hsq : ∑ j ∈ Idx, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
            have hsub : Idx ⊆ Finset.range (Idx.sup id + 1) := by
              intro j hj
              rw [Finset.mem_range]
              have := Finset.le_sup (f := id) hj
              simp at this
              omega
            calc ∑ j ∈ Idx, (1 : ℝ) / ((j : ℝ) + 1) ^ 2
                ≤ ∑ j ∈ Finset.range (Idx.sup id + 1), (1 : ℝ) / ((j : ℝ) + 1) ^ 2 :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
              _ ≤ 2 - 2 / (((Idx.sup id + 1 : ℕ) : ℝ) + 1) := LA_prep_sq_sum _
              _ ≤ 2 := by
                  have : (0 : ℝ) ≤ 2 / (((Idx.sup id + 1 : ℕ) : ℝ) + 1) := by positivity
                  linarith
          have htot := (h1.trans hold).trans (Finset.sum_le_sum hterm)
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hnew] at htot
          norm_num at htot hsq ⊢
          nlinarith
        · intro j
          rw [hfil j]
          rcases hTc j with ⟨h0, _⟩ | ⟨hk, hc⟩
          · left; exact h0
          · right
            refine ⟨⟨_, hc⟩, ?_, ?_⟩
            · have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 100) (B j).card
              rw [pow_succ, ← hc] at hlt
              calc 100 ^ j ≤ 100 ^ 4 * (j + 1) ^ 2 * (B j).card := hk
                _ ≤ 100 ^ 4 * (j + 1) ^ 2 * ((T j).card * 100) := Nat.mul_le_mul_left _ hlt.le
                _ = 100 ^ 5 * (j + 1) ^ 2 * (T j).card := by ring
            · have := Finset.card_le_card (hTB j)
              have := hA j
              omega
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_prep : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (𝓕 : Finset (Finset X))
      (w : Finset X → X → ℝ) (hw : ∀ S ∈ 𝓕, ∀ i, 0 ≤ w S i) (h1 : ∀ S ∈ 𝓕, 1 ≤ ∑ i ∈ S, w S i), ∃ S' : Finset X → Finset X, ∃ ℓ : Finset X → X → ℕ, ∀ S ∈ 𝓕,
        S' S ⊆ S ∧ (∀ i ∈ S' S, (1 / 100 : ℝ) ^ (ℓ S i) ≤ w S i) ∧
        (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ S' S, (1 / 100 : ℝ) ^ (ℓ S i) ∧
        ∀ j : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 0 ∨
          ((∃ k : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 100 ^ k) ∧
            100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * ((S' S).filter (fun i => ℓ S i = j)).card ∧
            ((S' S).filter (fun i => ℓ S i = j)).card < 2 * 100 ^ j) :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (𝓕 : Finset (Finset X))
        (w : Finset X → X → ℝ) (hw : ∀ S ∈ 𝓕, ∀ i, 0 ≤ w S i) (h1 : ∀ S ∈ 𝓕, 1 ≤ ∑ i ∈ S, w S i) => by
      classical
      have h : ∀ S : Finset X, ∃ S' : Finset X, ∃ ℓ : X → ℕ, S ∈ 𝓕 →
          (S' ⊆ S ∧ (∀ i ∈ S', (1 / 100 : ℝ) ^ (ℓ i) ≤ w S i) ∧
          (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ S', (1 / 100 : ℝ) ^ (ℓ i) ∧
          ∀ j : ℕ, (S'.filter (fun i => ℓ i = j)).card = 0 ∨
            ((∃ k : ℕ, (S'.filter (fun i => ℓ i = j)).card = 100 ^ k) ∧
              100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * (S'.filter (fun i => ℓ i = j)).card ∧
              (S'.filter (fun i => ℓ i = j)).card < 2 * 100 ^ j)) := by
        intro S
        by_cases hS : S ∈ 𝓕
        · obtain ⟨S', ℓ, hh⟩ := LA_prep_one X S (w S) (hw S hS) (h1 S hS)
          exact ⟨S', ℓ, fun _ => hh⟩
        · exact ⟨∅, fun _ => 0, fun h => absurd h hS⟩
      choose S' ℓ hS' using h
      exact ⟨S', ℓ, fun S hS => hS' S hS⟩
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_fd_lexmin : ∀ (X : Type u_1) (P : ℕ → Finset X → Prop) (h : ∃ c U, P c U), ∃ c U, P c U ∧ (∀ c' < c, ∀ U', ¬ P c' U') ∧ (∀ U', P c U' → U.card ≤ U'.card) :=
    fun (X : Type u_1) (P : ℕ → Finset X → Prop) (h : ∃ c U, P c U) => by
      classical
      have h1 : ∃ n, ∃ U, P (Nat.find h) U ∧ U.card = n := by
        obtain ⟨U, hU⟩ := Nat.find_spec h
        exact ⟨U.card, U, hU, rfl⟩
      obtain ⟨U, hU, hUc⟩ := Nat.find_spec h1
      refine ⟨Nat.find h, U, hU, ?_, ?_⟩
      · intro c' hc' U' hU'
        exact Nat.find_min h hc' ⟨U', hU'⟩
      · intro U' hU'
        rw [hUc]
        exact Nat.find_min' h1 ⟨U', hU', rfl⟩
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_fd_erase : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ) (c : ℕ)
      (Z : Finset X) (x : X) (t : ℕ) (hxZ : x ∈ Z) (ht : 1 ≤ t)
      (h : (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ) - (t : ℝ))
        ≤ ∑ i ∈ Z, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)), (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ) - ((t - 1 : ℕ) : ℝ))
        ≤ ∑ i ∈ Z.erase x, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0) :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ) (c : ℕ)
        (Z : Finset X) (x : X) (t : ℕ) (hxZ : x ∈ Z) (ht : 1 ≤ t)
        (h : (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
          - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ) - (t : ℝ))
          ≤ ∑ i ∈ Z, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) => by
      have hsplit := Finset.sum_erase_add Z
        (fun i => if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0) hxZ
      have hterm : (if x ∈ A ∧ c ≤ f x then (1/100:ℝ)^(f x) else 0) ≤ (1/100:ℝ)^c := by
        split_ifs with hh
        · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hh.2
        · positivity
      have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub ht]; simp
      rw [hcast]
      simp only at hsplit
      linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_fd_P0 : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ)
      (hA : (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ A, (1 / 100 : ℝ) ^ (f i))
      (W T : Finset X) (hW : ∑ i ∈ A ∩ W, (1 / 100 : ℝ) ^ (f i) < 1 / 10 ^ 10)
      (h : (∑ i, (if i ∈ A ∧ 0 ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^0 * (((A.filter (fun i => f i < 0)).card : ℝ) - (T.card : ℝ))
        ≤ ∑ i ∈ W ∪ T, (if i ∈ A ∧ 0 ≤ f i then (1/100:ℝ)^(f i) else 0)), False :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ)
        (hA : (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ A, (1 / 100 : ℝ) ^ (f i))
        (W T : Finset X) (hW : ∑ i ∈ A ∩ W, (1 / 100 : ℝ) ^ (f i) < 1 / 10 ^ 10)
        (h : (∑ i, (if i ∈ A ∧ 0 ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
          - (1/100:ℝ)^0 * (((A.filter (fun i => f i < 0)).card : ℝ) - (T.card : ℝ))
          ≤ ∑ i ∈ W ∪ T, (if i ∈ A ∧ 0 ≤ f i then (1/100:ℝ)^(f i) else 0)) => by
      simp only [Nat.zero_le, and_true, pow_zero, Nat.not_lt_zero, Finset.filter_false,
        Finset.card_empty, Nat.cast_zero, one_mul, _root_.zero_sub] at h
      rw [Finset.sum_ite_mem, Finset.univ_inter] at h
      have h1 := Finset.sum_union_inter (s₁ := W) (s₂ := T)
        (f := fun i => if i ∈ A then (1/100:ℝ)^(f i) else 0)
      have h2 : 0 ≤ ∑ i ∈ W ∩ T, (if i ∈ A then (1/100:ℝ)^(f i) else 0) :=
        Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
      have h3 : ∑ i ∈ T, (if i ∈ A then (1/100:ℝ)^(f i) else 0) ≤ T.card := by
        have := Finset.sum_le_card_nsmul T (fun i => if i ∈ A then (1/100:ℝ)^(f i) else 0) 1
          (fun i _ => by
            show (if i ∈ A then (1/100:ℝ)^(f i) else 0) ≤ 1
            split_ifs
            · exact pow_le_one₀ (by norm_num) (by norm_num)
            · norm_num)
        simpa using this
      have h4 : ∑ i ∈ W, (if i ∈ A then (1/100:ℝ)^(f i) else 0) = ∑ i ∈ A ∩ W, (1/100:ℝ)^(f i) := by
        rw [Finset.sum_ite_mem, Finset.inter_comm]
      have h5 : (1:ℝ) / 10^8 / 100 = 1 / 10^10 := by norm_num
      simp only at h1
      linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_fd_P4 : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ) (c : ℕ)
      (hc : 1 ≤ c) (hA : ∀ i ∈ A, f i ≠ c - 1) (Z : Finset X) (t : ℕ)
      (ht : t ≤ (A.filter (fun i => f i < c)).card)
      (h : (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ) - (t : ℝ))
        ≤ ∑ i ∈ Z, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)), A.filter (fun i => f i < c - 1) = A.filter (fun i => f i < c) ∧
      (∑ i, (if i ∈ A ∧ c - 1 ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^(c - 1) * (((A.filter (fun i => f i < c - 1)).card : ℝ) - (t : ℝ))
        ≤ ∑ i ∈ Z, (if i ∈ A ∧ c - 1 ≤ f i then (1/100:ℝ)^(f i) else 0) :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ) (c : ℕ)
        (hc : 1 ≤ c) (hA : ∀ i ∈ A, f i ≠ c - 1) (Z : Finset X) (t : ℕ)
        (ht : t ≤ (A.filter (fun i => f i < c)).card)
        (h : (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
          - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ) - (t : ℝ))
          ≤ ∑ i ∈ Z, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) => by
      have hfil : A.filter (fun i => f i < c - 1) = A.filter (fun i => f i < c) := by
        apply Finset.filter_congr
        intro i hi
        have := hA i hi
        omega
      have hG : ∀ i, (if i ∈ A ∧ c - 1 ≤ f i then (1/100:ℝ)^(f i) else 0)
          = (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0) := by
        intro i
        by_cases hi : i ∈ A
        · have := hA i hi
          have hiff : c - 1 ≤ f i ↔ c ≤ f i := by omega
          simp only [hi, true_and, hiff]
        · simp [hi]
      refine ⟨hfil, ?_⟩
      simp only [hG, hfil]
      have hd : (0:ℝ) ≤ ((A.filter (fun i => f i < c)).card : ℝ) - (t : ℝ) := by
        have : (t : ℝ) ≤ ((A.filter (fun i => f i < c)).card : ℝ) := by exact_mod_cast ht
        linarith
      have hpow : (1/100:ℝ)^c = (1/100:ℝ)^(c-1) * (1/100) := by
        rw [← pow_succ]; congr 1; omega
      have hpos : (0:ℝ) ≤ (1/100:ℝ)^(c-1) := by positivity
      rw [hpow] at h
      nlinarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_fd_P2 : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ) (c : ℕ)
      (hc : 1 ≤ c) (W : Finset X)
      (h : (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ)
            - (((A.filter (fun i => f i < c)) \\ W).card : ℝ))
        ≤ ∑ i ∈ W ∪ ((A.filter (fun i => f i < c)) \\ W),
            (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0))
      (hn : ¬ ((∑ i, (if i ∈ A ∧ c - 1 ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^(c - 1) * (((A.filter (fun i => f i < c - 1)).card : ℝ)
            - (((A.filter (fun i => f i < c - 1)) \\ W).card : ℝ))
        ≤ ∑ i ∈ W ∪ ((A.filter (fun i => f i < c - 1)) \\ W),
            (if i ∈ A ∧ c - 1 ≤ f i then (1/100:ℝ)^(f i) else 0))), 9 * (A.filter (fun i => f i < c)).card ≤ 10 * ((A.filter (fun i => f i < c)) \\ W).card :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ) (c : ℕ)
        (hc : 1 ≤ c) (W : Finset X)
        (h : (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
          - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ)
              - (((A.filter (fun i => f i < c)) \\ W).card : ℝ))
          ≤ ∑ i ∈ W ∪ ((A.filter (fun i => f i < c)) \\ W),
              (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0))
        (hn : ¬ ((∑ i, (if i ∈ A ∧ c - 1 ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
          - (1/100:ℝ)^(c - 1) * (((A.filter (fun i => f i < c - 1)).card : ℝ)
              - (((A.filter (fun i => f i < c - 1)) \\ W).card : ℝ))
          ≤ ∑ i ∈ W ∪ ((A.filter (fun i => f i < c - 1)) \\ W),
              (if i ∈ A ∧ c - 1 ≤ f i then (1/100:ℝ)^(f i) else 0))) => by
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hn
      push_neg at hn
      set b : ℝ := (1/100:ℝ)^(d+1) with hb
      set a : ℝ := (1/100:ℝ)^d with ha
      have hab : a = 100 * b := by rw [ha, hb, pow_succ]; ring
      have hbpos : 0 < b := by positivity
      have cardR : ∀ (s : Finset X), ((s.card : ℕ) : ℝ) = ∑ i, if i ∈ s then (1:ℝ) else 0 := by
        intro s
        rw [Finset.sum_ite_mem, Finset.univ_inter]; simp
      have hTc := Finset.card_sdiff_add_card_inter (A.filter (fun i => f i < d + 1)) W
      have hUc := Finset.card_sdiff_add_card_inter (A.filter (fun i => f i < d)) W
      have eN : (((A.filter (fun i => f i < d + 1)).card : ℕ) : ℝ)
          = ((A.filter (fun i => f i = d)).card : ℝ) + ((A.filter (fun i => f i < d)).card : ℝ) := by
        rw [cardR, cardR, cardR, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mem_filter]
        by_cases hi : i ∈ A <;> by_cases h1 : f i = d <;> by_cases h2 : f i < d <;>
          simp [hi, h1, h2] <;> omega
      have eA : ((((A.filter (fun i => f i < d + 1)) ∩ W).card : ℕ) : ℝ)
          = (((A.filter (fun i => f i < d)) ∩ W).card : ℝ)
            + ((W ∩ A.filter (fun i => f i = d)).card : ℝ) := by
        rw [cardR, cardR, cardR, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mem_filter, Finset.mem_inter]
        by_cases hi : i ∈ A <;> by_cases hw : i ∈ W <;> by_cases h1 : f i = d <;>
          by_cases h2 : f i < d <;> simp [hi, hw, h1, h2] <;> omega
      have hGpt : ∀ i, (if i ∈ A ∧ d ≤ f i then (1/100:ℝ)^(f i) else 0)
          = (if i ∈ A ∧ d + 1 ≤ f i then (1/100:ℝ)^(f i) else 0)
            + a * (if i ∈ A.filter (fun i => f i = d) then (1:ℝ) else 0) := by
        intro i
        simp only [Finset.mem_filter]
        by_cases hi : i ∈ A <;> by_cases h1 : f i = d <;> by_cases h2 : d + 1 ≤ f i <;>
          by_cases h3 : d ≤ f i <;> simp [hi, h1, h2, h3, ha] <;> omega
      have e5 : (∑ i, (if i ∈ A ∧ d ≤ f i then (1/100:ℝ)^(f i) else 0))
          = (∑ i, (if i ∈ A ∧ d + 1 ≤ f i then (1/100:ℝ)^(f i) else 0))
            + a * ((A.filter (fun i => f i = d)).card : ℝ) := by
        rw [cardR, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => hGpt i
      have e6 : (∑ i ∈ W, (if i ∈ A ∧ d ≤ f i then (1/100:ℝ)^(f i) else 0))
          = (∑ i ∈ W, (if i ∈ A ∧ d + 1 ≤ f i then (1/100:ℝ)^(f i) else 0))
            + a * ((W ∩ A.filter (fun i => f i = d)).card : ℝ) := by
        have : ((W ∩ A.filter (fun i => f i = d)).card : ℝ)
            = ∑ i ∈ W, if i ∈ A.filter (fun i => f i = d) then (1:ℝ) else 0 := by
          rw [Finset.sum_ite_mem]; simp
        rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => hGpt i
      have e7 : ∑ i ∈ W ∪ ((A.filter (fun i => f i < d + 1)) \\ W),
          (if i ∈ A ∧ d + 1 ≤ f i then (1/100:ℝ)^(f i) else 0)
          = ∑ i ∈ W, (if i ∈ A ∧ d + 1 ≤ f i then (1/100:ℝ)^(f i) else 0) := by
        rw [Finset.sum_union Finset.disjoint_sdiff]
        have : ∑ i ∈ (A.filter (fun i => f i < d + 1)) \\ W,
            (if i ∈ A ∧ d + 1 ≤ f i then (1/100:ℝ)^(f i) else 0) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          simp only [Finset.mem_sdiff, Finset.mem_filter] at hi
          rw [if_neg]; omega
        rw [this, add_zero]
      have e8 : ∑ i ∈ W ∪ ((A.filter (fun i => f i < d)) \\ W),
          (if i ∈ A ∧ d ≤ f i then (1/100:ℝ)^(f i) else 0)
          = ∑ i ∈ W, (if i ∈ A ∧ d ≤ f i then (1/100:ℝ)^(f i) else 0) := by
        rw [Finset.sum_union Finset.disjoint_sdiff]
        have : ∑ i ∈ (A.filter (fun i => f i < d)) \\ W,
            (if i ∈ A ∧ d ≤ f i then (1/100:ℝ)^(f i) else 0) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          simp only [Finset.mem_sdiff, Finset.mem_filter] at hi
          rw [if_neg]; omega
        rw [this, add_zero]
      rw [e7] at h
      rw [e8, e5, e6] at hn
      have hTcR : ((((A.filter (fun i => f i < d + 1)) \\ W).card : ℕ) : ℝ)
          + (((A.filter (fun i => f i < d + 1)) ∩ W).card : ℝ)
          = ((A.filter (fun i => f i < d + 1)).card : ℝ) := by exact_mod_cast hTc
      have hUcR : ((((A.filter (fun i => f i < d)) \\ W).card : ℕ) : ℝ)
          + (((A.filter (fun i => f i < d)) ∩ W).card : ℝ)
          = ((A.filter (fun i => f i < d)).card : ℝ) := by exact_mod_cast hUc
      rw [hab] at hn
      have e1 : ((A.filter (fun i => f i < d + 1)).card : ℝ)
          - (((A.filter (fun i => f i < d + 1)) \\ W).card : ℝ)
          = (((A.filter (fun i => f i < d + 1)) ∩ W).card : ℝ) := by linarith
      have e2 : ((A.filter (fun i => f i < d)).card : ℝ)
          - (((A.filter (fun i => f i < d)) \\ W).card : ℝ)
          = (((A.filter (fun i => f i < d)) ∩ W).card : ℝ) := by linarith
      rw [e1] at h
      rw [e2] at hn
      have key : 0 < b * (((A.filter (fun i => f i = d)).card : ℝ)
          - 99 * (((A.filter (fun i => f i < d + 1)) ∩ W).card : ℝ)) := by
        rw [eA] at h ⊢
        linarith
      have key2 := (mul_pos_iff_of_pos_left hbpos).mp key
      have hnn : (0:ℝ) ≤ ((A.filter (fun i => f i < d)).card : ℝ) := by positivity
      have hnn2 : (0:ℝ) ≤ (((A.filter (fun i => f i < d + 1)) ∩ W).card : ℝ) := by positivity
      have : (9:ℝ) * ((A.filter (fun i => f i < d + 1)).card : ℝ)
          ≤ 10 * (((A.filter (fun i => f i < d + 1)) \\ W).card : ℝ) := by linarith
      exact_mod_cast this
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_frag_det : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (𝓕 : Finset (Finset X))
      (S' : Finset X → Finset X) (ℓ : Finset X → X → ℕ)
      (hsum : ∀ S ∈ 𝓕, (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ S' S, (1 / 100 : ℝ) ^ (ℓ S i))
      (hlegal : ∀ S ∈ 𝓕, ∀ j : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 0 ∨
          ((∃ k : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 100 ^ k) ∧
            100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * ((S' S).filter (fun i => ℓ S i = j)).card ∧
            ((S' S).filter (fun i => ℓ S i = j)).card < 2 * 100 ^ j))
      (C : ℕ) (hC : ∀ S ∈ 𝓕, ∀ i ∈ S' S, ℓ S i < C), ∃ T : Finset X → Finset X → Finset X, ∃ κ : Finset X → Finset X → (Fin C → ℕ),
        (∀ S ∈ 𝓕, ∀ W : Finset X, T S W ⊆ S' S \\ W) ∧
        (∀ W : Finset X, (∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10) →
          ∀ S ∈ 𝓕, κ S W ≠ 0 ∧ 9 * ∑ j, κ S W j ≤ 10 * (T S W).card ∧
            ∀ j : Fin C, κ S W j = 0 ∨ κ S W j = ((S' S).filter (fun i => ℓ S i = j)).card) ∧
        (∀ (Z : Finset X) (v : Fin C → ℕ) (t : ℕ), ∃ R : Finset X, R.card ≤ ∑ j, v j ∧
          ∀ W : Finset X, (∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10) →
            ∀ S ∈ 𝓕, κ S W = v → (T S W).card = t → W ∪ T S W = Z → T S W ⊆ R) :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (𝓕 : Finset (Finset X))
        (S' : Finset X → Finset X) (ℓ : Finset X → X → ℕ)
        (hsum : ∀ S ∈ 𝓕, (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ S' S, (1 / 100 : ℝ) ^ (ℓ S i))
        (hlegal : ∀ S ∈ 𝓕, ∀ j : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 0 ∨
            ((∃ k : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 100 ^ k) ∧
              100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * ((S' S).filter (fun i => ℓ S i = j)).card ∧
              ((S' S).filter (fun i => ℓ S i = j)).card < 2 * 100 ^ j))
        (C : ℕ) (hC : ∀ S ∈ 𝓕, ∀ i ∈ S' S, ℓ S i < C) => by
      classical
      have hlowcard : ∀ (S₁ : Finset X) (c : ℕ), ((S' S₁).filter (fun i => ℓ S₁ i < c)).card
          = ∑ j ∈ range c, ((S' S₁).filter (fun i => ℓ S₁ i = j)).card := by
        intro S₁ c
        rw [Finset.card_eq_sum_card_fiberwise (f := ℓ S₁) (t := range c)
          (fun x hx => by simpa using (Finset.mem_filter.1 hx).2)]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.filter_filter]
        congr 1
        apply Finset.filter_congr
        intro i _
        simp only [Finset.mem_range] at hj
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨h ▸ hj, h⟩
      have key : ∀ S W : Finset X, ∃ c : ℕ, ∃ U : Finset X, ∃ S₁ : Finset X, S ∈ 𝓕 →
          (U ⊆ S' S \\ W ∧ (S₁ ∈ 𝓕 ∧ (∀ j < c, ((S' S₁).filter (fun i => ℓ S₁ i = j)).card = ((S' S).filter (fun i => ℓ S i = j)).card) ∧ (S' S₁).filter (fun i => ℓ S₁ i < c) ⊆ W ∪ U ∧ ((∑ i, (if i ∈ S' S₁ ∧ c ≤ ℓ S₁ i then (1/100:ℝ)^(ℓ S₁ i) else 0)) / 100 - (1/100:ℝ)^(c) * ((((S' S₁).filter (fun i => ℓ S₁ i < c)).card : ℝ) - ((U.card : ℕ) : ℝ)) ≤ ∑ i ∈ W ∪ U, (if i ∈ S' S₁ ∧ c ≤ ℓ S₁ i then (1/100:ℝ)^(ℓ S₁ i) else 0))) ∧ c ≤ C ∧
            (∀ c' < c, ∀ U' : Finset X, U' ⊆ S' S \\ W → ∀ S₂ : Finset X,
              ¬ (S₂ ∈ 𝓕 ∧ (∀ j < c', ((S' S₂).filter (fun i => ℓ S₂ i = j)).card = ((S' S).filter (fun i => ℓ S i = j)).card) ∧ (S' S₂).filter (fun i => ℓ S₂ i < c') ⊆ W ∪ U' ∧ ((∑ i, (if i ∈ S' S₂ ∧ c' ≤ ℓ S₂ i then (1/100:ℝ)^(ℓ S₂ i) else 0)) / 100 - (1/100:ℝ)^(c') * ((((S' S₂).filter (fun i => ℓ S₂ i < c')).card : ℝ) - ((U'.card : ℕ) : ℝ)) ≤ ∑ i ∈ W ∪ U', (if i ∈ S' S₂ ∧ c' ≤ ℓ S₂ i then (1/100:ℝ)^(ℓ S₂ i) else 0)))) ∧
            (∀ U' : Finset X, U' ⊆ S' S \\ W → ∀ S₂ : Finset X,
              (S₂ ∈ 𝓕 ∧ (∀ j < c, ((S' S₂).filter (fun i => ℓ S₂ i = j)).card = ((S' S).filter (fun i => ℓ S i = j)).card) ∧ (S' S₂).filter (fun i => ℓ S₂ i < c) ⊆ W ∪ U' ∧ ((∑ i, (if i ∈ S' S₂ ∧ c ≤ ℓ S₂ i then (1/100:ℝ)^(ℓ S₂ i) else 0)) / 100 - (1/100:ℝ)^(c) * ((((S' S₂).filter (fun i => ℓ S₂ i < c)).card : ℝ) - ((U'.card : ℕ) : ℝ)) ≤ ∑ i ∈ W ∪ U', (if i ∈ S' S₂ ∧ c ≤ ℓ S₂ i then (1/100:ℝ)^(ℓ S₂ i) else 0))) → U.card ≤ U'.card)) := by
        intro S W
        by_cases hS : S ∈ 𝓕
        swap
        · exact ⟨0, ∅, ∅, fun h => absurd h hS⟩
        have hz : ∀ i, (if i ∈ S' S ∧ C ≤ ℓ S i then (1/100:ℝ)^(ℓ S i) else 0) = 0 := by
          intro i
          rw [if_neg]
          rintro ⟨hi, hle⟩
          have := hC S hS i hi
          omega
        have hfull : (S' S).filter (fun i => ℓ S i < C) = S' S :=
          Finset.filter_true_of_mem (fun i hi => hC S hS i hi)
        have hexC : S' S \\ W ⊆ S' S \\ W ∧ ∃ S₁ : Finset X, (S₁ ∈ 𝓕 ∧ (∀ j < C, ((S' S₁).filter (fun i => ℓ S₁ i = j)).card = ((S' S).filter (fun i => ℓ S i = j)).card) ∧ (S' S₁).filter (fun i => ℓ S₁ i < C) ⊆ W ∪ (S' S \\ W) ∧ ((∑ i, (if i ∈ S' S₁ ∧ C ≤ ℓ S₁ i then (1/100:ℝ)^(ℓ S₁ i) else 0)) / 100 - (1/100:ℝ)^(C) * ((((S' S₁).filter (fun i => ℓ S₁ i < C)).card : ℝ) - (((S' S \\ W).card : ℕ) : ℝ)) ≤ ∑ i ∈ W ∪ (S' S \\ W), (if i ∈ S' S₁ ∧ C ≤ ℓ S₁ i then (1/100:ℝ)^(ℓ S₁ i) else 0))) := by
          refine ⟨subset_rfl, S, hS, fun j _ => rfl, ?_, ?_⟩
          · rw [hfull]; intro i hi; by_cases hw : i ∈ W <;> simp [hw, hi]
          · simp only [hz, Finset.sum_const_zero, zero_div, _root_.zero_sub, hfull]
            have : ((S' S \\ W).card : ℝ) ≤ ((S' S).card : ℝ) := by
              exact_mod_cast Finset.card_le_card Finset.sdiff_subset
            have : (0:ℝ) ≤ (1/100:ℝ)^C := by positivity
            nlinarith
        obtain ⟨c, U, ⟨hU, S₁, hF⟩, hminc, hminU⟩ := LA_fd_lexmin X
          (fun c U => U ⊆ S' S \\ W ∧ ∃ S₁ : Finset X, (S₁ ∈ 𝓕 ∧ (∀ j < c, ((S' S₁).filter (fun i => ℓ S₁ i = j)).card = ((S' S).filter (fun i => ℓ S i = j)).card) ∧ (S' S₁).filter (fun i => ℓ S₁ i < c) ⊆ W ∪ U ∧ ((∑ i, (if i ∈ S' S₁ ∧ c ≤ ℓ S₁ i then (1/100:ℝ)^(ℓ S₁ i) else 0)) / 100 - (1/100:ℝ)^(c) * ((((S' S₁).filter (fun i => ℓ S₁ i < c)).card : ℝ) - ((U.card : ℕ) : ℝ)) ≤ ∑ i ∈ W ∪ U, (if i ∈ S' S₁ ∧ c ≤ ℓ S₁ i then (1/100:ℝ)^(ℓ S₁ i) else 0))))
          ⟨C, S' S \\ W, hexC⟩
        refine ⟨c, U, S₁, fun _ => ⟨hU, hF, ?_, ?_, ?_⟩⟩
        · by_contra hcC
          push_neg at hcC
          exact hminc C hcC (S' S \\ W) hexC
        · intro c' hc' U' hU' S₂ hF₂
          exact hminc c' hc' U' ⟨hU', S₂, hF₂⟩
        · intro U' hU' S₂ hF₂
          exact hminU U' ⟨hU', S₂, hF₂⟩
      choose cf Tf Sf hkey using key
      have hP1 : ∀ S W : Finset X, S ∈ 𝓕 → ∀ S₂ : Finset X,
          (S₂ ∈ 𝓕 ∧ (∀ j < cf S W, ((S' S₂).filter (fun i => ℓ S₂ i = j)).card = ((S' S).filter (fun i => ℓ S i = j)).card) ∧ (S' S₂).filter (fun i => ℓ S₂ i < cf S W) ⊆ W ∪ Tf S W ∧ ((∑ i, (if i ∈ S' S₂ ∧ cf S W ≤ ℓ S₂ i then (1/100:ℝ)^(ℓ S₂ i) else 0)) / 100 - (1/100:ℝ)^(cf S W) * ((((S' S₂).filter (fun i => ℓ S₂ i < cf S W)).card : ℝ) - (((Tf S W).card : ℕ) : ℝ)) ≤ ∑ i ∈ W ∪ Tf S W, (if i ∈ S' S₂ ∧ cf S W ≤ ℓ S₂ i then (1/100:ℝ)^(ℓ S₂ i) else 0))) →
          Tf S W ⊆ (S' S₂).filter (fun i => ℓ S₂ i < cf S W) := by
        intro S W hS S₂ hF₂ x hx
        by_contra hxl
        obtain ⟨hTsub, -, -, -, hminU⟩ := hkey S W hS
        have hxW : x ∉ W := (Finset.mem_sdiff.1 (hTsub hx)).2
        have hcard1 : 1 ≤ (Tf S W).card := Finset.card_pos.2 ⟨x, hx⟩
        have hce : ((Tf S W).erase x).card = (Tf S W).card - 1 := Finset.card_erase_of_mem hx
        have hZe : (W ∪ Tf S W).erase x = W ∪ (Tf S W).erase x := by
          rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hxW]
        have hle := hminU ((Tf S W).erase x) ((Finset.erase_subset _ _).trans hTsub) S₂
          ⟨hF₂.1, hF₂.2.1, ?_, ?_⟩
        · omega
        · intro y hy
          have hy' := hF₂.2.2.1 hy
          have hyx : y ≠ x := fun h => hxl (h ▸ hy)
          rw [← hZe]
          exact Finset.mem_erase.2 ⟨hyx, hy'⟩
        · rw [hce, ← hZe]
          exact LA_fd_erase X (S' S₂) (ℓ S₂) (cf S W) (W ∪ Tf S W) x (Tf S W).card
            (Finset.mem_union_right _ hx) hcard1 hF₂.2.2.2
      have hTeq : ∀ S W : Finset X, S ∈ 𝓕 → ∀ S₂ : Finset X,
          (S₂ ∈ 𝓕 ∧ (∀ j < cf S W, ((S' S₂).filter (fun i => ℓ S₂ i = j)).card = ((S' S).filter (fun i => ℓ S i = j)).card) ∧ (S' S₂).filter (fun i => ℓ S₂ i < cf S W) ⊆ W ∪ Tf S W ∧ ((∑ i, (if i ∈ S' S₂ ∧ cf S W ≤ ℓ S₂ i then (1/100:ℝ)^(ℓ S₂ i) else 0)) / 100 - (1/100:ℝ)^(cf S W) * ((((S' S₂).filter (fun i => ℓ S₂ i < cf S W)).card : ℝ) - (((Tf S W).card : ℕ) : ℝ)) ≤ ∑ i ∈ W ∪ Tf S W, (if i ∈ S' S₂ ∧ cf S W ≤ ℓ S₂ i then (1/100:ℝ)^(ℓ S₂ i) else 0))) →
          Tf S W = (S' S₂).filter (fun i => ℓ S₂ i < cf S W) \\ W := by
        intro S W hS S₂ hF₂
        have hTsub := (hkey S W hS).1
        ext y
        constructor
        · intro hy
          exact Finset.mem_sdiff.2 ⟨hP1 S W hS S₂ hF₂ hy, (Finset.mem_sdiff.1 (hTsub hy)).2⟩
        · intro hy
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hy
          rcases Finset.mem_union.1 (hF₂.2.2.1 h1) with h | h
          · exact absurd h h2
          · exact h
      have hc1 : ∀ W : Finset X, (∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10) →
          ∀ S ∈ 𝓕, 1 ≤ cf S W := by
        intro W hW S hS
        by_contra h0
        have hc0 : cf S W = 0 := by omega
        obtain ⟨-, hF, -⟩ := hkey S W hS
        rw [hc0] at hF
        exact LA_fd_P0 X (S' (Sf S W)) (ℓ (Sf S W)) (hsum _ hF.1) W (Tf S W) (hW _ hF.1) hF.2.2.2
      have hsne : ∀ W : Finset X, (∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10) →
          ∀ S ∈ 𝓕, ((S' S).filter (fun i => ℓ S i = cf S W - 1)).card ≠ 0 := by
        intro W hW S hS h0
        obtain ⟨hTsub, hF, -, hminc, -⟩ := hkey S W hS
        have hc := hc1 W hW S hS
        have hprof := hF.2.1 (cf S W - 1) (by omega)
        have hA : ∀ i ∈ S' (Sf S W), ℓ (Sf S W) i ≠ cf S W - 1 := by
          intro i hi heq
          have hmem : i ∈ (S' (Sf S W)).filter (fun i => ℓ (Sf S W) i = cf S W - 1) :=
            Finset.mem_filter.2 ⟨hi, heq⟩
          rw [Finset.card_eq_zero.1 (hprof.trans h0)] at hmem
          simp at hmem
        have ht := Finset.card_le_card (hP1 S W hS _ hF)
        obtain ⟨hfil, hTI⟩ := LA_fd_P4 X (S' (Sf S W)) (ℓ (Sf S W)) (cf S W) hc hA (W ∪ Tf S W)
          (Tf S W).card ht hF.2.2.2
        exact hminc (cf S W - 1) (by omega) (Tf S W) hTsub (Sf S W)
          ⟨hF.1, fun j hj => hF.2.1 j (by omega), by rw [hfil]; exact hF.2.2.1, hTI⟩
      have hP2 : ∀ W : Finset X, (∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10) →
          ∀ S ∈ 𝓕, 9 * ((S' (Sf S W)).filter (fun i => ℓ (Sf S W) i < cf S W)).card
            ≤ 10 * (Tf S W).card := by
        intro W hW S hS
        obtain ⟨hTsub, hF, -, hminc, -⟩ := hkey S W hS
        have hc := hc1 W hW S hS
        have hTe := hTeq S W hS _ hF
        have h := hF.2.2.2
        rw [hTe] at h hTsub
        rw [hTe]
        apply LA_fd_P2 X (S' (Sf S W)) (ℓ (Sf S W)) (cf S W) hc W h
        intro hTI
        refine hminc (cf S W - 1) (by omega)
          ((S' (Sf S W)).filter (fun i => ℓ (Sf S W) i < cf S W - 1) \\ W) ?_ (Sf S W)
          ⟨hF.1, fun j hj => hF.2.1 j (by omega), ?_, hTI⟩
        · intro y hy
          apply hTsub
          simp only [Finset.mem_sdiff, Finset.mem_filter] at hy ⊢
          exact ⟨⟨hy.1.1, by omega⟩, hy.2⟩
        · intro y hy
          by_cases hw : y ∈ W
          · exact Finset.mem_union_left _ hw
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hy, hw⟩)
      have hsumκ : ∀ S W : Finset X, cf S W ≤ C →
          ∑ j : Fin C, (if (j : ℕ) < cf S W then ((S' S).filter (fun i => ℓ S i = j)).card else 0)
            = ∑ j ∈ range (cf S W), ((S' S).filter (fun i => ℓ S i = j)).card := by
        intro S W hcC
        rw [Fin.sum_univ_eq_sum_range
          (fun j => if j < cf S W then ((S' S).filter (fun i => ℓ S i = j)).card else 0) C,
          ← Finset.sum_filter]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      obtain ⟨κf, hκf⟩ : ∃ κf : Finset X → Finset X → Fin C → ℕ, ∀ S W j,
          κf S W j = if (j : ℕ) < cf S W then ((S' S).filter (fun i => ℓ S i = j)).card else 0 :=
        ⟨_, fun _ _ _ => rfl⟩
      have hκsum : ∀ S W : Finset X, cf S W ≤ C →
          ∑ j, κf S W j = ∑ j ∈ range (cf S W), ((S' S).filter (fun i => ℓ S i = j)).card := by
        intro S W hcC
        simp only [hκf]
        exact hsumκ S W hcC
      have hcdet : ∀ W W₁ S S₁ : Finset X,
          (∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W₁, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10) →
          S₁ ∈ 𝓕 → S ∈ 𝓕 → κf S W = κf S₁ W₁ → cf S₁ W₁ ≤ cf S W := by
        intro W W₁ S S₁ hW₁ hS₁ hS hk
        by_contra hlt
        push_neg at hlt
        have hcC := (hkey S₁ W₁ hS₁).2.2.1
        have hc := hc1 W₁ hW₁ S₁ hS₁
        have := congrFun hk ⟨cf S₁ W₁ - 1, by omega⟩
        rw [hκf, hκf] at this
        dsimp only at this
        rw [if_neg (by omega), if_pos (by omega)] at this
        exact hsne W₁ hW₁ S₁ hS₁ this.symm
      refine ⟨Tf, κf, ?_, ?_, ?_⟩
      · intro S hS W
        exact (hkey S W hS).1
      · intro W hW S hS
        obtain ⟨-, hF, hcC, -, -⟩ := hkey S W hS
        have hc := hc1 W hW S hS
        refine ⟨?_, ?_, ?_⟩
        · intro h0
          have := congrFun h0 ⟨cf S W - 1, by omega⟩
          rw [hκf] at this
          simp only [Pi.zero_apply] at this
          dsimp only at this
          rw [if_pos (by omega)] at this
          exact hsne W hW S hS this
        · rw [hκsum S W hcC]
          have : ∑ j ∈ range (cf S W), ((S' S).filter (fun i => ℓ S i = j)).card
              = ∑ j ∈ range (cf S W), ((S' (Sf S W)).filter (fun i => ℓ (Sf S W) i = j)).card :=
            Finset.sum_congr rfl (fun j hj => (hF.2.1 j (Finset.mem_range.1 hj)).symm)
          rw [this, ← hlowcard]
          exact hP2 W hW S hS
        · intro j
          rw [hκf]
          by_cases h : (j : ℕ) < cf S W
          · right; rw [if_pos h]
          · left; rw [if_neg h]
      · intro Z v t
        by_cases hex : ∃ W : Finset X,
            (∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10) ∧
            ∃ S ∈ 𝓕, κf S W = v ∧ (Tf S W).card = t ∧ W ∪ Tf S W = Z
        · obtain ⟨W₀, hW₀, S₀, hS₀, hk₀, ht₀, hZ₀⟩ := hex
          subst hk₀ ht₀ hZ₀
          obtain ⟨-, hF₀, hcC₀, -, -⟩ := hkey S₀ W₀ hS₀
          refine ⟨(S' (Sf S₀ W₀)).filter (fun i => ℓ (Sf S₀ W₀) i < cf S₀ W₀), ?_, ?_⟩
          · rw [hκsum S₀ W₀ hcC₀, hlowcard]
            apply le_of_eq
            exact Finset.sum_congr rfl (fun j hj => hF₀.2.1 j (Finset.mem_range.1 hj))
          · intro W hW S hS hk ht hZ
            have hceq : cf S W = cf S₀ W₀ :=
              le_antisymm (hcdet W₀ W S₀ S hW hS hS₀ hk.symm) (hcdet W W₀ S S₀ hW₀ hS₀ hS hk)
            have hcC := (hkey S W hS).2.2.1
            have hF' : ((Sf S₀ W₀) ∈ 𝓕 ∧ (∀ j < cf S W, ((S' (Sf S₀ W₀)).filter (fun i => ℓ (Sf S₀ W₀) i = j)).card = ((S' S).filter (fun i => ℓ S i = j)).card) ∧ (S' (Sf S₀ W₀)).filter (fun i => ℓ (Sf S₀ W₀) i < cf S W) ⊆ W ∪ Tf S W ∧ ((∑ i, (if i ∈ S' (Sf S₀ W₀) ∧ cf S W ≤ ℓ (Sf S₀ W₀) i then (1/100:ℝ)^(ℓ (Sf S₀ W₀) i) else 0)) / 100 - (1/100:ℝ)^(cf S W) * ((((S' (Sf S₀ W₀)).filter (fun i => ℓ (Sf S₀ W₀) i < cf S W)).card : ℝ) - (((Tf S W).card : ℕ) : ℝ)) ≤ ∑ i ∈ W ∪ Tf S W, (if i ∈ S' (Sf S₀ W₀) ∧ cf S W ≤ ℓ (Sf S₀ W₀) i then (1/100:ℝ)^(ℓ (Sf S₀ W₀) i) else 0))) := by
              refine ⟨hF₀.1, ?_, ?_, ?_⟩
              · intro j hj
                rw [hF₀.2.1 j (hceq ▸ hj)]
                have := congrFun hk ⟨j, by omega⟩
                rw [hκf, hκf] at this
                dsimp only at this
                rw [if_pos hj, if_pos (hceq ▸ hj)] at this
                exact this.symm
              · rw [hZ, hceq]; exact hF₀.2.2.1
              · rw [hZ, ht, hceq]; exact hF₀.2.2.2
            have := hP1 S W hS _ hF'
            rw [hceq] at this
            exact this
        · refine ⟨∅, by simp, ?_⟩
          intro W hW S hS hk ht hZ
          exact absurd ⟨W, hW, S, hS, hk, ht, hZ⟩ hex
  open MeasureTheory ProbabilityTheory Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_frag_num_h1 : ∀ (j : ℕ) (hj : 8 ≤ j), 100 ^ 5 * (j + 1) ^ 3 ≤ 100 ^ j :=
    fun (j : ℕ) (hj : 8 ≤ j) => by
      induction j, hj using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        have h2 : (n + 1 + 1) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have e : (2 * (n + 1)) ^ 3 = 8 * (n + 1) ^ 3 := by ring
        calc 100 ^ 5 * (n + 1 + 1) ^ 3 ≤ 100 ^ 5 * (8 * (n + 1) ^ 3) := by rw [← e]; omega
          _ ≤ 100 ^ 5 * (n + 1) ^ 3 * 100 := by ring_nf; omega
          _ ≤ 100 ^ n * 100 := Nat.mul_le_mul_right _ ih
          _ = 100 ^ (n + 1) := (pow_succ _ _).symm
  open MeasureTheory ProbabilityTheory Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_frag_num_h2 : ∀ (j k : ℕ) (h : 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k), j - 8 + 1 ≤ 100 ^ k :=
    fun (j k : ℕ) (h : 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k) => by
      by_contra hc
      push_neg at hc
      have hk1 : 1 ≤ 100 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have hj : 8 ≤ j := by omega
      have hlt : 100 ^ k < j + 1 := by omega
      have h3 : 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k < 100 ^ 5 * (j + 1) ^ 2 * (j + 1) :=
        Nat.mul_lt_mul_of_pos_left hlt (by positivity)
      have := LA_frag_num_h1 j hj
      have e : 100 ^ 5 * (j + 1) ^ 2 * (j + 1) = 100 ^ 5 * (j + 1) ^ 3 := by ring
      omega
  open MeasureTheory ProbabilityTheory Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_frag_num_h3 : ∀ (j k : ℕ) (h : 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k), (2 / 10 ^ 7 : ℝ) ^ (100 ^ k) ≤ (2 / 10 ^ 7) * (1 / 4) ^ (j - 8) :=
    fun (j k : ℕ) (h : 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k) => by
      have h2 := LA_frag_num_h2 j k h
      calc (2 / 10 ^ 7 : ℝ) ^ (100 ^ k) ≤ (2 / 10 ^ 7) ^ (j - 8 + 1) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) h2
        _ = (2 / 10 ^ 7) * (2 / 10 ^ 7) ^ (j - 8) := by rw [pow_succ]; ring
        _ ≤ (2 / 10 ^ 7) * (1 / 4) ^ (j - 8) := by
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
              (by norm_num)
  open MeasureTheory ProbabilityTheory Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_frag_num_h4 : ∀ (j : ℕ), ((j : ℝ) + 1) * ((2 / 10 ^ 7) * (1 / 4) ^ (j - 8)) ≤ (2 / 10 ^ 7) * 4 ^ 8 * (1 / 2) ^ j :=
    fun (j : ℕ) => by
      have e1 : (1 / 4 : ℝ) ^ (j - 8) = 4 ^ 8 * (1 / 4) ^ (j - 8 + 8) := by
        rw [pow_add]; field_simp
      have e2 : (1 / 4 : ℝ) ^ (j - 8 + 8) ≤ (1 / 4) ^ j :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have e3 : (1 / 4 : ℝ) ^ j = (1 / 2) ^ j * (1 / 2) ^ j := by
        rw [← mul_pow]; norm_num
      have e4 : ((j : ℝ) + 1) * (1 / 2) ^ j ≤ 1 := by
        have : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
        have : ((j : ℝ) + 1) ≤ 2 ^ j := by exact_mod_cast this
        rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
        exact this
      rw [e1]
      have hp : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
      have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
      calc ((j : ℝ) + 1) * ((2 / 10 ^ 7) * (4 ^ 8 * (1 / 4) ^ (j - 8 + 8)))
          ≤ ((j : ℝ) + 1) * ((2 / 10 ^ 7) * (4 ^ 8 * ((1 / 2) ^ j * (1 / 2) ^ j))) := by
            rw [← e3]; gcongr
        _ = (2 / 10 ^ 7) * 4 ^ 8 * (1 / 2) ^ j * (((j : ℝ) + 1) * (1 / 2) ^ j) := by ring
        _ ≤ (2 / 10 ^ 7) * 4 ^ 8 * (1 / 2) ^ j * 1 := by gcongr
        _ = _ := by ring
  open MeasureTheory ProbabilityTheory Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_frag_num_h5 : ∀ (j : ℕ), ∑ v ∈ insert 0 (((Finset.range (j + 1)).filter
            (fun k => 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k)).image
            (fun k => 100 ^ k)), (2 / 10 ^ 7 : ℝ) ^ v
        ≤ Real.exp ((2 / 10 ^ 7) * 4 ^ 8 * (1 / 2) ^ j) :=
    fun (j : ℕ) => by
      have h0 : (0 : ℕ) ∉ ((Finset.range (j + 1)).filter
              (fun k => 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k)).image (fun k => 100 ^ k) := by
        simp
      rw [Finset.sum_insert h0, pow_zero]
      refine le_trans ?_ (Real.add_one_le_exp _)
      rw [add_comm]
      gcongr
      refine (Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)).trans ?_
      calc ∑ k ∈ (Finset.range (j + 1)).filter
              (fun k => 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k), (2 / 10 ^ 7 : ℝ) ^ (100 ^ k)
          ≤ ∑ k ∈ (Finset.range (j + 1)).filter
              (fun k => 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k),
              (2 / 10 ^ 7 : ℝ) * (1 / 4) ^ (j - 8) := by
            apply Finset.sum_le_sum
            intro k hk
            exact LA_frag_num_h3 j k (Finset.mem_filter.1 hk).2
        _ ≤ ∑ k ∈ Finset.range (j + 1), (2 / 10 ^ 7 : ℝ) * (1 / 4) ^ (j - 8) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)
        _ = ((j : ℝ) + 1) * ((2 / 10 ^ 7) * (1 / 4) ^ (j - 8)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ _ := LA_frag_num_h4 j
  open MeasureTheory ProbabilityTheory Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_frag_num : ∀ (C : ℕ), ∑ sg ∈ (Fintype.piFinset (fun j : Fin C => insert 0
          (((Finset.range ((j : ℕ) + 1)).filter
            (fun k => 100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)).image
            (fun k => 100 ^ k)))).erase 0,
        (2 / 10 ^ 7 : ℝ) ^ (∑ j, sg j) ≤ 1 / 4 :=
    fun (C : ℕ) => by
      classical
      have hmem : (0 : Fin C → ℕ) ∈ Fintype.piFinset (fun j : Fin C => insert 0
            (((Finset.range ((j : ℕ) + 1)).filter
              (fun k => 100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)).image
              (fun k => 100 ^ k))) :=
        Fintype.mem_piFinset.2 (fun j => Finset.mem_insert_self _ _)
      rw [Finset.sum_erase_eq_sub hmem]
      simp only [Pi.zero_apply, Finset.sum_const_zero, pow_zero]
      have hprod : ∀ τ : Fin C → ℕ, (2 / 10 ^ 7 : ℝ) ^ (∑ j, τ j) = ∏ j, (2 / 10 ^ 7 : ℝ) ^ (τ j) :=
        fun τ => (Finset.prod_pow_eq_pow_sum _ _ _).symm
      simp only [hprod]
      rw [← Finset.prod_univ_sum]
      have hle : ∏ j : Fin C, ∑ v ∈ insert 0
            (((Finset.range ((j : ℕ) + 1)).filter
              (fun k => 100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)).image
              (fun k => 100 ^ k)), (2 / 10 ^ 7 : ℝ) ^ v
          ≤ ∏ j : Fin C, Real.exp ((2 / 10 ^ 7) * 4 ^ 8 * (1 / 2) ^ (j : ℕ)) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
          (fun j _ => LA_frag_num_h5 j)
      rw [← Real.exp_sum, ← Finset.mul_sum,
        Fin.sum_univ_eq_sum_range (fun j => (1 / 2 : ℝ) ^ j)] at hle
      have hg := sum_geometric_two_le C
      have hexp : Real.exp ((2 / 10 ^ 7) * 4 ^ 8 * ∑ j ∈ Finset.range C, (1 / 2 : ℝ) ^ j)
          ≤ Real.exp ((2 / 10 ^ 7) * 4 ^ 8 * 2) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hg (by norm_num))
      have hb := Real.exp_bound_div_one_sub_of_interval'
        (x := (2 / 10 ^ 7) * 4 ^ 8 * 2) (by norm_num) (by norm_num)
      have h54 : (1 : ℝ) / (1 - (2 / 10 ^ 7) * 4 ^ 8 * 2) ≤ 5 / 4 := by norm_num
      linarith
  open MeasureTheory ProbabilityTheory Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_frag_cnt : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (p : ℝ) (hp0 : 0 < p)
      (hpJ : 10 ^ 8 * p ≤ 1) (C : ℕ) (𝓑 : Finset (Finset X)) (𝓣 : Finset X → Finset (Finset X))
      (κ : Finset X → Finset X → (Fin C → ℕ))
      (hdisj : ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, Disjoint W T)
      (hleg : ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, ∀ j : Fin C, κ W T j = 0 ∨
          ∃ k : ℕ, k ≤ (j : ℕ) ∧ κ W T j = 100 ^ k ∧
            100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)
      (hne : ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, κ W T ≠ 0)
      (hbig : ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, 9 * ∑ j, κ W T j ≤ 10 * T.card)
      (hR : ∀ (Z : Finset X) (sg : Fin C → ℕ) (t : ℕ), ∃ R : Finset X, R.card ≤ ∑ j, sg j ∧
          ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, κ W T = sg → T.card = t → W ∪ T = Z → T ⊆ R), ∑ W ∈ 𝓑, (10 ^ 8 * p) ^ W.card * (1 - 10 ^ 8 * p) ^ (Fintype.card X - W.card) *
          ∑ T ∈ 𝓣 W, p ^ T.card ≤ 1 / 4 :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (p : ℝ) (hp0 : 0 < p)
        (hpJ : 10 ^ 8 * p ≤ 1) (C : ℕ) (𝓑 : Finset (Finset X)) (𝓣 : Finset X → Finset (Finset X))
        (κ : Finset X → Finset X → (Fin C → ℕ))
        (hdisj : ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, Disjoint W T)
        (hleg : ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, ∀ j : Fin C, κ W T j = 0 ∨
            ∃ k : ℕ, k ≤ (j : ℕ) ∧ κ W T j = 100 ^ k ∧
              100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)
        (hne : ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, κ W T ≠ 0)
        (hbig : ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, 9 * ∑ j, κ W T j ≤ 10 * T.card)
        (hR : ∀ (Z : Finset X) (sg : Fin C → ℕ) (t : ℕ), ∃ R : Finset X, R.card ≤ ∑ j, sg j ∧
            ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, κ W T = sg → T.card = t → W ∪ T = Z → T ⊆ R) => by
      classical
      set q : ℝ := 10 ^ 8 * p with hq
      set n := Fintype.card X with hn
      have hq0 : 0 ≤ q := by positivity
      have hq1 : 0 ≤ 1 - q := by linarith
      let μ : Finset X → ℝ := fun W => q ^ W.card * (1 - q) ^ (n - W.card)
      have hμ0 : ∀ W, 0 ≤ μ W := fun W => mul_nonneg (pow_nonneg hq0 _) (pow_nonneg hq1 _)
      have hμsum : ∑ Z : Finset X, μ Z = 1 := by
        have := Finset.sum_pow_mul_eq_add_pow q (1 - q) (Finset.univ : Finset X)
        rw [Finset.powerset_univ, Finset.card_univ] at this
        simp only [μ]; rw [this]; simp
      let Leg : Fin C → Finset ℕ := fun j => insert 0 (((Finset.range ((j : ℕ) + 1)).filter
              (fun k => 100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)).image
              (fun k => 100 ^ k))
      let K := (Fintype.piFinset Leg).erase 0
      let N : (Fin C → ℕ) → ℕ := fun τ => ∑ j, τ j
      let y : ℝ := 1 / 10 ^ 7
      let R : Finset X → (Fin C → ℕ) → ℕ → Finset X := fun Z τ t => (hR Z τ t).choose
      have hRc : ∀ Z τ t, (R Z τ t).card ≤ N τ := fun Z τ t => (hR Z τ t).choose_spec.1
      have hRs : ∀ Z τ t, ∀ W ∈ 𝓑, ∀ T ∈ 𝓣 W, κ W T = τ → T.card = t → W ∪ T = Z →
          T ⊆ R Z τ t := fun Z τ t => (hR Z τ t).choose_spec.2
      have step1 : ∑ W ∈ 𝓑, μ W * ∑ T ∈ 𝓣 W, p ^ T.card ≤
          ∑ x ∈ 𝓑.sigma 𝓣, μ (x.1 ∪ x.2) * y ^ N (κ x.1 x.2) := by
        rw [Finset.sum_sigma]
        apply Finset.sum_le_sum
        intro W hW
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro T hT
        have hd := hdisj W hW T hT
        have hcard : (W ∪ T).card = W.card + T.card := Finset.card_union_of_disjoint hd
        have hle : W.card + T.card ≤ n := hcard ▸ Finset.card_le_univ _
        have hb := hbig W hW T hT
        have e1 : μ W * p ^ T.card = μ (W ∪ T) * ((1 - q) ^ T.card * (1 / 10 ^ 8) ^ T.card) := by
          simp only [μ]; rw [hcard]
          have : n - W.card = (n - (W.card + T.card)) + T.card := by omega
          rw [this, pow_add, pow_add]
          have hp' : p = q * (1/10^8) := by rw [hq]; field_simp
          have hpt : p ^ T.card = q ^ T.card * (1/10^8 : ℝ) ^ T.card := by rw [← mul_pow, ← hp']
          rw [hpt]; ring
        rw [e1]
        apply mul_le_mul_of_nonneg_left _ (hμ0 _)
        calc (1 - q) ^ T.card * (1 / 10 ^ 8) ^ T.card ≤ 1 * (1 / 10 ^ 8 : ℝ) ^ T.card := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact pow_le_one₀ hq1 (by linarith)
          _ = (1/10 : ℝ) ^ (8 * T.card) := by rw [one_mul, pow_mul]; norm_num
          _ ≤ (1/10 : ℝ) ^ (7 * N (κ W T)) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by simp only [N]; omega)
          _ = y ^ N (κ W T) := by rw [pow_mul]; norm_num
      have hmaps : ∀ x ∈ 𝓑.sigma 𝓣, κ x.1 x.2 ∈ K := by
        rintro ⟨W, T⟩ hx
        rw [Finset.mem_sigma] at hx
        simp only [K, Finset.mem_erase, Fintype.mem_piFinset]
        refine ⟨hne W hx.1 T hx.2, fun j => ?_⟩
        rcases hleg W hx.1 T hx.2 j with h | ⟨k, hk, h1, h2⟩
        · simp [Leg, h]
        · simp only [Leg, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
          right; exact ⟨k, ⟨by omega, h2⟩, h1.symm⟩
      have hclass : ∀ τ ∈ K, ∑ x ∈ (𝓑.sigma 𝓣).filter (fun x => κ x.1 x.2 = τ),
          μ (x.1 ∪ x.2) * y ^ N (κ x.1 x.2) ≤ (2 / 10 ^ 7 : ℝ) ^ (∑ j, τ j) := by
        intro τ _
        set Pτ := (𝓑.sigma 𝓣).filter (fun x => κ x.1 x.2 = τ) with hPτ
        have e : ∑ x ∈ Pτ, μ (x.1 ∪ x.2) * y ^ N (κ x.1 x.2) =
            y ^ N τ * ∑ x ∈ Pτ, μ (x.1 ∪ x.2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx
          rw [(Finset.mem_filter.1 hx).2]; exact mul_comm _ _
        rw [e]
        have hmt : ∀ x ∈ Pτ, x.2.card ∈ Finset.range (N τ + 1) := by
          rintro ⟨W, T⟩ hx
          simp only [Pτ, Finset.mem_filter, Finset.mem_sigma] at hx
          rw [Finset.mem_range, Nat.lt_succ_iff]
          exact (Finset.card_le_card (hRs (W ∪ T) τ T.card W hx.1.1 T hx.1.2 hx.2 rfl rfl)).trans
            (hRc _ _ _)
        rw [← Finset.sum_fiberwise_of_maps_to hmt]
        have ht : ∀ t, ∑ x ∈ Pτ.filter (fun x => x.2.card = t), μ (x.1 ∪ x.2) ≤
            ((N τ).choose t : ℝ) := by
          intro t
          set Q := Pτ.filter (fun x => x.2.card = t) with hQ
          let φ : (Σ _ : Finset X, Finset X) → (Σ _ : Finset X, Finset X) :=
            fun x => ⟨x.1 ∪ x.2, x.2⟩
          have hinj : Set.InjOn φ Q := by
            rintro ⟨W, T⟩ hx ⟨W', T'⟩ hx' h
            simp only [φ, Sigma.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            have h2' : T = T' := eq_of_heq h2
            subst h2'
            simp only [Q, Pτ, Finset.coe_filter, Finset.mem_filter, Finset.mem_sigma,
              Set.mem_setOf_eq] at hx hx'
            have d1 := hdisj W hx.1.1.1 T hx.1.1.2
            have d2 := hdisj W' hx'.1.1.1 T hx'.1.1.2
            have : W = W' := by
              rw [← Finset.union_sdiff_cancel_right d1, ← Finset.union_sdiff_cancel_right d2, h1]
            subst this; rfl
          rw [← Finset.sum_image (f := fun z : (Σ _ : Finset X, Finset X) => μ z.1) hinj]
          calc ∑ z ∈ Q.image φ, μ z.1
              ≤ ∑ z ∈ (Finset.univ : Finset (Finset X)).sigma
                  (fun Z => (R Z τ t).powersetCard t), μ z.1 := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro z hz
                  rw [Finset.mem_image] at hz
                  obtain ⟨⟨W, T⟩, hx, rfl⟩ := hz
                  simp only [Q, Pτ, Finset.mem_filter, Finset.mem_sigma] at hx
                  simp only [φ, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_powersetCard]
                  exact ⟨hRs (W ∪ T) τ t W hx.1.1.1 T hx.1.1.2 hx.1.2 hx.2 rfl, hx.2⟩
                · intros; exact hμ0 _
            _ = ∑ Z : Finset X, ((R Z τ t).card.choose t : ℝ) * μ Z := by
                rw [Finset.sum_sigma]; apply Finset.sum_congr rfl; intro Z _
                show ∑ s ∈ (R Z τ t).powersetCard t, μ Z = _
                rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
            _ ≤ ∑ Z : Finset X, ((N τ).choose t : ℝ) * μ Z := by
                apply Finset.sum_le_sum; intro Z _
                apply mul_le_mul_of_nonneg_right _ (hμ0 _)
                exact_mod_cast Nat.choose_le_choose t (hRc Z τ t)
            _ = ((N τ).choose t : ℝ) := by rw [← Finset.mul_sum, hμsum, mul_one]
        calc y ^ N τ * ∑ t ∈ Finset.range (N τ + 1), ∑ x ∈ Pτ.filter (fun x => x.2.card = t),
              μ (x.1 ∪ x.2) ≤ y ^ N τ * ∑ t ∈ Finset.range (N τ + 1), ((N τ).choose t : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Finset.sum_le_sum (fun t _ => ht t)
          _ = y ^ N τ * 2 ^ N τ := by
              congr 1; exact_mod_cast Nat.sum_range_choose (N τ)
          _ = (2 / 10 ^ 7 : ℝ) ^ (∑ j, τ j) := by rw [← mul_pow]; simp only [y, N]; norm_num
      have key : ∑ W ∈ 𝓑, μ W * ∑ T ∈ 𝓣 W, p ^ T.card ≤ 1 / 4 := by
        refine step1.trans ?_
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine (Finset.sum_le_sum hclass).trans ?_
        exact LA_frag_num C
      exact key
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_frag : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (p : ℝ) (hp0 : 0 < p)
      (hpJ : 10 ^ 8 * p ≤ 1) (𝓕 : Finset (Finset X)) (S' : Finset X → Finset X)
      (ℓ : Finset X → X → ℕ)
      (hsum : ∀ S ∈ 𝓕, (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ S' S, (1 / 100 : ℝ) ^ (ℓ S i))
      (hlegal : ∀ S ∈ 𝓕, ∀ j : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 0 ∨
          ((∃ k : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 100 ^ k) ∧
            100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * ((S' S).filter (fun i => ℓ S i = j)).card ∧
            ((S' S).filter (fun i => ℓ S i = j)).card < 2 * 100 ^ j)), ∃ U : Finset X → Finset (Finset X),
        (∀ W : Finset X, (∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10) →
          ∀ S ∈ 𝓕, ∃ T ∈ U W, T ⊆ S' S) ∧
        ∑ W ∈ (Finset.univ : Finset (Finset X)).filter
            (fun W => ∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10),
          (10 ^ 8 * p) ^ W.card * (1 - 10 ^ 8 * p) ^ (Fintype.card X - W.card) *
            ∑ T ∈ U W, p ^ T.card ≤ 1 / 4 :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (p : ℝ) (hp0 : 0 < p)
        (hpJ : 10 ^ 8 * p ≤ 1) (𝓕 : Finset (Finset X)) (S' : Finset X → Finset X)
        (ℓ : Finset X → X → ℕ)
        (hsum : ∀ S ∈ 𝓕, (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ S' S, (1 / 100 : ℝ) ^ (ℓ S i))
        (hlegal : ∀ S ∈ 𝓕, ∀ j : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 0 ∨
            ((∃ k : ℕ, ((S' S).filter (fun i => ℓ S i = j)).card = 100 ^ k) ∧
              100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * ((S' S).filter (fun i => ℓ S i = j)).card ∧
              ((S' S).filter (fun i => ℓ S i = j)).card < 2 * 100 ^ j)) => by
      classical
      have hC : ∀ S ∈ 𝓕, ∀ i ∈ S' S, ℓ S i < (𝓕.sup fun S => (S' S).sup (ℓ S)) + 1 := by
        intro S hS i hi
        have h1 : ℓ S i ≤ (S' S).sup (ℓ S) := Finset.le_sup hi
        have h2 : (S' S).sup (ℓ S) ≤ 𝓕.sup (fun S => (S' S).sup (ℓ S)) :=
          Finset.le_sup (f := fun S => (S' S).sup (ℓ S)) hS
        omega
      obtain ⟨T, κ, hTsub, hgood, hRdet⟩ := LA_frag_det X 𝓕 S' ℓ hsum hlegal _ hC
      refine ⟨fun W => 𝓕.image (fun S => T S W), ?_, ?_⟩
      · intro W _ S hS
        exact ⟨T S W, Finset.mem_image_of_mem _ hS, (hTsub S hS W).trans Finset.sdiff_subset⟩
      · let key : Finset X → Finset X →
            (Fin ((𝓕.sup fun S => (S' S).sup (ℓ S)) + 1) → ℕ) := fun W T' =>
          if h : ∃ S ∈ 𝓕, T S W = T' then κ h.choose W else 0
        have hkey : ∀ W, ∀ T' ∈ 𝓕.image (fun S => T S W),
            ∃ S ∈ 𝓕, T S W = T' ∧ key W T' = κ S W := by
          intro W T' hT'
          have h : ∃ S ∈ 𝓕, T S W = T' := by simpa using hT'
          exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, by simp only [key, dif_pos h]⟩
        apply LA_frag_cnt X p hp0 hpJ _ _ _ key
        · intro W _ T' hT'
          obtain ⟨S, hS, rfl, -⟩ := hkey W T' hT'
          exact Finset.disjoint_of_subset_right (hTsub S hS W) Finset.disjoint_sdiff
        · intro W hW T' hT' j
          obtain ⟨S, hS, rfl, hk⟩ := hkey W _ hT'
          rw [hk]
          rcases (hgood W (Finset.mem_filter.1 hW).2 S hS).2.2 j with h0 | hs
          · exact Or.inl h0
          · rw [hs]
            rcases hlegal S hS j with h0 | ⟨⟨k, hk⟩, hlo, hhi⟩
            · exact Or.inl h0
            · right
              refine ⟨k, ?_, hk, hk ▸ hlo⟩
              by_contra hkj
              push_neg at hkj
              have : 100 ^ ((j : ℕ) + 1) ≤ 100 ^ k := Nat.pow_le_pow_right (by norm_num) hkj
              rw [pow_succ] at this
              omega
        · intro W hW T' hT'
          obtain ⟨S, hS, rfl, hk⟩ := hkey W _ hT'
          rw [hk]
          exact (hgood W (Finset.mem_filter.1 hW).2 S hS).1
        · intro W hW T' hT'
          obtain ⟨S, hS, rfl, hk⟩ := hkey W _ hT'
          rw [hk]
          exact (hgood W (Finset.mem_filter.1 hW).2 S hS).2.1
        · intro Z v t
          obtain ⟨R, hRc, hR⟩ := hRdet Z v t
          refine ⟨R, hRc, ?_⟩
          intro W hW T' hT' hkv htc hZ
          obtain ⟨S, hS, rfl, hk⟩ := hkey W _ hT'
          exact hR W (Finset.mem_filter.1 hW).2 S hS (hk ▸ hkv) htc hZ
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_core2 : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (p : ℝ) (hp0 : 0 < p)
      (hpJ : 10 ^ 8 * p ≤ 1) (𝓕 : Finset (Finset X)) (w : Finset X → X → ℝ)
      (hw : ∀ S ∈ 𝓕, ∀ i, 0 ≤ w S i) (h1 : ∀ S ∈ 𝓕, 1 ≤ ∑ i ∈ S, w S i)
      (hns : ¬ ∃ 𝓖 : Finset (Finset X), (∀ S ∈ 𝓕, ∃ G ∈ 𝓖, G ⊆ S) ∧ ∑ G ∈ 𝓖, p ^ G.card ≤ 1 / 2)
      (g : Finset X → ℝ) (hg : ∀ W : Finset X, ∀ S ∈ 𝓕, ∑ i ∈ S ∩ W, w S i ≤ g W), (1 : ℝ) / 10 ^ 11 ≤ ∑ W : Finset X, (10 ^ 8 * p) ^ W.card *
        (1 - 10 ^ 8 * p) ^ (Fintype.card X - W.card) * g W :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (p : ℝ) (hp0 : 0 < p)
        (hpJ : 10 ^ 8 * p ≤ 1) (𝓕 : Finset (Finset X)) (w : Finset X → X → ℝ)
        (hw : ∀ S ∈ 𝓕, ∀ i, 0 ≤ w S i) (h1 : ∀ S ∈ 𝓕, 1 ≤ ∑ i ∈ S, w S i)
        (hns : ¬ ∃ 𝓖 : Finset (Finset X), (∀ S ∈ 𝓕, ∃ G ∈ 𝓖, G ⊆ S) ∧ ∑ G ∈ 𝓖, p ^ G.card ≤ 1 / 2)
        (g : Finset X → ℝ) (hg : ∀ W : Finset X, ∀ S ∈ 𝓕, ∑ i ∈ S ∩ W, w S i ≤ g W) => by
      classical
      obtain ⟨S', ℓ, hprep⟩ := LA_prep X 𝓕 w hw h1
      obtain ⟨U, hUcov, hUsum⟩ := LA_frag X p hp0 hpJ 𝓕 S' ℓ (fun S hS => (hprep S hS).2.2.1)
        (fun S hS => (hprep S hS).2.2.2)
      set q : ℝ := 10 ^ 8 * p with hq
      set μ : Finset X → ℝ := fun W => q ^ W.card * (1 - q) ^ (Fintype.card X - W.card) with hμdef
      set bad : Finset X → Prop :=
        fun W => ∀ S ∈ 𝓕, ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) < 1 / 10 ^ 10 with hbaddef
      have hq0 : 0 ≤ q := by positivity
      have hq1 : 0 ≤ 1 - q := by linarith
      have hμ0 : ∀ W, 0 ≤ μ W := fun W => by positivity
      have htot : ∑ W : Finset X, μ W = 1 := by
        have h := Finset.sum_pow_mul_eq_add_pow q (1 - q) (Finset.univ : Finset X)
        rw [Finset.powerset_univ, _root_.add_sub_cancel, one_pow, Finset.card_univ] at h
        exact h
      have hcost : ∀ W, bad W → 1 / 2 < ∑ T ∈ U W, p ^ T.card := by
        intro W hW
        by_contra hle
        push_neg at hle
        exact hns ⟨U W, fun S hS => by
          obtain ⟨T, hT, hTS⟩ := hUcov W hW S hS
          exact ⟨T, hT, hTS.trans (hprep S hS).1⟩, hle⟩
      have hbad : ∑ W ∈ Finset.univ.filter bad, μ W ≤ 1 / 2 := by
        have h2 : ∑ W ∈ Finset.univ.filter bad, μ W * (1 / 2) ≤
            ∑ W ∈ Finset.univ.filter bad, μ W * ∑ T ∈ U W, p ^ T.card :=
          Finset.sum_le_sum (fun W hW =>
            mul_le_mul_of_nonneg_left (hcost W (Finset.mem_filter.1 hW).2).le (hμ0 W))
        rw [← Finset.sum_mul] at h2
        have h3 : ∑ W ∈ Finset.univ.filter bad, μ W * ∑ T ∈ U W, p ^ T.card ≤ 1 / 4 := by
          refine le_trans (le_of_eq ?_) hUsum
          refine Finset.sum_congr rfl (fun W _ => ?_)
          simp only [hμdef]
        linarith
      have hne : 𝓕.Nonempty := by
        rcases 𝓕.eq_empty_or_nonempty with h | h
        · exact absurd ⟨∅, by simp [h], by simp⟩ hns
        · exact h
      obtain ⟨S₀, hS₀⟩ := hne
      have hg0 : ∀ W, 0 ≤ g W := fun W =>
        le_trans (Finset.sum_nonneg (fun i _ => hw S₀ hS₀ i)) (hg W S₀ hS₀)
      have hggood : ∀ W, ¬ bad W → 1 / 10 ^ 10 ≤ g W := by
        intro W hW
        simp only [hbaddef, not_forall, not_lt] at hW
        obtain ⟨S, hS, hle⟩ := hW
        calc (1 : ℝ) / 10 ^ 10 ≤ ∑ i ∈ S' S ∩ W, (1 / 100 : ℝ) ^ (ℓ S i) := hle
          _ ≤ ∑ i ∈ S' S ∩ W, w S i :=
              Finset.sum_le_sum (fun i hi => (hprep S hS).2.1 i (Finset.mem_inter.1 hi).1)
          _ ≤ ∑ i ∈ S ∩ W, w S i :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_inter_right (hprep S hS).1)
                (fun i _ _ => hw S hS i)
          _ ≤ g W := hg W S hS
      have hgood : 1 / 2 ≤ ∑ W ∈ Finset.univ.filter (fun W => ¬ bad W), μ W := by
        have := Finset.sum_filter_add_sum_filter_not Finset.univ bad μ
        linarith
      calc (1 : ℝ) / 10 ^ 11 ≤ (1 / 2) * (1 / 10 ^ 10) := by norm_num
        _ ≤ (∑ W ∈ Finset.univ.filter (fun W => ¬ bad W), μ W) * (1 / 10 ^ 10) :=
            mul_le_mul_of_nonneg_right hgood (by norm_num)
        _ = ∑ W ∈ Finset.univ.filter (fun W => ¬ bad W), μ W * (1 / 10 ^ 10) := by rw [Finset.sum_mul]
        _ ≤ ∑ W ∈ Finset.univ.filter (fun W => ¬ bad W), μ W * g W :=
            Finset.sum_le_sum (fun W hW =>
              mul_le_mul_of_nonneg_left (hggood W (Finset.mem_filter.1 hW).2) (hμ0 W))
        _ ≤ ∑ W : Finset X, μ W * g W :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun W _ _ => mul_nonneg (hμ0 W) (hg0 W))
        _ = _ := by simp only [hμdef]
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_core : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
      (𝓕 : Finset (Finset X)) (w : Finset X → X → ℝ)
      (hw : ∀ S ∈ 𝓕, ∀ i, 0 ≤ w S i) (h1 : ∀ S ∈ 𝓕, 1 ≤ ∑ i ∈ S, w S i)
      (hns : ¬ ∃ 𝓖 : Finset (Finset X), (∀ S ∈ 𝓕, ∃ G ∈ 𝓖, G ⊆ S) ∧ ∑ G ∈ 𝓖, p ^ G.card ≤ 1 / 2)
      (g : Finset X → ℝ) (hg : ∀ W : Finset X, ∀ S ∈ 𝓕, ∑ i ∈ S ∩ W, w S i ≤ g W), (1 : ℝ) / 10 ^ 30 ≤ ∑ W : Finset X, p ^ W.card * (1 - p) ^ (Fintype.card X - W.card) * g W :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
        (𝓕 : Finset (Finset X)) (w : Finset X → X → ℝ)
        (hw : ∀ S ∈ 𝓕, ∀ i, 0 ≤ w S i) (h1 : ∀ S ∈ 𝓕, 1 ≤ ∑ i ∈ S, w S i)
        (hns : ¬ ∃ 𝓖 : Finset (Finset X), (∀ S ∈ 𝓕, ∃ G ∈ 𝓖, G ⊆ S) ∧ ∑ G ∈ 𝓖, p ^ G.card ≤ 1 / 2)
        (g : Finset X → ℝ) (hg : ∀ W : Finset X, ∀ S ∈ 𝓕, ∑ i ∈ S ∩ W, w S i ≤ g W) => by
      classical
      have hne : 𝓕.Nonempty := by
        rcases 𝓕.eq_empty_or_nonempty with h | h
        · exact absurd ⟨∅, by simp [h], by simp⟩ hns
        · exact h
      by_cases hJ : 10 ^ 8 * p ≤ 1
      · have hsel : ∀ W : Finset X, ∃ S ∈ 𝓕, ∀ S' ∈ 𝓕,
            ∑ i ∈ S' ∩ W, w S' i ≤ ∑ i ∈ S ∩ W, w S i :=
          fun W => Finset.exists_max_image 𝓕 (fun S => ∑ i ∈ S ∩ W, w S i) hne
        choose! SW hSW hSWmax using hsel
        set V : Finset X → X → ℝ := fun W i => if i ∈ SW W then w (SW W) i else 0 with hVdef
        have hV : ∀ W i, 0 ≤ V W i := fun W i => by
          simp only [hVdef]
          split_ifs
          · exact hw _ (hSW W) i
          · exact le_refl 0
        have hVsum : ∀ W U : Finset X, ∑ i ∈ U, V W i = ∑ i ∈ SW W ∩ U, w (SW W) i := by
          intro W U
          simp only [hVdef]
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
        have hthin := LA_thin X p (10 ^ 8 * p) hp0.le (by nlinarith) hJ (by positivity) V hV g
          (fun W U _ => by rw [hVsum W U]; exact hg U _ (hSW W))
        have hcore := LA_core2 X p hp0 hJ 𝓕 w hw h1 hns (fun W => ∑ i ∈ W, V W i)
          (fun W S hS => by beta_reduce; rw [hVsum W W]; exact hSWmax W S hS)
        have hpq : p / (10 ^ 8 * p) = 1 / 10 ^ 8 := by field_simp
        calc (1 : ℝ) / 10 ^ 30 ≤ p / (10 ^ 8 * p) * (1 / 10 ^ 11) := by rw [hpq]; norm_num
          _ ≤ p / (10 ^ 8 * p) * ∑ W : Finset X, (10 ^ 8 * p) ^ W.card *
                (1 - 10 ^ 8 * p) ^ (Fintype.card X - W.card) * ∑ i ∈ W, V W i :=
              mul_le_mul_of_nonneg_left hcore (by positivity)
          _ ≤ _ := hthin
      · push_neg at hJ
        obtain ⟨S₀, hS₀⟩ := hne
        set V : Finset X → X → ℝ := fun _ i => if i ∈ S₀ then w S₀ i else 0 with hVdef
        have hV : ∀ W i, 0 ≤ V W i := fun W i => by
          simp only [hVdef]
          split_ifs
          · exact hw _ hS₀ i
          · exact le_refl 0
        have hVsum : ∀ W U : Finset X, ∑ i ∈ U, V W i = ∑ i ∈ S₀ ∩ U, w S₀ i := by
          intro W U
          simp only [hVdef]
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
        have hthin := LA_thin X p 1 hp0.le hp1.le le_rfl one_pos V hV g
          (fun W U _ => by rw [hVsum W U]; exact hg U S₀ hS₀)
        have hone : ∑ W : Finset X, (1 : ℝ) ^ W.card * (1 - 1) ^ (Fintype.card X - W.card) *
            ∑ i ∈ W, V W i = ∑ i ∈ S₀, w S₀ i := by
          rw [Finset.sum_eq_single Finset.univ]
          · rw [hVsum Finset.univ Finset.univ]
            simp
          · intro W _ hW
            have hlt : W.card < Fintype.card X := by
              rw [← Finset.card_univ]
              exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hW)
            rw [_root_.sub_self, zero_pow (by omega)]
            simp
          · simp
        rw [hone] at hthin
        have := h1 S₀ hS₀
        calc (1 : ℝ) / 10 ^ 30 ≤ p / 1 * 1 := by
              rw [div_one, mul_one]
              have : (1 : ℝ) / 10 ^ 30 < 1 / 10 ^ 8 := by norm_num
              have h8 : 1 / 10 ^ 8 < p := by
                rw [div_lt_iff₀ (by positivity)]
                linarith
              linarith
          _ ≤ p / 1 * ∑ i ∈ S₀, w S₀ i := by
              apply mul_le_mul_of_nonneg_left this (by positivity)
          _ ≤ _ := hthin
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_fd_lexmin : ∀ (X : Type u_1) (P : ℕ → Finset X → Prop) (h : ∃ c U, P c U), ∃ c U, P c U ∧ (∀ c' < c, ∀ U', ¬ P c' U') ∧ (∀ U', P c U' → U.card ≤ U'.card) :=
    fun (X : Type u_1) (P : ℕ → Finset X → Prop) (h : ∃ c U, P c U) => by
      classical
      have h1 : ∃ n, ∃ U, P (Nat.find h) U ∧ U.card = n := by
        obtain ⟨U, hU⟩ := Nat.find_spec h
        exact ⟨U.card, U, hU, rfl⟩
      obtain ⟨U, hU, hUc⟩ := Nat.find_spec h1
      refine ⟨Nat.find h, U, hU, ?_, ?_⟩
      · intro c' hc' U' hU'
        exact Nat.find_min h hc' ⟨U', hU'⟩
      · intro U' hU'
        rw [hUc]
        exact Nat.find_min' h1 ⟨U', hU', rfl⟩
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_fd_erase : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ) (c : ℕ)
      (Z : Finset X) (x : X) (t : ℕ) (hxZ : x ∈ Z) (ht : 1 ≤ t)
      (h : (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ) - (t : ℝ))
        ≤ ∑ i ∈ Z, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)), (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ) - ((t - 1 : ℕ) : ℝ))
        ≤ ∑ i ∈ Z.erase x, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0) :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ) (c : ℕ)
        (Z : Finset X) (x : X) (t : ℕ) (hxZ : x ∈ Z) (ht : 1 ≤ t)
        (h : (∑ i, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
          - (1/100:ℝ)^c * (((A.filter (fun i => f i < c)).card : ℝ) - (t : ℝ))
          ≤ ∑ i ∈ Z, (if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0)) => by
      have hsplit := Finset.sum_erase_add Z
        (fun i => if i ∈ A ∧ c ≤ f i then (1/100:ℝ)^(f i) else 0) hxZ
      have hterm : (if x ∈ A ∧ c ≤ f x then (1/100:ℝ)^(f x) else 0) ≤ (1/100:ℝ)^c := by
        split_ifs with hh
        · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hh.2
        · positivity
      have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub ht]; simp
      rw [hcast]
      simp only at hsplit
      linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LA_fd_P0 : ∀ (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ)
      (hA : (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ A, (1 / 100 : ℝ) ^ (f i))
      (W T : Finset X) (hW : ∑ i ∈ A ∩ W, (1 / 100 : ℝ) ^ (f i) < 1 / 10 ^ 10)
      (h : (∑ i, (if i ∈ A ∧ 0 ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
        - (1/100:ℝ)^0 * (((A.filter (fun i => f i < 0)).card : ℝ) - (T.card : ℝ))
        ≤ ∑ i ∈ W ∪ T, (if i ∈ A ∧ 0 ≤ f i then (1/100:ℝ)^(f i) else 0)), False :=
    fun (X : Type u_1) [Fintype X] [DecidableEq X] (A : Finset X) (f : X → ℕ)
        (hA : (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ A, (1 / 100 : ℝ) ^ (f i))
        (W T : Finset X) (hW : ∑ i ∈ A ∩ W, (1 / 100 : ℝ) ^ (f i) < 1 / 10 ^ 10)
        (h : (∑ i, (if i ∈ A ∧ 0 ≤ f i then (1/100:ℝ)^(f i) else 0)) / 100
          - (1/100:ℝ)^0 * (((A.filter (fun i => f i < 0)).card : ℝ) - (T.card : ℝ))
          ≤ ∑ i ∈ W ∪ T, (if i ∈ A ∧ 0 ≤ f i then (1/100:ℝ)^(f i) else 0)) => by
      simp only [Nat.zero_le, and_true, pow_zero, Nat.not_lt_zero, Finset.filter_false,
        Finset.card_empty, Nat.cast_zero, one_mul, _root_.zero_sub] at h
      rw [Finset.sum_ite_mem, Finset.univ_inter] at h
      have h1 := Finset.sum_union_inter (s₁ := W) (s₂ := T)
        (f := fun i => if i ∈ A then (1/100:ℝ)^(f i) else 0)
      have h2 : 0 ≤ ∑ i ∈ W ∩ T, (if i ∈ A then (1/100:ℝ)^(f i) else 0) :=
        Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
      have h3 : ∑ i ∈ T, (if i ∈ A then (1/100:ℝ)^(f i) else 0) ≤ T.card := by
        have := Finset.sum_le_card_nsmul T (fun i => if i ∈ A then (1/100:ℝ)^(f i) else 0) 1
          (fun i _ => by
            show (if i ∈ A then (1/100:ℝ)^(f i) else 0) ≤ 1
            split_ifs
            · exact pow_le_one₀ (by norm_num) (by norm_num)
            · norm_num)
        simpa using this
      have h4 : ∑ i ∈ W, (if i ∈ A then (1/100:ℝ)^(f i) else 0) = ∑ i ∈ A ∩ W, (1/100:ℝ)^(f i) := by
        rw [Finset.sum_ite_mem, Finset.inter_comm]
      have h5 : (1:ℝ) / 10^8 / 100 = 1 / 10^10 := by norm_num
      simp only at h1
      linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  open Classical in
  have LA_main : ∀ (p : I) (hp₀ : 0 < p) (hp₁ : p < 1) (X : Type u_1) [Fintype X]
      (Λ : Set (X → ℝ≥0))
      (hE₀ : 0 < 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p])
      (hE : 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p] < ∞), IsSmall p {s : Set X | ⨆ f ∈ Λ, ∑ i ∈ s, (f i : ℝ≥0∞) ≥
          L₂ * 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p]} :=
    fun (p : I) (hp₀ : 0 < p) (hp₁ : p < 1) (X : Type u_1) [Fintype X]
        (Λ : Set (X → ℝ≥0))
        (hE₀ : 0 < 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p])
        (hE : 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p] < ∞) => by
      classical
      set φ : Set X → ℝ≥0∞ := fun s => ⨆ f ∈ Λ, ∑ i ∈ s, (f i : ℝ≥0∞) with hφ
      set E := ∫⁻ s, φ s ∂(binomialSetDistribution X p) with hE_def
      set μ : Finset X → ℝ := fun s => (p : ℝ) ^ s.card * (1 - (p : ℝ)) ^ (Fintype.card X - s.card)
        with hμ
      have hEsum : E = ∑ s : Finset X, ENNReal.ofReal (μ s) * φ ↑s := LA_bern X p φ
      have hp0 : (0 : ℝ) < p := hp₀
      have hp1 : (p : ℝ) < 1 := hp₁
      have hμpos : ∀ s, 0 < μ s := fun s => by
        simp only [hμ]; have : (0:ℝ) < 1 - p := by linarith
        positivity
      have hφfin : ∀ W : Finset X, φ ↑W < ∞ := by
        intro W
        have hle : ENNReal.ofReal (μ W) * φ ↑W ≤ E := by
          rw [hEsum]
          exact Finset.single_le_sum (f := fun s : Finset X => ENNReal.ofReal (μ s) * φ ↑s)
            (fun _ _ => _root_.zero_le _) (mem_univ W)
        rw [lt_top_iff_ne_top]
        intro htop
        rw [htop, ENNReal.mul_top (by simpa using hμpos W)] at hle
        exact absurd (top_le_iff.mp hle) hE.ne
      have hφW : ∀ W : Finset X, φ ↑W = ⨆ f ∈ Λ, ∑ i ∈ W, (f i : ℝ≥0∞) := by
        intro W; simp only [hφ, Finset.toFinset_coe]
      set Er := E.toReal with hEr
      have hErpos : 0 < Er := ENNReal.toReal_pos hE₀.ne' hE.ne
      have hL : ((L₂ : ℝ≥0) : ℝ) = 10 ^ 31 := by simp [L₂]
      set c : ℝ := (L₂ : ℝ) / 2 * Er with hc
      have hcpos : 0 < c := by rw [hc, hL]; positivity
      have hcL : ENNReal.ofReal c < (L₂ : ℝ≥0∞) * E := by
        have : (L₂ : ℝ≥0∞) * E = ENNReal.ofReal ((L₂ : ℝ) * Er) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, hEr,
            ENNReal.ofReal_toReal hE.ne]
        rw [this, ENNReal.ofReal_lt_ofReal_iff (by rw [hL]; positivity), hc, hL]
        nlinarith
      set 𝓕b : Finset (Finset X) := univ.filter (fun S : Finset X => φ ↑S ≥ (L₂ : ℝ≥0∞) * E)
        with h𝓕b
      have hsel : ∀ S ∈ 𝓕b, ∃ f, f ∈ Λ ∧ c < ∑ i ∈ S, (f i : ℝ) := by
        intro S hS
        rw [h𝓕b, Finset.mem_filter] at hS
        have h := lt_of_lt_of_le hcL hS.2
        rw [hφW] at h
        obtain ⟨f, hf⟩ := lt_iSup_iff.mp h
        obtain ⟨hfΛ, hf⟩ := lt_iSup_iff.mp hf
        refine ⟨f, hfΛ, ?_⟩
        rw [ENNReal.ofReal_lt_iff_lt_toReal hcpos.le (by simp)] at hf
        simpa [ENNReal.toReal_sum] using hf
      choose! fS hfSΛ hfS using hsel
      set w : Finset X → X → ℝ := fun S i => (fS S i : ℝ) / c with hw
      set g : Finset X → ℝ := fun W => (φ ↑W).toReal / c with hg
      have hsum : ∑ W : Finset X, μ W * g W = Er / c := by
        have : Er = ∑ W : Finset X, μ W * (φ ↑W).toReal := by
          rw [hEr, hEsum, ENNReal.toReal_sum (fun W _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (hφfin W).ne)]
          refine Finset.sum_congr rfl (fun W _ => ?_)
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hμpos W).le]
        rw [this, Finset.sum_div]
        refine Finset.sum_congr rfl (fun W _ => ?_)
        simp only [hg]; ring
      have hsmall : ∃ 𝓖 : Finset (Finset X), (∀ S ∈ 𝓕b, ∃ G ∈ 𝓖, G ⊆ S) ∧
          ∑ G ∈ 𝓖, (p : ℝ) ^ G.card ≤ 1 / 2 := by
        by_contra hns
        have hcore := LA_core X (p : ℝ) hp0 hp1 𝓕b w
          (fun S _ i => div_nonneg (NNReal.coe_nonneg _) hcpos.le)
          (fun S hS => by
            simp only [hw]
            rw [← Finset.sum_div, le_div_iff₀ hcpos, one_mul]
            exact (hfS S hS).le)
          hns g
          (fun W S hS => by
            simp only [hw, hg]
            rw [← Finset.sum_div]
            refine div_le_div_of_nonneg_right ?_ hcpos.le
            calc ∑ i ∈ S ∩ W, (fS S i : ℝ) ≤ ∑ i ∈ W, (fS S i : ℝ) :=
                  Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
                    (fun _ _ _ => NNReal.coe_nonneg _)
              _ = (∑ i ∈ W, (fS S i : ℝ≥0∞)).toReal := by simp [ENNReal.toReal_sum]
              _ ≤ (φ ↑W).toReal := by
                  refine ENNReal.toReal_mono (hφfin W).ne ?_
                  rw [hφW]
                  exact le_iSup₂_of_le (fS S) (hfSΛ S hS) le_rfl)
        rw [hsum, hc, hL] at hcore
        have : Er / (10 ^ 31 / 2 * Er) = 2 / 10 ^ 31 := by field_simp
        rw [this] at hcore
        norm_num at hcore
      obtain ⟨𝓖, hcov, hG⟩ := hsmall
      refine ⟨(fun G : Finset X => (G : Set X)) '' (𝓖 : Set (Finset X)), ?_, ?_⟩
      · intro s hs
        have hs' : s.toFinset ∈ 𝓕b := by
          rw [h𝓕b, Finset.mem_filter]
          refine ⟨mem_univ _, ?_⟩
          simpa [hφ, E] using hs
        obtain ⟨G, hG𝓖, hGs⟩ := hcov _ hs'
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
        exact ⟨G, ⟨G, hG𝓖, rfl⟩, by simpa using hGs⟩
      · have key : ∀ t : Finset (Set X), t = 𝓖.image (fun G : Finset X => (G : Set X)) →
            ∑ s ∈ t, (p : ℝ) ^ s.ncard ≤ 2⁻¹ := by
          rintro t rfl
          rw [Finset.sum_image (fun a _ b _ h => Finset.coe_injective h)]
          simp only [Set.ncard_coe_finset]
          linarith
        exact key _ (by ext t; simp)
  exact LA_main p hp₀ hp₁ X Λ hE₀ hE)")
    withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0, maxRecDepth := 100000 }) (do
      Lean.Elab.Tactic.evalTactic stx
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing)



/-- The constant `L` of Theorem 1.3. -/
noncomputable def L₃ : ℝ≥0 := 10 ^ 32

/-- The constant of Theorem 1.3 is positive. -/
theorem L₃_pos : L₃ > 0 := by unfold L₃; positivity

open Classical in
/--
Statement of Theorem 1.3:

There exists `L > 0` such that for any `N > 0`, i.i.d random variables `Y_1, …, Y_N` distributed
according to a Borel probability measure `ν` on a Polish space `𝕋`, if `𝓕` is a finite set of
non-negative functions in `L∞(𝕋)` and `0 < 𝔼[sup_{f ∈ 𝓕} Z Y f] < ∞` then there exists a finite
collection `𝓒` of pairs `(g, t)` where `g : 𝕋 → ℝ≥0`, `t > 0` such that

`{sup_{f ∈ 𝓕} Z N Y f ≥ L * 𝔼[sup_{f ∈ 𝓕} Z N Y f] } ⊆ ⋃ (g,t) ∈ 𝓒, {t ≤ Z N Y g}`

and

`∑ (g,t) ∈ 𝓒, P(t ≤ Z N Y g) ≤ 2⁻¹`.

Note: The requirement that the collection `𝓒` be finite is not explicitly stated in the paper.
However, `𝓒` must at least be assumed to be countable in order for the sum to make sense,
and the collections `𝓒` produced by the proof are indeed finite.

-/
theorem theorem_1_3 (N : ℕ) (N_pos : N > 0) (𝕋 : Type*) (t𝕋 : TopologicalSpace 𝕋)
    (p𝕋 : PolishSpace 𝕋)
    (m𝕋 : MeasurableSpace 𝕋) (b𝕋 : BorelSpace 𝕋) (ν : Measure 𝕋) (hν : IsProbabilityMeasure ν)
    (Ω : Type*) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (Y : Fin N → Ω → 𝕋)
    (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P)
    (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}) (h𝓕 : Finite 𝓕)
    (hZ₀ : 0 < 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]) (hZ : 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P] < ∞) :
    ∃ 𝓒 : Finset ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}),
      {ω | ⨆ f ∈ 𝓕, Z N Y f ω ≥ L₃ * 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]} ⊆ ⋃ c ∈ 𝓒, {ω | c.2 ≤ Z N Y c.1 ω}
      ∧ ∑ c : 𝓒, P {ω | c.val.2 ≤ Z N Y c.val.1 ω} ≤ 2⁻¹ := by
  set_option maxRecDepth 100000 in
  run_tac do
    let stx ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "(
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_cmp : ∀ (m N K : ℕ) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
      (Λ : Finset (Fin m → ℝ)) (hne : Λ.Nonempty) (hΛ : ∀ v ∈ Λ, ∀ x, 0 ≤ v x), ∑ y : Fin (K * N) → Fin m, (∏ k, μ (y k)) * Λ.sup' hne (fun v => ∑ k, v (y k)) ≤
        K * ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * Λ.sup' hne (fun v => ∑ k, v (y k)) :=
    fun (m N K : ℕ) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
        (Λ : Finset (Fin m → ℝ)) (hne : Λ.Nonempty) (hΛ : ∀ v ∈ Λ, ∀ x, 0 ≤ v x) => by
      classical
      set E : ℕ → ℝ := fun n =>
        ∑ y : Fin n → Fin m, (∏ k, μ (y k)) * Λ.sup' hne (fun v => ∑ k, v (y k)) with hE
      have hZ : ∀ n, ∑ y : Fin n → Fin m, ∏ k, μ (y k) = 1 := by
        intro n
        rw [← Fintype.prod_sum (fun (_ : Fin n) (x : Fin m) => μ x)]
        simp [hμ1]
      have hsub : ∀ a b, E (a + b) ≤ E a + E b := by
        intro a b
        simp only [hE]
        rw [← (Fin.appendEquiv a b).sum_comp, Fintype.sum_prod_type]
        have key : ∀ (y₁ : Fin a → Fin m) (y₂ : Fin b → Fin m),
            (∏ k, μ (Fin.appendEquiv a b (y₁, y₂) k)) *
                Λ.sup' hne (fun v => ∑ k, v (Fin.appendEquiv a b (y₁, y₂) k)) ≤
              (∏ k, μ (y₁ k)) * (∏ k, μ (y₂ k)) *
                (Λ.sup' hne (fun v => ∑ k, v (y₁ k)) + Λ.sup' hne (fun v => ∑ k, v (y₂ k))) := by
          intro y₁ y₂
          simp only [Fin.appendEquiv_apply, Fin.prod_univ_add, Fin.sum_univ_add, Fin.append_left,
            Fin.append_right]
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (Finset.prod_nonneg (fun k _ => hμ0 _)) (Finset.prod_nonneg (fun k _ => hμ0 _)))
          apply Finset.sup'_le
          intro v hv
          exact add_le_add (Finset.le_sup' (fun v => ∑ k, v (y₁ k)) hv)
            (Finset.le_sup' (fun v => ∑ k, v (y₂ k)) hv)
        refine le_trans (Finset.sum_le_sum (fun y₁ _ => Finset.sum_le_sum (fun y₂ _ => key y₁ y₂))) ?_
        apply le_of_eq
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · refine Finset.sum_congr rfl (fun y₁ _ => ?_)
          rw [← Finset.sum_mul, ← Finset.mul_sum, hZ b, mul_one]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y₂ _ => ?_)
          have : ∀ y₁ : Fin a → Fin m, (∏ k, μ (y₁ k)) * (∏ k, μ (y₂ k)) *
              Λ.sup' hne (fun v => ∑ k, v (y₂ k)) =
              (∏ k, μ (y₁ k)) * ((∏ k, μ (y₂ k)) * Λ.sup' hne (fun v => ∑ k, v (y₂ k))) :=
            fun y₁ => by ring
          simp only [this]
          rw [← Finset.sum_mul, hZ a, one_mul]
      induction K with
      | zero =>
        have : E 0 = 0 := by
          simp only [hE]
          apply Finset.sum_eq_zero
          intro y _
          simp
        show E (0 * N) ≤ ((0 : ℕ) : ℝ) * E N
        rw [Nat.zero_mul, this]
        simp
      | succ K ih =>
        have h1 : E ((K + 1) * N) = E (K * N + N) := by rw [Nat.succ_mul]
        calc E ((K + 1) * N) = E (K * N + N) := h1
          _ ≤ E (K * N) + E N := hsub _ _
          _ ≤ K * E N + E N := by linarith [ih]
          _ = ((K + 1 : ℕ) : ℝ) * E N := by push_cast; ring
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_prep_level : ∀ (x : ℝ) (hx : 0 < x), ∃ j : ℕ, (1 / 100 : ℝ) ^ j ≤ x ∧ (1 ≤ x → j = 0) ∧
      (x < 1 → x < 100 * (1 / 100 : ℝ) ^ j) :=
    fun (x : ℝ) (hx : 0 < x) => by
      classical
      by_cases h1 : 1 ≤ x
      · exact ⟨0, by simpa using h1, fun _ => rfl, fun h => absurd h (not_lt.mpr h1)⟩
      · have hex : ∃ j : ℕ, (1 / 100 : ℝ) ^ j ≤ x := by
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1 / 100 : ℝ) < 1)
          exact ⟨n, hn.le⟩
        refine ⟨Nat.find hex, Nat.find_spec hex, fun h => absurd h h1, fun _ => ?_⟩
        have hne : Nat.find hex ≠ 0 := by
          intro h0
          have := Nat.find_spec hex
          rw [h0] at this
          simp at this
          exact h1 this
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
        have hmin := Nat.find_min hex (show m < Nat.find hex by omega)
        rw [hm, pow_succ]
        push_neg at hmin
        linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_prep_sq_sum : ∀ (M : ℕ), ∑ j ∈ Finset.range M, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 - 2 / ((M : ℝ) + 1) :=
    fun (M : ℕ) => by
      induction M with
      | zero => norm_num
      | succ M ih =>
        rw [Finset.sum_range_succ]
        have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        have key : (1 : ℝ) / ((M : ℝ) + 1) ^ 2 ≤ 2 / ((M : ℝ) + 1) - 2 / (((M + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_prep_one : ∀ (X : Type) [Fintype X] [DecidableEq X] (S : Finset X) (v : X → ℝ)
      (hv : ∀ i, 0 ≤ v i) (h1 : 1 ≤ ∑ i ∈ S, v i), ∃ S' : Finset X, ∃ ℓ : X → ℕ, ∃ ℓ0 : ℝ → ℕ, (∀ i, ℓ i = ℓ0 (v i)) ∧
        S' ⊆ S ∧ (∀ i ∈ S', (1 / 100 : ℝ) ^ (ℓ i) ≤ v i) ∧
        (1 : ℝ) / 10 ^ 8 ≤ ∑ i ∈ S', (1 / 100 : ℝ) ^ (ℓ i) ∧
        ∀ j : ℕ, (S'.filter (fun i => ℓ i = j)).card = 0 ∨
          ((∃ k : ℕ, (S'.filter (fun i => ℓ i = j)).card = 100 ^ k) ∧
            100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * (S'.filter (fun i => ℓ i = j)).card ∧
            (S'.filter (fun i => ℓ i = j)).card < 2 * 100 ^ j) :=
    fun (X : Type) [Fintype X] [DecidableEq X] (S : Finset X) (v : X → ℝ)
        (hv : ∀ i, 0 ≤ v i) (h1 : 1 ≤ ∑ i ∈ S, v i) => by
      classical
      have hlev : ∀ t : ℝ, ∃ j : ℕ, 0 < t → ((1 / 100 : ℝ) ^ j ≤ t ∧ (1 ≤ t → j = 0) ∧
          (t < 1 → t < 100 * (1 / 100 : ℝ) ^ j)) := by
        intro t
        by_cases h : 0 < t
        · obtain ⟨j, hj⟩ := LB_prep_level _ h
          exact ⟨j, fun _ => hj⟩
        · exact ⟨0, fun h' => absurd h' h⟩
      choose ℓ0 hℓ0 using hlev
      obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : X → ℕ, ℓ = fun i => ℓ0 (v i) := ⟨_, rfl⟩
      have hℓeq : ∀ i, ℓ i = ℓ0 (v i) := fun i => by rw [hℓdef]
      have hℓ : ∀ i, 0 < v i → ((1 / 100 : ℝ) ^ (ℓ i) ≤ v i ∧ (1 ≤ v i → ℓ i = 0) ∧
          (v i < 1 → v i < 100 * (1 / 100 : ℝ) ^ (ℓ i))) := fun i => by rw [hℓeq i]; exact hℓ0 (v i)
      set B : ℕ → Finset X := fun j => S.filter (fun i => 0 < v i ∧ ℓ i = j) with hB
      have hBmem : ∀ j, ∀ i ∈ B j, i ∈ S ∧ 0 < v i ∧ ℓ i = j := by
        intro j i hi
        simp only [hB, Finset.mem_filter] at hi
        exact ⟨hi.1, hi.2.1, hi.2.2⟩
      by_cases hA : ∃ j, 100 ^ j ≤ (B j).card
      · obtain ⟨j, hj⟩ := hA
        obtain ⟨T, hTB, hTc⟩ := Finset.exists_subset_card_eq hj
        have hTmem : ∀ i ∈ T, i ∈ S ∧ 0 < v i ∧ ℓ i = j := fun i hi => hBmem j i (hTB hi)
        refine ⟨T, ℓ, ℓ0, hℓeq, fun i hi => (hTmem i hi).1, fun i hi => (hℓ i (hTmem i hi).2.1).1, ?_, ?_⟩
        · have : ∑ i ∈ T, (1 / 100 : ℝ) ^ (ℓ i) = ∑ i ∈ T, (1 / 100 : ℝ) ^ j :=
            Finset.sum_congr rfl (fun i hi => by rw [(hTmem i hi).2.2])
          rw [this, Finset.sum_const, hTc, nsmul_eq_mul]
          push_cast
          rw [← mul_pow]
          norm_num
        · intro j'
          by_cases hjj : j' = j
          · subst hjj
            have hf : T.filter (fun i => ℓ i = j') = T :=
              Finset.filter_true_of_mem (fun i hi => (hTmem i hi).2.2)
            rw [hf, hTc]
            right
            have hp := pow_pos (show 0 < 100 by norm_num) j'
            refine ⟨⟨j', rfl⟩, Nat.le_mul_of_pos_left _ (by positivity), by omega⟩
          · left
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro i hi
            rw [(hTmem i hi).2.2]
            exact fun h => hjj h.symm
      · push_neg at hA
        have hT : ∀ j, ∃ T ⊆ B j, (T.card = 0 ∧ 100 ^ 4 * (j + 1) ^ 2 * (B j).card < 100 ^ j) ∨
            (100 ^ j ≤ 100 ^ 4 * (j + 1) ^ 2 * (B j).card ∧
              T.card = 100 ^ (Nat.log 100 (B j).card)) := by
          intro j
          by_cases hk : 100 ^ j ≤ 100 ^ 4 * (j + 1) ^ 2 * (B j).card
          · have hpos : (B j).card ≠ 0 := by
              intro h0
              rw [h0] at hk
              have := pow_pos (show 0 < 100 by norm_num) j
              omega
            obtain ⟨T, hTB, hTc⟩ := Finset.exists_subset_card_eq (Nat.pow_log_le_self 100 hpos)
            exact ⟨T, hTB, Or.inr ⟨hk, hTc⟩⟩
          · exact ⟨∅, Finset.empty_subset _, Or.inl ⟨Finset.card_empty, not_le.mp hk⟩⟩
        choose T hTB hTc using hT
        have hTmem : ∀ j, ∀ i ∈ T j, i ∈ S ∧ 0 < v i ∧ ℓ i = j := fun j i hi => hBmem j i (hTB j hi)
        set S' := S.filter (fun i => i ∈ T (ℓ i)) with hS'
        have hfil : ∀ j, S'.filter (fun i => ℓ i = j) = T j := by
          intro j
          ext i
          simp only [hS', Finset.mem_filter]
          constructor
          · rintro ⟨⟨_, h⟩, rfl⟩
            exact h
          · intro h
            obtain ⟨h1, _, h3⟩ := hTmem j i h
            subst h3
            exact ⟨⟨h1, h⟩, rfl⟩
        refine ⟨S', ℓ, ℓ0, hℓeq, Finset.filter_subset _ _, ?_, ?_, ?_⟩
        · intro i hi
          simp only [hS', Finset.mem_filter] at hi
          exact (hℓ i (hTmem _ i hi.2).2.1).1
        · set Idx := S.image ℓ with hI
          have hnew : ∑ i ∈ S', (1 / 100 : ℝ) ^ (ℓ i) = ∑ j ∈ Idx, ((T j).card : ℝ) * (1 / 100 : ℝ) ^ j := by
            rw [← Finset.sum_fiberwise_of_maps_to (s := S') (t := Idx) (g := ℓ)
              (fun i hi => Finset.mem_image_of_mem ℓ (Finset.filter_subset _ _ hi))]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const,
              hfil j, nsmul_eq_mul]
          have hold : ∑ i ∈ S, v i ≤ ∑ j ∈ Idx, ((B j).card : ℝ) * (100 * (1 / 100 : ℝ) ^ j) := by
            have step1 : ∑ i ∈ S, v i ≤ ∑ i ∈ S, (if 0 < v i then 100 * (1 / 100 : ℝ) ^ (ℓ i) else 0) := by
              refine Finset.sum_le_sum (fun i hi => ?_)
              split_ifs with hpos
              · have hne : ℓ i ≠ 0 := by
                  intro h0
                  have hmem : i ∈ B 0 := by
                    simp only [hB, Finset.mem_filter]
                    exact ⟨hi, hpos, h0⟩
                  have h0' := hA 0
                  have hp := Finset.card_pos.mpr ⟨i, hmem⟩
                  rw [pow_zero] at h0'
                  omega
                have hlt1 : v i < 1 := by
                  by_contra hc
                  exact hne ((hℓ i hpos).2.1 (not_lt.mp hc))
                exact ((hℓ i hpos).2.2 hlt1).le
              · exact le_of_eq (le_antisymm (not_lt.mp hpos) (hv i))
            refine step1.trans (le_of_eq ?_)
            rw [← Finset.sum_filter]
            rw [← Finset.sum_fiberwise_of_maps_to (s := S.filter (fun i => 0 < v i)) (t := Idx) (g := ℓ)
              (fun i hi => Finset.mem_image_of_mem ℓ (Finset.filter_subset _ _ hi))]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const,
              nsmul_eq_mul, Finset.filter_filter]
          have hterm : ∀ j ∈ Idx, ((B j).card : ℝ) * (100 * (1 / 100 : ℝ) ^ j) ≤
              10 ^ 4 * (((T j).card : ℝ) * (1 / 100 : ℝ) ^ j) + 100 * (1 / 100 : ℝ) ^ 4 * ((1 : ℝ) / ((j : ℝ) + 1) ^ 2) := by
            intro j _
            have hy : (0 : ℝ) < (1 / 100 : ℝ) ^ j := by positivity
            have hy1 : (1 / 100 : ℝ) ^ j * (100 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
            rcases hTc j with ⟨h0, hd⟩ | ⟨_, hc⟩
            · rw [h0]
              have hc : (100 : ℝ) ^ 4 * ((j : ℝ) + 1) ^ 2 * ((B j).card : ℝ) ≤ (100 : ℝ) ^ j := by
                exact_mod_cast hd.le
              have key : ((B j).card : ℝ) * (1 / 100 : ℝ) ^ j * ((100 : ℝ) ^ 4 * ((j : ℝ) + 1) ^ 2) ≤ 1 := by
                nlinarith
              have hj : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
              simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
              rw [mul_one_div, le_div_iff₀ hj]
              norm_num at key ⊢
              nlinarith
            · have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 100) (B j).card
              rw [pow_succ, ← hc] at hlt
              have hlt' : ((B j).card : ℝ) ≤ ((T j).card : ℝ) * 100 := by exact_mod_cast hlt.le
              have : (0 : ℝ) ≤ 100 * (1 / 100 : ℝ) ^ 4 * ((1 : ℝ) / ((j : ℝ) + 1) ^ 2) := by positivity
              nlinarith
          have hsq : ∑ j ∈ Idx, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
            have hsub : Idx ⊆ Finset.range (Idx.sup id + 1) := by
              intro j hj
              rw [Finset.mem_range]
              have := Finset.le_sup (f := id) hj
              simp at this
              omega
            calc ∑ j ∈ Idx, (1 : ℝ) / ((j : ℝ) + 1) ^ 2
                ≤ ∑ j ∈ Finset.range (Idx.sup id + 1), (1 : ℝ) / ((j : ℝ) + 1) ^ 2 :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
              _ ≤ 2 - 2 / (((Idx.sup id + 1 : ℕ) : ℝ) + 1) := LB_prep_sq_sum _
              _ ≤ 2 := by
                  have : (0 : ℝ) ≤ 2 / (((Idx.sup id + 1 : ℕ) : ℝ) + 1) := by positivity
                  linarith
          have htot := (h1.trans hold).trans (Finset.sum_le_sum hterm)
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hnew] at htot
          norm_num at htot hsq ⊢
          nlinarith
        · intro j
          rw [hfil j]
          rcases hTc j with ⟨h0, _⟩ | ⟨hk, hc⟩
          · left; exact h0
          · right
            refine ⟨⟨_, hc⟩, ?_, ?_⟩
            · have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 100) (B j).card
              rw [pow_succ, ← hc] at hlt
              calc 100 ^ j ≤ 100 ^ 4 * (j + 1) ^ 2 * (B j).card := hk
                _ ≤ 100 ^ 4 * (j + 1) ^ 2 * ((T j).card * 100) := Nat.mul_le_mul_left _ hlt.le
                _ = 100 ^ 5 * (j + 1) ^ 2 * (T j).card := by ring
            · have := Finset.card_le_card (hTB j)
              have := hA j
              omega
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_prep_sigma_sum : ∀ (M : Type) [AddCommMonoid M] (m : ℕ) (n : Fin m → ℕ)
      (A : Finset (Σ x : Fin m, Fin (n x))) (g : Fin m → M), ∑ i ∈ A, g i.1 = ∑ x, ((Finset.univ : Finset (Fin (n x))).filter (fun k => (⟨x, k⟩ : Σ x : Fin m, Fin (n x)) ∈ A)).card • g x :=
    fun (M : Type) [AddCommMonoid M] (m : ℕ) (n : Fin m → ℕ)
        (A : Finset (Σ x : Fin m, Fin (n x))) (g : Fin m → M) => by
      classical
      have hA : A = Finset.univ.filter (fun i => i ∈ A) := by ext; simp
      rw [hA, Finset.sum_filter, Fintype.sum_sigma]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_filter]
      show ∑ _k ∈ _, g x = _
      rw [Finset.sum_const]
      congr 2
      ext k; simp
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_prep : ∀ (m : ℕ) (𝓢 : Finset (Fin m → ℕ)) (w : (Fin m → ℕ) → Fin m → ℝ)
      (hw : ∀ S ∈ 𝓢, ∀ x, 0 ≤ w S x) (h1 : ∀ S ∈ 𝓢, 1 ≤ ∑ x, (S x : ℝ) * w S x), ∃ S' : (Fin m → ℕ) → Fin m → ℕ, ∃ ℓ : (Fin m → ℕ) → Fin m → ℕ, ∀ S ∈ 𝓢,
        (∀ x, S' S x ≤ S x) ∧ (∀ x, 0 < S' S x → (1 / 100 : ℝ) ^ (ℓ S x) ≤ w S x) ∧
        (1 : ℝ) / 10 ^ 8 ≤ ∑ x, (S' S x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x) ∧
        ∀ j : ℕ, (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) = 0 ∨
          ((∃ k : ℕ, (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) = 100 ^ k) ∧
            100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ∧
            (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) < 2 * 100 ^ j) :=
    fun (m : ℕ) (𝓢 : Finset (Fin m → ℕ)) (w : (Fin m → ℕ) → Fin m → ℝ)
        (hw : ∀ S ∈ 𝓢, ∀ x, 0 ≤ w S x) (h1 : ∀ S ∈ 𝓢, 1 ≤ ∑ x, (S x : ℝ) * w S x) => by
      classical
      have h : ∀ S : Fin m → ℕ, ∃ a : Fin m → ℕ, ∃ l : Fin m → ℕ, S ∈ 𝓢 →
          ((∀ x, a x ≤ S x) ∧ (∀ x, 0 < a x → (1 / 100 : ℝ) ^ (l x) ≤ w S x) ∧
          (1 : ℝ) / 10 ^ 8 ≤ ∑ x, (a x : ℝ) * (1 / 100 : ℝ) ^ (l x) ∧
          ∀ j : ℕ, (∑ x ∈ Finset.univ.filter (fun x => l x = j), a x) = 0 ∨
            ((∃ k : ℕ, (∑ x ∈ Finset.univ.filter (fun x => l x = j), a x) = 100 ^ k) ∧
              100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * (∑ x ∈ Finset.univ.filter (fun x => l x = j), a x) ∧
              (∑ x ∈ Finset.univ.filter (fun x => l x = j), a x) < 2 * 100 ^ j)) := by
        intro S
        by_cases hS : S ∈ 𝓢
        swap
        · exact ⟨0, 0, fun h => absurd h hS⟩
        let v : (Σ x : Fin m, Fin (S x)) → ℝ := fun i => w S i.1
        have hv : ∀ i, 0 ≤ v i := fun i => hw S hS i.1
        have hsum : ∀ (A : Finset (Σ x : Fin m, Fin (S x))) (g : Fin m → ℝ), ∑ i ∈ A, g i.1 =
            ∑ x, (((Finset.univ : Finset (Fin (S x))).filter
              (fun k => (⟨x, k⟩ : Σ x : Fin m, Fin (S x)) ∈ A)).card : ℝ) * g x := by
          intro A g
          rw [LB_prep_sigma_sum ℝ m S A g]
          simp only [nsmul_eq_mul]
        have h1' : 1 ≤ ∑ i ∈ Finset.univ, v i := by
          have := hsum Finset.univ (w S)
          simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin] at this
          rw [this]; exact h1 S hS
        obtain ⟨T, ℓ, ℓ0, hℓeq, -, hT1, hT2, hT3⟩ := LB_prep_one (Σ x : Fin m, Fin (S x)) Finset.univ v hv h1'
        let a : Fin m → ℕ := fun x => ((Finset.univ : Finset (Fin (S x))).filter
              (fun k => (⟨x, k⟩ : Σ x : Fin m, Fin (S x)) ∈ T)).card
        refine ⟨a, fun x => ℓ0 (w S x), fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
        · intro x
          exact (Finset.card_filter_le _ _).trans (by simp)
        · intro x hx
          obtain ⟨k, hk⟩ := Finset.card_pos.mp hx
          have hk' := (Finset.mem_filter.mp hk).2
          have := hT1 _ hk'
          rw [hℓeq] at this
          exact this
        · have := hsum T (fun x => (1 / 100 : ℝ) ^ (ℓ0 (w S x)))
          have e : ∑ i ∈ T, (1 / 100 : ℝ) ^ (ℓ i) = ∑ i ∈ T, (1 / 100 : ℝ) ^ (ℓ0 (w S i.1)) :=
            Finset.sum_congr rfl (fun i _ => by rw [hℓeq])
          rw [e, this] at hT2
          exact hT2
        · intro j
          have e : (T.filter (fun i => ℓ i = j)).card = ∑ x ∈ Finset.univ.filter (fun x => ℓ0 (w S x) = j), a x := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
            have := LB_prep_sigma_sum ℕ m S T (fun x => if ℓ0 (w S x) = j then 1 else 0)
            simp only [smul_eq_mul, mul_ite, mul_one, mul_zero] at this
            rw [← this]
            exact Finset.sum_congr rfl (fun i _ => by rw [hℓeq])
          rw [← e]
          exact hT3 j
      choose S' ℓ hS' using h
      exact ⟨S', ℓ, fun S hS => hS' S hS⟩
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_P1 : ∀ (m : ℕ) (𝓢 : Finset (Fin m → ℕ)) (S' ℓ : (Fin m → ℕ) → Fin m → ℕ)
      (S W T : Fin m → ℕ) (c : ℕ)
      (hmin : ∀ U : Fin m → ℕ, ((∀ x, U x ≤ S' S x) ∧ ∃ S₁ ∈ 𝓢,
          (∀ j < c, (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) =
            ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ∧
          (∀ x, ℓ S₁ x < c → S' S₁ x ≤ W x + U x) ∧
          (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
              (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
            (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c,
                ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, U x : ℕ) : ℝ)) ≤
            ∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
              ((min (S' S₁ x) (W x + U x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) →
          ∑ x, T x ≤ ∑ x, U x)
      (hT : ∀ x, T x ≤ S' S x) (S₁ : Fin m → ℕ) (hS₁ : S₁ ∈ 𝓢)
      (hprof : ∀ j < c, (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) =
            ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x)
      (hF1 : ∀ x, ℓ S₁ x < c → S' S₁ x ≤ W x + T x)
      (hF2 : (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
              (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
            (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c,
                ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, T x : ℕ) : ℝ)) ≤
            ∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
              ((min (S' S₁ x) (W x + T x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)), ∀ x, W x + T x = max (if ℓ S₁ x < c then S' S₁ x else 0) (W x) :=
    fun (m : ℕ) (𝓢 : Finset (Fin m → ℕ)) (S' ℓ : (Fin m → ℕ) → Fin m → ℕ)
        (S W T : Fin m → ℕ) (c : ℕ)
        (hmin : ∀ U : Fin m → ℕ, ((∀ x, U x ≤ S' S x) ∧ ∃ S₁ ∈ 𝓢,
            (∀ j < c, (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) =
              ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ∧
            (∀ x, ℓ S₁ x < c → S' S₁ x ≤ W x + U x) ∧
            (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
              (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c,
                  ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, U x : ℕ) : ℝ)) ≤
              ∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                ((min (S' S₁ x) (W x + U x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) →
            ∑ x, T x ≤ ∑ x, U x)
        (hT : ∀ x, T x ≤ S' S x) (S₁ : Fin m → ℕ) (hS₁ : S₁ ∈ 𝓢)
        (hprof : ∀ j < c, (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) =
              ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x)
        (hF1 : ∀ x, ℓ S₁ x < c → S' S₁ x ≤ W x + T x)
        (hF2 : (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
              (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c,
                  ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, T x : ℕ) : ℝ)) ≤
              ∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                ((min (S' S₁ x) (W x + T x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) => by
      intro x
      have hge : max (if ℓ S₁ x < c then S' S₁ x else 0) (W x) ≤ W x + T x := by
        apply max_le
        · split_ifs with h
          · exact hF1 x h
          · exact Nat.zero_le _
        · omega
      by_contra hne
      have hlt : max (if ℓ S₁ x < c then S' S₁ x else 0) (W x) < W x + T x :=
        lt_of_le_of_ne hge (Ne.symm hne)
      have hWx : W x < W x + T x := lt_of_le_of_lt (le_max_right _ _) hlt
      have hTx : 0 < T x := by omega
      set U : Fin m → ℕ := Function.update T x (T x - 1) with hU
      have hUx : U x = T x - 1 := by simp [hU]
      have hUy : ∀ y, y ≠ x → U y = T y := fun y hy => by simp [hU, hy]
      have hsumU : ∑ y, U y + 1 = ∑ y, T y := by
        rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ x) U,
          Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ x) T, hUx]
        have : ∑ y ∈ Finset.univ \\ {x}, U y = ∑ y ∈ Finset.univ \\ {x}, T y := by
          apply Finset.sum_congr rfl
          intro y hy
          simp at hy
          exact hUy y hy
        rw [this]; omega
      have hcast : ((∑ y, U y : ℕ) : ℝ) = ((∑ y, T y : ℕ) : ℝ) - 1 := by
        rw [← hsumU]; push_cast; ring
      have key := hmin U ⟨?_, S₁, hS₁, hprof, ?_, ?_⟩
      · omega
      · intro y
        by_cases hy : y = x
        · subst hy; rw [hUx]; have := hT y; omega
        · rw [hUy y hy]; exact hT y
      · intro y hy
        by_cases hyx : y = x
        · subst hyx
          rw [hUx]
          have h1 : S' S₁ y < W y + T y := by
            rw [if_pos hy] at hlt
            exact lt_of_le_of_lt (le_max_left _ _) hlt
          omega
        · rw [hUy y hyx]; exact hF1 y hy
      · -- F2
        have hr : (0 : ℝ) ≤ (1 / 100 : ℝ) ^ c := by positivity
        have hRHS : (∑ y ∈ Finset.univ.filter (fun y => c ≤ ℓ S₁ y),
                ((min (S' S₁ y) (W y + T y) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ y)) ≤
              (∑ y ∈ Finset.univ.filter (fun y => c ≤ ℓ S₁ y),
                ((min (S' S₁ y) (W y + U y) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ y)) +
                (1 / 100 : ℝ) ^ c := by
          calc _ ≤ ∑ y ∈ Finset.univ.filter (fun y => c ≤ ℓ S₁ y),
                (((min (S' S₁ y) (W y + U y) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ y) +
                  if y = x then (1 / 100 : ℝ) ^ c else 0) := by
                apply Finset.sum_le_sum
                intro y hy
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
                by_cases hyx : y = x
                · subst hyx
                  rw [if_pos rfl, hUx]
                  have hm : ((min (S' S₁ y) (W y + T y) : ℕ) : ℝ) ≤
                      ((min (S' S₁ y) (W y + (T y - 1)) : ℕ) : ℝ) + 1 := by
                    have : min (S' S₁ y) (W y + T y) ≤ min (S' S₁ y) (W y + (T y - 1)) + 1 := by
                      omega
                    exact_mod_cast this
                  have hp : (1 / 100 : ℝ) ^ (ℓ S₁ y) ≤ (1 / 100 : ℝ) ^ c :=
                    pow_le_pow_of_le_one (by norm_num) (by norm_num) hy
                  have hp0 : (0 : ℝ) ≤ (1 / 100 : ℝ) ^ (ℓ S₁ y) := by positivity
                  nlinarith
                · rw [if_neg hyx, hUy y hyx, add_zero]
            _ ≤ _ := by
                rw [Finset.sum_add_distrib]
                gcongr
                rw [Finset.sum_ite_eq']
                split_ifs
                · exact le_refl _
                · exact hr
        have heq : (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c,
                  ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, U x : ℕ) : ℝ)) =
            (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c,
                  ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, T x : ℕ) : ℝ)) +
              (1 / 100 : ℝ) ^ c := by
          rw [hcast]; ring
        rw [heq]
        linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_P2_zero : ∀ (m : ℕ) (L : Fin m → ℕ) (g : Fin m → ℝ) (b c : ℕ) (hbc : c ≤ b), (∑ x, if b ≤ L x ∧ L x < c then g x else 0) = 0 :=
    fun (m : ℕ) (L : Fin m → ℕ) (g : Fin m → ℝ) (b c : ℕ) (hbc : c ≤ b) => by
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]
      omega
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_P2_abel : ∀ (m : ℕ) (L : Fin m → ℕ) (v : Fin m → ℝ) (r : ℝ) (hr0 : 0 < r)
      (hr1 : r ≤ 1) (c : ℕ)
      (h : ∀ b < c, 0 ≤ ∑ x, if b ≤ L x ∧ L x < c then r ^ L x * v x else 0), ∀ k b, b + k = c → (∑ x, if b ≤ L x ∧ L x < c then r ^ L x * v x else 0) ≤
        r ^ b * ∑ x, if b ≤ L x ∧ L x < c then v x else 0 :=
    fun (m : ℕ) (L : Fin m → ℕ) (v : Fin m → ℝ) (r : ℝ) (hr0 : 0 < r)
        (hr1 : r ≤ 1) (c : ℕ)
        (h : ∀ b < c, 0 ≤ ∑ x, if b ≤ L x ∧ L x < c then r ^ L x * v x else 0) => by
      intro k
      induction k with
      | zero =>
        intro b hb
        rw [LB_frag_P2_zero m L _ b c (by omega), LB_frag_P2_zero m L _ b c (by omega)]
        simp
      | succ k ih =>
        intro b hb
        have hG1 := ih (b+1) (by omega)
        have hG1nn : 0 ≤ ∑ x, if b + 1 ≤ L x ∧ L x < c then r ^ L x * v x else 0 := by
          rcases Nat.lt_or_ge (b+1) c with h1 | h1
          · exact h (b+1) h1
          · rw [LB_frag_P2_zero m L _ (b+1) c h1]
        have e1 : (∑ x, if b ≤ L x ∧ L x < c then r ^ L x * v x else 0) =
            r ^ b * (∑ x, if L x = b then v x else 0) +
            ∑ x, if b + 1 ≤ L x ∧ L x < c then r ^ L x * v x else 0 := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          by_cases h1 : L x = b
          · rw [if_pos (by omega), if_pos h1, if_neg (by omega), h1]; ring
          · by_cases h2 : b + 1 ≤ L x ∧ L x < c
            · rw [if_pos (by omega), if_neg h1, if_pos h2]; ring
            · rw [if_neg (by omega), if_neg h1, if_neg h2]; ring
        have e2 : (∑ x, if b ≤ L x ∧ L x < c then v x else 0) =
            (∑ x, if L x = b then v x else 0) +
            ∑ x, if b + 1 ≤ L x ∧ L x < c then v x else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          by_cases h1 : L x = b
          · rw [if_pos (by omega), if_pos h1, if_neg (by omega)]; ring
          · by_cases h2 : b + 1 ≤ L x ∧ L x < c
            · rw [if_pos (by omega), if_neg h1, if_pos h2]; ring
            · rw [if_neg (by omega), if_neg h1, if_neg h2]; ring
        rw [e1, e2]
        have hp : 0 < r ^ b := pow_pos hr0 b
        rw [pow_succ] at hG1
        set V1 := ∑ x, if b + 1 ≤ L x ∧ L x < c then v x else 0
        set G1 := ∑ x, if b + 1 ≤ L x ∧ L x < c then r ^ L x * v x else 0
        have hV1 : 0 ≤ V1 := by
          by_contra hneg
          push_neg at hneg
          have : r ^ b * r * V1 < 0 := mul_neg_of_pos_of_neg (mul_pos hp hr0) hneg
          linarith
        have h3 : 0 ≤ r ^ b * V1 * (1 - r) :=
          mul_nonneg (mul_nonneg hp.le hV1) (by linarith)
        nlinarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_P2 : ∀ (m : ℕ) (𝓢 : Finset (Fin m → ℕ)) (S' ℓ : (Fin m → ℕ) → Fin m → ℕ)
      (S W T : Fin m → ℕ) (c : ℕ)
      (hminc : ∀ c' < c, ∀ U : Fin m → ℕ, ¬ ((∀ x, U x ≤ S' S x) ∧ ∃ S₁ ∈ 𝓢,
          (∀ j < c', (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) =
            ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ∧
          (∀ x, ℓ S₁ x < c' → S' S₁ x ≤ W x + U x) ∧
          (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c' ≤ ℓ S₁ x),
              (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
            (1 / 100 : ℝ) ^ c' * (((∑ j ∈ Finset.range c',
                ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, U x : ℕ) : ℝ)) ≤
            ∑ x ∈ Finset.univ.filter (fun x => c' ≤ ℓ S₁ x),
              ((min (S' S₁ x) (W x + U x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)))
      (hT : ∀ x, T x ≤ S' S x) (S₁ : Fin m → ℕ) (hS₁ : S₁ ∈ 𝓢)
      (hprof : ∀ j < c, (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) =
            ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x)
      (hF1 : ∀ x, ℓ S₁ x < c → S' S₁ x ≤ W x + T x)
      (hF2 : (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
              (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
            (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c,
                ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, T x : ℕ) : ℝ)) ≤
            ∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
              ((min (S' S₁ x) (W x + T x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x))
      (hP1 : ∀ x, W x + T x = max (if ℓ S₁ x < c then S' S₁ x else 0) (W x)), 9 * (∑ j ∈ Finset.range c, ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ≤
        10 * ∑ x, T x :=
    fun (m : ℕ) (𝓢 : Finset (Fin m → ℕ)) (S' ℓ : (Fin m → ℕ) → Fin m → ℕ)
        (S W T : Fin m → ℕ) (c : ℕ)
        (hminc : ∀ c' < c, ∀ U : Fin m → ℕ, ¬ ((∀ x, U x ≤ S' S x) ∧ ∃ S₁ ∈ 𝓢,
            (∀ j < c', (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) =
              ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ∧
            (∀ x, ℓ S₁ x < c' → S' S₁ x ≤ W x + U x) ∧
            (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c' ≤ ℓ S₁ x),
                (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
              (1 / 100 : ℝ) ^ c' * (((∑ j ∈ Finset.range c',
                  ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, U x : ℕ) : ℝ)) ≤
              ∑ x ∈ Finset.univ.filter (fun x => c' ≤ ℓ S₁ x),
                ((min (S' S₁ x) (W x + U x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)))
        (hT : ∀ x, T x ≤ S' S x) (S₁ : Fin m → ℕ) (hS₁ : S₁ ∈ 𝓢)
        (hprof : ∀ j < c, (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) =
              ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x)
        (hF1 : ∀ x, ℓ S₁ x < c → S' S₁ x ≤ W x + T x)
        (hF2 : (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
              (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c,
                  ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, T x : ℕ) : ℝ)) ≤
              ∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                ((min (S' S₁ x) (W x + T x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x))
        (hP1 : ∀ x, W x + T x = max (if ℓ S₁ x < c then S' S₁ x else 0) (W x)) => by
      classical
      by_contra hneg
      push_neg at hneg
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc; simp at hneg
      have hT0 : ∀ x, c ≤ ℓ S₁ x → T x = 0 := by
        intro x hx; have := hP1 x; rw [if_neg (by omega)] at this; omega
      have hTle : ∀ x, ℓ S₁ x < c → T x ≤ S' S₁ x ∧ min (S' S₁ x) (W x) + T x = S' S₁ x := by
        intro x hx; have := hP1 x; rw [if_pos hx] at this; omega
      have hprofsum : ∀ b ≤ c, (∑ j ∈ Finset.range b,
          ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) =
          ∑ x, if ℓ S₁ x < b then S' S₁ x else 0 := by
        intro b hb
        rw [Finset.sum_congr rfl (fun j hj => (hprof j (by simp at hj; omega)).symm)]
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        simp [Finset.sum_ite_eq]
      have hr0 : (0 : ℝ) < 1 / 100 := by norm_num
      have hr1 : (1 / 100 : ℝ) ≤ 1 := by norm_num
      have hF2' := hF2
      rw [hprofsum c le_rfl] at hF2'
      simp only [Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] at hF2'
      have key : ∀ b < c, 0 ≤ ∑ x, if b ≤ ℓ S₁ x ∧ ℓ S₁ x < c then
          (1 / 100 : ℝ) ^ ℓ S₁ x * ((T x : ℝ) - 98 / 100 * (S' S₁ x : ℝ)) else 0 := by
        intro b hb
        by_contra hlt
        push_neg at hlt
        apply hminc b hb (fun x => if ℓ S₁ x < b then T x else 0)
        refine ⟨?_, S₁, hS₁, fun j hj => hprof j (by omega), ?_, ?_⟩
        · intro x
          split_ifs
          · exact hT x
          · exact Nat.zero_le _
        · intro x hx
          have := hF1 x (by omega)
          simp only [hx, if_true]
          exact this
        · rw [hprofsum b hb.le]
          simp only [Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
          have hpt : ∀ x,
              ((1 / 100 : ℝ) * (if b ≤ ℓ S₁ x then (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ ℓ S₁ x else 0) -
                (1 / 100 : ℝ) ^ b * ((if ℓ S₁ x < b then (S' S₁ x : ℝ) else 0) -
                  (if ℓ S₁ x < b then (T x : ℝ) else 0)) -
                (if b ≤ ℓ S₁ x then ((min (S' S₁ x) (W x + if ℓ S₁ x < b then T x else 0) : ℕ) : ℝ) *
                  (1 / 100 : ℝ) ^ ℓ S₁ x else 0)) ≤
              ((1 / 100 : ℝ) * (if c ≤ ℓ S₁ x then (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ ℓ S₁ x else 0) -
                (1 / 100 : ℝ) ^ c * ((if ℓ S₁ x < c then (S' S₁ x : ℝ) else 0) - (T x : ℝ)) -
                (if c ≤ ℓ S₁ x then ((min (S' S₁ x) (W x + T x) : ℕ) : ℝ) *
                  (1 / 100 : ℝ) ^ ℓ S₁ x else 0)) +
              (if b ≤ ℓ S₁ x ∧ ℓ S₁ x < c then
                (1 / 100 : ℝ) ^ ℓ S₁ x * ((T x : ℝ) - 98 / 100 * (S' S₁ x : ℝ)) else 0) := by
            intro x
            rcases Nat.lt_or_ge (ℓ S₁ x) b with h1 | h1
            · have h2 : ℓ S₁ x < c := by omega
              obtain ⟨h3, -⟩ := hTle x h2
              have h3' : (T x : ℝ) ≤ S' S₁ x := by exact_mod_cast h3
              have p1 : ¬ b ≤ ℓ S₁ x := by omega
              have p3 : ¬ c ≤ ℓ S₁ x := by omega
              simp only [p1, p3, h1, h2, if_true, if_false, false_and, mul_zero, _root_.sub_zero]
              have hrc : (1 / 100 : ℝ) ^ c ≤ (1 / 100 : ℝ) ^ b :=
                pow_le_pow_of_le_one hr0.le hr1 hb.le
              nlinarith
            · rcases Nat.lt_or_ge (ℓ S₁ x) c with h2 | h2
              · obtain ⟨h3, h4⟩ := hTle x h2
                have h3' : (T x : ℝ) ≤ S' S₁ x := by exact_mod_cast h3
                have h4' : ((min (S' S₁ x) (W x) : ℕ) : ℝ) = S' S₁ x - T x := by
                  have : ((min (S' S₁ x) (W x) : ℕ) : ℝ) + T x = S' S₁ x := by exact_mod_cast h4
                  linarith
                have p1 : b ≤ ℓ S₁ x := h1
                have p2 : ¬ ℓ S₁ x < b := by omega
                have p3 : ¬ c ≤ ℓ S₁ x := by omega
                simp only [p1, p2, p3, h2, if_true, if_false, and_self, mul_zero, _root_.sub_zero,
                  Nat.add_zero, h4']
                have hrc : (1 / 100 : ℝ) ^ c ≤ (1 / 100 : ℝ) ^ (ℓ S₁ x + 1) :=
                  pow_le_pow_of_le_one hr0.le hr1 h2
                rw [pow_succ] at hrc
                have hT' : (0 : ℝ) ≤ T x := Nat.cast_nonneg _
                have hS' : (0 : ℝ) ≤ S' S₁ x := Nat.cast_nonneg _
                have hpc : (0 : ℝ) ≤ (1 / 100 : ℝ) ^ c := pow_nonneg hr0.le _
                nlinarith [mul_nonneg hpc hT', mul_nonneg (sub_nonneg.mpr hrc) hS']
              · have h3 := hT0 x h2
                have p1 : b ≤ ℓ S₁ x := h1
                have p2 : ¬ ℓ S₁ x < b := by omega
                have p3 : c ≤ ℓ S₁ x := h2
                have p4 : ¬ ℓ S₁ x < c := by omega
                simp only [p1, p2, p3, p4, h3, if_true, if_false, and_false, Nat.add_zero]
                simp
          have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpt x)
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
          linarith
      have habel := LB_frag_P2_abel m (ℓ S₁) (fun x => (T x : ℝ) - 98 / 100 * (S' S₁ x : ℝ))
        (1 / 100) hr0 hr1 c key c 0 (by omega)
      have hk := key 0 hc
      have hsplit : (∑ x, if 0 ≤ ℓ S₁ x ∧ ℓ S₁ x < c then
          (T x : ℝ) - 98 / 100 * (S' S₁ x : ℝ) else 0) =
          (∑ x, (T x : ℝ)) - 98 / 100 * ∑ x, (if ℓ S₁ x < c then (S' S₁ x : ℝ) else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases h2 : ℓ S₁ x < c
        · rw [if_pos ⟨Nat.zero_le _, h2⟩, if_pos h2]
        · rw [if_neg (by omega), if_neg h2, hT0 x (by omega)]; simp
      simp only [pow_zero, one_mul] at habel
      rw [hsplit] at habel
      rw [hprofsum c le_rfl] at hneg
      have h1 : ((10 * ∑ x, T x : ℕ) : ℝ) < ((9 * ∑ x, if ℓ S₁ x < c then S' S₁ x else 0 : ℕ) : ℝ) := by
        exact_mod_cast hneg
      push_cast at h1
      have hnn : (0 : ℝ) ≤ ∑ x, (if ℓ S₁ x < c then (S' S₁ x : ℝ) else 0) :=
        Finset.sum_nonneg (fun x _ => by split_ifs <;> positivity)
      linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_det_fiber : ∀ (m : ℕ) (g f : Fin m → ℕ) (c : ℕ), ∑ x, (if g x < c then f x else 0) =
        ∑ j ∈ Finset.range c, ∑ x ∈ Finset.univ.filter (fun x => g x = j), f x :=
    fun (m : ℕ) (g f : Fin m → ℕ) (c : ℕ) => by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp [Finset.sum_ite_eq, Finset.mem_range]
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_det_shift : ∀ (m : ℕ) (g : Fin m → ℕ) (f : Fin m → ℝ) (c : ℕ)
      (h : ∀ x, g x = c → f x = 0), ∑ x ∈ Finset.univ.filter (fun x => c ≤ g x), f x =
        ∑ x ∈ Finset.univ.filter (fun x => c + 1 ≤ g x), f x :=
    fun (m : ℕ) (g : Fin m → ℕ) (f : Fin m → ℝ) (c : ℕ)
        (h : ∀ x, g x = c → f x = 0) => by
      simp only [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : g x = c
      · simp [h x hx]
      · split_ifs <;> first | rfl | (exfalso; omega)
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_det : ∀ (m : ℕ) (𝓢 : Finset (Fin m → ℕ)) (S' ℓ : (Fin m → ℕ) → Fin m → ℕ)
      (hsum : ∀ S ∈ 𝓢, (1 : ℝ) / 10 ^ 8 ≤ ∑ x, (S' S x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x)), ∃ Rsel : (Fin m → ℕ) → ℕ → (ℕ → ℕ) → ℕ → Fin m → ℕ,
      ∃ c : (Fin m → ℕ) → (Fin m → ℕ) → ℕ, ∃ T : (Fin m → ℕ) → (Fin m → ℕ) → Fin m → ℕ,
        ∀ W : Fin m → ℕ,
          (∀ S ∈ 𝓢, ∑ x, ((min (S' S x) (W x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x) < 1 / 10 ^ 10) →
          ∀ S ∈ 𝓢, (∀ x, T S W x ≤ S' S x) ∧ 1 ≤ c S W ∧
            (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = c S W - 1), S' S x) ≠ 0 ∧
            9 * (∑ j ∈ Finset.range (c S W), ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ≤
              10 * ∑ x, T S W x ∧
            (∑ x, Rsel (fun y => W y + T S W y) (c S W)
                (fun j => if j < c S W then ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x else 0)
                (∑ x, T S W x) x) ≤
              ∑ j ∈ Finset.range (c S W), ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x ∧
            ∀ x, W x + T S W x = max (Rsel (fun y => W y + T S W y) (c S W)
                (fun j => if j < c S W then ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x else 0)
                (∑ x, T S W x) x) (W x) :=
    fun (m : ℕ) (𝓢 : Finset (Fin m → ℕ)) (S' ℓ : (Fin m → ℕ) → Fin m → ℕ)
        (hsum : ∀ S ∈ 𝓢, (1 : ℝ) / 10 ^ 8 ≤ ∑ x, (S' S x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x)) => by
      classical
      let Frag : (Fin m → ℕ) → (Fin m → ℕ) → ℕ → (Fin m → ℕ) → Prop := fun S W c U =>
        (∀ x, U x ≤ S' S x) ∧ ∃ S₁ ∈ 𝓢,
            (∀ j < c, (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) =
              ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ∧
            (∀ x, ℓ S₁ x < c → S' S₁ x ≤ W x + U x) ∧
            (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
              (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c,
                  ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) - ((∑ x, U x : ℕ) : ℝ)) ≤
              ∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                ((min (S' S₁ x) (W x + U x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)
      let Feas : (Fin m → ℕ) → ℕ → (ℕ → ℕ) → ℕ → (Fin m → ℕ) → Prop := fun Z c sg t S₁ =>
        S₁ ∈ 𝓢 ∧ (∀ j < c, (∑ x ∈ Finset.univ.filter (fun x => ℓ S₁ x = j), S' S₁ x) = sg j) ∧
          (∀ x, ℓ S₁ x < c → S' S₁ x ≤ Z x) ∧
          (1 / 100 : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                (S' S₁ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)) -
              (1 / 100 : ℝ) ^ c * (((∑ j ∈ Finset.range c, sg j : ℕ) : ℝ) - (t : ℝ)) ≤
              ∑ x ∈ Finset.univ.filter (fun x => c ≤ ℓ S₁ x),
                ((min (S' S₁ x) (Z x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₁ x)
      have hexist : ∀ S ∈ 𝓢, ∀ W : Fin m → ℕ,
          Frag S W (∑ x, ℓ S x + 1) (fun x => S' S x - W x) := by
        intro S hS W
        refine ⟨fun x => Nat.sub_le _ _, S, hS, fun j _ => rfl, fun x _ => by beta_reduce; omega, ?_⟩
        have hlt : ∀ x, ℓ S x < ∑ y, ℓ S y + 1 := fun x =>
          Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x))
        have hempty : Finset.univ.filter (fun x => ∑ y, ℓ S y + 1 ≤ ℓ S x) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun x _ => by have := hlt x; omega)
        rw [hempty, Finset.sum_empty, Finset.sum_empty, mul_zero, _root_.zero_sub]
        have hN : ∑ x, (S' S x - W x) ≤ ∑ j ∈ Finset.range (∑ y, ℓ S y + 1),
            ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x := by
          rw [← LB_frag_det_fiber]
          exact Finset.sum_le_sum (fun x _ => by rw [if_pos (hlt x)]; exact Nat.sub_le _ _)
        have hN' : ((∑ x, (S' S x - W x) : ℕ) : ℝ) ≤ ((∑ j ∈ Finset.range (∑ y, ℓ S y + 1),
            ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) := by exact_mod_cast hN
        have hp : (0 : ℝ) ≤ (1 / 100 : ℝ) ^ (∑ y, ℓ S y + 1) := by positivity
        nlinarith [mul_nonneg hp (sub_nonneg.mpr hN')]
      have keyR : ∀ (Z : Fin m → ℕ) (c : ℕ) (sg : ℕ → ℕ) (t : ℕ), ∃ R : Fin m → ℕ, ∀ S₁,
          Feas Z c sg t S₁ → ∃ S₂, Feas Z c sg t S₂ ∧ ∀ x, R x = if ℓ S₂ x < c then S' S₂ x else 0 := by
        intro Z c sg t
        by_cases h : ∃ S₁, Feas Z c sg t S₁
        · obtain ⟨S₂, hS₂⟩ := h
          exact ⟨fun x => if ℓ S₂ x < c then S' S₂ x else 0, fun _ _ => ⟨S₂, hS₂, fun x => rfl⟩⟩
        · exact ⟨0, fun S₁ h1 => absurd ⟨S₁, h1⟩ h⟩
      choose Rsel hR using keyR
      have keyC : ∀ S W : Fin m → ℕ, ∃ c : ℕ, ∃ T : Fin m → ℕ, S ∈ 𝓢 →
          ((∀ c' < c, ∀ U, ¬ Frag S W c' U) ∧ Frag S W c T ∧
            ∀ U, Frag S W c U → ∑ x, T x ≤ ∑ x, U x) := by
        intro S W
        by_cases hS : S ∈ 𝓢
        · have hex : ∃ c, ∃ U, Frag S W c U := ⟨_, _, hexist S hS W⟩
          have h2 : ∃ n, ∃ U, Frag S W (Nat.find hex) U ∧ ∑ x, U x = n := by
            obtain ⟨U, hU⟩ := Nat.find_spec hex
            exact ⟨_, U, hU, rfl⟩
          obtain ⟨T, hT, hTn⟩ := Nat.find_spec h2
          refine ⟨Nat.find hex, T, fun _ => ⟨fun c' hc' U hU => Nat.find_min hex hc' ⟨U, hU⟩, hT,
            fun U hU => ?_⟩⟩
          rw [hTn]; exact Nat.find_min' h2 ⟨U, hU, rfl⟩
        · exact ⟨0, 0, fun h => absurd h hS⟩
      choose cf Tf hcT using keyC
      refine ⟨Rsel, cf, Tf, ?_⟩
      intro W hbad S hS
      obtain ⟨hminc, hfrag, hmin⟩ := hcT S W hS
      generalize cf S W = c at hminc hfrag hmin ⊢
      generalize Tf S W = T at hminc hfrag hmin ⊢
      obtain ⟨hTle, S₀, hS₀, hp₀, hF1₀, hF2₀⟩ := hfrag
      have hsgsum : ∑ j ∈ Finset.range c, (fun j => if j < c then
          ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x else 0) j =
          ∑ j ∈ Finset.range c, ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x :=
        Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))
      have hfeas0 : Feas (fun y => W y + T y) c (fun j => if j < c then
          ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x else 0) (∑ x, T x) S₀ := by
        refine ⟨hS₀, fun j hj => by rw [hp₀ j hj]; exact (if_pos hj).symm, hF1₀, ?_⟩
        rw [hsgsum]; exact hF2₀
      obtain ⟨S₂, ⟨hS₂, hp₂, hF1₂, hF2₂⟩, hReq⟩ := hR _ _ _ _ S₀ hfeas0
      have hp₂' : ∀ j < c, (∑ x ∈ Finset.univ.filter (fun x => ℓ S₂ x = j), S' S₂ x) =
          ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x := fun j hj => by
        rw [hp₂ j hj]; exact if_pos hj
      have hF2₂' := hF2₂
      rw [hsgsum] at hF2₂'
      have hP1 := LB_frag_P1 m 𝓢 S' ℓ S W T c hmin hTle S₂ hS₂ hp₂' hF1₂ hF2₂'
      have hRsum : ∑ x, (if ℓ S₂ x < c then S' S₂ x else 0) =
          ∑ j ∈ Finset.range c, ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x := by
        rw [LB_frag_det_fiber]
        exact Finset.sum_congr rfl (fun j hj => hp₂' j (Finset.mem_range.mp hj))
      have hTsum : ∑ x, T x ≤
          ∑ j ∈ Finset.range c, ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x := by
        rw [← hRsum]
        exact Finset.sum_le_sum (fun x _ => by have := hP1 x; omega)
      have hc1 : 1 ≤ c := by
        by_contra hc
        obtain rfl : c = 0 := by omega
        have hT0 : ∀ x, T x = 0 := by
          intro x
          have h := hP1 x
          rw [if_neg (Nat.not_lt_zero _)] at h
          omega
        have hF := hF2₂'
        simp only [_root_.zero_le, Finset.filter_true, hT0, add_zero, Finset.sum_range_zero,
          Finset.sum_const_zero, Nat.cast_zero, _root_.sub_zero, mul_zero, pow_zero] at hF
        have h1 := hsum S₂ hS₂
        have h2 := hbad S₂ hS₂
        norm_num at h1 h2 hF ⊢
        linarith
      have hlev : (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = c - 1), S' S x) ≠ 0 := by
        intro hlev0
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hlev0
        have hzero : ∀ x, ℓ S₂ x = c' → S' S₂ x = 0 := by
          intro x hx
          have h := hp₂' c' (lt_add_one c')
          rw [hlev0] at h
          exact Finset.sum_eq_zero_iff.mp h x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
        have hA : ∑ x ∈ Finset.univ.filter (fun x => c' ≤ ℓ S₂ x),
            (S' S₂ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₂ x) = ∑ x ∈ Finset.univ.filter (fun x => c' + 1 ≤ ℓ S₂ x),
            (S' S₂ x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₂ x) :=
          LB_frag_det_shift m (ℓ S₂) _ c' (fun x hx => by simp [hzero x hx])
        have hB : ∑ x ∈ Finset.univ.filter (fun x => c' ≤ ℓ S₂ x),
            ((min (S' S₂ x) (W x + T x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₂ x) =
            ∑ x ∈ Finset.univ.filter (fun x => c' + 1 ≤ ℓ S₂ x),
            ((min (S' S₂ x) (W x + T x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S₂ x) :=
          LB_frag_det_shift m (ℓ S₂) _ c' (fun x hx => by simp [hzero x hx])
        have hN : ∑ j ∈ Finset.range (c' + 1), ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x =
            ∑ j ∈ Finset.range c', ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x := by
          rw [Finset.sum_range_succ, hlev0, add_zero]
        refine hminc c' (lt_add_one c') T ⟨hTle, S₂, hS₂, fun j hj => hp₂' j (by omega),
          fun x hx => hF1₂ x (by omega), ?_⟩
        rw [hA, hB, ← hN]
        have hF := hF2₂'
        have hD : ((∑ x, T x : ℕ) : ℝ) ≤ ((∑ j ∈ Finset.range (c' + 1),
            ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x : ℕ) : ℝ) := by exact_mod_cast hTsum
        have hp : (0 : ℝ) ≤ (1 / 100 : ℝ) ^ c' := by positivity
        rw [pow_succ] at hF
        nlinarith [mul_nonneg hp (sub_nonneg.mpr hD)]
      have hP2 := LB_frag_P2 m 𝓢 S' ℓ S W T c hminc hTle S₂ hS₂ hp₂' hF1₂ hF2₂' hP1
      refine ⟨hTle, hc1, hlev, hP2, ?_, ?_⟩
      · rw [← hRsum]
        exact le_of_eq (Finset.sum_congr rfl (fun x _ => hReq x))
      · intro x
        rw [hReq x]
        exact hP1 x
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_pmf_shift : ∀ (m M : ℕ) (a : Fin m) (h : (Fin m → ℕ) → ℝ)
      (h0 : ∀ W : Fin m → ℕ, W a = 0 → h W = 0), ∑ W ∈ Finset.Nat.antidiagonalTuple m M, h (fun x => W x + if a = x then 1 else 0) =
        ∑ W ∈ Finset.Nat.antidiagonalTuple m (M + 1), h W :=
    fun (m M : ℕ) (a : Fin m) (h : (Fin m → ℕ) → ℝ)
        (h0 : ∀ W : Fin m → ℕ, W a = 0 → h W = 0) => by
      classical
      apply Finset.sum_bij_ne_zero (fun W _ _ => fun x => W x + if a = x then 1 else 0)
      · intro W hW _
        rw [Finset.Nat.mem_antidiagonalTuple] at hW ⊢
        rw [Finset.sum_add_distrib, hW]
        simp
      · intro W₁ _ _ W₂ _ _ heq
        funext x
        have := congrFun heq x
        simpa using this
      · intro W' hW' hne
        have ha : W' a ≠ 0 := fun hz => hne (h0 W' hz)
        refine ⟨fun x => W' x - if a = x then 1 else 0, ?_, ?_, ?_⟩
        · rw [Finset.Nat.mem_antidiagonalTuple] at hW' ⊢
          have hsplit : ∑ x, W' x = ∑ x, (W' x - if a = x then 1 else 0) + ∑ x, (if a = x then 1 else 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x _
            split_ifs with hx
            · subst hx; omega
            · omega
          simp at hsplit
          omega
        · have : (fun x => (W' x - if a = x then 1 else 0) + if a = x then 1 else 0) = W' := by
            funext x
            split_ifs with hx
            · subst hx; omega
            · omega
          rw [this]; exact hne
        · funext x
          show (W' x - if a = x then 1 else 0) + (if a = x then 1 else 0) = W' x
          split_ifs with hx
          · subst hx; omega
          · omega
      · intros; rfl
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_pmf : ∀ (m M : ℕ) (μ : Fin m → ℝ) (F : (Fin m → ℕ) → ℝ), ∑ y : Fin M → Fin m, (∏ k, μ (y k)) * F (fun x => (Finset.univ.filter (fun k => y k = x)).card) =
        ∑ W ∈ Finset.Nat.antidiagonalTuple m M,
          (M.factorial : ℝ) * (∏ x, μ x ^ (W x) / ((W x).factorial : ℝ)) * F W :=
    fun (m M : ℕ) (μ : Fin m → ℝ) (F : (Fin m → ℕ) → ℝ) => by
      classical
      induction M generalizing F with
      | zero =>
        simp [Finset.Nat.antidiagonalTuple_zero_right]
        rfl
      | succ M ih =>
        rw [← (Fin.consEquiv (fun _ => Fin m)).sum_comp, Fintype.sum_prod_type]
        have hcount : ∀ (a : Fin m) (y : Fin M → Fin m),
            (fun x => (Finset.univ.filter (fun k => (Fin.consEquiv (fun _ => Fin m) (a, y)) k = x)).card)
              = fun x => (Finset.univ.filter (fun k => y k = x)).card + if a = x then 1 else 0 := by
          intro a y
          funext x
          rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
          simp [Fin.consEquiv, add_comm]
        have hprod : ∀ (a : Fin m) (y : Fin M → Fin m),
            ∏ k, μ ((Fin.consEquiv (fun _ => Fin m) (a, y)) k) = μ a * ∏ k, μ (y k) := by
          intro a y
          rw [Fin.prod_univ_succ]
          simp [Fin.consEquiv]
        simp_rw [hcount, hprod, mul_assoc, ← Finset.mul_sum]
        have step : ∀ a : Fin m, μ a * ∑ i : Fin M → Fin m, (∏ k, μ (i k)) *
              F (fun x_1 => (Finset.univ.filter (fun k => i k = x_1)).card + if a = x_1 then 1 else 0) =
            ∑ W ∈ Finset.Nat.antidiagonalTuple m (M + 1),
              (M.factorial : ℝ) * (∏ x, μ x ^ (W x) / ((W x).factorial : ℝ)) * (W a : ℝ) * F W := by
          intro a
          rw [ih (fun W => F fun x => W x + if a = x then 1 else 0), Finset.mul_sum]
          rw [← LB_pmf_shift m M a (fun W => (M.factorial : ℝ) * (∏ x, μ x ^ (W x) / ((W x).factorial : ℝ)) * (W a : ℝ) * F W)
            (by intro W hW; simp [hW])]
          apply Finset.sum_congr rfl
          intro W _
          have key : μ a * ∏ x, μ x ^ (W x) / ((W x).factorial : ℝ) =
              (∏ x, μ x ^ (W x + if a = x then 1 else 0) / ((W x + if a = x then 1 else 0).factorial : ℝ)) *
                ((W a + if a = a then 1 else 0 : ℕ) : ℝ) := by
            rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ a),
              Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ a)
                (fun x => μ x ^ (W x + if a = x then 1 else 0) / ((W x + if a = x then 1 else 0).factorial : ℝ))]
            have hrest : ∏ x ∈ Finset.univ \\ {a}, μ x ^ (W x + if a = x then 1 else 0) /
                  ((W x + if a = x then 1 else 0).factorial : ℝ) =
                ∏ x ∈ Finset.univ \\ {a}, μ x ^ (W x) / ((W x).factorial : ℝ) := by
              apply Finset.prod_congr rfl
              intro x hx
              have : a ≠ x := by
                intro h; subst h; simp at hx
              simp [this]
            rw [hrest]
            simp only [if_true, Nat.factorial_succ]
            push_cast
            have : ((W a).factorial : ℝ) ≠ 0 := by positivity
            field_simp
            ring
          linear_combination ((M.factorial : ℝ) * F fun x => W x + if a = x then 1 else 0) * key
        rw [Finset.sum_congr rfl (fun a _ => step a), Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro W hW
        rw [Finset.Nat.mem_antidiagonalTuple] at hW
        have hsum : ∑ a, (W a : ℝ) = (M + 1 : ℕ) := by exact_mod_cast hW
        have hfac : ∀ x, ((M.factorial : ℝ) * ∏ x, μ x ^ W x / ((W x).factorial : ℝ)) * (W x : ℝ) * F W =
            ((M.factorial : ℝ) * (∏ x, μ x ^ W x / ((W x).factorial : ℝ)) * F W) * (W x : ℝ) := by
          intro x; ring
        simp_rw [hfac]
        rw [← Finset.mul_sum, hsum, Nat.factorial_succ]
        push_cast
        ring
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_class_pt : ∀ (m : ℕ) (μ : Fin m → ℝ) (c : ℝ) (W U : Fin m → ℕ), (∏ x, μ x ^ (W x) / ((W x).factorial : ℝ)) * ∏ x, (c * μ x) ^ (U x) / ((U x).factorial : ℝ) =
        c ^ (∑ x, U x) * ((∏ x, μ x ^ (W x + U x) / ((W x + U x).factorial : ℝ)) *
          ∏ x, (((W x + U x).choose (U x) : ℕ) : ℝ)) :=
    fun (m : ℕ) (μ : Fin m → ℝ) (c : ℝ) (W U : Fin m → ℕ) => by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro x _
      have h := Nat.add_choose_mul_factorial_mul_factorial (W x) (U x)
      have h' : (((W x + U x).choose (U x) : ℕ) : ℝ) * ((W x).factorial : ℝ) * ((U x).factorial : ℝ)
          = ((W x + U x).factorial : ℝ) := by exact_mod_cast h
      have h1 : ((W x).factorial : ℝ) ≠ 0 := by positivity
      have h2 : ((U x).factorial : ℝ) ≠ 0 := by positivity
      have h3 : ((W x + U x).factorial : ℝ) ≠ 0 := by positivity
      have hC : (((W x + U x).choose (U x) : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (Nat.le_add_left _ _)).ne'
      rw [← h']
      field_simp
      ring
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_class_fac : ∀ (N t : ℕ), ((10 ^ 6 * N).factorial : ℝ) * (Real.exp 1 * N) ^ t ≤
        (Real.exp 1 / 10 ^ 6) ^ t * ((10 ^ 6 * N + t).factorial : ℝ) :=
    fun (N t : ℕ) => by
      have h : (10 ^ 6 * N).factorial * (10 ^ 6 * N) ^ t ≤ (10 ^ 6 * N + t).factorial :=
        le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _))
          Nat.factorial_mul_pow_le_factorial
      have h' : ((10 ^ 6 * N).factorial : ℝ) * ((10 ^ 6 : ℝ) * N) ^ t ≤ ((10 ^ 6 * N + t).factorial : ℝ) := by
        exact_mod_cast h
      have he : (0 : ℝ) ≤ (Real.exp 1 / 10 ^ 6) ^ t := by positivity
      calc ((10 ^ 6 * N).factorial : ℝ) * (Real.exp 1 * N) ^ t
          = (Real.exp 1 / 10 ^ 6) ^ t * (((10 ^ 6 * N).factorial : ℝ) * ((10 ^ 6 : ℝ) * N) ^ t) := by
            rw [div_pow, mul_pow, mul_pow]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h' he
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_class_one : ∀ (m K : ℕ) (μ : Fin m → ℝ) (hμ1 : ∑ x, μ x = 1), ∑ Z ∈ Finset.Nat.antidiagonalTuple m K,
        (K.factorial : ℝ) * (∏ x, μ x ^ (Z x) / ((Z x).factorial : ℝ)) = 1 :=
    fun (m K : ℕ) (μ : Fin m → ℝ) (hμ1 : ∑ x, μ x = 1) => by
      have := LB_pmf m K μ (fun _ => 1)
      simp only [mul_one] at this
      rw [← this, ← Fintype.prod_sum (fun _ : Fin K => fun x => μ x)]
      simp [hμ1]
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_class_box : ∀ (m : ℕ) (r : Fin m → ℕ), ∑ U ∈ Fintype.piFinset (fun x => Finset.range (r x + 1)), ∏ x, (((r x).choose (U x) : ℕ) : ℝ) =
        2 ^ (∑ x, r x) :=
    fun (m : ℕ) (r : Fin m → ℕ) => by
      classical
      rw [← Finset.prod_univ_sum (fun x => Finset.range (r x + 1)) (fun x k => (((r x).choose k : ℕ) : ℝ)),
        ← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro x _
      exact_mod_cast Nat.sum_range_choose (r x)
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_class : ∀ (m N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
      (hμ1 : ∑ x, μ x = 1) (n t : ℕ) (R : (Fin m → ℕ) → Fin m → ℕ)
      (Bad : Finset (Fin m → ℕ)) (hBad : ∀ W ∈ Bad, ∑ x, W x = 10 ^ 6 * N)
      (V : (Fin m → ℕ) → Finset (Fin m → ℕ))
      (hV : ∀ W ∈ Bad, ∀ U ∈ V W, ∑ x, U x = t ∧ ∑ x, R (fun y => W y + U y) x ≤ n ∧
        ∀ x, W x + U x = max (R (fun y => W y + U y) x) (W x)), ∑ W ∈ Bad, ((10 ^ 6 * N).factorial : ℝ) * (∏ x, μ x ^ (W x) / ((W x).factorial : ℝ)) *
          ∑ U ∈ V W, ∏ x, (Real.exp 1 * N * μ x) ^ (U x) / ((U x).factorial : ℝ) ≤
        (Real.exp 1 / 10 ^ 6) ^ t * 2 ^ n :=
    fun (m N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
        (hμ1 : ∑ x, μ x = 1) (n t : ℕ) (R : (Fin m → ℕ) → Fin m → ℕ)
        (Bad : Finset (Fin m → ℕ)) (hBad : ∀ W ∈ Bad, ∑ x, W x = 10 ^ 6 * N)
        (V : (Fin m → ℕ) → Finset (Fin m → ℕ))
        (hV : ∀ W ∈ Bad, ∀ U ∈ V W, ∑ x, U x = t ∧ ∑ x, R (fun y => W y + U y) x ≤ n ∧
          ∀ x, W x + U x = max (R (fun y => W y + U y) x) (W x)) => by
      classical
      set M := 10 ^ 6 * N with hM
      set C := (Real.exp 1 / 10 ^ 6) ^ t with hC
      have hC0 : 0 ≤ C := by positivity
      set Q : (Fin m → ℕ) → ℝ := fun Z => ∏ x, μ x ^ (Z x) / ((Z x).factorial : ℝ) with hQ
      have hQ0 : ∀ Z, 0 ≤ Q Z := fun Z => Finset.prod_nonneg (fun x _ => by have := hμ0 x; positivity)
      let G : (Σ _ : Fin m → ℕ, Fin m → ℕ) → ℝ := fun q =>
        C * (((M + t).factorial : ℝ) * Q q.1) * ∏ x, (((R q.1 x).choose (q.2 x) : ℕ) : ℝ)
      let φ : (Σ _ : Fin m → ℕ, Fin m → ℕ) → (Σ _ : Fin m → ℕ, Fin m → ℕ) :=
        fun p => ⟨fun y => p.1 y + p.2 y, p.2⟩
      let T : Finset (Σ _ : Fin m → ℕ, Fin m → ℕ) :=
        ((Finset.Nat.antidiagonalTuple m (M + t)).filter (fun Z => ∑ x, R Z x ≤ n)).sigma
          (fun Z => Fintype.piFinset (fun x => Finset.range (R Z x + 1)))
      have hA : ∑ W ∈ Bad, ((M).factorial : ℝ) * (∏ x, μ x ^ (W x) / ((W x).factorial : ℝ)) *
            ∑ U ∈ V W, ∏ x, (Real.exp 1 * N * μ x) ^ (U x) / ((U x).factorial : ℝ) =
          ∑ p ∈ Bad.sigma V, ((M).factorial : ℝ) * (∏ x, μ x ^ (p.1 x) / ((p.1 x).factorial : ℝ)) *
            ∏ x, (Real.exp 1 * N * μ x) ^ (p.2 x) / ((p.2 x).factorial : ℝ) := by
        rw [Finset.sum_sigma]
        apply Finset.sum_congr rfl
        intro W _
        rw [Finset.mul_sum]
      rw [hA]
      have hB : ∀ p ∈ Bad.sigma V, ((M).factorial : ℝ) * (∏ x, μ x ^ (p.1 x) / ((p.1 x).factorial : ℝ)) *
            ∏ x, (Real.exp 1 * N * μ x) ^ (p.2 x) / ((p.2 x).factorial : ℝ) ≤ G (φ p) := by
        rintro ⟨W, U⟩ hp
        rw [Finset.mem_sigma] at hp
        obtain ⟨hU1, -, hU3⟩ := hV W hp.1 U hp.2
        rw [mul_assoc, LB_frag_class_pt, hU1]
        have hch : ∏ x, (((W x + U x).choose (U x) : ℕ) : ℝ) =
            ∏ x, (((R (fun y => W y + U y) x).choose (U x) : ℕ) : ℝ) := by
          apply Finset.prod_congr rfl
          intro x _
          have h3 := hU3 x
          rcases Nat.eq_zero_or_pos (U x) with h0 | h0
          · rw [h0]; simp
          · have : W x + U x = R (fun y => W y + U y) x := by omega
            rw [this]
        rw [hch]
        show _ ≤ C * (((M + t).factorial : ℝ) * Q (fun y => W y + U y)) *
          ∏ x, (((R (fun y => W y + U y) x).choose (U x) : ℕ) : ℝ)
        have hfac := LB_frag_class_fac N t
        have hP : 0 ≤ Q (fun y => W y + U y) * ∏ x, (((R (fun y => W y + U y) x).choose (U x) : ℕ) : ℝ) :=
          mul_nonneg (hQ0 _) (Finset.prod_nonneg (fun x _ => by positivity))
        calc ((M).factorial : ℝ) * ((Real.exp 1 * N) ^ t *
              (Q (fun y => W y + U y) * ∏ x, (((R (fun y => W y + U y) x).choose (U x) : ℕ) : ℝ)))
            = (((M).factorial : ℝ) * (Real.exp 1 * N) ^ t) *
              (Q (fun y => W y + U y) * ∏ x, (((R (fun y => W y + U y) x).choose (U x) : ℕ) : ℝ)) := by ring
          _ ≤ (C * ((M + t).factorial : ℝ)) *
              (Q (fun y => W y + U y) * ∏ x, (((R (fun y => W y + U y) x).choose (U x) : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_right hfac hP
          _ = _ := by ring
      have hinj : Set.InjOn φ (Bad.sigma V : Set (Σ _ : Fin m → ℕ, Fin m → ℕ)) := by
        rintro ⟨W, U⟩ _ ⟨W', U'⟩ _ h
        simp only [φ, Sigma.mk.injEq, heq_eq_eq] at h
        obtain ⟨h1, h2⟩ := h
        subst h2
        have : W = W' := by
          funext y
          have := congrFun h1 y
          omega
        subst this
        rfl
      have hsub : (Bad.sigma V).image φ ⊆ T := by
        intro q hq
        rw [Finset.mem_image] at hq
        obtain ⟨⟨W, U⟩, hp, rfl⟩ := hq
        rw [Finset.mem_sigma] at hp
        obtain ⟨hU1, hU2, hU3⟩ := hV W hp.1 U hp.2
        simp only [T, φ, Finset.mem_sigma, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple,
          Fintype.mem_piFinset, Finset.mem_range]
        refine ⟨⟨?_, hU2⟩, ?_⟩
        · rw [Finset.sum_add_distrib, hBad W hp.1, hU1]
        · intro x
          have := hU3 x
          omega
      have hG0 : ∀ q, 0 ≤ G q := fun q =>
        mul_nonneg (mul_nonneg hC0 (mul_nonneg (by positivity) (hQ0 _)))
          (Finset.prod_nonneg (fun x _ => by positivity))
      calc _ ≤ ∑ p ∈ Bad.sigma V, G (φ p) := Finset.sum_le_sum hB
        _ = ∑ q ∈ (Bad.sigma V).image φ, G q := (Finset.sum_image hinj).symm
        _ ≤ ∑ q ∈ T, G q := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hG0 q)
        _ = ∑ Z ∈ (Finset.Nat.antidiagonalTuple m (M + t)).filter (fun Z => ∑ x, R Z x ≤ n),
              C * (((M + t).factorial : ℝ) * Q Z) * 2 ^ (∑ x, R Z x) := by
            rw [Finset.sum_sigma]
            apply Finset.sum_congr rfl
            intro Z _
            show ∑ U ∈ Fintype.piFinset (fun x => Finset.range (R Z x + 1)),
                C * (((M + t).factorial : ℝ) * Q Z) * ∏ x, (((R Z x).choose (U x) : ℕ) : ℝ) = _
            rw [← Finset.mul_sum, LB_frag_class_box]
        _ ≤ ∑ Z ∈ (Finset.Nat.antidiagonalTuple m (M + t)).filter (fun Z => ∑ x, R Z x ≤ n),
              C * (((M + t).factorial : ℝ) * Q Z) * 2 ^ n := by
            apply Finset.sum_le_sum
            intro Z hZ
            rw [Finset.mem_filter] at hZ
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0 (mul_nonneg (by positivity) (hQ0 _)))
            exact pow_le_pow_right₀ (by norm_num) hZ.2
        _ ≤ ∑ Z ∈ Finset.Nat.antidiagonalTuple m (M + t),
              C * (((M + t).factorial : ℝ) * Q Z) * 2 ^ n :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun Z _ _ => mul_nonneg (mul_nonneg hC0 (mul_nonneg (by positivity) (hQ0 _))) (by positivity))
        _ = C * 2 ^ n := by
            rw [← Finset.sum_mul, ← Finset.mul_sum, LB_frag_class_one m (M + t) μ hμ1, mul_one]
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num_h1 : ∀ (j : ℕ) (hj : 8 ≤ j), 100 ^ 5 * (j + 1) ^ 3 ≤ 100 ^ j :=
    fun (j : ℕ) (hj : 8 ≤ j) => by
      induction j, hj using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        have h2 : (n + 1 + 1) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have e : (2 * (n + 1)) ^ 3 = 8 * (n + 1) ^ 3 := by ring
        calc 100 ^ 5 * (n + 1 + 1) ^ 3 ≤ 100 ^ 5 * (8 * (n + 1) ^ 3) := by rw [← e]; omega
          _ ≤ 100 ^ 5 * (n + 1) ^ 3 * 100 := by ring_nf; omega
          _ ≤ 100 ^ n * 100 := Nat.mul_le_mul_right _ ih
          _ = 100 ^ (n + 1) := (pow_succ _ _).symm
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num_h2 : ∀ (j k : ℕ) (h : 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k), j - 8 + 1 ≤ 100 ^ k :=
    fun (j k : ℕ) (h : 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k) => by
      by_contra hc
      push_neg at hc
      have hk1 : 1 ≤ 100 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have hj : 8 ≤ j := by omega
      have hlt : 100 ^ k < j + 1 := by omega
      have h3 : 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k < 100 ^ 5 * (j + 1) ^ 2 * (j + 1) :=
        Nat.mul_lt_mul_of_pos_left hlt (by positivity)
      have := LB_frag_num_h1 j hj
      have e : 100 ^ 5 * (j + 1) ^ 2 * (j + 1) = 100 ^ 5 * (j + 1) ^ 3 := by ring
      omega
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num_h3 : ∀ (j k : ℕ) (h : 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k), (1 / 12500 : ℝ) ^ (100 ^ k) ≤ (1 / 12500) * (1 / 12500) ^ (j - 8) :=
    fun (j k : ℕ) (h : 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k) => by
      have h2 := LB_frag_num_h2 j k h
      calc (1 / 12500 : ℝ) ^ (100 ^ k) ≤ (1 / 12500) ^ (j - 8 + 1) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) h2
        _ = (1 / 12500) * (1 / 12500) ^ (j - 8) := by rw [pow_succ]; ring
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num_h4n : ∀ (j : ℕ), j + 1 ≤ 9 * 2 ^ (j - 8) :=
    fun (j : ℕ) => by
      rcases Nat.lt_or_ge j 8 with h | h
      · have : j - 8 = 0 := by omega
        rw [this]; omega
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 8 := ⟨j - 8, by omega⟩
        have : m < 2 ^ m := Nat.lt_two_pow_self
        have e : m + 8 - 8 = m := by omega
        rw [e]; omega
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num_h4 : ∀ (j : ℕ), ((j : ℝ) + 1) * ((1 / 12500) * (1 / 12500) ^ (j - 8)) ≤ 9 * (1 / 12500) * (1 / 2) ^ (j - 8) :=
    fun (j : ℕ) => by
      have hn : ((j : ℝ) + 1) ≤ 9 * 2 ^ (j - 8) := by exact_mod_cast LB_frag_num_h4n j
      have e1 : (1 / 12500 : ℝ) ^ (j - 8) ≤ (1 / 2) ^ (j - 8) * (1 / 2) ^ (j - 8) := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have e2 : ((j : ℝ) + 1) * (1 / 2) ^ (j - 8) ≤ 9 := by
        rw [div_pow, one_pow, mul_one_div, div_le_iff₀ (by positivity)]
        exact hn
      have hp : (0 : ℝ) ≤ (1 / 2) ^ (j - 8) := by positivity
      have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
      calc ((j : ℝ) + 1) * ((1 / 12500) * (1 / 12500) ^ (j - 8))
          ≤ ((j : ℝ) + 1) * ((1 / 12500) * ((1 / 2) ^ (j - 8) * (1 / 2) ^ (j - 8))) := by gcongr
        _ = (1 / 12500) * (1 / 2) ^ (j - 8) * (((j : ℝ) + 1) * (1 / 2) ^ (j - 8)) := by ring
        _ ≤ (1 / 12500) * (1 / 2) ^ (j - 8) * 9 := by gcongr
        _ = _ := by ring
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num_h5 : ∀ (j : ℕ), ∑ v ∈ insert 0 (((Finset.range (j + 1)).filter
            (fun k => 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k)).image
            (fun k => 100 ^ k)), (1 / 12500 : ℝ) ^ v
        ≤ Real.exp (9 * (1 / 12500) * (1 / 2) ^ (j - 8)) :=
    fun (j : ℕ) => by
      have h0 : (0 : ℕ) ∉ ((Finset.range (j + 1)).filter
              (fun k => 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k)).image (fun k => 100 ^ k) := by
        simp
      rw [Finset.sum_insert h0, pow_zero]
      refine le_trans ?_ (Real.add_one_le_exp _)
      rw [add_comm]
      gcongr
      refine (Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)).trans ?_
      calc ∑ k ∈ (Finset.range (j + 1)).filter
              (fun k => 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k), (1 / 12500 : ℝ) ^ (100 ^ k)
          ≤ ∑ k ∈ (Finset.range (j + 1)).filter
              (fun k => 100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * 100 ^ k),
              (1 / 12500 : ℝ) * (1 / 12500) ^ (j - 8) := by
            apply Finset.sum_le_sum
            intro k hk
            exact LB_frag_num_h3 j k (Finset.mem_filter.1 hk).2
        _ ≤ ∑ k ∈ Finset.range (j + 1), (1 / 12500 : ℝ) * (1 / 12500) ^ (j - 8) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)
        _ = ((j : ℝ) + 1) * ((1 / 12500) * (1 / 12500) ^ (j - 8)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ _ := LB_frag_num_h4 j
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num_geom : ∀ (C : ℕ), ∑ j ∈ Finset.range C, (1 / 2 : ℝ) ^ (j - 8) ≤ 10 :=
    fun (C : ℕ) => by
      calc ∑ j ∈ Finset.range C, (1 / 2 : ℝ) ^ (j - 8)
          ≤ ∑ j ∈ Finset.range (8 + C), (1 / 2 : ℝ) ^ (j - 8) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
              (fun _ _ _ => by positivity)
        _ = 8 + ∑ k ∈ Finset.range C, (1 / 2 : ℝ) ^ k := by
            rw [Finset.sum_range_add]
            simp [Finset.sum_range_succ]
            norm_num
        _ ≤ 8 + 2 := by gcongr; exact sum_geometric_two_le C
        _ = 10 := by norm_num
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num_tot : ∀ (C : ℕ), ∑ τ ∈ (Fintype.piFinset (fun j : Fin C => insert 0
          (((Finset.range ((j : ℕ) + 1)).filter
            (fun k => 100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)).image
            (fun k => 100 ^ k)))).erase 0,
        (1 / 12500 : ℝ) ^ (∑ j, τ j) ≤ 1 / 4 :=
    fun (C : ℕ) => by
      classical
      have hmem : (0 : Fin C → ℕ) ∈ Fintype.piFinset (fun j : Fin C => insert 0
            (((Finset.range ((j : ℕ) + 1)).filter
              (fun k => 100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)).image
              (fun k => 100 ^ k))) :=
        Fintype.mem_piFinset.2 (fun j => Finset.mem_insert_self _ _)
      rw [Finset.sum_erase_eq_sub hmem]
      simp only [Pi.zero_apply, Finset.sum_const_zero, pow_zero]
      have hprod : ∀ τ : Fin C → ℕ, (1 / 12500 : ℝ) ^ (∑ j, τ j) = ∏ j, (1 / 12500 : ℝ) ^ (τ j) :=
        fun τ => (Finset.prod_pow_eq_pow_sum _ _ _).symm
      simp only [hprod]
      rw [← Finset.prod_univ_sum]
      have hle : ∏ j : Fin C, ∑ v ∈ insert 0
            (((Finset.range ((j : ℕ) + 1)).filter
              (fun k => 100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)).image
              (fun k => 100 ^ k)), (1 / 12500 : ℝ) ^ v
          ≤ ∏ j : Fin C, Real.exp (9 * (1 / 12500) * (1 / 2) ^ ((j : ℕ) - 8)) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
          (fun j _ => LB_frag_num_h5 j)
      rw [← Real.exp_sum, ← Finset.mul_sum,
        Fin.sum_univ_eq_sum_range (fun j => (1 / 2 : ℝ) ^ (j - 8))] at hle
      have hg := LB_frag_num_geom C
      have hexp : Real.exp (9 * (1 / 12500) * ∑ j ∈ Finset.range C, (1 / 2 : ℝ) ^ (j - 8))
          ≤ Real.exp (9 * (1 / 12500) * 10) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hg (by norm_num))
      have hb := Real.exp_bound_div_one_sub_of_interval'
        (x := 9 * (1 / 12500) * 10) (by norm_num) (by norm_num)
      have h54 : (1 : ℝ) / (1 - 9 * (1 / 12500) * 10) ≤ 5 / 4 := by norm_num
      linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num_r : ∀ (t N : ℕ) (h : 9 * N ≤ 10 * t), (Real.exp 1 / 10 ^ 6) ^ t ≤ (1 / 50000 : ℝ) ^ N :=
    fun (t N : ℕ) (h : 9 * N ≤ 10 * t) => by
      have hpos := Real.exp_pos 1
      have hh := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
      have hh0 := Real.exp_pos (1 / 2)
      have hh2 : Real.exp (1 / 2) ≤ 2 := by
        have : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
        linarith
      have he : Real.exp 1 ≤ 4 := by
        have e : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
          rw [← Real.exp_add]; norm_num
        rw [e]; nlinarith
      have r0 : 0 ≤ Real.exp 1 / 10 ^ 6 := by positivity
      have r1 : Real.exp 1 / 10 ^ 6 ≤ 1 := by rw [div_le_one (by norm_num)]; linarith
      have h9 : (Real.exp 1 / 10 ^ 6) ^ 9 ≤ (1 / 50000 : ℝ) ^ 10 := by
        calc (Real.exp 1 / 10 ^ 6) ^ 9 ≤ (4 / 10 ^ 6) ^ 9 := by gcongr
          _ ≤ _ := by norm_num
      have key : ((Real.exp 1 / 10 ^ 6) ^ t) ^ 10 ≤ ((1 / 50000 : ℝ) ^ N) ^ 10 := by
        calc ((Real.exp 1 / 10 ^ 6) ^ t) ^ 10 = (Real.exp 1 / 10 ^ 6) ^ (10 * t) := by
              rw [← pow_mul, mul_comm]
          _ ≤ (Real.exp 1 / 10 ^ 6) ^ (9 * N) := pow_le_pow_of_le_one r0 r1 h
          _ = ((Real.exp 1 / 10 ^ 6) ^ 9) ^ N := by rw [pow_mul]
          _ ≤ ((1 / 50000 : ℝ) ^ 10) ^ N := by gcongr
          _ = _ := by rw [← pow_mul, ← pow_mul, mul_comm]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 key
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag_num : ∀ (Keys : Finset (ℕ × (ℕ → ℕ) × ℕ))
      (hK : ∀ κ ∈ Keys, 1 ≤ κ.1 ∧ κ.2.1 (κ.1 - 1) ≠ 0 ∧ (∀ j, κ.1 ≤ j → κ.2.1 j = 0) ∧
        (∀ j < κ.1, κ.2.1 j = 0 ∨ ((∃ k : ℕ, κ.2.1 j = 100 ^ k) ∧
          100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * κ.2.1 j ∧ κ.2.1 j < 2 * 100 ^ j)) ∧
        9 * (∑ j ∈ Finset.range κ.1, κ.2.1 j) ≤ 10 * κ.2.2 ∧
        κ.2.2 ≤ ∑ j ∈ Finset.range κ.1, κ.2.1 j), ∑ κ ∈ Keys, (Real.exp 1 / 10 ^ 6) ^ κ.2.2 * (2 : ℝ) ^ (∑ j ∈ Finset.range κ.1, κ.2.1 j) ≤ 1 / 4 :=
    fun (Keys : Finset (ℕ × (ℕ → ℕ) × ℕ))
        (hK : ∀ κ ∈ Keys, 1 ≤ κ.1 ∧ κ.2.1 (κ.1 - 1) ≠ 0 ∧ (∀ j, κ.1 ≤ j → κ.2.1 j = 0) ∧
          (∀ j < κ.1, κ.2.1 j = 0 ∨ ((∃ k : ℕ, κ.2.1 j = 100 ^ k) ∧
            100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * κ.2.1 j ∧ κ.2.1 j < 2 * 100 ^ j)) ∧
          9 * (∑ j ∈ Finset.range κ.1, κ.2.1 j) ≤ 10 * κ.2.2 ∧
          κ.2.2 ≤ ∑ j ∈ Finset.range κ.1, κ.2.1 j) => by
      classical
      set C := Keys.sup (fun κ => κ.1) with hC
      have hcC : ∀ κ ∈ Keys, κ.1 ≤ C := fun κ hκ => Finset.le_sup (f := fun κ => κ.1) hκ
      have hN : ∀ κ ∈ Keys, ∑ j ∈ Finset.range κ.1, κ.2.1 j = ∑ j : Fin C, κ.2.1 j := by
        intro κ hκ
        rw [Fin.sum_univ_eq_sum_range (fun j => κ.2.1 j)]
        apply Finset.sum_subset (Finset.range_subset_range.2 (hcC κ hκ))
        intro j _ hj
        exact (hK κ hκ).2.2.1 j (by simpa using hj)
      let φ : ℕ × (ℕ → ℕ) × ℕ → (Fin C → ℕ) × ℕ := fun κ => (fun j => κ.2.1 j, κ.2.2)
      have hinj : ∀ κ ∈ Keys, ∀ κ' ∈ Keys, φ κ = φ κ' → κ = κ' := by
        intro κ hκ κ' hκ' he
        simp only [φ, Prod.mk.injEq] at he
        obtain ⟨h1, h2⟩ := he
        have hσ : κ.2.1 = κ'.2.1 := by
          funext j
          by_cases hj : j < C
          · simpa using congrFun h1 ⟨j, hj⟩
          · rw [(hK κ hκ).2.2.1 j (by have := hcC κ hκ; omega),
              (hK κ' hκ').2.2.1 j (by have := hcC κ' hκ'; omega)]
        have hc : κ.1 = κ'.1 := by
          obtain ⟨a1, a2, a3, -⟩ := hK κ hκ
          obtain ⟨b1, b2, b3, -⟩ := hK κ' hκ'
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · exact b2 (by rw [← hσ]; exact a3 _ (by omega))
          · exact a2 (by rw [hσ]; exact b3 _ (by omega))
        exact Prod.ext hc (Prod.ext hσ h2)
      let P := (Fintype.piFinset (fun j : Fin C => insert 0
            (((Finset.range ((j : ℕ) + 1)).filter
              (fun k => 100 ^ (j : ℕ) ≤ 100 ^ 5 * ((j : ℕ) + 1) ^ 2 * 100 ^ k)).image
              (fun k => 100 ^ k)))).erase 0
      have hmemP : ∀ κ ∈ Keys, (φ κ).1 ∈ P := by
        intro κ hκ
        obtain ⟨a1, a2, a3, a4, -⟩ := hK κ hκ
        refine Finset.mem_erase.2 ⟨?_, Fintype.mem_piFinset.2 ?_⟩
        · intro h0
          have := congrFun h0 ⟨κ.1 - 1, by have := hcC κ hκ; omega⟩
          exact a2 (by simpa [φ] using this)
        · intro j
          show κ.2.1 j ∈ _
          by_cases hj : (j : ℕ) < κ.1
          · rcases a4 j hj with h0 | ⟨⟨k, hk⟩, hl, hu⟩
            · rw [h0]; exact Finset.mem_insert_self _ _
            · rw [hk] at hl hu ⊢
              refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨?_, hl⟩, rfl⟩)
              rw [Finset.mem_range]
              by_contra hkj
              have h3 : 100 ^ ((j : ℕ) + 1) ≤ 100 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
              rw [pow_succ] at h3
              omega
          · rw [a3 j (by omega)]; exact Finset.mem_insert_self _ _
      let B := Keys.sup (fun κ => κ.2.2) + 1
      let Q := (P ×ˢ Finset.range B).filter (fun p => p.2 ≤ ∑ j, p.1 j)
      have himg : Keys.image φ ⊆ Q := by
        intro p hp
        obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.1 hp
        refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hmemP κ hκ, ?_⟩, ?_⟩
        · have : κ.2.2 ≤ Keys.sup (fun κ => κ.2.2) :=
            Finset.le_sup (f := fun κ : ℕ × (ℕ → ℕ) × ℕ => κ.2.2) hκ
          rw [Finset.mem_range]; show κ.2.2 < B; omega
        · show κ.2.2 ≤ ∑ j : Fin C, κ.2.1 j
          rw [← hN κ hκ]; exact (hK κ hκ).2.2.2.2.2
      calc ∑ κ ∈ Keys, (Real.exp 1 / 10 ^ 6) ^ κ.2.2 * (2 : ℝ) ^ (∑ j ∈ Finset.range κ.1, κ.2.1 j)
          = ∑ κ ∈ Keys, (Real.exp 1 / 10 ^ 6) ^ κ.2.2 * (2 : ℝ) ^ (∑ j : Fin C, κ.2.1 j) :=
            Finset.sum_congr rfl (fun κ hκ => by rw [hN κ hκ])
        _ ≤ ∑ κ ∈ Keys, (1 / 25000 : ℝ) ^ (∑ j : Fin C, κ.2.1 j) := by
            apply Finset.sum_le_sum
            intro κ hκ
            have h9 := (hK κ hκ).2.2.2.2.1
            rw [hN κ hκ] at h9
            have := LB_frag_num_r _ _ h9
            calc (Real.exp 1 / 10 ^ 6) ^ κ.2.2 * (2 : ℝ) ^ (∑ j : Fin C, κ.2.1 j)
                ≤ (1 / 50000 : ℝ) ^ (∑ j : Fin C, κ.2.1 j) * (2 : ℝ) ^ (∑ j : Fin C, κ.2.1 j) := by
                  gcongr
              _ = _ := by rw [← mul_pow]; norm_num
        _ = ∑ p ∈ Keys.image φ, (1 / 25000 : ℝ) ^ (∑ j, p.1 j) := (Finset.sum_image (f := fun p : (Fin C → ℕ) × ℕ =>
              (1 / 25000 : ℝ) ^ (∑ j, p.1 j)) hinj).symm
        _ ≤ ∑ p ∈ Q, (1 / 25000 : ℝ) ^ (∑ j, p.1 j) :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
        _ = ∑ τ ∈ P, ∑ t ∈ (Finset.range B).filter (fun t => t ≤ ∑ j, τ j),
              (1 / 25000 : ℝ) ^ (∑ j, τ j) := by
            rw [Finset.sum_filter, Finset.sum_product]
            refine Finset.sum_congr rfl (fun τ _ => ?_)
            rw [Finset.sum_filter]
        _ ≤ ∑ τ ∈ P, (1 / 12500 : ℝ) ^ (∑ j, τ j) := by
            apply Finset.sum_le_sum
            intro τ _
            rw [Finset.sum_const, nsmul_eq_mul]
            have hc : ((Finset.range B).filter (fun t => t ≤ ∑ j, τ j)).card ≤ (∑ j, τ j) + 1 := by
              calc _ ≤ (Finset.range ((∑ j, τ j) + 1)).card := by
                    apply Finset.card_le_card
                    intro t ht
                    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
                    omega
                _ = _ := Finset.card_range _
            have h2 : (∑ j, τ j) + 1 ≤ 2 ^ (∑ j, τ j) := Nat.lt_two_pow_self
            have h3 : ((((Finset.range B).filter (fun t => t ≤ ∑ j, τ j)).card : ℕ) : ℝ)
                ≤ (2 : ℝ) ^ (∑ j, τ j) := by exact_mod_cast hc.trans h2
            calc _ ≤ (2 : ℝ) ^ (∑ j, τ j) * (1 / 25000 : ℝ) ^ (∑ j, τ j) := by gcongr
              _ = _ := by rw [← mul_pow]; norm_num
        _ ≤ 1 / 4 := LB_frag_num_tot C
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_frag : ∀ (m N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
      (hμ1 : ∑ x, μ x = 1) (𝓢 : Finset (Fin m → ℕ)) (S' ℓ : (Fin m → ℕ) → Fin m → ℕ)
      (hsum : ∀ S ∈ 𝓢, (1 : ℝ) / 10 ^ 8 ≤ ∑ x, (S' S x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x))
      (hlegal : ∀ S ∈ 𝓢, ∀ j : ℕ, (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) = 0 ∨
          ((∃ k : ℕ, (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) = 100 ^ k) ∧
            100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ∧
            (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) < 2 * 100 ^ j)), ∃ U : (Fin m → ℕ) → Finset (Fin m → ℕ),
        (∀ W : Fin m → ℕ,
          (∀ S ∈ 𝓢, ∑ x, ((min (S' S x) (W x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x) < 1 / 10 ^ 10) →
          ∀ S ∈ 𝓢, ∃ T ∈ U W, ∀ x, T x ≤ S' S x) ∧
        ∑ W ∈ (Finset.Nat.antidiagonalTuple m (10 ^ 6 * N)).filter (fun W => ∀ S ∈ 𝓢,
            ∑ x, ((min (S' S x) (W x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x) < 1 / 10 ^ 10),
          ((10 ^ 6 * N).factorial : ℝ) * (∏ x, μ x ^ (W x) / ((W x).factorial : ℝ)) *
            ∑ T ∈ U W, ∏ x, (Real.exp 1 * N * μ x) ^ (T x) / ((T x).factorial : ℝ) ≤ 1 / 4 :=
    fun (m N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
        (hμ1 : ∑ x, μ x = 1) (𝓢 : Finset (Fin m → ℕ)) (S' ℓ : (Fin m → ℕ) → Fin m → ℕ)
        (hsum : ∀ S ∈ 𝓢, (1 : ℝ) / 10 ^ 8 ≤ ∑ x, (S' S x : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x))
        (hlegal : ∀ S ∈ 𝓢, ∀ j : ℕ, (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) = 0 ∨
            ((∃ k : ℕ, (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) = 100 ^ k) ∧
              100 ^ j ≤ 100 ^ 5 * (j + 1) ^ 2 * (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) ∧
              (∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x) < 2 * 100 ^ j)) => by
      classical
      obtain ⟨Rsel, cf, Tf, hdet⟩ := LB_frag_det m 𝓢 S' ℓ hsum
      refine ⟨fun W => 𝓢.image (fun S => Tf S W), ?_, ?_⟩
      · intro W hW S hS
        exact ⟨Tf S W, Finset.mem_image_of_mem _ hS, (hdet W hW S hS).1⟩
      set Bad := (Finset.Nat.antidiagonalTuple m (10 ^ 6 * N)).filter (fun W => ∀ S ∈ 𝓢,
              ∑ x, ((min (S' S x) (W x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x) < 1 / 10 ^ 10) with hBad
      let lev : (Fin m → ℕ) → ℕ → ℕ := fun S j =>
        ∑ x ∈ Finset.univ.filter (fun x => ℓ S x = j), S' S x
      let key : (Fin m → ℕ) → (Fin m → ℕ) → ℕ × (ℕ → ℕ) × ℕ := fun S W =>
        (cf S W, fun j => if j < cf S W then lev S j else 0, ∑ x, Tf S W x)
      let Keys := (Bad ×ˢ 𝓢).image (fun p => key p.2 p.1)
      let V : ℕ × (ℕ → ℕ) × ℕ → (Fin m → ℕ) → Finset (Fin m → ℕ) := fun κ W =>
        (𝓢.filter (fun S => key S W = κ)).image (fun S => Tf S W)
      let cost : (Fin m → ℕ) → ℝ := fun U =>
        ∏ x, (Real.exp 1 * N * μ x) ^ (U x) / ((U x).factorial : ℝ)
      let P : (Fin m → ℕ) → ℝ := fun W =>
        ((10 ^ 6 * N).factorial : ℝ) * (∏ x, μ x ^ (W x) / ((W x).factorial : ℝ))
      have hcost0 : ∀ U, 0 ≤ cost U := fun U =>
        Finset.prod_nonneg (fun x _ => by have := hμ0 x; positivity)
      have hP0 : ∀ W, 0 ≤ P W := fun W =>
        mul_nonneg (by positivity) (Finset.prod_nonneg (fun x _ => by have := hμ0 x; positivity))
      have step1 : ∀ W ∈ Bad, ∑ U ∈ 𝓢.image (fun S => Tf S W), cost U ≤
          ∑ κ ∈ Keys, ∑ U ∈ V κ W, cost U := by
        intro W hW
        rw [Finset.sum_sigma' Keys (fun κ => V κ W) (fun _ U => cost U)]
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := (Keys.sigma (fun κ => V κ W)).image
          Sigma.snd) ?_ (fun U _ _ => hcost0 U)) (Finset.sum_image_le_of_nonneg (fun U _ => hcost0 U))
        intro U hU
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
        refine Finset.mem_image.mpr ⟨⟨key S W, Tf S W⟩, ?_, rfl⟩
        refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨(W, S), Finset.mem_product.mpr ⟨hW, hS⟩, rfl⟩
        · exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, rfl⟩, rfl⟩
      have step2 : ∀ κ ∈ Keys, ∑ W ∈ Bad, P W * ∑ U ∈ V κ W, cost U ≤
          (Real.exp 1 / 10 ^ 6) ^ κ.2.2 * 2 ^ (∑ j ∈ Finset.range κ.1, κ.2.1 j) := by
        intro κ _
        refine LB_frag_class m N hN μ hμ0 hμ1 (∑ j ∈ Finset.range κ.1, κ.2.1 j) κ.2.2
          (fun Z => Rsel Z κ.1 κ.2.1 κ.2.2) Bad ?_ (V κ) ?_
        · intro W hW
          have := (Finset.mem_filter.mp hW).1
          rw [Finset.Nat.mem_antidiagonalTuple] at this
          simpa using this
        · intro W hW U hU
          obtain ⟨S, hS', rfl⟩ := Finset.mem_image.mp hU
          obtain ⟨hS, hkey⟩ := Finset.mem_filter.mp hS'
          subst hkey
          have hd := hdet W (Finset.mem_filter.mp hW).2 S hS
          refine ⟨rfl, ?_, hd.2.2.2.2.2⟩
          refine le_trans hd.2.2.2.2.1 (le_of_eq ?_)
          refine Finset.sum_congr rfl (fun j hj => ?_)
          simp only [key, if_pos (Finset.mem_range.mp hj)]
          rfl
      have step3 := LB_frag_num Keys (by
        intro κ hκ
        obtain ⟨⟨W, S⟩, hp, rfl⟩ := Finset.mem_image.mp hκ
        obtain ⟨hW, hS⟩ := Finset.mem_product.mp hp
        have hd := hdet W (Finset.mem_filter.mp hW).2 S hS
        have hsumeq : (∑ j ∈ Finset.range (cf S W), (if j < cf S W then lev S j else 0)) =
            ∑ j ∈ Finset.range (cf S W), lev S j :=
          Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))
        have hTR : ∑ x, Tf S W x ≤ ∑ j ∈ Finset.range (cf S W), lev S j := by
          refine le_trans (Finset.sum_le_sum (fun x _ => ?_)) hd.2.2.2.2.1
          have := hd.2.2.2.2.2 x
          omega
        refine ⟨hd.2.1, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [key, if_pos (show cf S W - 1 < cf S W by have := hd.2.1; omega)]
          exact hd.2.2.1
        · intro j hj
          simp only [key] at hj
          simp only [key, if_neg (show ¬ j < cf S W by omega)]
        · intro j hj
          simp only [key, if_pos hj]
          exact hlegal S hS j
        · simp only [key]
          rw [hsumeq]
          exact hd.2.2.2.1
        · simp only [key]
          rw [hsumeq]
          exact hTR)
      calc ∑ W ∈ Bad, P W * ∑ U ∈ 𝓢.image (fun S => Tf S W), cost U
          ≤ ∑ W ∈ Bad, P W * ∑ κ ∈ Keys, ∑ U ∈ V κ W, cost U :=
            Finset.sum_le_sum (fun W hW => mul_le_mul_of_nonneg_left (step1 W hW) (hP0 W))
        _ = ∑ κ ∈ Keys, ∑ W ∈ Bad, P W * ∑ U ∈ V κ W, cost U := by
            simp_rw [Finset.mul_sum]
            exact Finset.sum_comm
        _ ≤ ∑ κ ∈ Keys, (Real.exp 1 / 10 ^ 6) ^ κ.2.2 * 2 ^ (∑ j ∈ Finset.range κ.1, κ.2.1 j) :=
            Finset.sum_le_sum step2
        _ ≤ 1 / 4 := step3
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_fin_factor_ge_one : ∀ (a : ℕ) (b : ℝ) (hb : (a : ℝ) < b), 1 ≤ (Real.exp 1 * b) ^ a / (a.factorial : ℝ) :=
    fun (a : ℕ) (b : ℝ) (hb : (a : ℝ) < b) => by
      have hb0 : 0 ≤ b := le_trans (Nat.cast_nonneg a) hb.le
      have hf : (0 : ℝ) < (a.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos a
      rw [le_div_iff₀ hf, one_mul]
      have h1 : (a.factorial : ℝ) ≤ (a : ℝ) ^ a := by exact_mod_cast Nat.factorial_le_pow a
      have h2 : (a : ℝ) ^ a ≤ b ^ a := pow_le_pow_left₀ (Nat.cast_nonneg a) hb.le a
      have h3 : b ^ a ≤ (Real.exp 1 * b) ^ a := by
        apply pow_le_pow_left₀ hb0
        have : 1 ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
        nlinarith
      linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_fin : ∀ (m N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
      (Λ : Finset (Fin m → ℝ)) (hΛ : ∀ v ∈ Λ, ∀ x, 0 ≤ v x)
      (g : (Fin N → Fin m) → ℝ) (hg : ∀ y, ∀ v ∈ Λ, ∑ k, v (y k) ≤ g y)
      (hpos : 0 < ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g y), ∃ 𝓖 : Finset (Fin m → ℕ),
        (∀ S : Fin m → ℕ, ∑ x, S x = N → (∀ x, 0 < S x → 0 < μ x) →
          (∃ v ∈ Λ, (10 : ℝ) ^ 30 * ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g y ≤ ∑ x, (S x : ℝ) * v x) →
          ∃ G ∈ 𝓖, ∀ x, G x ≤ S x) ∧
        (∀ G ∈ 𝓖, ∀ x, 0 < G x → 0 < μ x ∧ (N : ℝ) * μ x ≤ G x) ∧
        ∑ G ∈ 𝓖, ∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ) ≤ 1 / 2 :=
    fun (m N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
        (Λ : Finset (Fin m → ℝ)) (hΛ : ∀ v ∈ Λ, ∀ x, 0 ≤ v x)
        (g : (Fin N → Fin m) → ℝ) (hg : ∀ y, ∀ v ∈ Λ, ∑ k, v (y k) ≤ g y)
        (hpos : 0 < ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g y) => by
      classical
      set E := ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g y with hE
      set θ : ℝ := (10 : ℝ) ^ 30 * E with hθdef
      have hθ : 0 < θ := by positivity
      set cost : Finset (Fin m → ℕ) → ℝ := fun 𝓒 =>
        ∑ G ∈ 𝓒, ∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ) with hcost
      have hc0 : ∀ G : Fin m → ℕ, 0 ≤ ∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ) :=
        fun G => Finset.prod_nonneg (fun x _ => by have := hμ0 x; positivity)
      set 𝓢 : Finset (Fin m → ℕ) := (Finset.Nat.antidiagonalTuple m N).filter
        (fun S => (∀ x, 0 < S x → 0 < μ x) ∧ ∃ v ∈ Λ, θ ≤ ∑ x, (S x : ℝ) * v x) with h𝓢def
      -- clean-up of a cover
      have clean : ∀ 𝓒 : Finset (Fin m → ℕ), (∀ S ∈ 𝓢, ∃ T ∈ 𝓒, ∀ x, T x ≤ S x) → cost 𝓒 ≤ 1 / 2 →
          ∃ 𝓖 : Finset (Fin m → ℕ),
          (∀ S : Fin m → ℕ, ∑ x, S x = N → (∀ x, 0 < S x → 0 < μ x) →
            (∃ v ∈ Λ, θ ≤ ∑ x, (S x : ℝ) * v x) →
            ∃ G ∈ 𝓖, ∀ x, G x ≤ S x) ∧
          (∀ G ∈ 𝓖, ∀ x, 0 < G x → 0 < μ x ∧ (N : ℝ) * μ x ≤ G x) ∧
          ∑ G ∈ 𝓖, ∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ) ≤ 1 / 2 := by
        intro 𝓒 hcov hcost𝓒
        let trim : (Fin m → ℕ) → Fin m → ℕ := fun T x => if (N : ℝ) * μ x ≤ T x then T x else 0
        let 𝓒₁ := 𝓒.filter (fun T => ∃ S ∈ 𝓢, ∀ x, T x ≤ S x)
        refine ⟨𝓒₁.image trim, ?_, ?_, ?_⟩
        · intro S hS1 hS2 hS3
          have hS : S ∈ 𝓢 := by
            rw [h𝓢def, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
            exact ⟨hS1, hS2, hS3⟩
          obtain ⟨T, hT, hle⟩ := hcov S hS
          refine ⟨trim T, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hT, S, hS, hle⟩), ?_⟩
          intro x
          simp only [trim]
          split_ifs
          · exact hle x
          · exact Nat.zero_le _
        · intro G hG x hx
          obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hG
          obtain ⟨-, S, hS, hle⟩ := Finset.mem_filter.mp hT
          simp only [trim] at hx ⊢
          split_ifs at hx ⊢ with h
          · refine ⟨?_, h⟩
            have hS' := (Finset.mem_filter.mp hS).2.1
            exact hS' x (lt_of_lt_of_le hx (hle x))
          · exact absurd hx (lt_irrefl 0)
        · refine le_trans (Finset.sum_image_le_of_nonneg (fun u _ => hc0 u)) ?_
          refine le_trans ?_ hcost𝓒
          refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun T => ∃ S ∈ 𝓢, ∀ x, T x ≤ S x) 𝓒)
            (fun u _ _ => hc0 u))
          apply Finset.sum_le_sum
          intro T _
          apply Finset.prod_le_prod
          · intro x _
            have := hμ0 x
            positivity
          · intro x _
            simp only [trim]
            split_ifs with h
            · exact le_rfl
            · push_neg at h
              simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
              have := LB_fin_factor_ge_one (T x) ((N : ℝ) * μ x) h
              rwa [mul_assoc]
      by_cases h𝓢 : 𝓢 = ∅
      · exact clean ∅ (by simp [h𝓢]) (by simp [hcost])
      have hne : 𝓢.Nonempty := Finset.nonempty_iff_ne_empty.mpr h𝓢
      let vS : (Fin m → ℕ) → Fin m → ℝ := fun S =>
        if h : ∃ v ∈ Λ, θ ≤ ∑ x, (S x : ℝ) * v x then h.choose else 0
      have hvS : ∀ S ∈ 𝓢, vS S ∈ Λ ∧ θ ≤ ∑ x, (S x : ℝ) * vS S x := by
        intro S hS
        have h := (Finset.mem_filter.mp hS).2.2
        simp only [vS, dif_pos h]
        exact h.choose_spec
      let w : (Fin m → ℕ) → Fin m → ℝ := fun S x => vS S x / θ
      have hw : ∀ S ∈ 𝓢, ∀ x, 0 ≤ w S x := fun S hS x =>
        div_nonneg (hΛ _ (hvS S hS).1 x) hθ.le
      have h1 : ∀ S ∈ 𝓢, 1 ≤ ∑ x, (S x : ℝ) * w S x := by
        intro S hS
        have : ∑ x, (S x : ℝ) * w S x = (∑ x, (S x : ℝ) * vS S x) / θ := by
          simp only [w, Finset.sum_div, mul_div_assoc]
        rw [this, le_div_iff₀ hθ, one_mul]
        exact (hvS S hS).2
      obtain ⟨S', ℓ, hprep⟩ := LB_prep m 𝓢 w hw h1
      obtain ⟨U, hUcov, hUsum⟩ := LB_frag m N hN μ hμ0 hμ1 𝓢 S' ℓ (fun S hS => (hprep S hS).2.2.1)
        (fun S hS => (hprep S hS).2.2.2)
      by_cases hex : ∃ W ∈ Finset.Nat.antidiagonalTuple m (10 ^ 6 * N), (∀ S ∈ 𝓢,
          ∑ x, ((min (S' S x) (W x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x) < 1 / 10 ^ 10) ∧
          cost (U W) ≤ 1 / 2
      · obtain ⟨W, -, hb, hc⟩ := hex
        apply clean (U W) _ hc
        intro S hS
        obtain ⟨T, hT, hle⟩ := hUcov W hb S hS
        exact ⟨T, hT, fun x => (hle x).trans ((hprep S hS).1 x)⟩
      exfalso
      push_neg at hex
      -- multinomial pmf
      set A := Finset.Nat.antidiagonalTuple m (10 ^ 6 * N) with hA
      let bad : (Fin m → ℕ) → Prop := fun W => ∀ S ∈ 𝓢,
          ∑ x, ((min (S' S x) (W x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x) < 1 / 10 ^ 10
      let pmf : (Fin m → ℕ) → ℝ := fun W =>
        ((10 ^ 6 * N).factorial : ℝ) * (∏ x, μ x ^ (W x) / ((W x).factorial : ℝ))
      have hpmf0 : ∀ W, 0 ≤ pmf W := fun W =>
        mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun x _ => by have := hμ0 x; positivity))
      have hZ : ∀ n, ∑ y : Fin n → Fin m, ∏ k, μ (y k) = 1 := by
        intro n
        rw [← Fintype.prod_sum (fun (_ : Fin n) (x : Fin m) => μ x)]
        simp [hμ1]
      have htot : ∑ W ∈ A, pmf W = 1 := by
        have := LB_pmf m (10 ^ 6 * N) μ (fun _ => 1)
        simp only [mul_one] at this
        rw [← hZ (10 ^ 6 * N), this]
      have hbad : ∑ W ∈ A.filter bad, pmf W ≤ 1 / 2 := by
        have h2 : ∑ W ∈ A.filter bad, pmf W * (1 / 2) ≤ ∑ W ∈ A.filter bad, pmf W * cost (U W) := by
          apply Finset.sum_le_sum
          intro W hW
          obtain ⟨hWA, hWb⟩ := Finset.mem_filter.mp hW
          exact mul_le_mul_of_nonneg_left (hex W hWA hWb).le (hpmf0 W)
        have h3 : ∑ W ∈ A.filter bad, pmf W * cost (U W) ≤ 1 / 4 := hUsum
        rw [← Finset.sum_mul] at h2
        linarith
      let F : (Fin m → ℕ) → ℝ := fun W => 𝓢.sup' hne
        (fun S => ∑ x, ((min (S' S x) (W x) : ℕ) : ℝ) * (1 / 100 : ℝ) ^ (ℓ S x))
      have hF0 : ∀ W, 0 ≤ F W := by
        intro W
        obtain ⟨S, hS⟩ := hne
        refine le_trans ?_ (Finset.le_sup' (fun S => ∑ x, ((min (S' S x) (W x) : ℕ) : ℝ) *
          (1 / 100 : ℝ) ^ (ℓ S x)) hS)
        exact Finset.sum_nonneg (fun x _ => by positivity)
      have hgood : ∀ W, ¬ bad W → 1 / 10 ^ 10 ≤ F W := by
        intro W hW
        simp only [bad, not_forall, not_lt] at hW
        obtain ⟨S, hS, hle⟩ := hW
        exact le_trans hle (Finset.le_sup' (fun S => ∑ x, ((min (S' S x) (W x) : ℕ) : ℝ) *
          (1 / 100 : ℝ) ^ (ℓ S x)) hS)
      have hlow : 1 / 10 ^ 10 / 2 ≤ ∑ W ∈ A, pmf W * F W := by
        rw [← Finset.sum_filter_add_sum_filter_not A bad]
        have e1 : 0 ≤ ∑ W ∈ A.filter bad, pmf W * F W :=
          Finset.sum_nonneg (fun W _ => mul_nonneg (hpmf0 W) (hF0 W))
        have e2 : ∑ W ∈ A.filter (fun W => ¬ bad W), pmf W * (1 / 10 ^ 10) ≤
            ∑ W ∈ A.filter (fun W => ¬ bad W), pmf W * F W := by
          apply Finset.sum_le_sum
          intro W hW
          exact mul_le_mul_of_nonneg_left (hgood W (Finset.mem_filter.mp hW).2) (hpmf0 W)
        have e3 := Finset.sum_filter_add_sum_filter_not A bad pmf
        rw [htot] at e3
        rw [← Finset.sum_mul] at e2
        nlinarith
      have hpmfF := LB_pmf m (10 ^ 6 * N) μ F
      -- comparison family
      let Λ' := 𝓢.image w
      have hne' : Λ'.Nonempty := hne.image w
      have hΛ' : ∀ v ∈ Λ', ∀ x, 0 ≤ v x := by
        intro v hv x
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
        exact hw S hS x
      have hcmp := LB_cmp m N (10 ^ 6) μ hμ0 hμ1 Λ' hne' hΛ'
      have hcnt : ∀ (n : ℕ) (y : Fin n → Fin m) (v : Fin m → ℝ),
          ∑ k, v (y k) = ∑ x, ((Finset.univ.filter (fun k => y k = x)).card : ℝ) * v x := by
        intro n y v
        rw [← Finset.sum_fiberwise Finset.univ y (fun k => v (y k))]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const,
          nsmul_eq_mul]
      have hFle : ∀ y : Fin (10 ^ 6 * N) → Fin m,
          F (fun x => (Finset.univ.filter (fun k => y k = x)).card) ≤ Λ'.sup' hne' (fun v => ∑ k, v (y k)) := by
        intro y
        apply Finset.sup'_le
        intro S hS
        refine le_trans ?_ (Finset.le_sup' (fun v => ∑ k, v (y k)) (Finset.mem_image_of_mem w hS))
        rw [hcnt]
        apply Finset.sum_le_sum
        intro x _
        have hw0 := hw S hS x
        have hc0' : (0 : ℝ) ≤ ((Finset.univ.filter (fun k => y k = x)).card : ℝ) := Nat.cast_nonneg _
        rcases Nat.eq_zero_or_pos (S' S x) with h0 | h0
        · rw [h0, Nat.zero_min, Nat.cast_zero, zero_mul]
          exact mul_nonneg hc0' hw0
        · have hl := (hprep S hS).2.1 x h0
          have hmin : ((min (S' S x) (Finset.univ.filter (fun k => y k = x)).card : ℕ) : ℝ) ≤
              ((Finset.univ.filter (fun k => y k = x)).card : ℝ) := by
            exact_mod_cast min_le_right _ _
          exact mul_le_mul hmin hl (by positivity) hc0'
      have hNle : ∀ y : Fin N → Fin m, Λ'.sup' hne' (fun v => ∑ k, v (y k)) ≤ g y / θ := by
        intro y
        apply Finset.sup'_le
        intro v hv
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
        have : ∑ k, w S (y k) = (∑ k, vS S (y k)) / θ := by simp only [w, Finset.sum_div]
        rw [this]
        exact div_le_div_of_nonneg_right (hg y _ (hvS S hS).1) hθ.le
      have hEN : ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * Λ'.sup' hne' (fun v => ∑ k, v (y k)) ≤ E / θ := by
        rw [hE, Finset.sum_div]
        apply Finset.sum_le_sum
        intro y _
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hNle y) (Finset.prod_nonneg (fun k _ => hμ0 _))
      have hEM : ∑ W ∈ A, pmf W * F W ≤
          ∑ y : Fin (10 ^ 6 * N) → Fin m, (∏ k, μ (y k)) * Λ'.sup' hne' (fun v => ∑ k, v (y k)) := by
        rw [hA, ← hpmfF]
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hFle y) (Finset.prod_nonneg (fun k _ => hμ0 _))
      have hEθ : E / θ = 1 / 10 ^ 30 := by
        rw [hθdef]; field_simp
      rw [Nat.cast_pow, Nat.cast_ofNat] at hcmp
      rw [hEθ] at hEN
      linarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_law : ∀ (N : ℕ) (N_pos : N > 0) (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
      (hν : IsProbabilityMeasure ν) (Ω : Type u_2) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (Y : Fin N → Ω → 𝕋) (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P), IsProbabilityMeasure P ∧ AEMeasurable (fun ω i => Y i ω) P ∧
        P.map (fun ω i => Y i ω) = Measure.pi (fun _ : Fin N => ν) :=
    fun (N : ℕ) (N_pos : N > 0) (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
        (hν : IsProbabilityMeasure ν) (Ω : Type u_2) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
        (Y : Fin N → Ω → 𝕋) (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P) => by
      have hP : IsProbabilityMeasure P := by
        have h0 := Y_law_ν ⟨0, N_pos⟩
        constructor
        have hu : (P.map (Y ⟨0, N_pos⟩)) Set.univ = P Set.univ := by
          rw [Measure.map_apply_of_aemeasurable h0.aemeasurable MeasurableSet.univ]
          rfl
        rw [← hu, h0.map_eq]
        exact measure_univ
      refine ⟨hP, aemeasurable_pi_lambda _ (fun i => (Y_law_ν i).aemeasurable), ?_⟩
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (Y_law_ν i).aemeasurable)).1 Y_indep]
      congr 1
      funext i
      exact (Y_law_ν i).map_eq
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_push : ∀ (N : ℕ) (N_pos : N > 0) (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
      (hν : IsProbabilityMeasure ν) (Ω : Type u_2) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (Y : Fin N → Ω → 𝕋) (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P)
      (m : ℕ) (π : 𝕋 → Fin m) (hπ : Measurable π) (F : (Fin N → Fin m) → ℝ≥0∞), ∫⁻ ω, F (fun k => π (Y k ω)) ∂P =
        ∑ y : Fin N → Fin m, (∏ k, ν (π ⁻¹' {y k})) * F y :=
    fun (N : ℕ) (N_pos : N > 0) (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
        (hν : IsProbabilityMeasure ν) (Ω : Type u_2) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
        (Y : Fin N → Ω → 𝕋) (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P)
        (m : ℕ) (π : 𝕋 → Fin m) (hπ : Measurable π) (F : (Fin N → Fin m) → ℝ≥0∞) => by
      obtain ⟨hP, hae, hmap⟩ := LB_law N N_pos 𝕋 m𝕋 ν hν Ω mΩ P Y Y_indep Y_law_ν
      have hπN : Measurable (fun (z : Fin N → 𝕋) (k : Fin N) => π (z k)) :=
        measurable_pi_lambda _ (fun k => hπ.comp (measurable_pi_apply k))
      have hF : Measurable F := measurable_of_countable F
      have h1 : ∫⁻ ω, F (fun k => π (Y k ω)) ∂P =
          ∫⁻ z, F (fun k => π (z k)) ∂(P.map (fun ω i => Y i ω)) :=
        (lintegral_map' (f := fun z : Fin N → 𝕋 => F (fun k => π (z k)))
          ((hF.comp hπN).aemeasurable) hae).symm
      rw [h1, hmap]
      have h2 : (Measure.pi (fun _ : Fin N => ν)).map (fun (z : Fin N → 𝕋) (k : Fin N) => π (z k)) =
          Measure.pi (fun _ : Fin N => ν.map π) :=
        Measure.pi_map_pi (fun _ => hπ.aemeasurable)
      rw [← lintegral_map hF hπN, h2, lintegral_fintype]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Measure.pi_singleton, mul_comm]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      rw [Measure.map_apply hπ (measurableSet_singleton _)]
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_markov : ∀ (m N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
      (G : Fin m → ℕ) (hG : ∀ x, 0 < G x → 0 < μ x ∧ (N : ℝ) * μ x ≤ G x), ∑ y : Fin N → Fin m, (∏ k, μ (y k)) *
          (if ∑ x, (G x : ℝ) * (if 0 < G x then Real.log (G x / (N * μ x)) else 0) ≤
              ∑ k, (if 0 < G (y k) then Real.log (G (y k) / (N * μ (y k))) else 0) then 1 else 0) ≤
        ∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ) :=
    fun (m N : ℕ) (hN : 0 < N) (μ : Fin m → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
        (G : Fin m → ℕ) (hG : ∀ x, 0 < G x → 0 < μ x ∧ (N : ℝ) * μ x ≤ G x) => by
      set c : Fin m → ℝ := fun x => if 0 < G x then Real.log (G x / (N * μ x)) else 0 with hc
      set T : ℝ := ∑ x, (G x : ℝ) * c x with hT
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      -- step 1: indicator ≤ exp
      have step1 : ∀ y : Fin N → Fin m,
          (∏ k, μ (y k)) * (if T ≤ ∑ k, c (y k) then 1 else 0) ≤
            (∏ k, μ (y k) * Real.exp (c (y k))) * Real.exp (-T) := by
        intro y
        have hprod : 0 ≤ ∏ k, μ (y k) := Finset.prod_nonneg (fun k _ => hμ0 _)
        rw [Finset.prod_mul_distrib, mul_assoc, ← Real.exp_sum, ← Real.exp_add]
        apply mul_le_mul_of_nonneg_left _ hprod
        split_ifs with h
        · rw [Real.one_le_exp_iff]; linarith
        · exact (Real.exp_pos _).le
      have hsum_le : ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * (if T ≤ ∑ k, c (y k) then 1 else 0) ≤
          (∑ x, μ x * Real.exp (c x)) ^ N * Real.exp (-T) := by
        calc _ ≤ ∑ y : Fin N → Fin m, (∏ k, μ (y k) * Real.exp (c (y k))) * Real.exp (-T) :=
              Finset.sum_le_sum (fun y _ => step1 y)
          _ = (∑ x, μ x * Real.exp (c x)) ^ N * Real.exp (-T) := by
              rw [← Finset.sum_mul]
              congr 1
              rw [← Fin.prod_const, Fintype.prod_sum]
      have hmgf : ∑ x, μ x * Real.exp (c x) ≤ 1 + (∑ x, (G x : ℝ)) / N := by
        have key : ∀ x, μ x * Real.exp (c x) ≤ μ x + (G x : ℝ) / N := by
          intro x
          by_cases hx : 0 < G x
          · obtain ⟨hμx, -⟩ := hG x hx
            have hcx : c x = Real.log (G x / (N * μ x)) := by simp [hc, hx]
            have hGpos : (0 : ℝ) < G x := by exact_mod_cast hx
            rw [hcx, Real.exp_log (by positivity)]
            have : μ x * (G x / (N * μ x)) = G x / N := by field_simp
            rw [this]; linarith [hμ0 x]
          · have hcx : c x = 0 := by simp [hc, hx]
            rw [hcx, Real.exp_zero, mul_one]
            have : (0 : ℝ) ≤ G x / N := by positivity
            linarith
        calc _ ≤ ∑ x, (μ x + (G x : ℝ) / N) := Finset.sum_le_sum (fun x _ => key x)
          _ = 1 + (∑ x, (G x : ℝ)) / N := by rw [Finset.sum_add_distrib, hμ1, Finset.sum_div]
      have hpow : (∑ x, μ x * Real.exp (c x)) ^ N ≤ Real.exp (∑ x, (G x : ℝ)) := by
        have h := Real.add_one_le_exp ((∑ x, (G x : ℝ)) / N)
        have h0 : 0 ≤ ∑ x, μ x * Real.exp (c x) :=
          Finset.sum_nonneg (fun x _ => mul_nonneg (hμ0 x) (Real.exp_pos _).le)
        calc (∑ x, μ x * Real.exp (c x)) ^ N ≤ (Real.exp ((∑ x, (G x : ℝ)) / N)) ^ N :=
              pow_le_pow_left₀ h0 (by linarith) N
          _ = Real.exp (∑ x, (G x : ℝ)) := by
              rw [← Real.exp_nat_mul]; congr 1; field_simp
      have hfinal : Real.exp (∑ x, (G x : ℝ)) * Real.exp (-T) ≤
          ∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ) := by
        rw [← Real.exp_add, hT, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Real.exp_sum]
        apply Finset.prod_le_prod (fun x _ => (Real.exp_pos _).le)
        intro x _
        by_cases hx : 0 < G x
        · obtain ⟨hμx, -⟩ := hG x hx
          have hcx : c x = Real.log (G x / (N * μ x)) := by simp [hc, hx]
          have hGpos : (0 : ℝ) < G x := by exact_mod_cast hx
          have ha : (0 : ℝ) < G x / (N * μ x) := by positivity
          have e1 : (G x : ℝ) + -((G x : ℝ) * c x) = (G x : ℕ) * (1 - Real.log (G x / (N * μ x))) := by
            rw [hcx]; ring
          rw [e1, Real.exp_nat_mul, Real.exp_sub, Real.exp_log ha]
          have e2 : Real.exp 1 / (G x / (N * μ x)) = Real.exp 1 * N * μ x / G x := by
            field_simp
          rw [e2, div_pow]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact_mod_cast Nat.factorial_le_pow (G x)
        · have hG0 : G x = 0 := by omega
          have hcx : c x = 0 := by simp [hc, hx]
          simp [hG0, hcx]
      calc _ = ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * (if T ≤ ∑ k, c (y k) then 1 else 0) := rfl
        _ ≤ (∑ x, μ x * Real.exp (c x)) ^ N * Real.exp (-T) := hsum_le
        _ ≤ Real.exp (∑ x, (G x : ℝ)) * Real.exp (-T) :=
            mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
        _ ≤ _ := hfinal
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_main_bdd : ∀ (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
      (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}) (h𝓕 : Finite 𝓕), ∃ C : ℝ, 0 ≤ C ∧ ∀ f ∈ 𝓕, ∀ᵐ y ∂ν, ((f.1 y : ℝ≥0) : ℝ) ≤ C :=
    fun (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
        (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}) (h𝓕 : Finite 𝓕) => by
      classical
      haveI : Fintype 𝓕 := Fintype.ofFinite _
      have h1 : ∀ f : 𝓕, ∃ C : ℝ, ∀ᵐ y ∂ν, ((f.1.1 y : ℝ≥0) : ℝ) ≤ C := by
        intro f
        have hlt := f.1.2.2.eLpNorm_lt_top
        rw [eLpNorm_exponent_top] at hlt
        refine ⟨(eLpNormEssSup f.1.1 ν).toReal, ?_⟩
        filter_upwards [ae_le_eLpNormEssSup (μ := ν) (f := f.1.1)] with y hy
        have : ((f.1.1 y : ℝ≥0) : ℝ≥0∞) ≤ eLpNormEssSup f.1.1 ν := by simpa using hy
        have h2 := ENNReal.toReal_mono hlt.ne this
        simpa using h2
      choose Cf hCf using h1
      refine ⟨∑ f : 𝓕, |Cf f|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
      intro f hf
      filter_upwards [hCf ⟨f, hf⟩] with y hy
      calc _ ≤ Cf ⟨f, hf⟩ := hy
        _ ≤ |Cf ⟨f, hf⟩| := le_abs_self _
        _ ≤ _ := Finset.single_le_sum (f := fun f => |Cf f|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_main_disc : ∀ (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
      (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}) (h𝓕 : Finite 𝓕) (ε : ℝ) (hε : 0 < ε), ∃ (m : ℕ) (π : 𝕋 → Fin m) (_ : Measurable π)
        (v : {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν} → Fin m → ℝ),
        (∀ f x, 0 ≤ v f x) ∧ (∀ f ∈ 𝓕, ∀ y, v f (π y) ≤ ((f.1 y : ℝ≥0) : ℝ)) ∧
        (∀ f ∈ 𝓕, ∀ y, ν (π ⁻¹' {π y}) ≠ 0 → ((f.1 y : ℝ≥0) : ℝ) ≤ v f (π y) + ε) :=
    fun (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
        (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}) (h𝓕 : Finite 𝓕) (ε : ℝ) (hε : 0 < ε) => by
      classical
      haveI : Fintype 𝓕 := Fintype.ofFinite _
      obtain ⟨C, hC0, hC⟩ := LB_main_bdd 𝕋 m𝕋 ν 𝓕 h𝓕
      set K : ℕ := ⌈C / ε⌉₊ with hK
      let hfin : ℕ → Fin (K + 2) := fun n => ⟨min n (K + 1), by omega⟩
      let code : 𝕋 → (𝓕 → Fin (K + 2)) := fun y f => hfin ⌊((f.1.1 y : ℝ≥0) : ℝ) / ε⌋₊
      let e := Fintype.equivFin (𝓕 → Fin (K + 2))
      refine ⟨Fintype.card (𝓕 → Fin (K + 2)), fun y => e (code y), ?_,
        fun f x => if h : f ∈ 𝓕 then ε * (((e.symm x) ⟨f, h⟩ : Fin (K + 2)) : ℕ) else 0, ?_, ?_, ?_⟩
      · have hc : Measurable code := by
          refine measurable_pi_lambda _ (fun f => ?_)
          have hfl : Measurable (Nat.floor : ℝ → ℕ) := Monotone.measurable Nat.floor_mono
          exact (measurable_from_nat (f := hfin)).comp
            (hfl.comp ((measurable_coe_nnreal_real.comp f.1.2.1).div_const ε))
        exact (measurable_of_countable e).comp hc
      · intro f x
        dsimp only; split_ifs
        · positivity
        · exact le_refl _
      · intro f hf y
        simp only [hf, dite_true, Equiv.symm_apply_apply, code, hfin]
        have h1 : ((min ⌊((f.1 y : ℝ≥0) : ℝ) / ε⌋₊ (K + 1) : ℕ) : ℝ) ≤ ⌊((f.1 y : ℝ≥0) : ℝ) / ε⌋₊ := by
          exact_mod_cast min_le_left _ _
        have h2 : (⌊((f.1 y : ℝ≥0) : ℝ) / ε⌋₊ : ℝ) ≤ ((f.1 y : ℝ≥0) : ℝ) / ε :=
          Nat.floor_le (div_nonneg (NNReal.coe_nonneg _) hε.le)
        have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hε.le
        rwa [mul_div_cancel₀ _ hε.ne'] at h3
      · intro f hf y hy
        simp only [hf, dite_true, Equiv.symm_apply_apply, code, hfin]
        have hfl : ⌊((f.1 y : ℝ≥0) : ℝ) / ε⌋₊ ≤ K := by
          by_contra hcon
          push_neg at hcon
          apply hy
          apply measure_mono_null (t := {y' | ¬ ((f.1 y' : ℝ≥0) : ℝ) ≤ C})
          · intro y' hy'
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy'
            have hcy := congrArg (fun c => ((c ⟨f, hf⟩ : Fin (K + 2)) : ℕ)) (e.injective hy')
            simp only [code, hfin] at hcy
            have hge : K + 1 ≤ ⌊((f.1 y' : ℝ≥0) : ℝ) / ε⌋₊ := by
              by_contra h4; push_neg at h4; omega
            simp only [Set.mem_setOf_eq, not_le]
            have h5 : ((K + 1 : ℕ) : ℝ) ≤ ((f.1 y' : ℝ≥0) : ℝ) / ε := by
              have := Nat.floor_le (div_nonneg (NNReal.coe_nonneg (f.1 y')) hε.le)
              exact le_trans (by exact_mod_cast hge) this
            have h6 : C / ε ≤ (K : ℝ) := Nat.le_ceil _
            rw [le_div_iff₀ hε] at h5
            rw [div_le_iff₀ hε] at h6
            push_cast at h5
            nlinarith
          · have := hC f hf
            rw [ae_iff] at this
            exact this
        rw [min_eq_left (by omega)]
        have h2 := Nat.lt_floor_add_one (((f.1 y : ℝ≥0) : ℝ) / ε)
        rw [div_lt_iff₀ hε] at h2
        nlinarith
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  open Classical in
  have LB_main_prob : ∀ (N : ℕ) (N_pos : N > 0) (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
      (hν : IsProbabilityMeasure ν) (Ω : Type u_2) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (Y : Fin N → Ω → 𝕋) (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P)
      (m : ℕ) (π : 𝕋 → Fin m) (hπ : Measurable π) (S : Set (Fin N → Fin m)) (A : Set Ω)
      (hA : A ⊆ {ω | (fun k => π (Y k ω)) ∈ S}), P A ≤ ENNReal.ofReal (∑ y : Fin N → Fin m,
        (∏ k, (ν (π ⁻¹' {y k})).toReal) * (if y ∈ S then 1 else 0)) :=
    fun (N : ℕ) (N_pos : N > 0) (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
        (hν : IsProbabilityMeasure ν) (Ω : Type u_2) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
        (Y : Fin N → Ω → 𝕋) (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P)
        (m : ℕ) (π : 𝕋 → Fin m) (hπ : Measurable π) (S : Set (Fin N → Fin m)) (A : Set Ω)
        (hA : A ⊆ {ω | (fun k => π (Y k ω)) ∈ S}) => by
      classical
      obtain ⟨_, hY, _⟩ := LB_law N N_pos 𝕋 m𝕋 ν hν Ω mΩ P Y Y_indep Y_law_ν
      have hpush := LB_push N N_pos 𝕋 m𝕋 ν hν Ω mΩ P Y Y_indep Y_law_ν m π hπ
        (fun y => if y ∈ S then 1 else 0)
      have hmeas : AEMeasurable (fun ω => (fun y : Fin N → Fin m => if y ∈ S then (1:ℝ≥0∞) else 0)
          (fun k => π (Y k ω))) P := by
        have h1 : Measurable (fun z : Fin N → 𝕋 => fun k => π (z k)) :=
          measurable_pi_lambda _ (fun k => hπ.comp (measurable_pi_apply k))
        exact (measurable_of_countable (fun y : Fin N → Fin m => if y ∈ S then (1:ℝ≥0∞) else 0)).comp_aemeasurable
          (h1.comp_aemeasurable hY)
      calc P A ≤ P {ω | (1:ℝ≥0∞) ≤ (fun y : Fin N → Fin m => if y ∈ S then (1:ℝ≥0∞) else 0)
              (fun k => π (Y k ω))} := by
            apply measure_mono
            intro ω hω
            have := hA hω
            simp only [Set.mem_setOf_eq] at this ⊢
            simp [this]
        _ = 1 * P {ω | (1:ℝ≥0∞) ≤ (fun y : Fin N → Fin m => if y ∈ S then (1:ℝ≥0∞) else 0)
              (fun k => π (Y k ω))} := (one_mul _).symm
        _ ≤ _ := mul_meas_ge_le_lintegral₀ hmeas 1
        _ = _ := hpush
        _ = _ := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            · refine Finset.sum_congr rfl (fun y _ => ?_)
              rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)),
                ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
              congr 1
              · refine Finset.prod_congr rfl (fun k _ => ?_)
                rw [ENNReal.ofReal_toReal (measure_ne_top ν _)]
              · split_ifs <;> simp
            · intro y _
              exact mul_nonneg (Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))
                (by split_ifs <;> norm_num)
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  open Classical in
  have LB_main_null : ∀ (N : ℕ) (m : ℕ) (μ : Fin m → ℝ), ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * (if y ∈ {y : Fin N → Fin m | ∃ k, μ (y k) = 0} then 1 else 0)
        = 0 :=
    fun (N : ℕ) (m : ℕ) (μ : Fin m → ℝ) => by
      classical
      refine Finset.sum_eq_zero (fun y _ => ?_)
      split_ifs with h
      · obtain ⟨k, hk⟩ := h
        rw [Finset.prod_eq_zero (Finset.mem_univ k) hk, zero_mul]
      · rw [mul_zero]
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_main_iSup_eq : ∀ (α : Type u_1) (s : Set α) (hs : Finite s) (h : α → ℝ≥0), ∃ T : Finset α, (∀ x, x ∈ T ↔ x ∈ s) ∧ ⨆ x ∈ s, h x = T.sup h :=
    fun (α : Type u_1) (s : Set α) (hs : Finite s) (h : α → ℝ≥0) => by
      classical
      have hfin : s.Finite := Set.toFinite s
      refine ⟨hfin.toFinset, fun x => hfin.mem_toFinset, ?_⟩
      have hle : ∀ x, ⨆ (_ : x ∈ s), h x ≤ hfin.toFinset.sup h := by
        intro x
        refine ciSup_le' (fun hx => ?_)
        exact Finset.le_sup (f := h) (hfin.mem_toFinset.mpr hx)
      apply le_antisymm
      · exact ciSup_le' hle
      · refine Finset.sup_le (fun x hx => ?_)
        have hx' : x ∈ s := hfin.mem_toFinset.mp hx
        have hb : BddAbove (Set.range fun x => ⨆ (_ : x ∈ s), h x) := by
          refine ⟨hfin.toFinset.sup h, ?_⟩
          rintro _ ⟨y, rfl⟩
          exact hle y
        refine le_ciSup_of_le hb x ?_
        rw [ciSup_pos hx']
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_main_fiber : ∀ (N m : ℕ) (w : Fin m → ℝ) (y : Fin N → Fin m), ∑ x, (((Finset.univ.filter (fun k => y k = x)).card : ℕ) : ℝ) * w x = ∑ k, w (y k) :=
    fun (N m : ℕ) (w : Fin m → ℝ) (y : Fin N → Fin m) => by
      classical
      rw [← Finset.sum_fiberwise Finset.univ y (fun k => w (y k))]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_congr rfl (g := fun _ => w x) (fun k hk => by rw [(Finset.mem_filter.mp hk).2])]
      rw [Finset.sum_const, nsmul_eq_mul]
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_main_card : ∀ (N m : ℕ) (y : Fin N → Fin m), ∑ x, (Finset.univ.filter (fun k => y k = x)).card = N :=
    fun (N m : ℕ) (y : Fin N → Fin m) => by
      classical
      have := Finset.card_eq_sum_card_fiberwise (f := y) (s := Finset.univ) (t := Finset.univ)
        (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
      simpa using this.symm
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_main_fac : ∀ (a : ℕ), 1 ≤ (Real.exp 1 * a) ^ a / (a.factorial : ℝ) :=
    fun (a : ℕ) => by
      have hpos : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
      rw [le_div_iff₀ hpos, one_mul]
      have h1 : (a.factorial : ℝ) ≤ (a : ℝ) ^ a := by exact_mod_cast Nat.factorial_le_pow a
      have h2 : (a : ℝ) ≤ Real.exp 1 * a := by
        have := Real.add_one_le_exp 1
        nlinarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
      exact h1.trans (pow_le_pow_left₀ (Nat.cast_nonneg a) h2 a)
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  have LB_main_prob1 : ∀ (m : ℕ) (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
      (hν : IsProbabilityMeasure ν) (π : 𝕋 → Fin m) (hπ : Measurable π), ∑ x, (ν (π ⁻¹' {x})).toReal = 1 :=
    fun (m : ℕ) (𝕋 : Type u_1) (m𝕋 : MeasurableSpace 𝕋) (ν : Measure 𝕋)
        (hν : IsProbabilityMeasure ν) (π : 𝕋 → Fin m) (hπ : Measurable π) => by
      rw [← ENNReal.toReal_sum (fun x _ => measure_ne_top ν _),
        sum_measure_preimage_singleton _ (fun y _ => hπ (measurableSet_singleton y))]
      simp
  open MeasureTheory ProbabilityTheory unitInterval Finset NNReal ENNReal SupremumOfSelectorProcesses in
  set_option autoImplicit true in
  open Classical in
  have LB_main : ∀ (N : ℕ) (N_pos : N > 0) (𝕋 : Type u_1) (t𝕋 : TopologicalSpace 𝕋)
      (p𝕋 : PolishSpace 𝕋)
      (m𝕋 : MeasurableSpace 𝕋) (b𝕋 : BorelSpace 𝕋) (ν : Measure 𝕋) (hν : IsProbabilityMeasure ν)
      (Ω : Type u_2) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (Y : Fin N → Ω → 𝕋)
      (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P)
      (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}) (h𝓕 : Finite 𝓕)
      (hZ₀ : 0 < 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]) (hZ : 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P] < ∞), ∃ 𝓒 : Finset ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}),
        {ω | ⨆ f ∈ 𝓕, Z N Y f ω ≥ L₃ * 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]} ⊆ ⋃ c ∈ 𝓒, {ω | c.2 ≤ Z N Y c.1 ω}
        ∧ ∑ c : 𝓒, P {ω | c.val.2 ≤ Z N Y c.val.1 ω} ≤ 2⁻¹ :=
    fun (N : ℕ) (N_pos : N > 0) (𝕋 : Type u_1) (t𝕋 : TopologicalSpace 𝕋)
        (p𝕋 : PolishSpace 𝕋)
        (m𝕋 : MeasurableSpace 𝕋) (b𝕋 : BorelSpace 𝕋) (ν : Measure 𝕋) (hν : IsProbabilityMeasure ν)
        (Ω : Type u_2) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (Y : Fin N → Ω → 𝕋)
        (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P)
        (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}) (h𝓕 : Finite 𝓕)
        (hZ₀ : 0 < 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]) (hZ : 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P] < ∞) => by
      set E := 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P] with hEdef
      have hEr : 0 < E.toReal := ENNReal.toReal_pos hZ₀.ne' hZ.ne
      have hNr : (0 : ℝ) < N := by exact_mod_cast N_pos
      obtain ⟨m, π, hπ, v, hv0, hvle, hvge⟩ := LB_main_disc 𝕋 m𝕋 ν 𝓕 h𝓕 E.toReal hEr
      set μ : Fin m → ℝ := fun x => (ν (π ⁻¹' {x})).toReal with hμdef
      have hμ0 : ∀ x, 0 ≤ μ x := fun x => ENNReal.toReal_nonneg
      have hμ1 : ∑ x, μ x = 1 := LB_main_prob1 m 𝕋 m𝕋 ν hν π hπ
      -- the sup as a finite sup
      have hsupω : ∀ ω, (⨆ f ∈ 𝓕, fun x => Z N Y (↑f) x) ω = ⨆ f ∈ 𝓕, Z N Y (↑f) ω := by
        intro ω; simp only [iSup_apply]
      obtain ⟨T, hT, -⟩ := LB_main_iSup_eq _ 𝓕 h𝓕 (fun f => (0 : ℝ≥0))
      have hsupT : ∀ ω, ⨆ f ∈ 𝓕, Z N Y (↑f) ω = T.sup (fun f => Z N Y (↑f) ω) := by
        intro ω
        obtain ⟨T', hT', h'⟩ := LB_main_iSup_eq _ 𝓕 h𝓕 (fun f => Z N Y (↑f) ω)
        rw [h']
        have : T' = T := by ext x; rw [hT', hT]
        rw [this]
      have hZsum : ∀ (f : 𝕋 → ℝ≥0) ω, ((Z N Y f ω : ℝ≥0) : ℝ) * N = ∑ k, ((f (Y k ω) : ℝ≥0) : ℝ) := by
        intro f ω
        simp only [Z, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast, NNReal.coe_sum]
        field_simp
      -- Λ and g
      set Λ : Finset (Fin m → ℝ) := T.image v with hΛdef
      have hΛ : ∀ w ∈ Λ, ∀ x, 0 ≤ w x := by
        intro w hw x
        obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hw
        exact hv0 f x
      set g0 : (Fin N → Fin m) → ℝ := fun y => ⨆ f : T, ∑ k, v f (y k) with hg0def
      have hg0 : ∀ y, ∀ f ∈ T, ∑ k, v f (y k) ≤ g0 y := by
        intro y f hf
        exact le_ciSup (f := fun f : T => ∑ k, v f (y k)) (Set.finite_range _).bddAbove ⟨f, hf⟩
      have hg00 : ∀ y, 0 ≤ g0 y := fun y =>
        Real.iSup_nonneg (fun f => Finset.sum_nonneg (fun k _ => hv0 _ _))
      set g : (Fin N → Fin m) → ℝ := fun y => N * E.toReal + g0 y with hgdef
      have hg : ∀ y, ∀ w ∈ Λ, ∑ k, w (y k) ≤ g y := by
        intro y w hw
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hw
        have := hg0 y f hf
        simp only [hgdef]; nlinarith
      have hprod1 : ∑ y : Fin N → Fin m, ∏ k, μ (y k) = 1 := by
        rw [← Fintype.prod_sum (fun (_ : Fin N) x => μ x), hμ1, Finset.prod_const_one]
      have hEg0 : ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g0 y ≤ N * E.toReal := by
        have hpt : ∀ ω, ENNReal.ofReal (g0 (fun k => π (Y k ω))) ≤
            (N : ℝ≥0∞) * ↑((⨆ f ∈ 𝓕, fun x => Z N Y (↑f) x) ω) := by
          intro ω
          rw [hsupω, hsupT]
          have hle : g0 (fun k => π (Y k ω)) ≤ N * ((T.sup (fun f => Z N Y (↑f) ω) : ℝ≥0) : ℝ) := by
            refine Real.iSup_le (fun f => ?_) (by positivity)
            have hfT : f.1 ∈ 𝓕 := (hT f.1).mp f.2
            calc ∑ k, v f.1 (π (Y k ω)) ≤ ∑ k, ((f.1.1 (Y k ω) : ℝ≥0) : ℝ) :=
                  Finset.sum_le_sum (fun k _ => hvle f.1 hfT (Y k ω))
              _ = ((Z N Y f.1.1 ω : ℝ≥0) : ℝ) * N := (hZsum _ ω).symm
              _ ≤ ((T.sup (fun f => Z N Y (↑f) ω) : ℝ≥0) : ℝ) * N := by
                  gcongr
                  exact Finset.le_sup (s := T) (f := fun f => Z N Y (↑f) ω) f.2
              _ = _ := mul_comm _ _
          calc ENNReal.ofReal (g0 (fun k => π (Y k ω)))
              ≤ ENNReal.ofReal (N * ((T.sup (fun f => Z N Y (↑f) ω) : ℝ≥0) : ℝ)) :=
                ENNReal.ofReal_le_ofReal hle
            _ = _ := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]
        have hpush := LB_push N N_pos 𝕋 m𝕋 ν hν Ω mΩ P Y Y_indep Y_law_ν m π hπ
          (fun y => ENNReal.ofReal (g0 y))
        have hint : ∫⁻ ω, ENNReal.ofReal (g0 (fun k => π (Y k ω))) ∂P ≤ (N : ℝ≥0∞) * E := by
          rw [hEdef, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
          exact lintegral_mono hpt
        have hsum : ENNReal.ofReal (∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g0 y) =
            ∑ y : Fin N → Fin m, (∏ k, ν (π ⁻¹' {y k})) * ENNReal.ofReal (g0 y) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun y _ =>
            mul_nonneg (Finset.prod_nonneg (fun k _ => hμ0 _)) (hg00 y))]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun k _ => hμ0 _)),
            ENNReal.ofReal_prod_of_nonneg (fun k _ => hμ0 _)]
          congr 1
          refine Finset.prod_congr rfl (fun k _ => ?_)
          rw [hμdef, ENNReal.ofReal_toReal (measure_ne_top ν _)]
        have h3 : ENNReal.ofReal (∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g0 y) ≤ (N : ℝ≥0∞) * E := by
          rw [hsum, ← hpush]; exact hint
        rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hZ.ne)] at h3
        simpa [ENNReal.toReal_mul] using h3
      have hEg : ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g y =
          N * E.toReal + ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g0 y := by
        simp only [hgdef, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hprod1, one_mul]
      have hg0s : 0 ≤ ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g0 y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (Finset.prod_nonneg (fun k _ => hμ0 _)) (hg00 y))
      have hpos : 0 < ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g y := by
        rw [hEg]; positivity
      obtain ⟨𝓖, hcov, hGsupp, hcost⟩ := LB_fin m N N_pos μ hμ0 hμ1 Λ hΛ g hg hpos
      -- the cost functions
      set c : (Fin m → ℕ) → Fin m → ℝ :=
        fun G x => if 0 < G x then Real.log (G x / (N * μ x)) else 0 with hcdef
      have hc0 : ∀ G ∈ 𝓖, ∀ x, 0 ≤ c G x := by
        intro G hG x
        simp only [hcdef]
        split_ifs with h
        · obtain ⟨h1, h2⟩ := hGsupp G hG x h
          apply Real.log_nonneg
          rw [le_div_iff₀ (by positivity)]; linarith
        · exact le_refl _
      have hcostnn : ∀ G : Fin m → ℕ,
          0 ≤ ∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ) :=
        fun G => Finset.prod_nonneg (fun x _ => div_nonneg (pow_nonneg (mul_nonneg
          (mul_nonneg (Real.exp_pos 1).le hNr.le) (hμ0 x)) _) (Nat.cast_nonneg _))
      set A : (Fin m → ℕ) → ℝ := fun G => ∑ x, (G x : ℝ) * c G x with hAdef
      have hApos : ∀ G ∈ 𝓖, 0 < A G := by
        intro G hG
        have hA0 : 0 ≤ A G :=
          Finset.sum_nonneg (fun x _ => mul_nonneg (Nat.cast_nonneg _) (hc0 G hG x))
        by_contra hneg
        have hA : A G = 0 := le_antisymm (not_lt.mp hneg) hA0
        have hterm := (Finset.sum_eq_zero_iff_of_nonneg
          (fun x _ => mul_nonneg (Nat.cast_nonneg _) (hc0 G hG x))).mp hA
        have h1 : ∏ _x : Fin m, (1 : ℝ) ≤
            ∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => zero_le_one) (fun x _ => ?_)
          by_cases hx : 0 < G x
          · have h2 := hterm x (Finset.mem_univ x)
            have hGx : (G x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
            have hcx : c G x = 0 := by
              rcases mul_eq_zero.mp h2 with h | h
              · exact absurd h hGx
              · exact h
            simp only [hcdef, hx, if_true] at hcx
            obtain ⟨hμx, hNμ⟩ := hGsupp G hG x hx
            have hqpos : 0 < (G x : ℝ) / (N * μ x) := by
              have : (0 : ℝ) < G x := by exact_mod_cast hx
              positivity
            have hq : (G x : ℝ) / (N * μ x) = 1 := by
              rcases Real.log_eq_zero.mp hcx with h | h | h
              · linarith
              · exact h
              · linarith
            have : (N : ℝ) * μ x = G x := by
              rw [div_eq_one_iff_eq (by positivity)] at hq; linarith
            rw [mul_assoc, this]; exact LB_main_fac (G x)
          · have : G x = 0 := by omega
            rw [this]; simp
        rw [Finset.prod_const_one] at h1
        have h2 := le_trans (Finset.single_le_sum (fun G _ => hcostnn G) hG) hcost
        linarith
      have hcc : ∀ G ∈ 𝓖, ∀ x, ((c G x).toNNReal : ℝ) = c G x :=
        fun G hG x => Real.coe_toNNReal _ (hc0 G hG x)
      have hgGm : ∀ G : Fin m → ℕ, Measurable (fun y => Real.toNNReal (c G (π y))) :=
        fun G => (measurable_of_countable (fun x => Real.toNNReal (c G x))).comp hπ
      have hNinv : (0 : ℝ≥0) < (N : ℝ≥0)⁻¹ := inv_pos.mpr (by exact_mod_cast N_pos)
      have htG : ∀ G ∈ 𝓖, (N : ℝ≥0)⁻¹ * Real.toNNReal (A G) ∈ {t : ℝ≥0 | t > 0} := by
        intro G hG
        simp only [Set.mem_setOf_eq]
        exact mul_pos hNinv (Real.toNNReal_pos.mpr (hApos G hG))
      set gnull : 𝕋 → ℝ≥0 := fun y => if μ (π y) = 0 then 1 else 0 with hgnull
      have hgnullm : Measurable gnull :=
        (measurable_of_countable (fun x => if μ x = 0 then (1:ℝ≥0) else 0)).comp hπ
      have htnull : (N : ℝ≥0)⁻¹ ∈ {t : ℝ≥0 | t > 0} := hNinv
      set φ : 𝓖 → ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}) := fun G =>
        (⟨fun y => Real.toNNReal (c G.1 (π y)), hgGm G.1⟩,
          ⟨(N : ℝ≥0)⁻¹ * Real.toNNReal (A G.1), htG G.1 G.2⟩) with hφ
      set c0 : ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}) :=
        (⟨gnull, hgnullm⟩, ⟨(N : ℝ≥0)⁻¹, htnull⟩) with hc0def
      -- key inequality for the G-events
      have hZG : ∀ G ∈ 𝓖, ∀ ω, (N : ℝ≥0)⁻¹ * Real.toNNReal (A G) ≤
          Z N Y (fun y => Real.toNNReal (c G (π y))) ω ↔ A G ≤ ∑ k, c G (π (Y k ω)) := by
        intro G hG ω
        simp only [Z]
        rw [← Real.toNNReal_sum_of_nonneg (fun k _ => hc0 G hG _)]
        constructor
        · intro h
          have h2 := le_of_mul_le_mul_left h hNinv
          exact (Real.toNNReal_le_toNNReal_iff
            (Finset.sum_nonneg (fun k _ => hc0 G hG _))).mp h2
        · intro h
          exact mul_le_mul_left' (Real.toNNReal_le_toNNReal h) _
      have hevG : ∀ G (hG : G ∈ 𝓖), P {ω | ((φ ⟨G, hG⟩).2 : ℝ≥0) ≤ Z N Y (φ ⟨G, hG⟩).1 ω} ≤
          ENNReal.ofReal (∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ)) := by
        intro G hG
        refine le_trans (LB_main_prob N N_pos 𝕋 m𝕋 ν hν Ω mΩ P Y Y_indep Y_law_ν m π hπ
          {y | A G ≤ ∑ k, c G (y k)} _ ?_) (ENNReal.ofReal_le_ofReal ?_)
        · intro ω hω
          simp only [Set.mem_setOf_eq, hφ] at hω ⊢
          exact (hZG G hG ω).mp hω
        · refine le_trans (le_of_eq ?_) (LB_markov m N N_pos μ hμ0 hμ1 G (hGsupp G hG))
          refine Finset.sum_congr rfl (fun y _ => ?_)
          simp only [Set.mem_setOf_eq, hAdef, hcdef, hμdef]
      have hnull : P {ω | ((c0.2 : ℝ≥0)) ≤ Z N Y c0.1 ω} = 0 := by
        refine le_antisymm (le_trans (LB_main_prob N N_pos 𝕋 m𝕋 ν hν Ω mΩ P Y Y_indep Y_law_ν m π hπ
          {y | ∃ k, μ (y k) = 0} _ ?_) (le_of_eq ?_)) (_root_.zero_le _)
        · intro ω hω
          simp only [Set.mem_setOf_eq, hc0def, Z] at hω ⊢
          by_contra hne
          push_neg at hne
          have : ∑ k, gnull (Y k ω) = 0 :=
            Finset.sum_eq_zero (fun k _ => by simp only [hgnull]; rw [if_neg (hne k)])
          rw [this, mul_zero] at hω
          exact absurd hω (not_le.mpr hNinv)
        · have := LB_main_null N m μ
          simp only [hμdef] at this ⊢
          rw [this, ENNReal.ofReal_zero]
      refine ⟨insert c0 (𝓖.attach.image φ), ?_, ?_⟩
      · intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        rw [Set.mem_iUnion₂]
        by_cases h0 : ∃ k, μ (π (Y k ω)) = 0
        · refine ⟨c0, Finset.mem_insert_self _ _, ?_⟩
          obtain ⟨k0, hk0⟩ := h0
          simp only [Set.mem_setOf_eq, hc0def, Z]
          have h1 : (1 : ℝ≥0) ≤ ∑ k, gnull (Y k ω) := by
            have : gnull (Y k0 ω) = 1 := by simp only [hgnull]; rw [if_pos hk0]
            rw [← this]
            exact Finset.single_le_sum (f := fun k => gnull (Y k ω)) (fun _ _ => _root_.zero_le _)
              (Finset.mem_univ k0)
          calc (N : ℝ≥0)⁻¹ = (N : ℝ≥0)⁻¹ * 1 := (mul_one _).symm
            _ ≤ _ := mul_le_mul_left' h1 _
        · push_neg at h0
          -- a function in 𝓕 with a large value
          have hL : (L₃ : ℝ) = 10 ^ 32 := by simp [L₃]
          have hbig : (L₃ : ℝ) * E.toReal ≤ ((⨆ f ∈ 𝓕, Z N Y (↑f) ω : ℝ≥0) : ℝ) := by
            have := ENNReal.toReal_mono ENNReal.coe_ne_top hω
            simpa [ENNReal.toReal_mul] using this
          rw [hsupT] at hbig
          have hlt : Real.toNNReal ((L₃ : ℝ) * E.toReal / 2) < T.sup (fun f => Z N Y (↑f) ω) := by
            rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by positivity)]
            have : 0 < (L₃ : ℝ) * E.toReal := by rw [hL]; positivity
            linarith
          obtain ⟨f, hfT, hf⟩ := Finset.lt_sup_iff.mp hlt
          have hf𝓕 : f ∈ 𝓕 := (hT f).mp hfT
          have hfZ : (L₃ : ℝ) * E.toReal / 2 < ((Z N Y f.1 ω : ℝ≥0) : ℝ) := by
            have := (NNReal.coe_lt_coe.mpr hf)
            rwa [Real.coe_toNNReal _ (by rw [hL]; positivity)] at this
          set S : Fin m → ℕ := fun x => (Finset.univ.filter (fun k => π (Y k ω) = x)).card with hSdef
          have hS1 : ∑ x, S x = N := LB_main_card N m (fun k => π (Y k ω))
          have hS2 : ∀ x, 0 < S x → 0 < μ x := by
            intro x hx
            obtain ⟨k, hk⟩ := Finset.card_pos.mp hx
            have hk' := (Finset.mem_filter.mp hk).2
            rw [← hk']
            exact lt_of_le_of_ne (hμ0 _) (h0 k).symm
          have hS3 : ∃ w ∈ Λ, (10 : ℝ) ^ 30 * ∑ y : Fin N → Fin m, (∏ k, μ (y k)) * g y ≤
              ∑ x, (S x : ℝ) * w x := by
            refine ⟨v f, Finset.mem_image_of_mem v hfT, ?_⟩
            rw [LB_main_fiber N m (v f) (fun k => π (Y k ω))]
            have hlow : ∑ k, (((f.1 (Y k ω) : ℝ≥0) : ℝ) - E.toReal) ≤ ∑ k, v f (π (Y k ω)) := by
              refine Finset.sum_le_sum (fun k _ => ?_)
              have hν0 : ν (π ⁻¹' {π (Y k ω)}) ≠ 0 := by
                intro h; apply h0 k; simp only [hμdef, h, ENNReal.toReal_zero]
              have := hvge f hf𝓕 (Y k ω) hν0
              linarith
            rw [Finset.sum_sub_distrib, ← hZsum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul] at hlow
            rw [hEg]
            rw [hL] at hfZ
            have h5 : (2 * 10 ^ 30 + 1) * E.toReal * N ≤ ((Z N Y f.1 ω : ℝ≥0) : ℝ) * N := by
              apply mul_le_mul_of_nonneg_right _ hNr.le
              nlinarith
            nlinarith
          obtain ⟨G, hG, hGS⟩ := hcov S hS1 hS2 hS3
          refine ⟨φ ⟨G, hG⟩, Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨⟨G, hG⟩, Finset.mem_attach _ _, rfl⟩), ?_⟩
          simp only [Set.mem_setOf_eq, hφ]
          rw [hZG G hG ω]
          rw [← LB_main_fiber N m (c G) (fun k => π (Y k ω))]
          refine Finset.sum_le_sum (fun x _ => ?_)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hGS x) (hc0 G hG x)
      · rw [Finset.sum_coe_sort (insert c0 (𝓖.attach.image φ))
          (fun c => P {ω | (c.2 : ℝ≥0) ≤ Z N Y c.1 ω})]
        have hins : ∑ c ∈ insert c0 (𝓖.attach.image φ), P {ω | (c.2 : ℝ≥0) ≤ Z N Y c.1 ω} ≤
            P {ω | (c0.2 : ℝ≥0) ≤ Z N Y c0.1 ω} +
              ∑ c ∈ 𝓖.attach.image φ, P {ω | (c.2 : ℝ≥0) ≤ Z N Y c.1 ω} := by
          by_cases hmem : c0 ∈ 𝓖.attach.image φ
          · rw [Finset.insert_eq_of_mem hmem]; exact le_add_self
          · rw [Finset.sum_insert hmem]
        refine le_trans hins ?_
        rw [hnull, zero_add]
        refine le_trans (Finset.sum_image_le_of_nonneg (fun _ _ => _root_.zero_le _)) ?_
        calc ∑ G ∈ 𝓖.attach, P {ω | ((φ G).2 : ℝ≥0) ≤ Z N Y (φ G).1 ω}
            ≤ ∑ G ∈ 𝓖.attach, ENNReal.ofReal
                (∏ x, (Real.exp 1 * N * μ x) ^ (G.1 x) / ((G.1 x).factorial : ℝ)) :=
              Finset.sum_le_sum (fun G _ => hevG G.1 G.2)
          _ = ENNReal.ofReal (∑ G ∈ 𝓖, ∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ)) := by
              rw [Finset.sum_attach 𝓖 (fun G => ENNReal.ofReal
                (∏ x, (Real.exp 1 * N * μ x) ^ (G x) / ((G x).factorial : ℝ))),
                ENNReal.ofReal_sum_of_nonneg (fun G _ => hcostnn G)]
          _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hcost
          _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  exact LB_main N N_pos 𝕋 t𝕋 p𝕋 m𝕋 b𝕋 ν hν Ω mΩ P Y Y_indep Y_law_ν 𝓕 h𝓕 hZ₀ hZ)")
    withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0, maxRecDepth := 100000 }) (do
      Lean.Elab.Tactic.evalTactic stx
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing)

end SupremumOfSelectorProcesses

end Submission
