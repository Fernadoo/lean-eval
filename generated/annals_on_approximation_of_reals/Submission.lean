import ChallengeDeps
import Submission.Helpers
import Lean

open OnApproximationOfReals
open NNReal ENNReal

set_option autoImplicit false

namespace Submission

theorem theorem_1_1 (n : ℕ) (hn : n ≥ 2) (ξ : ℝ) (hξ : Transcendental ℚ ξ) :
    letI a : ℝ := 1 / (2 - Real.log 2)
    (ω⋆ n ξ : EReal) ≥ (a : EReal) * n := by
  run_tac do
    let stx ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "(
  have L_absorb_roots_finite : ∀ (d : ℕ) (p : Polynomial ℂ), p.natDegree ≤ d → p ≠ 0 →
      {z : ℂ | p.eval z = 0}.Finite :=
    (by
      intro d
      induction d with
      | zero =>
        intro p hp hp0
        have hpc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hp
        have hc : p.coeff 0 ≠ 0 := by
          intro h0; apply hp0; rw [hpc, h0, map_zero]
        convert Set.finite_empty
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [hpc, Polynomial.eval_C]; exact hc
      | succ d ih =>
        intro p hp hp0
        by_cases hr : ∃ a, p.IsRoot a
        · obtain ⟨a, ha⟩ := hr
          have hmul := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr ha
          have hq0 : p /ₘ (Polynomial.X - Polynomial.C a) ≠ 0 := by
            intro h0; apply hp0; rw [← hmul, h0, mul_zero]
          have hqd : (p /ₘ (Polynomial.X - Polynomial.C a)).natDegree ≤ d := by
            rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C a),
              Polynomial.natDegree_X_sub_C]
            omega
          have hfin := ih _ hqd hq0
          apply (hfin.insert a).subset
          intro z hz
          simp only [Set.mem_setOf_eq] at hz
          rw [← hmul, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C] at hz
          rw [Set.mem_insert_iff]
          rcases mul_eq_zero.mp hz with h1 | h1
          · left; exact sub_eq_zero.mp h1
          · right; exact h1
        · convert Set.finite_empty
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro hz; exact hr ⟨z, hz⟩
    )
  have L_absorb_rat_finite : ∀ (B : ℕ), {q : ℚ | q.num.natAbs ≤ B ∧ q.den ≤ B}.Finite :=
    (fun (B : ℕ) => by
      have hfin : ((Set.Icc (-(B:ℤ)) B) ×ˢ (Set.Icc (0:ℕ) B)).Finite :=
        (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
      apply (hfin.image (fun x : ℤ × ℕ => (x.1 : ℚ) / x.2)).subset
      intro q hq
      obtain ⟨h1, h2⟩ := hq
      refine ⟨(q.num, q.den), ⟨⟨?_, ?_⟩, ?_, ?_⟩, Rat.num_div_den q⟩
      · show -(B:ℤ) ≤ q.num
        omega
      · show q.num ≤ (B:ℤ)
        omega
      · show 0 ≤ q.den
        omega
      · exact h2
    )
  have L_absorb_isIntegral : ∀ (α : ℂ) (hα : IsAlgebraic ℚ α), IsIntegral ℚ α :=
    (fun (α : ℂ) (hα : IsAlgebraic ℚ α) => by
      obtain ⟨p, hp0, hpα⟩ := hα
      refine ⟨p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp0, ?_⟩
      rw [← Polynomial.aeval_def, map_mul, hpα, zero_mul]
    )
  have L_absorb_coeff : ∀ (α : ℂ) (hα : IsAlgebraic ℚ α) (B : ℕ) (hB : height α ≤ B) (i : ℕ), (minpoly ℚ α).coeff i ∈ {q : ℚ | q.num.natAbs ≤ B ∧ q.den ≤ B} :=
    (fun (α : ℂ) (hα : IsAlgebraic ℚ α) (B : ℕ) (hB : height α ≤ B) (i : ℕ) => by
      have hint := L_absorb_isIntegral α hα
      have hmon : (minpoly ℚ α).Monic := minpoly.monic hint
      have hp0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hint
      obtain ⟨D, hD⟩ : ∃ D : ℕ, D = Multiset.lcm (Multiset.map (fun i ↦ ((minpoly ℚ α).coeff i).den)
          (minpoly ℚ α).support.val) := ⟨_, rfl⟩
      have hH : height α = Finset.sup (minpoly ℚ α).support
          (fun i ↦ ((D:ℚ) * (minpoly ℚ α).coeff i).num.natAbs) := by rw [hD]; rfl
      have hle : ∀ j ∈ (minpoly ℚ α).support, ((D:ℚ) * (minpoly ℚ α).coeff j).num.natAbs ≤ B :=
        fun j hj => le_trans (Finset.le_sup (f := fun i ↦ ((D:ℚ) * (minpoly ℚ α).coeff i).num.natAbs) hj)
          (hH ▸ hB)
      have hD0 : D ≠ 0 := by
        rw [hD, Ne, Multiset.lcm_eq_zero_iff]
        intro h
        obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp h
        exact ((minpoly ℚ α).coeff j).den_nz hj
      have hDB : D ≤ B := by
        have h1 := hle (minpoly ℚ α).natDegree (Polynomial.natDegree_mem_support_of_nonzero hp0)
        rw [show (minpoly ℚ α).coeff (minpoly ℚ α).natDegree = 1 from hmon, mul_one,
          Rat.num_natCast] at h1
        simpa using h1
      by_cases hi : i ∈ (minpoly ℚ α).support
      · have hdvd : ((minpoly ℚ α).coeff i).den ∣ D := by
          rw [hD]; exact Multiset.dvd_lcm (Multiset.mem_map_of_mem _ hi)
        obtain ⟨k, hk⟩ := hdvd
        have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact hD0 hk
        have heq : (D:ℚ) * (minpoly ℚ α).coeff i = ((k * ((minpoly ℚ α).coeff i).num : ℤ) : ℚ) := by
          rw [hk]; push_cast
          rw [← Rat.mul_den_eq_num]; ring
        have h1 := hle i hi
        rw [heq, Rat.num_intCast, Int.natAbs_mul] at h1
        refine ⟨le_trans ?_ h1, le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) ⟨k, hk⟩) hDB⟩
        have : 1 ≤ (k:ℤ).natAbs := by simp; omega
        exact le_trans (le_of_eq (one_mul _).symm) (Nat.mul_le_mul_right _ this)
      · have h0 : (minpoly ℚ α).coeff i = 0 := Polynomial.notMem_support_iff.mp hi
        rw [h0]; simp; omega
    )
  have L_absorb_northcott : ∀ (n B : ℕ), {α : AlgebraicDegLE n | height α.1 ≤ B}.Finite :=
    (fun (n B : ℕ) => by
      have hFfin := L_absorb_rat_finite B
      have hPfin : ((fun α : AlgebraicDegLE n => minpoly ℚ α.1) ''
          {α : AlgebraicDegLE n | height α.1 ≤ B}).Finite := by
        apply Set.Finite.of_finite_image (f := fun p : Polynomial ℚ => fun i : Fin (n+1) => p.coeff i)
        · apply (Set.Finite.pi (t := fun _ : Fin (n+1) => {q : ℚ | q.num.natAbs ≤ B ∧ q.den ≤ B})
            (fun _ => hFfin)).subset
          rintro v ⟨p, ⟨α, hα, rfl⟩, rfl⟩
          intro i _
          exact L_absorb_coeff α.1 α.2.1 B hα i
        · rintro p ⟨α, hα, rfl⟩ q ⟨β, hβ, rfl⟩ hpq
          ext i
          show (minpoly ℚ α.1).coeff i = (minpoly ℚ β.1).coeff i
          by_cases hi : i ≤ n
          · exact congrFun hpq ⟨i, by omega⟩
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := α.2.2; omega),
                Polynomial.coeff_eq_zero_of_natDegree_lt (by have := β.2.2; omega)]
      apply (hPfin.biUnion (t := fun p => {α : AlgebraicDegLE n | Polynomial.aeval α.1 p = 0}) ?_).subset
      · intro α hα
        exact Set.mem_biUnion ⟨α, hα, rfl⟩ (minpoly.aeval ℚ α.1)
      · rintro p ⟨α₀, -, rfl⟩
        have hint := L_absorb_isIntegral α₀.1 α₀.2.1
        have hp0 := minpoly.ne_zero hint
        have hmap0 : (minpoly ℚ α₀.1).map (algebraMap ℚ ℂ) ≠ 0 := by
          intro h; apply hp0
          exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective (by rw [h, Polynomial.map_zero])
        have hfin := L_absorb_roots_finite _ _ le_rfl hmap0
        apply (hfin.preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
        intro α hα
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hα ⊢
        rw [Polynomial.eval_map_algebraMap]; exact hα
    )
  have L_absorb_ne : ∀ (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (α : AlgebraicDegLE n), 0 < ‖(ξ : ℂ) - α.1‖ :=
    (fun (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (α : AlgebraicDegLE n) => by
      rw [norm_pos_iff, sub_ne_zero]
      intro heq
      apply hξ
      obtain ⟨p, hp0, hpα⟩ := α.2.1
      refine ⟨p, hp0, ?_⟩
      rw [← heq] at hpα
      have h2 : (Polynomial.aeval (ξ:ℂ) p) = ((Polynomial.aeval ξ p : ℝ) : ℂ) := by
        rw [show (ξ:ℂ) = algebraMap ℝ ℂ ξ from rfl, Polynomial.aeval_algebraMap_apply]; rfl
      rw [h2] at hpα
      exact_mod_cast hpα
    )
  have L_absorb_eta : ∀ {ι : Type} (U : Set ι) (hU : U.Finite) (f : ι → ℝ) (hf : ∀ i, 0 < f i), ∃ η : ℝ, 0 < η ∧ ∀ i ∈ U, η ≤ f i :=
    (fun {ι : Type} (U : Set ι) (hU : U.Finite) (f : ι → ℝ) (hf : ∀ i, 0 < f i) => by
      rcases U.eq_empty_or_nonempty with hUe | hUne
      · exact ⟨1, one_pos, by intro i hi; rw [hUe] at hi; simp at hi⟩
      · obtain ⟨a, -, hmin⟩ := Set.exists_min_image U f hU hUne
        exact ⟨f a, hf a, hmin⟩
    )
  have L_absorb : ∀ (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (ω : ℝ≥0) (hω : 0 < (ω : ℝ))
      (ω' K : ℝ) (hωω' : (ω : ℝ) < ω') (hK : 0 < K)
      (h : ∀ η : ℝ, 0 < η → ∃ α : AlgebraicDegLE n,
        ‖(ξ : ℂ) - α.1‖ < η ∧ ‖(ξ : ℂ) - α.1‖ ≤ K * (height α.1 : ℝ) ^ (-ω' - 1)), ω ∈ ω_stars n ξ :=
    (fun (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (ω : ℝ≥0) (hω : 0 < (ω : ℝ))
        (ω' K : ℝ) (hωω' : (ω : ℝ) < ω') (hK : 0 < K)
        (h : ∀ η : ℝ, 0 < η → ∃ α : AlgebraicDegLE n,
          ‖(ξ : ℂ) - α.1‖ < η ∧ ‖(ξ : ℂ) - α.1‖ ≤ K * (height α.1 : ℝ) ^ (-ω' - 1)) => by
      refine ⟨by exact_mod_cast hω, ?_⟩
      intro hfin
      obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, B₀ = K ^ (ω' - ω)⁻¹ := ⟨_, rfl⟩
      obtain ⟨N, hN⟩ : ∃ N : ℕ, B₀ < N := exists_nat_gt B₀
      obtain ⟨η, hη0, hη⟩ := L_absorb_eta _ (hfin.union (L_absorb_northcott n N))
        (fun β : AlgebraicDegLE n => ‖(ξ:ℂ) - β.1‖) (L_absorb_ne n ξ hξ)
      obtain ⟨α, hα1, hα2⟩ := h η hη0
      have hHN : N < height α.1 := by
        by_contra hc
        push_neg at hc
        have := hη α (Or.inr hc)
        simp only at this
        linarith
      have hd : 0 < ω' - ω := sub_pos.mpr hωω'
      have hB0 : 0 ≤ B₀ := by rw [hB₀]; exact Real.rpow_nonneg hK.le _
      have hH : B₀ < (height α.1 : ℝ) := lt_trans hN (by exact_mod_cast hHN)
      have hHpos : 0 < (height α.1 : ℝ) := lt_of_le_of_lt hB0 hH
      have hK' : K < (height α.1 : ℝ) ^ (ω' - ω) := by
        have := Real.rpow_lt_rpow hB0 hH hd
        rwa [hB₀, Real.rpow_inv_rpow hK.le hd.ne'] at this
      have hsplit : (height α.1 : ℝ) ^ (-(ω:ℝ) - 1) =
          (height α.1 : ℝ) ^ (ω' - ω) * (height α.1 : ℝ) ^ (-ω' - 1) := by
        rw [← Real.rpow_add hHpos]; congr 1; ring
      have hpos2 : 0 < (height α.1 : ℝ) ^ (-ω' - 1) := Real.rpow_pos_of_pos hHpos _
      have hmem : 0 < ‖(ξ:ℂ) - α.1‖ ∧
          ‖(ξ:ℂ) - α.1‖ ≤ ((height α.1 : ℕ) : ℝ) ^ (-(ω:ℝ) - 1) := by
        refine ⟨L_absorb_ne n ξ hξ α, le_trans hα2 ?_⟩
        rw [hsplit]
        nlinarith
      have := hη α (Or.inl hmem)
      simp only at this
      linarith
    )
  have L_approx_height_ge_one : ∀ (α : ℂ) (hα : IsAlgebraic ℚ α), (1 : ℝ) ≤ (height α : ℝ) :=
    (fun (α : ℂ) (hα : IsAlgebraic ℚ α) => by
      have hint : IsIntegral ℚ α := by
        obtain ⟨p, hp0, hpα⟩ := hα
        refine ⟨p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp0, ?_⟩
        rw [← Polynomial.aeval_def, map_mul, hpα, zero_mul]
      have hmon : (minpoly ℚ α).Monic := minpoly.monic hint
      have hp0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hint
      obtain ⟨D, hD⟩ : ∃ D : ℕ, D = Multiset.lcm (Multiset.map (fun i ↦ ((minpoly ℚ α).coeff i).den)
          (minpoly ℚ α).support.val) := ⟨_, rfl⟩
      have hH : height α = Finset.sup (minpoly ℚ α).support
          (fun i ↦ ((D:ℚ) * (minpoly ℚ α).coeff i).num.natAbs) := by rw [hD]; rfl
      have hD0 : D ≠ 0 := by
        rw [hD, Ne, Multiset.lcm_eq_zero_iff]
        intro h
        obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp h
        exact ((minpoly ℚ α).coeff j).den_nz hj
      have h1 : ((D:ℚ) * (minpoly ℚ α).coeff (minpoly ℚ α).natDegree).num.natAbs ≤ height α := by
        rw [hH]
        exact Finset.le_sup (f := fun i ↦ ((D:ℚ) * (minpoly ℚ α).coeff i).num.natAbs)
          (Polynomial.natDegree_mem_support_of_nonzero hp0)
      rw [show (minpoly ℚ α).coeff (minpoly ℚ α).natDegree = 1 from hmon, mul_one,
          Rat.num_natCast] at h1
      have h2 : D ≤ height α := by simpa using h1
      have : 1 ≤ height α := by omega
      exact_mod_cast this
    )
  have L_approx_a_ge_one : ∀ (n : ℕ) (a : ℕ → ℝ) (ha2 : a 2 = 1)
      (hmono : ∀ i, 2 ≤ i → i ≤ n → a i ≤ a (i + 1)) (i : ℕ) (hi2 : 2 ≤ i) (hin : i ≤ n + 1), 1 ≤ a i :=
    (fun (n : ℕ) (a : ℕ → ℝ) (ha2 : a 2 = 1)
        (hmono : ∀ i, 2 ≤ i → i ≤ n → a i ≤ a (i + 1)) (i : ℕ) (hi2 : 2 ≤ i) (hin : i ≤ n + 1) => by
      induction i with
      | zero => omega
      | succ j ih =>
        rcases Nat.lt_or_ge j 2 with hj | hj
        · have : j + 1 = 2 := by omega
          rw [this, ha2]
        · have := hmono j hj (by omega)
          linarith [ih hj (by omega)]
    )
  have L_approx_Ak_ge_one : ∀ (n : ℕ) (x : ℝ) (hx : (n:ℝ) ≤ x) (a : ℕ → ℝ) (ha2 : a 2 = 1)
      (hmono : ∀ i, 2 ≤ i → i ≤ n → a i ≤ a (i + 1))
      (hsum : ∑ i ∈ Finset.Icc 2 (n + 1), a i = x) (k : ℕ) (hk : k ∈ Finset.Icc 2 (n + 1)), 1 ≤ 2 * x - 2 * ((n : ℝ) + 1 - k) - ∑ i ∈ Finset.Icc 2 k, a i :=
    (fun (n : ℕ) (x : ℝ) (hx : (n:ℝ) ≤ x) (a : ℕ → ℝ) (ha2 : a 2 = 1)
        (hmono : ∀ i, 2 ≤ i → i ≤ n → a i ≤ a (i + 1))
        (hsum : ∑ i ∈ Finset.Icc 2 (n + 1), a i = x) (k : ℕ) (hk : k ∈ Finset.Icc 2 (n + 1)) => by
      obtain ⟨hk2, hkn⟩ := Finset.mem_Icc.mp hk
      have key : ∀ j : ℕ, k + j ≤ n + 1 →
          ∑ i ∈ Finset.Icc 2 k, a i + j ≤ ∑ i ∈ Finset.Icc 2 (k + j), a i := by
        intro j
        induction j with
        | zero => intro _; simp
        | succ j ih =>
          intro hj
          rw [show k + (j + 1) = (k + j) + 1 by omega, Finset.sum_Icc_succ_top (by omega)]
          have h1 := L_approx_a_ge_one n a ha2 hmono (k + j + 1) (by omega) (by omega)
          have h2 := ih (by omega)
          push_cast
          linarith
      have h := key (n + 1 - k) (by omega)
      rw [show k + (n + 1 - k) = n + 1 by omega, hsum] at h
      have hc : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - k := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hc] at h
      have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    )
  have L_approx_family : ∀ (n : ℕ) (H : ℕ → ℝ) (h1 : 1 < H 1)
      (hmono : ∀ i j, i ≤ j → j ≤ n → H i ≤ H j) (a : ℕ → ℝ)
      (ha : a = fun i => Real.log (H (i - 1)) / Real.log (H 1)) (x : ℝ)
      (hx : x = Real.log (∏ j ∈ Finset.Icc 1 n, H j) / Real.log (H 1)), a 2 = 1 ∧ (∀ i, 2 ≤ i → i ≤ n → a i ≤ a (i + 1)) ∧ ∑ i ∈ Finset.Icc 2 (n + 1), a i = x ∧
        (n : ℝ) ≤ x ∧ H 1 ^ x = ∏ j ∈ Finset.Icc 1 n, H j ∧
        (∀ i, 2 ≤ i → i ≤ n + 1 → H 1 ^ a i = H (i - 1)) :=
    (fun (n : ℕ) (H : ℕ → ℝ) (h1 : 1 < H 1)
        (hmono : ∀ i j, i ≤ j → j ≤ n → H i ≤ H j) (a : ℕ → ℝ)
        (ha : a = fun i => Real.log (H (i - 1)) / Real.log (H 1)) (x : ℝ)
        (hx : x = Real.log (∏ j ∈ Finset.Icc 1 n, H j) / Real.log (H 1)) => by
      subst ha hx
      have hl : 0 < Real.log (H 1) := Real.log_pos h1
      have hpos : ∀ j, 1 ≤ j → j ≤ n → 0 < H j := fun j hj hjn =>
        lt_of_lt_of_le (by linarith) (hmono 1 j hj hjn)
      have hlog_prod : Real.log (∏ j ∈ Finset.Icc 1 n, H j) = ∑ j ∈ Finset.Icc 1 n, Real.log (H j) :=
        Real.log_prod (fun j hj => (hpos j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2).ne')
      have hprod_pos : 0 < ∏ j ∈ Finset.Icc 1 n, H j :=
        Finset.prod_pos (fun j hj => hpos j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Real.log (H (2-1)) / Real.log (H 1) = 1
        exact div_self hl.ne'
      · intro i hi2 hin
        show Real.log (H (i - 1)) / Real.log (H 1) ≤ Real.log (H (i + 1 - 1)) / Real.log (H 1)
        apply div_le_div_of_nonneg_right _ hl.le
        apply Real.log_le_log (hpos _ (by omega) (by omega))
        exact hmono _ _ (by omega) (by omega)
      · show ∑ i ∈ Finset.Icc 2 (n + 1), Real.log (H (i - 1)) / Real.log (H 1) =
          Real.log (∏ j ∈ Finset.Icc 1 n, H j) / Real.log (H 1)
        rw [hlog_prod, div_eq_mul_inv, Finset.sum_mul, ← Finset.map_add_right_Icc 1 n 1, Finset.sum_map]
        simp [div_eq_mul_inv]
      · show (n : ℝ) ≤ Real.log (∏ j ∈ Finset.Icc 1 n, H j) / Real.log (H 1)
        rw [hlog_prod, div_eq_mul_inv, Finset.sum_mul]
        simp only [← div_eq_mul_inv]
        have : ∑ j ∈ Finset.Icc 1 n, (1 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 n, Real.log (H j) / Real.log (H 1) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
          rw [le_div_iff₀ hl, one_mul]
          exact Real.log_le_log (by linarith) (hmono 1 j hj1 hjn)
        simpa using this
      · show H 1 ^ (Real.log (∏ j ∈ Finset.Icc 1 n, H j) / Real.log (H 1)) = ∏ j ∈ Finset.Icc 1 n, H j
        rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hl.ne', Real.exp_log hprod_pos]
      · intro i hi2 hin
        show H 1 ^ (Real.log (H (i - 1)) / Real.log (H 1)) = H (i - 1)
        rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hl.ne',
          Real.exp_log (hpos _ (by omega) (by omega))]
    )
  have L_approx_max_eq : ∀ (H2 x ε P : ℝ) (n : ℕ) (hH2 : 1 ≤ H2) (hP : H2 ^ x = P) (hPpos : 0 < P), max (H2 ^ ε / P) (H2 ^ (-(2 * (n : ℝ)))) = H2 ^ (-(min (x - ε) (2 * n))) :=
    (fun (H2 x ε P : ℝ) (n : ℕ) (hH2 : 1 ≤ H2) (hP : H2 ^ x = P) (hPpos : 0 < P) => by
      have hpos : 0 < H2 := by linarith
      rw [← hP, ← Real.rpow_sub hpos]
      rcases le_total (x - ε) (2 * (n:ℝ)) with h | h
      · rw [min_eq_left h, max_eq_left (Real.rpow_le_rpow_of_exponent_le hH2 (by linarith))]
        congr 1; ring
      · rw [min_eq_right h, max_eq_right (Real.rpow_le_rpow_of_exponent_le hH2 (by linarith))]
    )
  have L_approx_reindex : ∀ (f : ℕ → ℝ) (hf1 : f 1 = 1) (k : ℕ) (hk2 : 2 ≤ k), ∑ i ∈ Finset.Icc 2 k, f (i - 1) = 1 + ∑ i ∈ Finset.Ico 2 k, f i :=
    (fun (f : ℕ → ℝ) (hf1 : f 1 = 1) (k : ℕ) (hk2 : 2 ≤ k) => by
      induction k, hk2 using Nat.le_induction with
      | base => simp [hf1]
      | succ k hk ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Ico_succ_top hk]
        simp only [Nat.add_sub_cancel]
        ring
    )
  have L_approx_prod_bound : ∀ (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) (H : ℕ → ℝ) (C y : ℝ)
      (hC : 0 < C) (h1 : 1 < H 1) (h0 : 0 ≤ H 0) (h01 : H 0 ≤ H 1)
      (hmono : ∀ i j, i ≤ j → j ≤ n → H i ≤ H j), (C * H 1 ^ (-y)) ^ 2 * H 0 ^ (n + 1 - k) * H 1 ^ (n + 2 - k) * (∏ i ∈ Finset.Ico 2 k, H i) ≤
        C ^ 2 * H 1 ^ (-(2 * y - 2 * ((n : ℝ) + 1 - k) -
          ∑ i ∈ Finset.Icc 2 k, Real.log (H (i - 1)) / Real.log (H 1))) :=
    (fun (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) (H : ℕ → ℝ) (C y : ℝ)
        (hC : 0 < C) (h1 : 1 < H 1) (h0 : 0 ≤ H 0) (h01 : H 0 ≤ H 1)
        (hmono : ∀ i j, i ≤ j → j ≤ n → H i ≤ H j) => by
      have hH1 : 0 < H 1 := by linarith
      have hl : 0 < Real.log (H 1) := Real.log_pos h1
      have hpos : ∀ j, 1 ≤ j → j ≤ n → 0 < H j := fun j hj hjn =>
        lt_of_lt_of_le (by linarith) (hmono 1 j hj hjn)
      have hsum := L_approx_reindex (fun i => Real.log (H i) / Real.log (H 1)) (div_self hl.ne') k hk2
      simp only at hsum
      rw [hsum]
      set S := ∑ i ∈ Finset.Ico 2 k, Real.log (H i) / Real.log (H 1) with hS
      have hprod : ∏ i ∈ Finset.Ico 2 k, H i = H 1 ^ S := by
        rw [Real.rpow_def_of_pos hH1, hS, Finset.mul_sum, Real.exp_sum]
        apply Finset.prod_congr rfl
        intro i hi
        obtain ⟨hi2, hik⟩ := Finset.mem_Ico.mp hi
        rw [mul_div_cancel₀ _ hl.ne', Real.exp_log (hpos i (by omega) (by omega))]
      rw [hprod]
      have h0le : H 0 ^ (n + 1 - k) ≤ H 1 ^ (n + 1 - k) := pow_le_pow_left₀ h0 h01 _
      have hcast1 : (H 1 ^ (n + 1 - k) : ℝ) = H 1 ^ ((n:ℝ) + 1 - k) := by
        rw [← Real.rpow_natCast, Nat.cast_sub hkn]; push_cast; ring_nf
      have hcast2 : (H 1 ^ (n + 2 - k) : ℝ) = H 1 ^ ((n:ℝ) + 1 - k + 1) := by
        rw [← Real.rpow_natCast, Nat.cast_sub (by omega)]; push_cast; ring_nf
      have hsq : (C * H 1 ^ (-y)) ^ 2 = C ^ 2 * H 1 ^ (-2 * y) := by
        rw [mul_pow, ← Real.rpow_natCast (H 1 ^ (-y)), ← Real.rpow_mul hH1.le]; push_cast; ring_nf
      rw [hsq, hcast2]
      calc C ^ 2 * H 1 ^ (-2 * y) * H 0 ^ (n + 1 - k) * H 1 ^ ((n:ℝ) + 1 - k + 1) * H 1 ^ S
          ≤ C ^ 2 * H 1 ^ (-2 * y) * H 1 ^ ((n:ℝ) + 1 - k) * H 1 ^ ((n:ℝ) + 1 - k + 1) * H 1 ^ S := by
            rw [← hcast1]; gcongr
        _ = C ^ 2 * H 1 ^ (-(2 * y - 2 * ((n : ℝ) + 1 - k) - (1 + S))) := by
            rw [show ∀ a b c d e : ℝ, a * b * c * d * e = a * (b * c * d * e) from
              fun _ _ _ _ _ => by ring]
            congr 1
            rw [← Real.rpow_add hH1, ← Real.rpow_add hH1, ← Real.rpow_add hH1]
            congr 1; ring
    )
  have L_approx_final_bound : ∀ (Cr H Nm H2 A ak ω : ℝ) (hCr : 0 < Cr) (hH : 1 ≤ H) (hNm : 1 ≤ Nm)
      (hH2 : 1 ≤ H2) (hHle : H ≤ Cr * Nm) (hNmle : Nm ≤ H2 ^ ak) (hak : 1 ≤ ak) (hω : 0 ≤ ω)
      (hA : ω * ak ≤ A), H2 ^ (-A) / Nm ≤ Cr ^ (ω + 1) * H ^ (-ω - 1) :=
    (fun (Cr H Nm H2 A ak ω : ℝ) (hCr : 0 < Cr) (hH : 1 ≤ H) (hNm : 1 ≤ Nm)
        (hH2 : 1 ≤ H2) (hHle : H ≤ Cr * Nm) (hNmle : Nm ≤ H2 ^ ak) (hak : 1 ≤ ak) (hω : 0 ≤ ω)
        (hA : ω * ak ≤ A) => by
      have hH2pos : 0 < H2 := by linarith
      have hNmpos : 0 < Nm := by linarith
      have hHpos : 0 < H := by linarith
      have ht : 0 < ω + 1 := by linarith
      have e1 : Nm ^ ω ≤ H2 ^ (ak * ω) := by
        rw [Real.rpow_mul hH2pos.le]
        exact Real.rpow_le_rpow hNmpos.le hNmle hω
      have e2 : H2 ^ (-A) * H2 ^ (ak * ω) ≤ 1 := by
        rw [← Real.rpow_add hH2pos]
        exact Real.rpow_le_one_of_one_le_of_nonpos hH2 (by nlinarith)
      have e3 : H2 ^ (-A) * Nm ^ ω ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left e1 (Real.rpow_nonneg hH2pos.le _)) e2
      have e4 : H ^ (ω + 1) ≤ Cr ^ (ω + 1) * Nm ^ (ω + 1) := by
        rw [← Real.mul_rpow hCr.le hNmpos.le]
        exact Real.rpow_le_rpow (by linarith) hHle ht.le
      have e5 : Nm ^ (ω + 1) = Nm ^ ω * Nm := by
        rw [Real.rpow_add hNmpos, Real.rpow_one]
      have hHt : 0 < H ^ (ω + 1) := Real.rpow_pos_of_pos hHpos _
      have hCrt : 0 < Cr ^ (ω + 1) := Real.rpow_pos_of_pos hCr _
      have hA0 : 0 ≤ H2 ^ (-A) := Real.rpow_nonneg hH2pos.le _
      have key : H2 ^ (-A) * H ^ (ω + 1) ≤ Cr ^ (ω + 1) * Nm := by
        calc H2 ^ (-A) * H ^ (ω + 1) ≤ H2 ^ (-A) * (Cr ^ (ω + 1) * (Nm ^ ω * Nm)) := by
              rw [← e5]; exact mul_le_mul_of_nonneg_left e4 hA0
          _ = Cr ^ (ω + 1) * Nm * (H2 ^ (-A) * Nm ^ ω) := by ring
          _ ≤ Cr ^ (ω + 1) * Nm * 1 := by
              exact mul_le_mul_of_nonneg_left e3 (by positivity)
          _ = Cr ^ (ω + 1) * Nm := by ring
      rw [show -ω - 1 = -(ω + 1) by ring, Real.rpow_neg hHpos.le]
      rw [div_le_iff₀ hNmpos]
      have : Cr ^ (ω + 1) * (H ^ (ω + 1))⁻¹ * Nm = (Cr ^ (ω + 1) * Nm) / H ^ (ω + 1) := by
        field_simp
      rw [this, le_div_iff₀ hHt]
      exact key
    )
  have L_approx_eta : ∀ (H1 Nm A Cr C η : ℝ) (hCr : 0 < Cr) (hC : 0 < C) (hη : 0 < η)
      (hNm : 1 ≤ Nm) (hA : 1 / 2 ≤ A) (hBt : (Cr * C ^ 2 / η) ^ 2 + 2 ≤ H1), Cr * C ^ 2 * (H1 ^ (-A) / Nm) < η :=
    (fun (H1 Nm A Cr C η : ℝ) (hCr : 0 < Cr) (hC : 0 < C) (hη : 0 < η)
        (hNm : 1 ≤ Nm) (hA : 1 / 2 ≤ A) (hBt : (Cr * C ^ 2 / η) ^ 2 + 2 ≤ H1) => by
      have hK : 0 < Cr * C ^ 2 := by positivity
      have hH1 : 0 < H1 := by nlinarith [sq_nonneg (Cr * C ^ 2 / η)]
      have hH1' : 1 ≤ H1 := by nlinarith [sq_nonneg (Cr * C ^ 2 / η)]
      have hNmpos : 0 < Nm := by linarith
      have e1 : H1 ^ (-A) / Nm ≤ H1 ^ (-(1/2 : ℝ)) := by
        rw [div_le_iff₀ hNmpos]
        calc H1 ^ (-A) ≤ H1 ^ (-(1/2 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hH1' (by linarith)
          _ ≤ H1 ^ (-(1/2 : ℝ)) * Nm := le_mul_of_one_le_right (Real.rpow_nonneg hH1.le _) hNm
      have e2 : (H1 ^ (-(1/2 : ℝ))) ^ 2 * H1 = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hH1.le]
        norm_num [Real.rpow_neg_one]
        field_simp
      set s := H1 ^ (-(1/2 : ℝ)) with hs
      have hs0 : 0 ≤ s := Real.rpow_nonneg hH1.le _
      set t := Cr * C ^ 2 / η with ht
      have htη : Cr * C ^ 2 = t * η := by rw [ht]; field_simp
      have e3 : t * s < 1 := by
        by_contra hcon
        push_neg at hcon
        have : 1 ≤ (t * s) ^ 2 := by nlinarith
        have : (t * s) ^ 2 * H1 = t ^ 2 := by rw [mul_pow, mul_assoc, e2, mul_one]
        nlinarith [sq_nonneg t]
      calc Cr * C ^ 2 * (H1 ^ (-A) / Nm) ≤ Cr * C ^ 2 * s := by gcongr
        _ = η * (t * s) := by rw [htη]; ring
        _ < η * 1 := by gcongr
        _ = η := mul_one η
    )
  have L_approx_ne : ∀ (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (α : AlgebraicDegLE n), 0 < ‖(ξ : ℂ) - α.1‖ :=
    (fun (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (α : AlgebraicDegLE n) => by
      rw [norm_pos_iff, sub_ne_zero]
      intro heq
      apply hξ
      obtain ⟨p, hp0, hpα⟩ := α.2.1
      refine ⟨p, hp0, ?_⟩
      rw [← heq] at hpα
      have h2 : (Polynomial.aeval (ξ:ℂ) p) = ((Polynomial.aeval ξ p : ℝ) : ℂ) := by
        rw [show (ξ:ℂ) = algebraMap ℝ ℂ ξ from rfl, Polynomial.aeval_algebraMap_apply]; rfl
      rw [h2] at hpα
      exact_mod_cast hpα
    )
  have L_approx : ∀ (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hconfig : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, ∃ Q : ℕ → Polynomial ℤ,
        (∀ i, (Q i).natDegree ≤ n) ∧
        LinearIndependent ℚ (fun i : Fin (n + 1) => (Q i).map (Int.castRingHom ℚ)) ∧
        IsCoprime ((Q 0).map (Int.castRingHom ℚ)) ((Q 1).map (Int.castRingHom ℚ)) ∧
        B ≤ N (Q 1) ∧
        (∀ i j, i ≤ j → j ≤ n → N (Q i) ≤ N (Q j)) ∧
        (∀ i, i ≤ n → |Polynomial.aeval ξ (Q i)| ≤
          C * max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ))))))
      (hres : ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (P : ℕ → Polynomial ℤ) (δ : ℝ), 2 ≤ k → k ≤ n + 1 →
        (∀ i, (P i).natDegree ≤ n) →
        LinearIndependent ℚ (fun i : Fin k => (P i).map (Int.castRingHom ℚ)) →
        IsCoprime ((P 0).map (Int.castRingHom ℚ)) ((P 1).map (Int.castRingHom ℚ)) →
        (∀ i j, i ≤ j → j < k → N (P i) ≤ N (P j)) →
        (∀ i, i < k → |Polynomial.aeval ξ (P i)| ≤ δ) →
        ∃ α : AlgebraicDegLE n, ∃ m, m < k ∧ (height α.1 : ℝ) ≤ C * N (P m) ∧
          ‖(ξ : ℂ) - α.1‖ ≤ C * δ ^ 2 * N (P 0) ^ (n + 1 - k) * N (P 1) ^ (n + 2 - k) *
            (∏ i ∈ Finset.Ico 2 k, N (P i)) / N (P m))
      (hopt : ∀ (x : ℝ), (n : ℝ) ≤ x → ∀ (a : ℕ → ℝ), a 2 = 1 →
        (∀ i, 2 ≤ i → i ≤ n → a i ≤ a (i + 1)) →
        ∑ i ∈ Finset.Icc 2 (n + 1), a i = x →
        ∃ k ∈ Finset.Icc 2 (n + 1),
          1 / (2 - Real.log 2) * n ≤ (2 * x - 2 * ((n : ℝ) + 1 - k) - ∑ i ∈ Finset.Icc 2 k, a i) / a k)
      (ω : ℝ) (hω : ω < 1 / (2 - Real.log 2) * n), ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ α : AlgebraicDegLE n,
        ‖(ξ : ℂ) - α.1‖ < η ∧ ‖(ξ : ℂ) - α.1‖ ≤ K * (height α.1 : ℝ) ^ (-ω - 1) :=
    (fun (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hconfig : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, ∃ Q : ℕ → Polynomial ℤ,
          (∀ i, (Q i).natDegree ≤ n) ∧
          LinearIndependent ℚ (fun i : Fin (n + 1) => (Q i).map (Int.castRingHom ℚ)) ∧
          IsCoprime ((Q 0).map (Int.castRingHom ℚ)) ((Q 1).map (Int.castRingHom ℚ)) ∧
          B ≤ N (Q 1) ∧
          (∀ i j, i ≤ j → j ≤ n → N (Q i) ≤ N (Q j)) ∧
          (∀ i, i ≤ n → |Polynomial.aeval ξ (Q i)| ≤
            C * max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ))))))
        (hres : ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (P : ℕ → Polynomial ℤ) (δ : ℝ), 2 ≤ k → k ≤ n + 1 →
          (∀ i, (P i).natDegree ≤ n) →
          LinearIndependent ℚ (fun i : Fin k => (P i).map (Int.castRingHom ℚ)) →
          IsCoprime ((P 0).map (Int.castRingHom ℚ)) ((P 1).map (Int.castRingHom ℚ)) →
          (∀ i j, i ≤ j → j < k → N (P i) ≤ N (P j)) →
          (∀ i, i < k → |Polynomial.aeval ξ (P i)| ≤ δ) →
          ∃ α : AlgebraicDegLE n, ∃ m, m < k ∧ (height α.1 : ℝ) ≤ C * N (P m) ∧
            ‖(ξ : ℂ) - α.1‖ ≤ C * δ ^ 2 * N (P 0) ^ (n + 1 - k) * N (P 1) ^ (n + 2 - k) *
              (∏ i ∈ Finset.Ico 2 k, N (P i)) / N (P m))
        (hopt : ∀ (x : ℝ), (n : ℝ) ≤ x → ∀ (a : ℕ → ℝ), a 2 = 1 →
          (∀ i, 2 ≤ i → i ≤ n → a i ≤ a (i + 1)) →
          ∑ i ∈ Finset.Icc 2 (n + 1), a i = x →
          ∃ k ∈ Finset.Icc 2 (n + 1),
            1 / (2 - Real.log 2) * n ≤ (2 * x - 2 * ((n : ℝ) + 1 - k) - ∑ i ∈ Finset.Icc 2 k, a i) / a k)
        (ω : ℝ) (hω : ω < 1 / (2 - Real.log 2) * n) => by
      have hlog2 : Real.log 2 < 1 := by
        have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num); linarith
      have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (2 - Real.log 2) * n := ⟨_, rfl⟩
      rw [← hc] at hω
      have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
      have hcpos : 0 < c := by
        rw [hc]; apply _root_.mul_pos (div_pos one_pos (by linarith)) (by linarith)
      have hcn : c ≤ n := by
        rw [hc, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
        have := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 2 - Real.log 2 by linarith) (by linarith : (0:ℝ) ≤ n)
        linarith
      obtain ⟨ω', hω'⟩ : ∃ ω' : ℝ, ω' = max ω 0 := ⟨_, rfl⟩
      have hω'0 : 0 ≤ ω' := by rw [hω']; exact le_max_right _ _
      have hωω' : ω ≤ ω' := by rw [hω']; exact le_max_left _ _
      have hω'c : ω' < c := by rw [hω']; exact max_lt hω hcpos
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (1/4) ((c - ω') / 4) := ⟨_, rfl⟩
      have hε0 : 0 < ε := by rw [hε]; apply lt_min (by norm_num); linarith
      have hε14 : ε ≤ 1/4 := by rw [hε]; exact min_le_left _ _
      have hεc : ε ≤ (c - ω') / 4 := by rw [hε]; exact min_le_right _ _
      obtain ⟨C, hC, hQ⟩ := hconfig ε hε0 (by linarith)
      obtain ⟨Cr, hCr, hR⟩ := hres
      refine ⟨Cr * C ^ 2 * Cr ^ (ω' + 1), by positivity, ?_⟩
      intro η hη
      obtain ⟨Q, hdeg, hli, hcop, hB, hmono, hval⟩ := hQ (max 2 ((Cr * C ^ 2 / η) ^ 2 + 2))
      obtain ⟨H, hH⟩ : ∃ H : ℕ → ℝ, H = fun i => N (Q i) := ⟨_, rfl⟩
      have hHi : ∀ i, N (Q i) = H i := by intro i; rw [hH]
      simp only [hHi] at hB hmono hval
      have hB2 : 2 ≤ H 1 := le_trans (le_max_left _ _) hB
      have hBt : (Cr * C ^ 2 / η) ^ 2 + 2 ≤ H 1 := le_trans (le_max_right _ _) hB
      have h1 : 1 < H 1 := by linarith
      have hH1pos : 0 < H 1 := by linarith
      have hnat : ∀ i, ∃ t : ℕ, H i = t := fun i => ⟨_, by rw [← hHi, hN]⟩
      have h0 : 0 ≤ H 0 := by obtain ⟨t, ht⟩ := hnat 0; rw [ht]; positivity
      obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun i => Real.log (H (i - 1)) / Real.log (H 1) := ⟨_, rfl⟩
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.log (∏ j ∈ Finset.Icc 1 n, H j) / Real.log (H 1) := ⟨_, rfl⟩
      obtain ⟨ha2, hamono, hsum, hxn, hHx, hHa⟩ := L_approx_family n H h1 hmono a ha x hx
      have hPpos : 0 < ∏ j ∈ Finset.Icc 1 n, H j := by rw [← hHx]; exact Real.rpow_pos_of_pos hH1pos _
      obtain ⟨y, hy⟩ : ∃ y : ℝ, y = min (x - ε) (2 * n) := ⟨_, rfl⟩
      have hδ : ∀ i, i ≤ n → |Polynomial.aeval ξ (Q i)| ≤ C * H 1 ^ (-y) := by
        intro i hi
        have := hval i hi
        rwa [L_approx_max_eq (H 1) x ε _ n h1.le hHx hPpos, ← hy] at this
      -- choose k
      obtain ⟨k, hk2, hkn, hAω, hA12⟩ : ∃ k : ℕ, 2 ≤ k ∧ k ≤ n + 1 ∧
          ω' * a k ≤ 2 * y - 2 * ((n : ℝ) + 1 - k) - ∑ i ∈ Finset.Icc 2 k, a i ∧
          1 / 2 ≤ 2 * y - 2 * ((n : ℝ) + 1 - k) - ∑ i ∈ Finset.Icc 2 k, a i := by
        rcases le_or_gt (x - ε) (2 * n) with hxe | hxe
        · have hyx : y = x - ε := by rw [hy, min_eq_left hxe]
          obtain ⟨k, hk, hck⟩ := hopt x hxn a ha2 hamono hsum
          rw [← hc] at hck
          obtain ⟨hk2, hkn⟩ := Finset.mem_Icc.mp hk
          have hak := L_approx_a_ge_one n a ha2 hamono k hk2 hkn
          have hAx := L_approx_Ak_ge_one n x hxn a ha2 hamono hsum k hk
          rw [le_div_iff₀ (by linarith)] at hck
          refine ⟨k, hk2, hkn, ?_, ?_⟩
          · rw [hyx]
            have h3 : ω' ≤ c - 2 * ε := by linarith
            have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : (0:ℝ) ≤ a k)
            have h5 := mul_le_mul_of_nonneg_left hak hε0.le
            linarith
          · rw [hyx]; linarith
        · have hyn : y = 2 * n := by rw [hy, min_eq_right hxe.le]
          refine ⟨2, le_refl _, by omega, ?_, ?_⟩
          · rw [hyn, ha2, Finset.Icc_self, Finset.sum_singleton, ha2]; push_cast; linarith
          · rw [hyn, Finset.Icc_self, Finset.sum_singleton, ha2]; push_cast; linarith
      set A := 2 * y - 2 * ((n : ℝ) + 1 - k) - ∑ i ∈ Finset.Icc 2 k, a i with hA
      have hhk : k - 1 ≤ n := by omega
      obtain ⟨α, m, hm, hhα, hdist⟩ := hR k Q (C * H 1 ^ (-y)) hk2 hkn hdeg
        (hli.comp (Fin.castLE hkn) (Fin.castLE_injective hkn)) hcop
        (fun i j hij hj => by simp only [hHi]; exact hmono i j hij (by omega))
        (fun i hi => hδ i (by omega))
      simp only [hHi] at hhα hdist
      have hpb := L_approx_prod_bound n k hk2 hkn H C y hC h1 h0 (hmono 0 1 (by omega) (by omega)) hmono
      rw [show (∑ i ∈ Finset.Icc 2 k, Real.log (H (i - 1)) / Real.log (H 1)) =
        ∑ i ∈ Finset.Icc 2 k, a i by rw [ha], ← hA] at hpb
      have hpos := L_approx_ne n ξ hξ α
      -- Nm ≥ 1
      have hNm : 1 ≤ H m := by
        obtain ⟨t, ht⟩ := hnat m
        rcases Nat.eq_zero_or_pos t with h | h
        · rw [ht, h, Nat.cast_zero, _root_.div_zero] at hdist; linarith
        · rw [ht]; exact_mod_cast h
      have hNmpos : 0 < H m := by linarith
      have hNmle : H m ≤ H 1 ^ a k := by
        rw [hHa k hk2 hkn]; exact hmono m (k - 1) (by omega) hhk
      have hα1 := L_approx_height_ge_one α.1 α.2.1
      have hak := L_approx_a_ge_one n a ha2 hamono k hk2 hkn
      have hd2 : ‖(ξ : ℂ) - α.1‖ ≤ Cr * C ^ 2 * (H 1 ^ (-A) / H m) := by
        refine le_trans hdist ?_
        rw [show Cr * (C * H 1 ^ (-y)) ^ 2 * H 0 ^ (n + 1 - k) * H 1 ^ (n + 2 - k) *
            (∏ i ∈ Finset.Ico 2 k, H i) / H m = Cr * ((C * H 1 ^ (-y)) ^ 2 * H 0 ^ (n + 1 - k) *
            H 1 ^ (n + 2 - k) * (∏ i ∈ Finset.Ico 2 k, H i)) / H m by ring,
          show Cr * C ^ 2 * (H 1 ^ (-A) / H m) = Cr * (C ^ 2 * H 1 ^ (-A)) / H m by ring]
        gcongr
      have hfb := L_approx_final_bound Cr (height α.1) (H m) (H 1) A (a k) ω' hCr hα1 hNm h1.le hhα
        hNmle hak hω'0 hAω
      refine ⟨α, ?_, ?_⟩
      · refine lt_of_le_of_lt hd2 ?_
        exact L_approx_eta (H 1) (H m) A Cr C η hCr hC hη hNm hA12 hBt
      · refine le_trans hd2 ?_
        calc Cr * C ^ 2 * (H 1 ^ (-A) / H m) ≤ Cr * C ^ 2 * (Cr ^ (ω' + 1) * (height α.1 : ℝ) ^ (-ω' - 1)) :=
              mul_le_mul_of_nonneg_left hfb (by positivity)
          _ = Cr * C ^ 2 * Cr ^ (ω' + 1) * (height α.1 : ℝ) ^ (-ω' - 1) := by ring
          _ ≤ Cr * C ^ 2 * Cr ^ (ω' + 1) * (height α.1 : ℝ) ^ (-ω - 1) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hα1 (by linarith))
                (by positivity)
    )
  have L_config_N_ge_one : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (p : Polynomial ℤ) (hp : p ≠ 0), 1 ≤ N p :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (p : Polynomial ℤ) (hp : p ≠ 0) => by
      rw [hN]
      have hmem : p.natDegree ∈ p.support := Polynomial.natDegree_mem_support_of_nonzero hp
      have hle : (p.coeff p.natDegree).natAbs ≤ p.support.sup fun i => (p.coeff i).natAbs :=
        Finset.le_sup (f := fun i => (p.coeff i).natAbs) hmem
      have hpos : 0 < (p.coeff p.natDegree).natAbs := by
        rw [Int.natAbs_pos]; exact Polynomial.leadingCoeff_ne_zero.mpr hp
      exact_mod_cast (show 1 ≤ _ from le_trans hpos hle)
    )
  have L_config_N_add : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (p q : Polynomial ℤ), N (p + q) ≤ N p + N q :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (p q : Polynomial ℤ) => by
      rw [hN, hN, hN]
      have key : ∀ r : Polynomial ℤ, ∀ i, (r.coeff i).natAbs ≤ r.support.sup fun i => (r.coeff i).natAbs := by
        intro r i
        by_cases h : r.coeff i = 0
        · simp [h]
        · exact Finset.le_sup (f := fun i => (r.coeff i).natAbs) (Polynomial.mem_support_iff.mpr h)
      have : ((p+q).support.sup fun i => ((p+q).coeff i).natAbs) ≤
          (p.support.sup fun i => (p.coeff i).natAbs) + (q.support.sup fun i => (q.coeff i).natAbs) := by
        apply Finset.sup_le
        intro i _
        rw [Polynomial.coeff_add]
        exact le_trans (Int.natAbs_add_le _ _) (add_le_add (key p i) (key q i))
      exact_mod_cast this
    )
  have L_config_N_smul : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (k : ℤ) (p : Polynomial ℤ), N (Polynomial.C k * p) = |(k : ℝ)| * N p :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (k : ℤ) (p : Polynomial ℤ) => by
      rw [hN, hN]
      have key : ∀ r : Polynomial ℤ, ∀ i, (r.coeff i).natAbs ≤ r.support.sup fun i => (r.coeff i).natAbs := by
        intro r i
        by_cases h : r.coeff i = 0
        · simp [h]
        · exact Finset.le_sup (f := fun i => (r.coeff i).natAbs) (Polynomial.mem_support_iff.mpr h)
      have hle : ((Polynomial.C k * p).support.sup fun i => ((Polynomial.C k * p).coeff i).natAbs)
          ≤ k.natAbs * (p.support.sup fun i => (p.coeff i).natAbs) := by
        apply Finset.sup_le
        intro i _
        rw [Polynomial.coeff_C_mul, Int.natAbs_mul]
        exact Nat.mul_le_mul_left _ (key p i)
      have hge : k.natAbs * (p.support.sup fun i => (p.coeff i).natAbs) ≤
          ((Polynomial.C k * p).support.sup fun i => ((Polynomial.C k * p).coeff i).natAbs) := by
        rcases Nat.eq_zero_or_pos (p.support.sup fun i => (p.coeff i).natAbs) with h0 | hpos
        · rw [h0]; simp
        · obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup p.support
            (by by_contra hc; rw [Finset.not_nonempty_iff_eq_empty] at hc; simp [hc] at hpos)
            (fun i => (p.coeff i).natAbs)
          rw [hmax]
          have := key (Polynomial.C k * p) i
          rw [Polynomial.coeff_C_mul, Int.natAbs_mul] at this
          exact this
      have heq := le_antisymm hle hge
      rw [heq]
      push_cast
      rw [Nat.cast_natAbs]
      simp
    )
  have L_config_aeval_ne_zero : ∀ (ξ : ℝ) (hξ : Transcendental ℚ ξ)
      (p : Polynomial ℤ) (hp : p ≠ 0), Polynomial.aeval ξ p ≠ 0 :=
    (fun (ξ : ℝ) (hξ : Transcendental ℚ ξ)
        (p : Polynomial ℤ) (hp : p ≠ 0) => by
      intro h
      apply hξ
      refine ⟨p.map (Int.castRingHom ℚ), ?_, ?_⟩
      · exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hp
      · rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]; exact h
    )
  have L_config_minpoint : ∀ (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (H : ℝ) (hH : 1 ≤ H), ∃ Q : Polynomial ℤ, Q ≠ 0 ∧ Q.natDegree ≤ n ∧ N Q ≤ H ∧
        ∀ R : Polynomial ℤ, R ≠ 0 → R.natDegree ≤ n → N R ≤ H →
          |Polynomial.aeval ξ Q| ≤ |Polynomial.aeval ξ R| :=
    (fun (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (H : ℝ) (hH : 1 ≤ H) => by
      classical
      set K : ℕ := ⌊H⌋₊
      let enc : (Fin (n + 1) → Finset.Icc (-(K : ℤ)) K) → Polynomial ℤ :=
        fun c => ∑ i : Fin (n + 1), Polynomial.C ((c i : ℤ)) * Polynomial.X ^ (i : ℕ)
      let S : Finset (Polynomial ℤ) := (Finset.univ.image enc).filter
        (fun R => R ≠ 0 ∧ R.natDegree ≤ n ∧ N R ≤ H)
      have key : ∀ r : Polynomial ℤ, ∀ i, (r.coeff i).natAbs ≤ r.support.sup fun i => (r.coeff i).natAbs := by
        intro r i
        by_cases h : r.coeff i = 0
        · simp [h]
        · exact Finset.le_sup (f := fun i => (r.coeff i).natAbs) (Polynomial.mem_support_iff.mpr h)
      have hmem : ∀ R : Polynomial ℤ, R ≠ 0 → R.natDegree ≤ n → N R ≤ H → R ∈ S := by
        intro R hR hd hH'
        simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨?_, hR, hd, hH'⟩
        have hcK : ∀ i, (R.coeff i).natAbs ≤ K := by
          intro i
          apply Nat.le_floor
          rw [hN] at hH'
          exact le_trans (by exact_mod_cast key R i) hH'
        refine ⟨fun i => ⟨R.coeff i, ?_⟩, ?_⟩
        · rw [Finset.mem_Icc]
          have := hcK i
          constructor <;> omega
        · simp only [enc]
          have h := Polynomial.as_sum_range' R (n + 1) (by omega)
          rw [← Fin.sum_univ_eq_sum_range] at h
          conv_rhs => rw [h]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact Polynomial.C_mul_X_pow_eq_monomial
      have hN1 : N 1 ≤ H := by
        rw [hN]
        have : ((1 : Polynomial ℤ).support.sup fun i => ((1 : Polynomial ℤ).coeff i).natAbs) ≤ 1 :=
          Finset.sup_le (fun i _ => by rw [Polynomial.coeff_one]; split_ifs <;> simp)
        exact le_trans (by exact_mod_cast this) hH
      have hne : S.Nonempty := ⟨1, hmem 1 one_ne_zero (by simp) hN1⟩
      obtain ⟨Q, hQS, hQmin⟩ := Finset.exists_min_image S (fun R => |Polynomial.aeval ξ R|) hne
      simp only [S, Finset.mem_filter] at hQS
      exact ⟨Q, hQS.2.1, hQS.2.2.1, hQS.2.2.2, fun R hR hd hH' => hQmin R (hmem R hR hd hH')⟩
    )
  have L_config_dirichlet : ∀ (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hmii : ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∃ P : Fin (n + 1) → Polynomial ℤ,
        (∀ i, (P i).natDegree ≤ n) ∧
        LinearIndependent ℚ (fun i => (P i).map (Int.castRingHom ℚ)) ∧
        ∏ i, max (N (P i)) (Real.exp q * |Polynomial.aeval ξ (P i)|) ≤ C * Real.exp q), ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∃ R : Polynomial ℤ, R ≠ 0 ∧ R.natDegree ≤ n ∧
        N R ≤ H ∧ |Polynomial.aeval ξ R| ≤ C * H ^ (-(n : ℝ)) :=
    (fun (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hmii : ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∃ P : Fin (n + 1) → Polynomial ℤ,
          (∀ i, (P i).natDegree ≤ n) ∧
          LinearIndependent ℚ (fun i => (P i).map (Int.castRingHom ℚ)) ∧
          ∏ i, max (N (P i)) (Real.exp q * |Polynomial.aeval ξ (P i)|) ≤ C * Real.exp q) => by
      obtain ⟨CM, hCM, hmii⟩ := hmii
      refine ⟨max CM 1, by positivity, fun H hH => ?_⟩
      have hH0 : 0 < H := by linarith
      have hrp : H ^ (-(n : ℝ)) = (H ^ n)⁻¹ := by rw [Real.rpow_neg hH0.le, Real.rpow_natCast]
      rw [hrp]
      have hHn : 0 < H ^ n := pow_pos hH0 n
      by_cases hsmall : H ^ (n + 1) ≤ CM
      · refine ⟨1, one_ne_zero, by simp, ?_, ?_⟩
        · rw [hN]
          have : ((1 : Polynomial ℤ).support.sup fun i => ((1 : Polynomial ℤ).coeff i).natAbs) ≤ 1 :=
            Finset.sup_le (fun i _ => by rw [Polynomial.coeff_one]; split_ifs <;> simp)
          exact le_trans (by exact_mod_cast this) hH
        · simp only [map_one, abs_one]
          rw [le_mul_inv_iff₀ hHn, one_mul]
          have : H ^ n ≤ H ^ (n + 1) := pow_le_pow_right₀ hH (by omega)
          linarith [le_max_left CM 1]
      · push_neg at hsmall
        set q := Real.log (H ^ (n + 1) / CM) with hqdef
        have hq : 0 ≤ q := Real.log_nonneg (by rw [le_div_iff₀ hCM]; linarith)
        have heq : Real.exp q = H ^ (n + 1) / CM := Real.exp_log (by positivity)
        obtain ⟨P, hdeg, hli, hprod⟩ := hmii q hq
        rw [heq, mul_div_cancel₀ _ hCM.ne'] at hprod
        by_contra hcon
        push_neg at hcon
        have hgt : ∀ i, H < max (N (P i)) (Real.exp q * |Polynomial.aeval ξ (P i)|) := by
          intro i
          have hPi : P i ≠ 0 := by
            intro h0; apply hli.ne_zero i; simp [h0]
          by_contra hle
          push_neg at hle
          have h1 : N (P i) ≤ H := le_trans (le_max_left _ _) hle
          have h2 : Real.exp q * |Polynomial.aeval ξ (P i)| ≤ H := le_trans (le_max_right _ _) hle
          rw [heq] at h2
          have e1 : |Polynomial.aeval ξ (P i)|
              = (CM / H ^ (n + 1)) * ((H ^ (n + 1) / CM) * |Polynomial.aeval ξ (P i)|) := by
            field_simp
          have e2 : (CM / H ^ (n + 1)) * H = CM * (H ^ n)⁻¹ := by
            rw [pow_succ]; field_simp
          have h3 : |Polynomial.aeval ξ (P i)| ≤ CM * (H ^ n)⁻¹ := by
            calc |Polynomial.aeval ξ (P i)| = _ := e1
              _ ≤ (CM / H ^ (n + 1)) * H := mul_le_mul_of_nonneg_left h2 (by positivity)
              _ = _ := e2
          have h4 := le_trans h3 (mul_le_mul_of_nonneg_right (le_max_left CM 1) (inv_nonneg.mpr hHn.le))
          exact absurd h4 (not_le.mpr (hcon (P i) hPi (hdeg i) h1))
        have hlt := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := fun _ => H)
          (fun i _ => hH0) (fun i _ => hgt i) Finset.univ_nonempty
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hlt
        rw [heq] at hlt
        linarith
    )
  have L_config_coprime : ∀ (p q : Polynomial ℚ) (hp : Irreducible p) (hpq : ¬ p ∣ q), IsCoprime p q :=
    (fun (p q : Polynomial ℚ) (hp : Irreducible p) (hpq : ¬ p ∣ q) => by
      classical
      have hp0 : p ≠ 0 := hp.ne_zero
      have hex : ∃ d : ℕ, ∃ a b : Polynomial ℚ, a * p + b * q ≠ 0 ∧ (a * p + b * q).natDegree = d :=
        ⟨_, 1, 0, by simpa using hp0, rfl⟩
      obtain ⟨a, b, hg0, hgd⟩ := Nat.find_spec hex
      set g := a * p + b * q with hg
      have hmin : ∀ a' b' : Polynomial ℚ, a' * p + b' * q ≠ 0 →
          Nat.find hex ≤ (a' * p + b' * q).natDegree :=
        fun a' b' h => Nat.find_min' hex ⟨a', b', h, rfl⟩
      have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
      set g' := g * Polynomial.C g.leadingCoeff⁻¹ with hg'
      have hmon : g'.Monic := Polynomial.monic_mul_leadingCoeff_inv hg0
      have hdvd : ∀ a' b' : Polynomial ℚ, g' ∣ a' * p + b' * q := by
        intro a' b'
        set r := a' * p + b' * q
        have hdiv := Polynomial.modByMonic_add_div r hmon
        have hrem : r %ₘ g' = (a' - (r /ₘ g') * Polynomial.C g.leadingCoeff⁻¹ * a) * p
            + (b' - (r /ₘ g') * Polynomial.C g.leadingCoeff⁻¹ * b) * q := by
          have : r %ₘ g' = r - g' * (r /ₘ g') := by rw [eq_sub_iff_add_eq]; exact hdiv
          rw [this, hg', hg]; ring
        by_contra hnd
        have hne : r %ₘ g' ≠ 0 := by
          intro h0
          apply hnd
          exact (Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp h0
        have hlt := Polynomial.degree_modByMonic_lt r hmon
        have h1 := hmin _ _ (hrem ▸ hne)
        rw [← hrem] at h1
        have hdeg' : g'.natDegree = g.natDegree := by
          rw [hg', Polynomial.natDegree_mul_C (inv_ne_zero hlc)]
        have := Polynomial.natDegree_lt_natDegree hne hlt
        omega
      have hgp : g' ∣ p := by simpa using hdvd 1 0
      have hgq : g' ∣ q := by simpa using hdvd 0 1
      obtain ⟨c, hc⟩ := hgp
      rcases hp.isUnit_or_isUnit hc with hu | hu
      · obtain ⟨u, hu'⟩ := hu
        refine ⟨Polynomial.C g.leadingCoeff⁻¹ * ↑u⁻¹ * a, Polynomial.C g.leadingCoeff⁻¹ * ↑u⁻¹ * b, ?_⟩
        have : g * Polynomial.C g.leadingCoeff⁻¹ = ↑u := by rw [← hg', hu']
        calc Polynomial.C g.leadingCoeff⁻¹ * ↑u⁻¹ * a * p + Polynomial.C g.leadingCoeff⁻¹ * ↑u⁻¹ * b * q
            = (g * Polynomial.C g.leadingCoeff⁻¹) * ↑u⁻¹ := by rw [hg]; ring
          _ = 1 := by rw [this, Units.mul_inv]
      · exfalso
        apply hpq
        obtain ⟨v, hv⟩ := hu
        refine dvd_trans ⟨↑v⁻¹, ?_⟩ hgq
        rw [hc, ← hv, mul_assoc, Units.mul_inv, mul_one]
    )
  have L_config_exchange : ∀ (n : ℕ)
      (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (v : Fin (n + 1) → Polynomial ℚ) (hv : LinearIndependent ℚ v)
      (hdeg : ∀ i, (v i).natDegree ≤ n)
      (w : Polynomial ℚ) (hw : w ≠ 0) (hwdeg : w.natDegree ≤ n), ∃ j, LinearIndependent ℚ (Function.update v j w) :=
    (fun (n : ℕ)
        (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (v : Fin (n + 1) → Polynomial ℚ) (hv : LinearIndependent ℚ v)
        (hdeg : ∀ i, (v i).natDegree ≤ n)
        (w : Polynomial ℚ) (hw : w ≠ 0) (hwdeg : w.natDegree ≤ n) => by
      have hdep := hdim (n + 1) (Fin.cons w v) (by
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp only [Fin.cons_zero]; omega
        · simp only [Fin.cons_succ]; have := hdeg i; omega)
      rw [Fintype.not_linearIndependent_iff] at hdep
      obtain ⟨g, hg, i₁, hi₁⟩ := hdep
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      rw [Fintype.linearIndependent_iff] at hv
      have hg0 : g 0 ≠ 0 := by
        intro h0
        rw [h0, zero_smul, zero_add] at hg
        have := hv _ hg
        revert hi₁
        refine Fin.cases ?_ (fun i => ?_) i₁
        · exact fun h => h h0
        · exact fun h => h (this i)
      have hw' : w = ∑ i, (-(g 0)⁻¹ * g i.succ) • v i := by
        have h0 : g 0 • w = -∑ i, g i.succ • v i := eq_neg_of_add_eq_zero_left hg
        calc w = (g 0)⁻¹ • (g 0 • w) := by rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
          _ = _ := by
            rw [h0, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [smul_smul, ← neg_smul, neg_mul]
      have hj : ∃ j : Fin (n + 1), g j.succ ≠ 0 := by
        by_contra hc
        push_neg at hc
        apply hw
        rw [hw']
        simp [hc]
      obtain ⟨j, hj⟩ := hj
      refine ⟨j, ?_⟩
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hs : ∑ i, c i • Function.update v j w i
          = ∑ i, (c i - (if i = j then c j else 0) + c j * (-(g 0)⁻¹ * g i.succ)) • v i := by
        have e1 : ∀ i, c i • Function.update v j w i
            = (c i - (if i = j then c j else 0)) • v i + (if i = j then c j • w else 0) := by
          intro i
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hw', Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul, ← add_smul]
      rw [hs] at hc
      have hcoef := hv _ hc
      have hcj : c j = 0 := by
        have := hcoef j
        simp only [if_true, sub_self, zero_add] at this
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exfalso
          rcases mul_eq_zero.mp h with h' | h'
          · exact hg0 (by simpa using h')
          · exact hj h'
      intro i
      by_cases hij : i = j
      · rw [hij]; exact hcj
      · have := hcoef i
        simpa [hij, hcj] using this
    )
  have L_config_exchange_keep : ∀ (n : ℕ)
      (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (v : Fin (n + 1) → Polynomial ℚ) (hv : LinearIndependent ℚ v)
      (hdeg : ∀ i, (v i).natDegree ≤ n) (k₀ : Fin (n + 1))
      (w : Polynomial ℚ) (hw : ∀ c : ℚ, w ≠ c • v k₀) (hwdeg : w.natDegree ≤ n), ∃ j, j ≠ k₀ ∧ LinearIndependent ℚ (Function.update v j w) :=
    (fun (n : ℕ)
        (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (v : Fin (n + 1) → Polynomial ℚ) (hv : LinearIndependent ℚ v)
        (hdeg : ∀ i, (v i).natDegree ≤ n) (k₀ : Fin (n + 1))
        (w : Polynomial ℚ) (hw : ∀ c : ℚ, w ≠ c • v k₀) (hwdeg : w.natDegree ≤ n) => by
      have hdep := hdim (n + 1) (Fin.cons w v) (by
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp only [Fin.cons_zero]; omega
        · simp only [Fin.cons_succ]; have := hdeg i; omega)
      rw [Fintype.not_linearIndependent_iff] at hdep
      obtain ⟨g, hg, i₁, hi₁⟩ := hdep
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      rw [Fintype.linearIndependent_iff] at hv
      have hg0 : g 0 ≠ 0 := by
        intro h0
        rw [h0, zero_smul, zero_add] at hg
        have := hv _ hg
        revert hi₁
        refine Fin.cases ?_ (fun i => ?_) i₁
        · exact fun h => h h0
        · exact fun h => h (this i)
      have hw' : w = ∑ i, (-(g 0)⁻¹ * g i.succ) • v i := by
        have h0 : g 0 • w = -∑ i, g i.succ • v i := eq_neg_of_add_eq_zero_left hg
        calc w = (g 0)⁻¹ • (g 0 • w) := by rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
          _ = _ := by
            rw [h0, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [smul_smul, ← neg_smul, neg_mul]
      have hj : ∃ j : Fin (n + 1), j ≠ k₀ ∧ g j.succ ≠ 0 := by
        by_contra hc
        push_neg at hc
        apply hw (-(g 0)⁻¹ * g k₀.succ)
        rw [hw', Finset.sum_eq_single k₀]
        · intro b _ hb; rw [hc b hb, mul_zero, zero_smul]
        · intro h; exact absurd (Finset.mem_univ _) h
      obtain ⟨j, hjk, hj⟩ := hj
      refine ⟨j, hjk, ?_⟩
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hs : ∑ i, c i • Function.update v j w i
          = ∑ i, (c i - (if i = j then c j else 0) + c j * (-(g 0)⁻¹ * g i.succ)) • v i := by
        have e1 : ∀ i, c i • Function.update v j w i
            = (c i - (if i = j then c j else 0)) • v i + (if i = j then c j • w else 0) := by
          intro i
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hw', Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul, ← add_smul]
      rw [hs] at hc
      have hcoef := hv _ hc
      have hcj : c j = 0 := by
        have := hcoef j
        simp only [if_true, sub_self, zero_add] at this
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exfalso
          rcases mul_eq_zero.mp h with h' | h'
          · exact hg0 (by simpa using h')
          · exact hj h'
      intro i
      by_cases hij : i = j
      · rw [hij]; exact hcj
      · have := hcoef i
        simpa [hij, hcj] using this
    )
  have L_config_shift : ∀ {m : ℕ} (v : Fin m → Polynomial ℚ) (hv : LinearIndependent ℚ v)
      (i₀ : Fin m) (a : Fin m → ℚ) (ha : a i₀ = 0), LinearIndependent ℚ (fun i => v i + a i • v i₀) :=
    (fun {m : ℕ} (v : Fin m → Polynomial ℚ) (hv : LinearIndependent ℚ v)
        (i₀ : Fin m) (a : Fin m → ℚ) (ha : a i₀ = 0) => by
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro g hg
      have hsum : ∑ i, (g i + if i = i₀ then ∑ j, g j * a j else 0) • v i = 0 := by
        rw [← hg]
        simp only [add_smul, Finset.sum_add_distrib, smul_add, ite_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul, Finset.sum_smul]
      have h1 := hv _ hsum
      have hne : ∀ i, i ≠ i₀ → g i = 0 := by
        intro i hi
        have := h1 i
        simpa [hi] using this
      have hz : ∑ j, g j * a j = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : j = i₀
        · subst hj; simp [ha]
        · simp [hne j hj]
      intro i
      by_cases hi : i = i₀
      · have := h1 i; simpa [hi, hz] using this
      · exact hne i hi
    )
  have L_config_sort : ∀ (m : ℕ) (f : Fin m → ℝ), ∃ σ : Equiv.Perm (Fin m), Monotone (f ∘ σ) :=
    (fun (m : ℕ) (f : Fin m → ℝ) => by
      induction m with
      | zero => exact ⟨1, fun a => Fin.elim0 a⟩
      | succ k ih =>
        obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ f ⟨0, Finset.mem_univ _⟩
        set τ : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 i₀
        obtain ⟨ρ, hρ⟩ := ih (fun j => f (τ j.succ))
        let ρ' : Fin (k + 1) → Fin (k + 1) := fun j => Fin.cases 0 (fun j => (ρ j).succ) j
        have hinj : Function.Injective (τ ∘ ρ') := by
          refine τ.injective.comp ?_
          intro a b
          refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b <;>
            intro hab' <;> simp [ρ'] at hab'
          all_goals first | rfl | exact absurd hab'.symm (Fin.succ_ne_zero _) | exact absurd hab' (Fin.succ_ne_zero _) | exact congrArg Fin.succ hab'
        let σ : Equiv.Perm (Fin (k + 1)) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
        refine ⟨σ, ?_⟩
        have h0 : ∀ j : Fin k, σ j.succ = τ (ρ j).succ := fun j => rfl
        have hz : σ 0 = i₀ := by
          show τ 0 = i₀
          simp [τ]
        intro a b
        refine Fin.cases ?_ (fun a' => ?_) a
        · intro _
          simp only [Function.comp]
          rw [hz]; exact hi₀ _ (Finset.mem_univ _)
        · refine Fin.cases (fun h => ?_) (fun b' h => ?_) b
          · exact absurd h (by simp [Fin.le_def])
          · simp only [Function.comp]
            rw [h0, h0]
            exact hρ (Fin.succ_le_succ_iff.mp h)
    )
  have L_config_correct : ∀ (ξ : ℝ) (P' Q : Polynomial ℤ) (hQ : Polynomial.aeval ξ Q ≠ 0), |Polynomial.aeval ξ (P' - Polynomial.C ⌊Polynomial.aeval ξ P' / Polynomial.aeval ξ Q⌋ * Q)|
        < |Polynomial.aeval ξ Q| :=
    (fun (ξ : ℝ) (P' Q : Polynomial ℤ) (hQ : Polynomial.aeval ξ Q ≠ 0) => by
      have h1 : Polynomial.aeval ξ (P' - Polynomial.C ⌊Polynomial.aeval ξ P' / Polynomial.aeval ξ Q⌋ * Q)
          = Polynomial.aeval ξ Q * Int.fract (Polynomial.aeval ξ P' / Polynomial.aeval ξ Q) := by
        simp only [map_sub, map_mul, eq_intCast, map_intCast]
        rw [Int.fract]
        field_simp
      rw [h1, abs_mul, abs_of_nonneg (Int.fract_nonneg _)]
      have hb : 0 < |Polynomial.aeval ξ Q| := abs_pos.mpr hQ
      calc |Polynomial.aeval ξ Q| * Int.fract _ < |Polynomial.aeval ξ Q| * 1 :=
            mul_lt_mul_of_pos_left (Int.fract_lt_one _) hb
        _ = _ := mul_one _
    )
  have L_config_step1 : ∀ (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (P' : Fin (n + 1) → Polynomial ℤ) (hP'd : ∀ i, (P' i).natDegree ≤ n)
      (hP' : LinearIndependent ℚ (fun i => (P' i).map (Int.castRingHom ℚ)))
      (Q₀ : Polynomial ℤ) (hQ₀ : Q₀ ≠ 0) (hQ₀d : Q₀.natDegree ≤ n)
      (hδ : Polynomial.aeval ξ Q₀ ≠ 0), ∃ j : Fin (n + 1), ∃ R : Fin (n + 1) → Polynomial ℤ, R j = Q₀ ∧
        (∀ i, (R i).natDegree ≤ n) ∧
        LinearIndependent ℚ (fun i => (R i).map (Int.castRingHom ℚ)) ∧
        ∀ i, i ≠ j → |Polynomial.aeval ξ (R i)| < |Polynomial.aeval ξ Q₀| ∧
          N (R i) ≤ N (P' i) + (|Polynomial.aeval ξ (P' i)| / |Polynomial.aeval ξ Q₀| + 1) * N Q₀ :=
    (fun (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (P' : Fin (n + 1) → Polynomial ℤ) (hP'd : ∀ i, (P' i).natDegree ≤ n)
        (hP' : LinearIndependent ℚ (fun i => (P' i).map (Int.castRingHom ℚ)))
        (Q₀ : Polynomial ℤ) (hQ₀ : Q₀ ≠ 0) (hQ₀d : Q₀.natDegree ≤ n)
        (hδ : Polynomial.aeval ξ Q₀ ≠ 0) => by
      classical
      set v : Fin (n + 1) → Polynomial ℚ := fun i => (P' i).map (Int.castRingHom ℚ) with hv
      have hQm0 : Q₀.map (Int.castRingHom ℚ) ≠ 0 :=
        (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hQ₀
      obtain ⟨j, hj⟩ := L_config_exchange n hdim v hP'
        (fun i => le_trans (Polynomial.natDegree_map_le) (hP'd i)) _ hQm0
        (le_trans (Polynomial.natDegree_map_le) hQ₀d)
      set U : Fin (n + 1) → Polynomial ℤ := Function.update P' j Q₀ with hU
      have hUv : (fun i => (U i).map (Int.castRingHom ℚ)) = Function.update v j (Q₀.map (Int.castRingHom ℚ)) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [U]
        · simp [U, v, Function.update_of_ne hi]
      set k : Fin (n + 1) → ℤ := fun i => if i = j then 0 else
        ⌊Polynomial.aeval ξ (P' i) / Polynomial.aeval ξ Q₀⌋ with hk
      refine ⟨j, fun i => U i - Polynomial.C (k i) * Q₀, ?_, ?_, ?_, ?_⟩
      · simp [U, k]
      · intro i
        refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
        · by_cases hi : i = j
          · subst hi; simp [U, hQ₀d]
          · simp only [U, Function.update_of_ne hi]; exact hP'd i
        · exact le_trans (Polynomial.natDegree_C_mul_le _ _) hQ₀d
      · have hsh := L_config_shift (Function.update v j (Q₀.map (Int.castRingHom ℚ))) hj j
          (fun i => -((k i : ℤ) : ℚ)) (by simp [k])
        convert hsh using 1
        funext i
        simp only [Function.update_self]
        rw [← hUv]
        simp only [eq_intCast,
          Polynomial.smul_eq_C_mul, Polynomial.C_neg, neg_mul, sub_eq_add_neg]
        simp
      · intro i hi
        have hUi : U i = P' i := by simp only [U, Function.update_of_ne hi]
        have hki : k i = ⌊Polynomial.aeval ξ (P' i) / Polynomial.aeval ξ Q₀⌋ := by simp [k, hi]
        simp only [hUi, hki]
        refine ⟨L_config_correct ξ (P' i) Q₀ hδ, ?_⟩
        set x := Polynomial.aeval ξ (P' i) / Polynomial.aeval ξ Q₀
        have hsplit : P' i - Polynomial.C ⌊x⌋ * Q₀ = P' i + Polynomial.C (-⌊x⌋) * Q₀ := by
          simp [sub_eq_add_neg]
        rw [hsplit]
        refine le_trans (L_config_N_add N hN _ _) ?_
        rw [L_config_N_smul N hN]
        have hNQ : 0 ≤ N Q₀ := by rw [hN]; positivity
        have hfl : |((-⌊x⌋ : ℤ) : ℝ)| ≤ |x| + 1 := by
          push_cast
          rw [abs_neg]
          have h1 := Int.floor_le x
          have h2 := Int.lt_floor_add_one x
          rw [abs_le]
          constructor <;> rcases abs_cases x with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> linarith
        have hx : |x| = |Polynomial.aeval ξ (P' i)| / |Polynomial.aeval ξ Q₀| := abs_div _ _
        rw [← hx]
        linarith [mul_le_mul_of_nonneg_right hfl hNQ]
    )
  have L_config_step2 : ∀ (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (R : Fin (n + 1) → Polynomial ℤ) (hRd : ∀ i, (R i).natDegree ≤ n)
      (hR : LinearIndependent ℚ (fun i => (R i).map (Int.castRingHom ℚ)))
      (j : Fin (n + 1)) (P : Polynomial ℤ) (hPd : P.natDegree ≤ n)
      (hP : ∀ c : ℚ, P.map (Int.castRingHom ℚ) ≠ c • (R j).map (Int.castRingHom ℚ)), ∃ i₁ : Fin (n + 1), i₁ ≠ j ∧ ∃ F : Fin (n + 1) → Polynomial ℤ, F j = R j ∧ F i₁ = P ∧
        (∀ i, (F i).natDegree ≤ n) ∧
        LinearIndependent ℚ (fun i => (F i).map (Int.castRingHom ℚ)) ∧
        ∀ i, i ≠ j → i ≠ i₁ → N P ≤ N (F i) ∧ N (F i) ≤ N (R i) + 3 * N P ∧
          |Polynomial.aeval ξ (F i)| ≤ |Polynomial.aeval ξ (R i)| + 3 * |Polynomial.aeval ξ P| :=
    (fun (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (R : Fin (n + 1) → Polynomial ℤ) (hRd : ∀ i, (R i).natDegree ≤ n)
        (hR : LinearIndependent ℚ (fun i => (R i).map (Int.castRingHom ℚ)))
        (j : Fin (n + 1)) (P : Polynomial ℤ) (hPd : P.natDegree ≤ n)
        (hP : ∀ c : ℚ, P.map (Int.castRingHom ℚ) ≠ c • (R j).map (Int.castRingHom ℚ)) => by
      have hvd : ∀ i, ((R i).map (Int.castRingHom ℚ)).natDegree ≤ n :=
        fun i => Polynomial.natDegree_map_le.trans (hRd i)
      obtain ⟨i₁, hi₁j, hind⟩ := L_config_exchange_keep n hdim (fun i => (R i).map (Int.castRingHom ℚ))
        hR hvd j (P.map (Int.castRingHom ℚ)) hP (Polynomial.natDegree_map_le.trans hPd)
      have hSmap : (fun i => ((Function.update R i₁ P) i).map (Int.castRingHom ℚ)) =
          Function.update (fun i => (R i).map (Int.castRingHom ℚ)) i₁ (P.map (Int.castRingHom ℚ)) := by
        funext i
        by_cases h : i = i₁
        · subst h; simp
        · simp [h]
      have hind' : LinearIndependent ℚ (fun i => ((Function.update R i₁ P) i).map (Int.castRingHom ℚ)) := by
        rw [hSmap]; exact hind
      have hNnn : ∀ p, 0 ≤ N p := fun p => by rw [hN]; positivity
      let lam : Fin (n + 1) → ℤ := fun i =>
        if i = j ∨ i = i₁ then 0 else if N P < N (R i) then 0 else 3
      have hlamj : lam j = 0 := by simp [lam]
      have hlami₁ : lam i₁ = 0 := by simp [lam]
      refine ⟨i₁, hi₁j, fun i => Function.update R i₁ P i + Polynomial.C (lam i) * P, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hlamj, Function.update_of_ne (Ne.symm hi₁j)]
      · simp [hlami₁]
      · intro i
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ((Polynomial.natDegree_C_mul_le _ _).trans hPd))
        by_cases h : i = i₁
        · subst h; simpa using hPd
        · simpa [h] using hRd i
      · have heq : (fun i => (Function.update R i₁ P i + Polynomial.C (lam i) * P).map (Int.castRingHom ℚ)) =
            fun i => ((Function.update R i₁ P) i).map (Int.castRingHom ℚ) +
              ((lam i : ℚ)) • ((Function.update R i₁ P) i₁).map (Int.castRingHom ℚ) := by
          funext i
          rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.smul_eq_C_mul]
          simp
        rw [heq]
        exact L_config_shift _ hind' i₁ (fun i => (lam i : ℚ)) (by simp [hlami₁])
      · intro i hij hii₁
        have hS : Function.update R i₁ P i = R i := Function.update_of_ne hii₁ _ _
        simp only [hS]
        by_cases hlt : N P < N (R i)
        · have hl : lam i = 0 := by simp [lam, hij, hii₁, hlt]
          simp only [hl, Polynomial.C_0, zero_mul, add_zero]
          refine ⟨hlt.le, by linarith [hNnn P], by linarith [abs_nonneg (Polynomial.aeval ξ P)]⟩
        · have hl : lam i = 3 := by simp [lam, hij, hii₁, hlt]
          simp only [hl]
          push_neg at hlt
          have h3 : N (Polynomial.C (3 : ℤ) * P) = 3 * N P := by
            rw [L_config_N_smul N hN]; norm_num
          refine ⟨?_, ?_, ?_⟩
          · have e : Polynomial.C (3 : ℤ) * P = (R i + Polynomial.C 3 * P) + Polynomial.C (-1) * R i := by
              simp
            have h1 := L_config_N_add N hN (R i + Polynomial.C 3 * P) (Polynomial.C (-1) * R i)
            rw [← e, h3, L_config_N_smul N hN] at h1
            have hm1 : |((-1 : ℤ) : ℝ)| = 1 := by norm_num
            rw [hm1, one_mul] at h1
            linarith [hNnn P]
          · have h1 := L_config_N_add N hN (R i) (Polynomial.C 3 * P)
            rw [h3] at h1; exact h1
          · rw [map_add, map_mul, Polynomial.aeval_C]
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul]
            norm_num
    )
  have L_config_reorder : ∀ (n : ℕ) (hn : 1 ≤ n) (N : Polynomial ℤ → ℝ)
      (F : Fin (n + 1) → Polynomial ℤ)
      (hF : LinearIndependent ℚ (fun i => (F i).map (Int.castRingHom ℚ)))
      (hdeg : ∀ i, (F i).natDegree ≤ n) (j i₁ : Fin (n + 1)) (hji : i₁ ≠ j)
      (h0 : N (F j) ≤ N (F i₁)) (h1 : ∀ i, i ≠ j → i ≠ i₁ → N (F i₁) ≤ N (F i)), ∃ Q : ℕ → Polynomial ℤ, Q 0 = F j ∧ Q 1 = F i₁ ∧
        (∀ i, (Q i).natDegree ≤ n) ∧
        LinearIndependent ℚ (fun i : Fin (n + 1) => (Q i).map (Int.castRingHom ℚ)) ∧
        (∀ i j, i ≤ j → j ≤ n → N (Q i) ≤ N (Q j)) ∧
        (∀ i, i ≤ n → ∃ k, Q i = F k) ∧
        ∏ m ∈ Finset.Icc 1 n, N (Q m) = ∏ i ∈ Finset.univ.erase j, N (F i) :=
    (fun (n : ℕ) (hn : 1 ≤ n) (N : Polynomial ℤ → ℝ)
        (F : Fin (n + 1) → Polynomial ℤ)
        (hF : LinearIndependent ℚ (fun i => (F i).map (Int.castRingHom ℚ)))
        (hdeg : ∀ i, (F i).natDegree ≤ n) (j i₁ : Fin (n + 1)) (hji : i₁ ≠ j)
        (h0 : N (F j) ≤ N (F i₁)) (h1 : ∀ i, i ≠ j → i ≠ i₁ → N (F i₁) ≤ N (F i)) => by
      set g : Fin (n + 1) → ℝ := fun i =>
        if i = j then 0 else if i = i₁ then 1 else 2 + (N (F i) - N (F i₁)) with hg
      have gj : g j = 0 := by simp [hg]
      have gi₁ : g i₁ = 1 := by simp [hg, hji]
      have gother : ∀ i, i ≠ j → i ≠ i₁ → g i = 2 + (N (F i) - N (F i₁)) := by
        intro i h1' h2'; simp [hg, h1', h2']
      have gge : ∀ i, i ≠ j → i ≠ i₁ → 2 ≤ g i := by
        intro i h1' h2'; rw [gother i h1' h2']; linarith [h1 i h1' h2']
      have gge1 : ∀ i, i ≠ j → 1 ≤ g i := by
        intro i h1'
        by_cases h2' : i = i₁
        · rw [h2', gi₁]
        · linarith [gge i h1' h2']
      obtain ⟨σ, hσ⟩ := L_config_sort (n + 1) g
      have hσm : ∀ a b : Fin (n + 1), a ≤ b → g (σ a) ≤ g (σ b) := fun a b h => hσ h
      have hσ0 : σ 0 = j := by
        by_contra hne
        have := hσm 0 (σ.symm j) (Fin.zero_le _)
        rw [Equiv.apply_symm_apply, gj] at this
        linarith [gge1 _ hne]
      have h10 : (1 : Fin (n + 1)) ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)] at this
      have hσ1 : σ 1 = i₁ := by
        have hb : σ.symm i₁ ≠ 0 := by
          intro h
          have : σ (σ.symm i₁) = σ 0 := by rw [h]
          rw [Equiv.apply_symm_apply, hσ0] at this
          exact hji this
        have hb1 : (1 : Fin (n + 1)) ≤ σ.symm i₁ := by
          rw [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
          have : (σ.symm i₁).val ≠ 0 := fun h => hb (Fin.ext h)
          omega
        have hnj : σ 1 ≠ j := by
          intro h
          rw [← hσ0] at h
          exact h10 (σ.injective h)
        have := hσm 1 (σ.symm i₁) hb1
        rw [Equiv.apply_symm_apply, gi₁] at this
        by_contra hne
        linarith [gge _ hnj hne]
      have hNj : ∀ k, N (F j) ≤ N (F k) := by
        intro k
        by_cases hk : k = j
        · rw [hk]
        by_cases hk' : k = i₁
        · rw [hk']; exact h0
        · linarith [h1 k hk hk']
      have hmonoF : ∀ a b : Fin (n + 1), a ≤ b → N (F (σ a)) ≤ N (F (σ b)) := by
        intro a b hab
        have hg' := hσm a b hab
        by_cases ha : σ a = j
        · rw [ha]; exact hNj _
        by_cases ha' : σ a = i₁
        · have hbj : σ b ≠ j := by
            intro h; rw [h, gj] at hg'; linarith [gge1 _ ha]
          rw [ha']
          by_cases hb' : σ b = i₁
          · rw [hb']
          · exact h1 _ hbj hb'
        · have hbj : σ b ≠ j := by
            intro h; rw [h, gj] at hg'; linarith [gge _ ha ha']
          have hbi : σ b ≠ i₁ := by
            intro h; rw [h, gi₁] at hg'; linarith [gge _ ha ha']
          rw [gother _ ha ha', gother _ hbj hbi] at hg'
          linarith
      set Q : ℕ → Polynomial ℤ := fun m => if h : m < n + 1 then F (σ ⟨m, h⟩) else 0 with hQ
      have hQv : ∀ m (h : m < n + 1), Q m = F (σ ⟨m, h⟩) := by
        intro m h; exact dif_pos h
      refine ⟨Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hQv 0 (by omega)]; exact congrArg F hσ0
      · rw [hQv 1 (by omega)]
        have : (⟨1, by omega⟩ : Fin (n + 1)) = 1 := by
          ext; rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
        rw [this, hσ1]
      · intro i
        by_cases h : i < n + 1
        · rw [hQv i h]; exact hdeg _
        · have : Q i = 0 := dif_neg h
          rw [this]; simp
      · have : (fun i : Fin (n + 1) => (Q i).map (Int.castRingHom ℚ)) =
            (fun i => (F i).map (Int.castRingHom ℚ)) ∘ σ := by
          funext i
          simp only [Function.comp]
          rw [hQv i i.2]
        rw [this]
        exact hF.comp σ σ.injective
      · intro a b hab hb
        rw [hQv a (by omega), hQv b (by omega)]
        exact hmonoF _ _ (by rw [Fin.le_def]; exact hab)
      · intro i hi
        exact ⟨_, hQv i (by omega)⟩
      · refine Finset.prod_nbij' (fun m => if h : m < n + 1 then σ ⟨m, h⟩ else j)
          (fun k => (σ.symm k).val) ?_ ?_ ?_ ?_ ?_
        · intro m hm
          have hm' := Finset.mem_Icc.mp hm
          have hlt : m < n + 1 := by omega
          simp only [dif_pos hlt]
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ _⟩
          intro h
          rw [← hσ0] at h
          have := congrArg Fin.val (σ.injective h)
          simp at this; omega
        · intro k hk
          have hk' := (Finset.mem_erase.mp hk).1
          rw [Finset.mem_Icc]
          have hne : σ.symm k ≠ 0 := by
            intro h
            have : σ (σ.symm k) = σ 0 := by rw [h]
            rw [Equiv.apply_symm_apply, hσ0] at this
            exact hk' this
          have h0' : (σ.symm k).val ≠ 0 := fun h => hne (Fin.ext h)
          have := (σ.symm k).isLt
          show 1 ≤ (σ.symm k).val ∧ (σ.symm k).val ≤ n
          omega
        · intro m hm
          have hm' := Finset.mem_Icc.mp hm
          have hlt : m < n + 1 := by omega
          simp only [dif_pos hlt, Equiv.symm_apply_apply]
        · intro k hk
          simp only [dif_pos (σ.symm k).isLt]
          simp
        · intro m hm
          have hm' := Finset.mem_Icc.mp hm
          have hlt : m < n + 1 := by omega
          simp only [dif_pos hlt]
          rw [hQv m hlt]
    )
  have L_config_family : ∀ (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hmii : ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∃ P : Fin (n + 1) → Polynomial ℤ,
        (∀ i, (P i).natDegree ≤ n) ∧
        LinearIndependent ℚ (fun i => (P i).map (Int.castRingHom ℚ)) ∧
        ∏ i, max (N (P i)) (Real.exp q * |Polynomial.aeval ξ (P i)|) ≤ C * Real.exp q)
      (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
        N A * N B ≤ C * N (A * B))
      (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
        P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S)
      (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v), ∃ C' K : ℝ, 0 < C' ∧ 1 ≤ K ∧ ∀ P : Polynomial ℤ, P.natDegree ≤ n →
        Irreducible (P.map (Int.castRingHom ℚ)) →
        (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) → K ≤ N P →
        ∃ Q : ℕ → Polynomial ℤ, Q 1 = P ∧ Q 0 ≠ 0 ∧ N (Q 0) ≤ N P / K ∧
          (∀ R : Polynomial ℤ, R ≠ 0 → R.natDegree ≤ n → N R ≤ N P / K →
            |Polynomial.aeval ξ (Q 0)| ≤ |Polynomial.aeval ξ R|) ∧
          (∀ i, (Q i).natDegree ≤ n) ∧
          LinearIndependent ℚ (fun i : Fin (n + 1) => (Q i).map (Int.castRingHom ℚ)) ∧
          IsCoprime ((Q 0).map (Int.castRingHom ℚ)) ((Q 1).map (Int.castRingHom ℚ)) ∧
          (∀ i j, i ≤ j → j ≤ n → N (Q i) ≤ N (Q j)) ∧
          |Polynomial.aeval ξ (Q 0)| * ∏ j ∈ Finset.Icc 1 n, N (Q j) ≤ C' ∧
          (∀ i, i ≤ n → |Polynomial.aeval ξ (Q i)| ≤
            4 * max |Polynomial.aeval ξ (Q 0)| |Polynomial.aeval ξ (Q 1)|) :=
    (fun (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hmii : ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∃ P : Fin (n + 1) → Polynomial ℤ,
          (∀ i, (P i).natDegree ≤ n) ∧
          LinearIndependent ℚ (fun i => (P i).map (Int.castRingHom ℚ)) ∧
          ∏ i, max (N (P i)) (Real.exp q * |Polynomial.aeval ξ (P i)|) ≤ C * Real.exp q)
        (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
          N A * N B ≤ C * N (A * B))
        (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
          P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S)
        (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v) => by
      classical
      obtain ⟨CG, hCG, hgel⟩ := hgel
      obtain ⟨CM, hCM, hmii⟩ := hmii
      have hN1 : N 1 = 1 := by
        rw [hN]
        have h1 : ((1 : Polynomial ℤ).support.sup fun i => ((1 : Polynomial ℤ).coeff i).natAbs) ≤ 1 :=
          Finset.sup_le (fun i _ => by rw [Polynomial.coeff_one]; split_ifs <;> simp)
        have h2 : 1 ≤ ((1 : Polynomial ℤ).support.sup fun i => ((1 : Polynomial ℤ).coeff i).natAbs) := by
          have hm : (0:ℕ) ∈ (1 : Polynomial ℤ).support := by simp [Polynomial.mem_support_iff]
          exact le_trans (by simp) (Finset.le_sup (f := fun i => ((1 : Polynomial ℤ).coeff i).natAbs) hm)
        exact_mod_cast le_antisymm h1 h2
      have hN0 : ∀ p, 0 ≤ N p := fun p => by rw [hN]; positivity
      have hCG1 : 1 ≤ CG := by
        have := hgel 1 1 one_ne_zero one_ne_zero (by simp)
        rw [mul_one, hN1] at this; linarith
      refine ⟨(1 + 3 * (2 * CG)) ^ n * 3 ^ n * CM, 2 * CG, by positivity, by linarith, ?_⟩
      intro P hPd hPirr hPprim hKP
      have hK0 : 0 < 2 * CG := by linarith
      set K := 2 * CG with hKdef
      set H := N P / K with hHdef
      have hH1 : 1 ≤ H := by rw [hHdef, le_div_iff₀ hK0]; linarith
      have hNPH : N P = K * H := by rw [hHdef]; field_simp
      obtain ⟨Q₀, hQ₀ne, hQ₀d, hQ₀N, hQ₀min⟩ := L_config_minpoint n ξ N hN H hH1
      have hδne := L_config_aeval_ne_zero ξ hξ Q₀ hQ₀ne
      set δ := |Polynomial.aeval ξ Q₀| with hδdef
      have hδ0 : 0 < δ := abs_pos.mpr hδne
      have hδ1 : δ ≤ 1 := by
        have := hQ₀min 1 one_ne_zero (by simp) (by rw [hN1]; exact hH1)
        simpa using this
      have hP0 : P ≠ 0 := by
        intro h; apply hPirr.ne_zero; rw [h, Polynomial.map_zero]
      have hNP1 : 1 ≤ N P := L_config_N_ge_one N hN P hP0
      have hndvd : ¬ P.map (Int.castRingHom ℚ) ∣ Q₀.map (Int.castRingHom ℚ) := by
        intro hd
        obtain ⟨T, hT⟩ := hgauss P Q₀ hPprim hd
        have hT0 : T ≠ 0 := by rintro rfl; rw [mul_zero] at hT; exact hQ₀ne hT
        have h1 := hgel P T hP0 hT0 (by rw [← hT]; exact hQ₀d)
        rw [← hT] at h1
        have h2 := L_config_N_ge_one N hN T hT0
        have h3 : N P * 1 ≤ N P * N T := mul_le_mul_of_nonneg_left h2 (hN0 P)
        have h4 : CG * N Q₀ ≤ CG * H := mul_le_mul_of_nonneg_left hQ₀N hCG.le
        have h5 : CG * H * 2 = N P := by rw [hNPH, hKdef]; ring
        linarith
      have hcop : IsCoprime (Q₀.map (Int.castRingHom ℚ)) (P.map (Int.castRingHom ℚ)) :=
        (L_config_coprime _ _ hPirr hndvd).symm
      have hnmul : ∀ c : ℚ, P.map (Int.castRingHom ℚ) ≠ c • Q₀.map (Int.castRingHom ℚ) := by
        intro c hc
        apply hndvd
        by_cases hc0 : c = 0
        · exfalso; rw [hc0, zero_smul] at hc; exact hPirr.ne_zero hc
        · refine ⟨Polynomial.C c⁻¹, ?_⟩
          rw [hc, Polynomial.smul_eq_C_mul, mul_comm, ← mul_assoc, ← Polynomial.C_mul,
            inv_mul_cancel₀ hc0, Polynomial.C_1, one_mul]
      set q := Real.log (H / δ) with hqdef
      have hHδ : 1 ≤ H / δ := by rw [le_div_iff₀ hδ0]; linarith
      have hq : 0 ≤ q := Real.log_nonneg hHδ
      have heq : Real.exp q = H / δ := Real.exp_log (by linarith)
      have hfirst : ∀ R : Polynomial ℤ, R ≠ 0 → R.natDegree ≤ n →
          H ≤ max (N R) (Real.exp q * |Polynomial.aeval ξ R|) := by
        intro R hR hRd
        by_cases hRH : N R ≤ H
        · have := hQ₀min R hR hRd hRH
          refine le_max_of_le_right ?_
          rw [heq]
          calc H = H / δ * δ := by field_simp
            _ ≤ H / δ * |Polynomial.aeval ξ R| := mul_le_mul_of_nonneg_left this (by positivity)
        · exact le_max_of_le_left (le_of_lt (not_le.mp hRH))
      obtain ⟨P', hP'd, hP'li, hprod⟩ := hmii q hq
      have hP'ne : ∀ i, P' i ≠ 0 := by
        intro i h0; apply hP'li.ne_zero i; simp [h0]
      obtain ⟨j, R, hRj, hRd, hRli, hRb⟩ := L_config_step1 n ξ N hN hdim P' hP'd hP'li Q₀ hQ₀ne hQ₀d hδne
      set ν : Fin (n + 1) → ℝ := fun i => max (N (P' i)) (Real.exp q * |Polynomial.aeval ξ (P' i)|)
        with hνdef
      have hνH : ∀ i, H ≤ ν i := fun i => hfirst (P' i) (hP'ne i) (hP'd i)
      have hRne : ∀ i, R i ≠ 0 := by
        intro i h0; apply hRli.ne_zero i; simp [h0]
      have hRH : ∀ i, i ≠ j → H < N (R i) := by
        intro i hi
        by_contra hc
        push_neg at hc
        have := hQ₀min (R i) (hRne i) (hRd i) hc
        linarith [(hRb i hi).1]
      have hR3 : ∀ i, i ≠ j → N (R i) ≤ 3 * ν i := by
        intro i hi
        have hb := (hRb i hi).2
        have hν1 : N (P' i) ≤ ν i := le_max_left _ _
        have hν2 : Real.exp q * |Polynomial.aeval ξ (P' i)| ≤ ν i := le_max_right _ _
        have e1 : (|Polynomial.aeval ξ (P' i)| / δ + 1) * H
            = Real.exp q * |Polynomial.aeval ξ (P' i)| + H := by rw [heq]; field_simp
        have e2 : (|Polynomial.aeval ξ (P' i)| / δ + 1) * N Q₀ ≤ (|Polynomial.aeval ξ (P' i)| / δ + 1) * H :=
          mul_le_mul_of_nonneg_left hQ₀N (by positivity)
        linarith [hνH i]
      have hRj' : ∀ c : ℚ, P.map (Int.castRingHom ℚ) ≠ c • (R j).map (Int.castRingHom ℚ) := by
        rw [hRj]; exact hnmul
      obtain ⟨i₁, hi₁, F, hFj, hFi₁, hFd, hFli, hFb⟩ := L_config_step2 n ξ N hN hdim R hRd hRli j P hPd hRj'
      have hHNP : H ≤ N P := by rw [hNPH]; nlinarith
      obtain ⟨Q, hQ0, hQ1, hQd, hQli, hQmono, hQin, hQprod⟩ := L_config_reorder n (by omega) N F hFli hFd j i₁ hi₁
        (by rw [hFj, hFi₁, hRj]; linarith) (fun i hi hi' => by rw [hFi₁]; exact (hFb i hi hi').1)
      have hQ0' : Q 0 = Q₀ := by rw [hQ0, hFj, hRj]
      have hQ1' : Q 1 = P := by rw [hQ1, hFi₁]
      refine ⟨Q, hQ1', by rw [hQ0']; exact hQ₀ne, by rw [hQ0']; exact hQ₀N, by rw [hQ0']; exact hQ₀min,
        hQd, hQli, by rw [hQ0', hQ1']; exact hcop, hQmono, ?_, ?_⟩
      · rw [hQprod, hQ0', ← hδdef]
        have hFbd : ∀ i ∈ Finset.univ.erase j, N (F i) ≤ ((1 + 3 * K) * 3) * ν i := by
          intro i hi
          have hij : i ≠ j := Finset.ne_of_mem_erase hi
          have hr := hRH i hij
          have h3 := hR3 i hij
          by_cases hii : i = i₁
          · rw [hii, hFi₁]
            rw [← hii]
            have : N P ≤ K * N (R i) := by rw [hNPH]; exact mul_le_mul_of_nonneg_left hr.le hK0.le
            nlinarith [hN0 (R i)]
          · have hb := (hFb i hij hii).2.1
            have : N P ≤ K * N (R i) := by rw [hNPH]; exact mul_le_mul_of_nonneg_left hr.le hK0.le
            nlinarith [hN0 (R i)]
        have hle := Finset.prod_le_prod (fun i _ => hN0 (F i)) hFbd
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at hle
        have hνprod : δ * ∏ i ∈ Finset.univ.erase j, ν i ≤ CM := by
          have hpe := Finset.prod_erase_mul Finset.univ ν (Finset.mem_univ j)
          have hp0 : 0 ≤ ∏ i ∈ Finset.univ.erase j, ν i :=
            Finset.prod_nonneg (fun i _ => le_trans (by linarith) (hνH i))
          have h1 : (∏ i ∈ Finset.univ.erase j, ν i) * H ≤ CM * (H / δ) := by
            calc (∏ i ∈ Finset.univ.erase j, ν i) * H ≤ (∏ i ∈ Finset.univ.erase j, ν i) * ν j :=
                  mul_le_mul_of_nonneg_left (hνH j) hp0
              _ = ∏ i, ν i := hpe
              _ ≤ CM * Real.exp q := hprod
              _ = CM * (H / δ) := by rw [heq]
          have h2 : CM * (H / δ) * δ = CM * H := by field_simp
          have h3 : (δ * ∏ i ∈ Finset.univ.erase j, ν i) * H ≤ CM * H := by
            nlinarith
          exact le_of_mul_le_mul_right h3 (by linarith)
        have hc0 : 0 ≤ ((1 + 3 * K) * 3) ^ n := by positivity
        calc δ * ∏ i ∈ Finset.univ.erase j, N (F i)
            ≤ δ * (((1 + 3 * K) * 3) ^ n * ∏ i ∈ Finset.univ.erase j, ν i) :=
              mul_le_mul_of_nonneg_left hle hδ0.le
          _ = ((1 + 3 * K) * 3) ^ n * (δ * ∏ i ∈ Finset.univ.erase j, ν i) := by ring
          _ ≤ ((1 + 3 * K) * 3) ^ n * CM := mul_le_mul_of_nonneg_left hνprod hc0
          _ = _ := by rw [mul_pow]
      · intro i hi
        rw [hQ0', hQ1', ← hδdef]
        obtain ⟨k, hk⟩ := hQin i hi
        rw [hk]
        have hm1 : δ ≤ max δ |Polynomial.aeval ξ P| := le_max_left _ _
        have hm2 : |Polynomial.aeval ξ P| ≤ max δ |Polynomial.aeval ξ P| := le_max_right _ _
        have hm0 : 0 ≤ |Polynomial.aeval ξ P| := abs_nonneg _
        by_cases hkj : k = j
        · rw [hkj, hFj, hRj]; linarith
        · by_cases hki : k = i₁
          · rw [hki, hFi₁]; linarith
          · have h1 := (hFb k hkj hki).2.2
            have h2 := (hRb k hkj).1
            linarith
    )
  have L_config : ∀ (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hmii : ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∃ P : Fin (n + 1) → Polynomial ℤ,
        (∀ i, (P i).natDegree ≤ n) ∧
        LinearIndependent ℚ (fun i => (P i).map (Int.castRingHom ℚ)) ∧
        ∏ i, max (N (P i)) (Real.exp q * |Polynomial.aeval ξ (P i)|) ≤ C * Real.exp q)
      (hgood : ∀ W ε : ℝ, 0 ≤ W → 0 < ε → ε ≤ 1 → ∃ w : ℝ, 0 ≤ w ∧
        (∀ B : ℝ, ∃ P : Polynomial ℤ, P.natDegree ≤ n ∧ Irreducible (P.map (Int.castRingHom ℚ)) ∧
            (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) ∧ B ≤ N P ∧
            |Polynomial.aeval ξ P| ≤ N P ^ (-w)) ∧
        (W ≤ w ∨ ∃ B₀ : ℝ, ∀ R : Polynomial ℤ, R ≠ 0 → R.natDegree ≤ n → B₀ ≤ N R →
            N R ^ (-(w + ε)) ≤ |Polynomial.aeval ξ R|))
      (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
        N A * N B ≤ C * N (A * B))
      (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
        P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S)
      (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1), ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, ∃ Q : ℕ → Polynomial ℤ,
        (∀ i, (Q i).natDegree ≤ n) ∧
        LinearIndependent ℚ (fun i : Fin (n + 1) => (Q i).map (Int.castRingHom ℚ)) ∧
        IsCoprime ((Q 0).map (Int.castRingHom ℚ)) ((Q 1).map (Int.castRingHom ℚ)) ∧
        B ≤ N (Q 1) ∧
        (∀ i j, i ≤ j → j ≤ n → N (Q i) ≤ N (Q j)) ∧
        (∀ i, i ≤ n → |Polynomial.aeval ξ (Q i)| ≤
          C * max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ))))) :=
    (fun (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hmii : ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∃ P : Fin (n + 1) → Polynomial ℤ,
          (∀ i, (P i).natDegree ≤ n) ∧
          LinearIndependent ℚ (fun i => (P i).map (Int.castRingHom ℚ)) ∧
          ∏ i, max (N (P i)) (Real.exp q * |Polynomial.aeval ξ (P i)|) ≤ C * Real.exp q)
        (hgood : ∀ W ε : ℝ, 0 ≤ W → 0 < ε → ε ≤ 1 → ∃ w : ℝ, 0 ≤ w ∧
          (∀ B : ℝ, ∃ P : Polynomial ℤ, P.natDegree ≤ n ∧ Irreducible (P.map (Int.castRingHom ℚ)) ∧
              (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) ∧ B ≤ N P ∧
              |Polynomial.aeval ξ P| ≤ N P ^ (-w)) ∧
          (W ≤ w ∨ ∃ B₀ : ℝ, ∀ R : Polynomial ℤ, R ≠ 0 → R.natDegree ≤ n → B₀ ≤ N R →
              N R ^ (-(w + ε)) ≤ |Polynomial.aeval ξ R|))
        (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
          N A * N B ≤ C * N (A * B))
        (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
          P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S)
        (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) => by
      obtain ⟨C', K, hC', hK, hfam⟩ := L_config_family n hn ξ hξ N hN hmii hgel hgauss hdim
      obtain ⟨w, hw0, hgoodP, hcase⟩ := hgood (2 * n) ε (by positivity) hε hε1
      refine ⟨4 * C' + 4, by positivity, fun B => ?_⟩
      rcases hcase with hW | ⟨B₀, hB₀⟩
      · -- case 2n ≤ w
        obtain ⟨P, hPd, hPirr, hPprim, hPB, hPval⟩ := hgoodP (max B K)
        obtain ⟨Q, hQ1, hQ0ne, hQ0N, hQ0min, hdeg, hli, hcop, hmono, hprod, hval⟩ :=
          hfam P hPd hPirr hPprim (le_trans (le_max_right _ _) hPB)
        refine ⟨Q, hdeg, hli, hcop, hQ1 ▸ le_trans (le_max_left _ _) hPB, hmono, fun i hi => ?_⟩
        have hN0 : 1 ≤ N (Q 0) := L_config_N_ge_one N hN _ hQ0ne
        have hNj : ∀ j ∈ Finset.Icc 1 n, 1 ≤ N (Q j) := fun j hj =>
          le_trans hN0 (hmono 0 j (Nat.zero_le _) (Finset.mem_Icc.mp hj).2)
        have hPiprod : 0 < ∏ j ∈ Finset.Icc 1 n, N (Q j) :=
          Finset.prod_pos (fun j hj => lt_of_lt_of_le one_pos (hNj j hj))
        have hN1 : 1 ≤ N (Q 1) := hNj 1 (Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩)
        have hM0 : 0 ≤ max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ)))) :=
          le_trans (Real.rpow_nonneg (by linarith) _) (le_max_right _ _)
        have hδ : |Polynomial.aeval ξ (Q 0)| ≤ C' *
            max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ)))) := by
          have h1 : |Polynomial.aeval ξ (Q 0)| ≤ C' / ∏ j ∈ Finset.Icc 1 n, N (Q j) := by
            rw [le_div_iff₀ hPiprod]; exact hprod
          have h2 : C' / ∏ j ∈ Finset.Icc 1 n, N (Q j) ≤
              C' * (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) := by
            rw [mul_div_assoc']
            apply div_le_div_of_nonneg_right _ hPiprod.le
            exact le_mul_of_one_le_right hC'.le (Real.one_le_rpow hN1 hε.le)
          exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left (le_max_left _ _) hC'.le))
        have hP : |Polynomial.aeval ξ (Q 1)| ≤
            max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ)))) := by
          have h1 : |Polynomial.aeval ξ (Q 1)| ≤ N (Q 1) ^ (-w) := by rw [hQ1]; exact hPval
          have h2 : N (Q 1) ^ (-w) ≤ N (Q 1) ^ (-(2 * (n : ℝ))) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
          exact le_trans h1 (le_trans h2 (le_max_right _ _))
        calc |Polynomial.aeval ξ (Q i)| ≤ 4 * max |Polynomial.aeval ξ (Q 0)| |Polynomial.aeval ξ (Q 1)| :=
              hval i hi
          _ ≤ 4 * (C' * max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ))))
                + max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ))))) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              apply max_le
              · linarith
              · nlinarith
          _ = _ := by ring
      · -- case ∃ B₀ (lower bound exponent w+ε)
        -- GAP T: threshold B' (depends on B₀, K, CD from L_config_dirichlet, m₀ from L_config_minpoint
        -- at max B₀ 1 + L_config_aeval_ne_zero) s.t. B' ≤ N P ⇒ minimal Q0 at scale N P / K has B₀ ≤ N Q0.
        have hthr : ∃ B' : ℝ, K ≤ B' ∧ ∀ P Q0 : Polynomial ℤ, B' ≤ N P → Q0 ≠ 0 → Q0.natDegree ≤ n →
            N Q0 ≤ N P / K → (∀ R : Polynomial ℤ, R ≠ 0 → R.natDegree ≤ n → N R ≤ N P / K →
              |Polynomial.aeval ξ Q0| ≤ |Polynomial.aeval ξ R|) → B₀ ≤ N Q0 := by
          obtain ⟨CD, hCD, hdir⟩ := L_config_dirichlet n ξ N hN hmii
          obtain ⟨Q₀', hQ₀'ne, hQ₀'d, -, hQ₀'min⟩ :=
            L_config_minpoint n ξ N hN (max B₀ 1) (le_max_right _ _)
          have hm₀ : 0 < |Polynomial.aeval ξ Q₀'| := abs_pos.mpr (L_config_aeval_ne_zero ξ hξ _ hQ₀'ne)
          set m₀ := |Polynomial.aeval ξ Q₀'| with hm₀def
          set H₁ := max (max B₀ 1) (CD / m₀ + 1) with hH₁
          have hH₁1 : 1 ≤ H₁ := le_trans (le_max_right _ _) (le_max_left _ _)
          have hK0 : 0 < K := by linarith
          refine ⟨K * H₁, le_mul_of_one_le_right hK0.le hH₁1, fun P Q0 hPB hQ0 hQ0d hQ0N hQ0min => ?_⟩
          have hHge : H₁ ≤ N P / K := by rw [le_div_iff₀ hK0]; linarith [mul_comm K H₁]
          have hH1 : 1 ≤ N P / K := le_trans hH₁1 hHge
          by_contra hlt
          push_neg at hlt
          have hδ : m₀ ≤ |Polynomial.aeval ξ Q0| :=
            hQ₀'min Q0 hQ0 hQ0d (le_trans hlt.le (le_max_left _ _))
          obtain ⟨R, hRne, hRd, hRN, hRv⟩ := hdir (N P / K) hH1
          have hδR := hQ0min R hRne hRd hRN
          have hpow : (N P / K) ^ (-(n : ℝ)) ≤ (N P / K)⁻¹ := by
            rw [← Real.rpow_neg_one]
            exact Real.rpow_le_rpow_of_exponent_le hH1 (by
              have : (2 : ℝ) ≤ n := by exact_mod_cast hn
              linarith)
          have hHpos : 0 < N P / K := by linarith
          have hbig : CD / m₀ + 1 ≤ N P / K := le_trans (le_max_right _ _) hHge
          have hlt2 : CD * (N P / K)⁻¹ < m₀ := by
            rw [← div_eq_mul_inv, div_lt_iff₀ hHpos]
            have : CD / m₀ < N P / K := by linarith
            rw [div_lt_iff₀ hm₀] at this
            linarith
          have := le_trans hδ (le_trans hδR (le_trans hRv (mul_le_mul_of_nonneg_left hpow hCD.le)))
          linarith
        obtain ⟨B', hB'K, hB'⟩ := hthr
        obtain ⟨P, hPd, hPirr, hPprim, hPB, hPval⟩ := hgoodP (max B B')
        obtain ⟨Q, hQ1, hQ0ne, hQ0N, hQ0min, hdeg, hli, hcop, hmono, hprod, hval⟩ :=
          hfam P hPd hPirr hPprim (le_trans hB'K (le_trans (le_max_right _ _) hPB))
        have hQ0B : B₀ ≤ N (Q 0) := hB' P (Q 0) (le_trans (le_max_right _ _) hPB) hQ0ne (hdeg 0) hQ0N hQ0min
        refine ⟨Q, hdeg, hli, hcop, hQ1 ▸ le_trans (le_max_left _ _) hPB, hmono, fun i hi => ?_⟩
        have hN0 : 1 ≤ N (Q 0) := L_config_N_ge_one N hN _ hQ0ne
        have hNj : ∀ j ∈ Finset.Icc 1 n, 1 ≤ N (Q j) := fun j hj =>
          le_trans hN0 (hmono 0 j (Nat.zero_le _) (Finset.mem_Icc.mp hj).2)
        have hPiprod : 0 < ∏ j ∈ Finset.Icc 1 n, N (Q j) :=
          Finset.prod_pos (fun j hj => lt_of_lt_of_le one_pos (hNj j hj))
        have hN1 : 1 ≤ N (Q 1) := hNj 1 (Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩)
        have hM0 : 0 ≤ max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ)))) :=
          le_trans (Real.rpow_nonneg (by linarith) _) (le_max_right _ _)
        have h1 : |Polynomial.aeval ξ (Q 0)| ≤ C' / ∏ j ∈ Finset.Icc 1 n, N (Q j) := by
          rw [le_div_iff₀ hPiprod]; exact hprod
        have h2 : C' / ∏ j ∈ Finset.Icc 1 n, N (Q j) ≤
            C' * (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) := by
          rw [mul_div_assoc']
          apply div_le_div_of_nonneg_right _ hPiprod.le
          exact le_mul_of_one_le_right hC'.le (Real.one_le_rpow hN1 hε.le)
        have hQ01 : N (Q 0) ≤ N (Q 1) := hmono 0 1 (by omega) (by omega)
        have hP : |Polynomial.aeval ξ (Q 1)| ≤ max |Polynomial.aeval ξ (Q 0)|
            (C' * (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j))) := by
          have hPv : |Polynomial.aeval ξ (Q 1)| ≤ N (Q 1) ^ (-w) := by rw [hQ1]; exact hPval
          have hlow : N (Q 1) ^ (-(w + ε)) ≤ |Polynomial.aeval ξ (Q 0)| := by
            refine le_trans ?_ (hB₀ (Q 0) hQ0ne (hdeg 0) hQ0B)
            rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
            exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
              (Real.rpow_le_rpow (by linarith) hQ01 (by linarith))
          have hsplit : N (Q 1) ^ (-w) = N (Q 1) ^ ε * N (Q 1) ^ (-(w + ε)) := by
            rw [← Real.rpow_add (by linarith)]; congr 1; ring
          refine le_max_of_le_right ?_
          calc |Polynomial.aeval ξ (Q 1)| ≤ N (Q 1) ^ ε * N (Q 1) ^ (-(w + ε)) := hsplit ▸ hPv
            _ ≤ N (Q 1) ^ ε * (C' / ∏ j ∈ Finset.Icc 1 n, N (Q j)) :=
              mul_le_mul_of_nonneg_left (le_trans hlow h1) (Real.rpow_nonneg (by linarith) _)
            _ = _ := by ring
        have hδ : |Polynomial.aeval ξ (Q 0)| ≤ C' *
            max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ)))) :=
          le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left (le_max_left _ _) hC'.le))
        have hP' : |Polynomial.aeval ξ (Q 1)| ≤ C' *
            max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ)))) :=
          le_trans hP (max_le hδ (mul_le_mul_of_nonneg_left (le_max_left _ _) hC'.le))
        calc |Polynomial.aeval ξ (Q i)| ≤ 4 * max |Polynomial.aeval ξ (Q 0)| |Polynomial.aeval ξ (Q 1)| :=
              hval i hi
          _ ≤ 4 * (C' * max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ))))
                + max (N (Q 1) ^ ε / ∏ j ∈ Finset.Icc 1 n, N (Q j)) (N (Q 1) ^ (-(2 * (n : ℝ))))) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              apply max_le
              · linarith
              · linarith
          _ = _ := by ring
    )
  have L_det2_coeff_le : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (p : Polynomial ℤ) (k : ℕ), |((p.coeff k : ℤ) : ℝ)| ≤ N p :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (p : Polynomial ℤ) (k : ℕ) => by
      rw [hN]
      have h1 : (p.coeff k).natAbs ≤ p.support.sup fun i => (p.coeff i).natAbs := by
        by_cases hk : k ∈ p.support
        · exact Finset.le_sup (f := fun i => (p.coeff i).natAbs) hk
        · rw [Polynomial.notMem_support_iff.mp hk, Int.natAbs_zero]
          exact Nat.zero_le _
      have h2 : |((p.coeff k : ℤ) : ℝ)| = (((p.coeff k).natAbs : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [h2]
      exact_mod_cast h1
    )
  have L_det2_taylor_bound : ∀ (M : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (T : Polynomial ℤ) (i : ℕ), |∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) * ((T.coeff k : ℤ) : ℝ) * ξ ^ (k - i)|
        ≤ (∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) * |ξ| ^ (k - i)) * N T :=
    (fun (M : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (T : Polynomial ℤ) (i : ℕ) => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast]
      have hc := L_det2_coeff_le N hN T k
      have h0 : (0:ℝ) ≤ ((k.choose i : ℕ) : ℝ) * |ξ| ^ (k - i) :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (abs_nonneg _) _)
      calc ((k.choose i : ℕ) : ℝ) * |((T.coeff k : ℤ) : ℝ)| * |ξ| ^ (k - i)
          = (((k.choose i : ℕ) : ℝ) * |ξ| ^ (k - i)) * |((T.coeff k : ℤ) : ℝ)| := by ring
        _ ≤ (((k.choose i : ℕ) : ℝ) * |ξ| ^ (k - i)) * N T := mul_le_mul_of_nonneg_left hc h0
    )
  have L_det2_y0 : ∀ (M : ℕ) (ξ : ℝ) (T : Polynomial ℤ) (hT : T.natDegree ≤ M), ∑ k ∈ Finset.range (M + 1), ((k.choose 0 : ℕ) : ℝ) * ((T.coeff k : ℤ) : ℝ) * ξ ^ (k - 0)
        = Polynomial.aeval ξ T :=
    (fun (M : ℕ) (ξ : ℝ) (T : Polynomial ℤ) (hT : T.natDegree ≤ M) => by
      rw [Polynomial.aeval_eq_sum_range' (n := M + 1) (Nat.lt_succ_of_le hT)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul, zsmul_eq_mul]
    )
  have L_det2_y1 : ∀ (M : ℕ) (ξ : ℝ) (T : Polynomial ℤ) (hT : T.natDegree ≤ M), ∑ k ∈ Finset.range (M + 1), ((k.choose 1 : ℕ) : ℝ) * ((T.coeff k : ℤ) : ℝ) * ξ ^ (k - 1)
        = Polynomial.aeval ξ (Polynomial.derivative T) :=
    (fun (M : ℕ) (ξ : ℝ) (T : Polynomial ℤ) (hT : T.natDegree ≤ M) => by
      have hd : (Polynomial.derivative T).natDegree < M + 1 := by
        have := Polynomial.natDegree_derivative_le T
        omega
      rw [Polynomial.aeval_eq_sum_range' hd]
      conv_lhs => rw [Finset.sum_range_succ']
      conv_rhs => rw [Finset.sum_range_succ]
      have htop : (Polynomial.derivative T).coeff M = 0 := by
        rw [Polynomial.coeff_derivative, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
          zero_mul]
      rw [htop, zero_smul, add_zero, Nat.choose_one_right 0, Nat.cast_zero, zero_mul, zero_mul,
        add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.coeff_derivative, Nat.choose_one_right, Nat.add_sub_cancel, zsmul_eq_mul]
      push_cast
      ring
    )
  have L_det2_y_lin : ∀ (M : ℕ) (ξ : ℝ) (S : Fin (M + 1) → Polynomial ℤ) (c : Fin (M + 1) → ℕ)
      (i : ℕ), ∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) *
          (((∑ j, Polynomial.C ((c j : ℤ)) * S j).coeff k : ℤ) : ℝ) * ξ ^ (k - i)
        = ∑ j, (c j : ℝ) * ∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) *
          (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - i) :=
    (fun (M : ℕ) (ξ : ℝ) (S : Fin (M + 1) → Polynomial ℤ) (c : Fin (M + 1) → ℕ)
        (i : ℕ) => by
      simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Int.cast_sum, Int.cast_mul,
        Int.cast_natCast, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    )
  have L_det2_floor_inj : ∀ (M : ℕ) (ξ : ℝ) (T T' : Polynomial ℤ) (hT : T.natDegree ≤ M)
      (hT' : T'.natDegree ≤ M)
      (h : ∀ i : Fin (M + 1),
        ⌊∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) * ((T.coeff k : ℤ) : ℝ) * ξ ^ (k - i)⌋ =
        ⌊∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) * ((T'.coeff k : ℤ) : ℝ) * ξ ^ (k - i)⌋), T = T' :=
    (fun (M : ℕ) (ξ : ℝ) (T T' : Polynomial ℤ) (hT : T.natDegree ≤ M)
        (hT' : T'.natDegree ≤ M)
        (h : ∀ i : Fin (M + 1),
          ⌊∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) * ((T.coeff k : ℤ) : ℝ) * ξ ^ (k - i)⌋ =
          ⌊∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) * ((T'.coeff k : ℤ) : ℝ) * ξ ^ (k - i)⌋) => by
      have hdiff : ∀ i : Fin (M + 1),
          |∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) *
              (((T.coeff k - T'.coeff k : ℤ)) : ℝ) * ξ ^ (k - i)| < 1 := by
        intro i
        have h1 := Int.abs_sub_lt_one_of_floor_eq_floor (h i)
        have h2 : ∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) *
              (((T.coeff k - T'.coeff k : ℤ)) : ℝ) * ξ ^ (k - i)
            = (∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) * ((T.coeff k : ℤ) : ℝ) *
                ξ ^ (k - i)) -
              (∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) * ((T'.coeff k : ℤ) : ℝ) *
                ξ ^ (k - i)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro k _
          push_cast
          ring
        rw [h2]
        exact h1
      have key : ∀ t : ℕ, ∀ k : ℕ, M + 1 ≤ k + t → T.coeff k = T'.coeff k := by
        intro t
        induction t with
        | zero =>
          intro k hk
          have hk' : M < k := by omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hT hk'),
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hT' hk')]
        | succ t ih =>
          intro k hk
          by_cases hk2 : M + 1 ≤ k + t
          · exact ih k hk2
          · have hkM : k < M + 1 := by omega
            have hd : |∑ j ∈ Finset.range (M + 1), ((j.choose k : ℕ) : ℝ) *
                (((T.coeff j - T'.coeff j : ℤ)) : ℝ) * ξ ^ (j - k)| < 1 := hdiff ⟨k, hkM⟩
            have hsum : ∑ j ∈ Finset.range (M + 1), ((j.choose k : ℕ) : ℝ) *
                (((T.coeff j - T'.coeff j : ℤ)) : ℝ) * ξ ^ (j - k)
                = (((T.coeff k - T'.coeff k : ℤ)) : ℝ) := by
              rw [Finset.sum_eq_single k]
              · simp
              · intro j _ hjk
                rcases lt_or_gt_of_ne hjk with hlt | hgt
                · rw [Nat.choose_eq_zero_of_lt hlt]
                  simp
                · have hj : T.coeff j = T'.coeff j := ih j (by omega)
                  rw [hj, sub_self]
                  simp
              · intro hk'
                exact absurd (Finset.mem_range.mpr hkM) hk'
            rw [hsum] at hd
            have hz : |(T.coeff k - T'.coeff k : ℤ)| < 1 := by
              exact_mod_cast hd
            have hz' := Int.abs_lt_one_iff.mp hz
            omega
      ext k
      exact key (M + 1) k (by omega)
    )
  have L_det2_comb_inj : ∀ (M : ℕ) (S : Fin (M + 1) → Polynomial ℤ)
      (hli : LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)))
      (c c' : Fin (M + 1) → ℕ)
      (h : ∑ j, Polynomial.C ((c j : ℤ)) * S j = ∑ j, Polynomial.C ((c' j : ℤ)) * S j), c = c' :=
    (fun (M : ℕ) (S : Fin (M + 1) → Polynomial ℤ)
        (hli : LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)))
        (c c' : Fin (M + 1) → ℕ)
        (h : ∑ j, Polynomial.C ((c j : ℤ)) * S j = ∑ j, Polynomial.C ((c' j : ℤ)) * S j) => by
      have h1 := congrArg (Polynomial.map (Int.castRingHom ℚ)) h
      simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C] at h1
      simp only [Int.coe_castRingHom, Int.cast_natCast] at h1
      have h2 : ∑ j, (((c j : ℚ) - (c' j : ℚ))) • (S j).map (Int.castRingHom ℚ) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, Polynomial.smul_eq_C_mul]
        rw [sub_eq_zero]
        exact h1
      have h3 := Fintype.linearIndependent_iff.mp hli _ h2
      funext j
      have h4 := h3 j
      have h5 : (c j : ℚ) = (c' j : ℚ) := by linarith
      exact_mod_cast h5
    )
  have L_det2_B_factor : ∀ (W : ℝ) (hW : 0 ≤ W), (((⌊W⌋ + 1 - ⌊-W⌋).toNat : ℕ) : ℝ) ≤ 2 * W + 2 :=
    (fun (W : ℝ) (hW : 0 ≤ W) => by
      have h1 : (⌊W⌋ : ℝ) ≤ W := Int.floor_le W
      have h2 : -W - 1 < (⌊-W⌋ : ℝ) := Int.sub_one_lt_floor (-W)
      have h3 : (0 : ℤ) ≤ ⌊W⌋ := Int.floor_nonneg.mpr hW
      have h4 : ⌊-W⌋ ≤ 0 := Int.floor_nonpos (by linarith)
      have hnn : (0 : ℤ) ≤ ⌊W⌋ + 1 - ⌊-W⌋ := by omega
      have hc : (((⌊W⌋ + 1 - ⌊-W⌋).toNat : ℕ) : ℝ) = ((⌊W⌋ + 1 - ⌊-W⌋ : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
      rw [hc]
      push_cast
      linarith
    )
  have L_det2_count : ∀ (M : ℕ) (ξ : ℝ) (S : Fin (M + 1) → Polynomial ℤ)
      (hdeg : ∀ j, (S j).natDegree ≤ M)
      (hli : LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)))
      (Bn : Fin (M + 1) → ℕ), (∏ j, (Bn j : ℝ)) ≤ ∏ i : Fin (M + 1),
        (2 * ∑ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M + 1), ((k.choose i : ℕ) : ℝ) *
          (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - i)| + 2) :=
    (fun (M : ℕ) (ξ : ℝ) (S : Fin (M + 1) → Polynomial ℤ)
        (hdeg : ∀ j, (S j).natDegree ≤ M)
        (hli : LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)))
        (Bn : Fin (M + 1) → ℕ) => by
      classical
      set W : Fin (M + 1) → ℝ := fun i => ∑ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M + 1),
        ((k.choose (i : ℕ) : ℕ) : ℝ) * (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))| with hW
      have hW0 : ∀ i, 0 ≤ W i := fun i =>
        Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
      set A := Fintype.piFinset (fun j : Fin (M + 1) => Finset.range (Bn j)) with hA
      set Box := Fintype.piFinset (fun i : Fin (M + 1) => Finset.Icc ⌊-W i⌋ ⌊W i⌋) with hBox
      set φ : (Fin (M + 1) → ℕ) → (Fin (M + 1) → ℤ) := fun c i =>
        ⌊∑ k ∈ Finset.range (M + 1), ((k.choose (i : ℕ) : ℕ) : ℝ) *
          (((∑ j, Polynomial.C ((c j : ℤ)) * S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))⌋ with hφ
      have hmaps : ∀ c ∈ A, φ c ∈ Box := by
        intro c hc
        rw [hA, Fintype.mem_piFinset] at hc
        rw [hBox, Fintype.mem_piFinset]
        intro i
        have hy := L_det2_y_lin M ξ S c (i : ℕ)
        have hbound : |∑ k ∈ Finset.range (M + 1), ((k.choose (i : ℕ) : ℕ) : ℝ) *
            (((∑ j, Polynomial.C ((c j : ℤ)) * S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))| ≤ W i := by
          rw [hy]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          have := hc j
          rw [Finset.mem_range] at this
          exact_mod_cast this.le
        rw [Finset.mem_Icc]
        have h1 := abs_le.mp hbound
        exact ⟨Int.floor_mono h1.1, Int.floor_mono h1.2⟩
      have hdegc : ∀ c : Fin (M + 1) → ℕ,
          (∑ j, Polynomial.C ((c j : ℤ)) * S j).natDegree ≤ M := by
        intro c
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro j _
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) (hdeg j)
      have hinj : Set.InjOn φ A := by
        intro c _ c' _ h
        apply L_det2_comb_inj M S hli c c'
        apply L_det2_floor_inj M ξ _ _ (hdegc c) (hdegc c')
        intro i
        exact congrFun h i
      have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
      rw [hA, hBox, Fintype.card_piFinset, Fintype.card_piFinset] at hcard
      simp only [Finset.card_range, Int.card_Icc] at hcard
      have hcardR : ((∏ j, Bn j : ℕ) : ℝ) ≤ ((∏ i, (⌊W i⌋ + 1 - ⌊-W i⌋).toNat : ℕ) : ℝ) := by
        exact_mod_cast hcard
      rw [Nat.cast_prod, Nat.cast_prod] at hcardR
      refine le_trans hcardR ?_
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.cast_nonneg _
      · intro i _
        exact L_det2_B_factor (W i) (hW0 i)
    )
  have L_det2_C_key : ∀ (P a b e B : ℝ) (k : ℕ) (hP : 0 < P) (hB : 0 < B)
      (h1 : B ^ (k + 2) / P ≤ (a * B + 2) * (b * B + 2) * (e * B + 2) ^ k), 1 / P ≤ (a + 2 / B) * (b + 2 / B) * (e + 2 / B) ^ k :=
    (fun (P a b e B : ℝ) (k : ℕ) (hP : 0 < P) (hB : 0 < B)
        (h1 : B ^ (k + 2) / P ≤ (a * B + 2) * (b * B + 2) * (e * B + 2) ^ k) => by
      have hB' : B ≠ 0 := ne_of_gt hB
      have hBk : 0 < B ^ (k + 2) := pow_pos hB _
      have e1 : a * B + 2 = B * (a + 2 / B) := by
        rw [mul_add, mul_div_cancel₀ (2 : ℝ) hB', mul_comm]
      have e2 : b * B + 2 = B * (b + 2 / B) := by
        rw [mul_add, mul_div_cancel₀ (2 : ℝ) hB', mul_comm]
      have e3 : e * B + 2 = B * (e + 2 / B) := by
        rw [mul_add, mul_div_cancel₀ (2 : ℝ) hB', mul_comm]
      have eq : (a * B + 2) * (b * B + 2) * (e * B + 2) ^ k
          = B ^ (k + 2) * ((a + 2 / B) * (b + 2 / B) * (e + 2 / B) ^ k) := by
        rw [e1, e2, e3, mul_pow]
        ring
      rw [eq, div_le_iff₀ hP] at h1
      rw [div_le_iff₀ hP]
      have h2 : B ^ (k + 2) * 1 ≤ B ^ (k + 2) * ((a + 2 / B) * (b + 2 / B) * (e + 2 / B) ^ k * P) := by
        rw [mul_one]
        calc B ^ (k + 2) ≤ B ^ (k + 2) * ((a + 2 / B) * (b + 2 / B) * (e + 2 / B) ^ k) * P := h1
          _ = B ^ (k + 2) * ((a + 2 / B) * (b + 2 / B) * (e + 2 / B) ^ k * P) := by ring
      exact le_of_mul_le_mul_left h2 hBk
    )
  have L_det2_limit : ∀ (P a b e B0 : ℝ) (k : ℕ) (hP : 0 < P)
      (h : ∀ B : ℝ, B0 ≤ B → 0 < B →
        B ^ (k + 2) / P ≤ (a * B + 2) * (b * B + 2) * (e * B + 2) ^ k), 1 ≤ P * (a * b * e ^ k) :=
    (fun (P a b e B0 : ℝ) (k : ℕ) (hP : 0 < P)
        (h : ∀ B : ℝ, B0 ≤ B → 0 < B →
          B ^ (k + 2) / P ≤ (a * B + 2) * (b * B + 2) * (e * B + 2) ^ k) => by
      have h0 : Filter.Tendsto (fun B : ℝ => 2 / B) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop Filter.tendsto_id
      have hc : ∀ x : ℝ, Filter.Tendsto (fun B : ℝ => x + 2 / B) Filter.atTop (nhds x) := by
        intro x
        have := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => x) Filter.atTop (nhds x)).add h0
        rwa [add_zero] at this
      have hlim : Filter.Tendsto (fun B : ℝ => (a + 2 / B) * (b + 2 / B) * (e + 2 / B) ^ k)
          Filter.atTop (nhds (a * b * e ^ k)) :=
        ((hc a).mul (hc b)).mul ((hc e).pow k)
      have hev : ∀ᶠ B in Filter.atTop, 1 / P ≤ (a + 2 / B) * (b + 2 / B) * (e + 2 / B) ^ k := by
        rw [Filter.eventually_atTop]
        refine ⟨max B0 1, fun B hB => ?_⟩
        have hB0 : B0 ≤ B := le_trans (le_max_left _ _) hB
        have hBpos : 0 < B := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hB)
        exact L_det2_C_key P a b e B k hP hBpos (h B hB0 hBpos)
      have h1 : 1 / P ≤ a * b * e ^ k := ge_of_tendsto hlim hev
      rw [div_le_iff₀ hP] at h1
      rw [mul_comm]
      exact h1
    )
  have L_det2 : ∀ (M : ℕ) (hM : 1 ≤ M) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)), ∃ C : ℝ, 0 < C ∧ ∀ S : Fin (M + 1) → Polynomial ℤ, (∀ j, (S j).natDegree ≤ M) →
        LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)) →
        ∀ δ μ ν : ℝ, (∀ j, |Polynomial.aeval ξ (S j)| ≤ δ) →
          (∀ j, |Polynomial.aeval ξ (Polynomial.derivative (S j))| ≤ μ * N (S j)) →
          (∀ j, ν ≤ N (S j)) → 0 < ν →
          1 ≤ C * δ * μ * (∏ j, N (S j)) / ν :=
    (fun (M : ℕ) (hM : 1 ≤ M) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) => by
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      set m1 : ℝ := ((M' + 1 + 1 : ℕ) : ℝ) with hm1
      have hm1pos : 0 < m1 := by rw [hm1]; positivity
      set c : ℝ := 1 + ∑ i : Fin (M' + 1 + 1), ∑ k ∈ Finset.range (M' + 1 + 1),
          ((k.choose (i : ℕ) : ℕ) : ℝ) * |ξ| ^ (k - (i : ℕ)) with hc
      have hci : ∀ i : Fin (M' + 1 + 1), ∑ k ∈ Finset.range (M' + 1 + 1),
          ((k.choose (i : ℕ) : ℕ) : ℝ) * |ξ| ^ (k - (i : ℕ)) ≤ c := by
        intro i
        have hnn : ∀ i' : Fin (M' + 1 + 1), 0 ≤ ∑ k ∈ Finset.range (M' + 1 + 1),
            ((k.choose (i' : ℕ) : ℕ) : ℝ) * |ξ| ^ (k - (i' : ℕ)) := fun i' =>
          Finset.sum_nonneg (fun k _ => by positivity)
        have := Finset.single_le_sum (f := fun i' : Fin (M' + 1 + 1) => ∑ k ∈ Finset.range (M' + 1 + 1),
            ((k.choose (i' : ℕ) : ℕ) : ℝ) * |ξ| ^ (k - (i' : ℕ))) (fun i' _ => hnn i') (Finset.mem_univ i)
        rw [hc]; linarith
      have hcpos : 0 < c := by
        rw [hc]
        have : 0 ≤ ∑ i : Fin (M' + 1 + 1), ∑ k ∈ Finset.range (M' + 1 + 1),
          ((k.choose (i : ℕ) : ℕ) : ℝ) * |ξ| ^ (k - (i : ℕ)) :=
          Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => by positivity))
        linarith
      refine ⟨(4 * m1) ^ 2 * (4 * m1 * c) ^ M', by positivity, ?_⟩
      intro S hdeg hli δ μ ν hδ hμ hν hν0
      have hNpos : ∀ j, 0 < N (S j) := fun j => lt_of_lt_of_le hν0 (hν j)
      have hP : 0 < ∏ j, N (S j) := Finset.prod_pos (fun j _ => hNpos j)
      have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ 0)
      have hμ0 : 0 ≤ μ := by
        by_contra hneg
        push_neg at hneg
        have h1 := mul_neg_of_neg_of_pos hneg (hNpos 0)
        have h2 := hμ 0
        linarith [abs_nonneg (Polynomial.aeval ξ (Polynomial.derivative (S 0)))]
      have hrw : (4 * m1) ^ 2 * (4 * m1 * c) ^ M' * δ * μ * (∏ j, N (S j)) / ν
          = (∏ j, N (S j)) * ((4 * m1 * δ / ν) * (4 * m1 * μ) * (4 * m1 * c) ^ M') := by
        field_simp
      rw [hrw]
      apply L_det2_limit (∏ j, N (S j)) (4 * m1 * δ / ν) (4 * m1 * μ) (4 * m1 * c)
        (∑ j, N (S j)) M' hP
      intro B hB hBpos
      have hNB : ∀ j, N (S j) ≤ B := fun j => le_trans
        (Finset.single_le_sum (f := fun j => N (S j)) (fun j _ => (hNpos j).le) (Finset.mem_univ j)) hB
      set Bn : Fin (M' + 1 + 1) → ℕ := fun j => ⌈B / N (S j)⌉₊ with hBn
      have hBn_ge : ∀ j, B / N (S j) ≤ (Bn j : ℝ) := fun j => Nat.le_ceil _
      have hBn_le : ∀ j, (Bn j : ℝ) ≤ 2 * B / N (S j) := by
        intro j
        have h1 : (Bn j : ℝ) < B / N (S j) + 1 :=
          Nat.ceil_lt_add_one (div_nonneg hBpos.le (hNpos j).le)
        have h2 : 1 ≤ B / N (S j) := (one_le_div (hNpos j)).mpr (hNB j)
        have h3 : 2 * B / N (S j) = B / N (S j) + B / N (S j) := by ring
        linarith
      have hcount := L_det2_count (M' + 1) ξ S hdeg hli Bn
      have hlow : B ^ (M' + 2) / (∏ j, N (S j)) ≤ ∏ j, (Bn j : ℝ) := by
        have : B ^ (M' + 2) / (∏ j, N (S j)) = ∏ j, (B / N (S j)) := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [this]
        exact Finset.prod_le_prod (fun j _ => div_nonneg hBpos.le (hNpos j).le) (fun j _ => hBn_ge j)
      -- per-row bounds
      have hrow0 : 2 * ∑ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
          ((k.choose ((0 : Fin (M' + 1 + 1)) : ℕ) : ℕ) : ℝ) *
            (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - ((0 : Fin (M' + 1 + 1)) : ℕ))| + 2
          ≤ 4 * m1 * δ / ν * B + 2 := by
        have hj : ∀ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
            ((k.choose ((0 : Fin (M' + 1 + 1)) : ℕ) : ℕ) : ℝ) *
              (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - ((0 : Fin (M' + 1 + 1)) : ℕ))| ≤ 2 * B / ν * δ := by
          intro j
          rw [Fin.val_zero, L_det2_y0 (M' + 1) ξ (S j) (hdeg j)]
          calc (Bn j : ℝ) * |Polynomial.aeval ξ (S j)| ≤ (2 * B / N (S j)) * δ :=
                mul_le_mul (hBn_le j) (hδ j) (abs_nonneg _) (by have := hNpos j; positivity)
            _ ≤ 2 * B / ν * δ := by
                apply mul_le_mul_of_nonneg_right _ hδ0
                exact div_le_div_of_nonneg_left (by positivity) hν0 (hν j)
        have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
        have : 2 * (((M' + 1 + 1 : ℕ) : ℝ) * (2 * B / ν * δ)) + 2 = 4 * m1 * δ / ν * B + 2 := by
          rw [hm1]; ring
        linarith
      have hrow1 : 2 * ∑ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
          ((k.choose ((Fin.succ (0 : Fin (M' + 1))) : ℕ) : ℕ) : ℝ) *
            (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - ((Fin.succ (0 : Fin (M' + 1))) : ℕ))| + 2
          ≤ 4 * m1 * μ * B + 2 := by
        have hj : ∀ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
            ((k.choose ((Fin.succ (0 : Fin (M' + 1))) : ℕ) : ℕ) : ℝ) *
              (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - ((Fin.succ (0 : Fin (M' + 1))) : ℕ))| ≤ 2 * B * μ := by
          intro j
          rw [Fin.val_succ, Fin.val_zero, zero_add, L_det2_y1 (M' + 1) ξ (S j) (hdeg j)]
          calc (Bn j : ℝ) * |Polynomial.aeval ξ (Polynomial.derivative (S j))|
                ≤ (2 * B / N (S j)) * (μ * N (S j)) :=
                mul_le_mul (hBn_le j) (hμ j) (abs_nonneg _) (by have := hNpos j; positivity)
            _ = 2 * B * μ := by have := (hNpos j).ne'; field_simp
        have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
        have : 2 * (((M' + 1 + 1 : ℕ) : ℝ) * (2 * B * μ)) + 2 = 4 * m1 * μ * B + 2 := by
          rw [hm1]; ring
        linarith
      have hrow2 : ∀ i : Fin (M' + 1 + 1), 2 * ∑ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
          ((k.choose (i : ℕ) : ℕ) : ℝ) *
            (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))| + 2
          ≤ 4 * m1 * c * B + 2 := by
        intro i
        have hj : ∀ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
            ((k.choose (i : ℕ) : ℕ) : ℝ) *
              (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))| ≤ 2 * B * c := by
          intro j
          have hb := L_det2_taylor_bound (M' + 1) ξ N hN (S j) (i : ℕ)
          have hb2 : |∑ k ∈ Finset.range (M' + 1 + 1),
            ((k.choose (i : ℕ) : ℕ) : ℝ) *
              (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))| ≤ c * N (S j) :=
            le_trans hb (mul_le_mul_of_nonneg_right (hci i) (hNpos j).le)
          calc (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
            ((k.choose (i : ℕ) : ℕ) : ℝ) *
              (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))|
                ≤ (2 * B / N (S j)) * (c * N (S j)) :=
                mul_le_mul (hBn_le j) hb2 (abs_nonneg _) (by have := hNpos j; positivity)
            _ = 2 * B * c := by have := (hNpos j).ne'; field_simp
        have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
        have : 2 * (((M' + 1 + 1 : ℕ) : ℝ) * (2 * B * c)) + 2 = 4 * m1 * c * B + 2 := by
          rw [hm1]; ring
        linarith
      have hnn : ∀ i : Fin (M' + 1 + 1), 0 ≤ 2 * ∑ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
          ((k.choose (i : ℕ) : ℕ) : ℝ) *
            (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))| + 2 := by
        intro i
        have : 0 ≤ ∑ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
          ((k.choose (i : ℕ) : ℕ) : ℝ) *
            (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))| :=
          Finset.sum_nonneg (fun j _ => by positivity)
        linarith
      have hup : ∏ i : Fin (M' + 1 + 1), (2 * ∑ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
          ((k.choose (i : ℕ) : ℕ) : ℝ) * (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - (i : ℕ))| + 2)
          ≤ (4 * m1 * δ / ν * B + 2) * (4 * m1 * μ * B + 2) * (4 * m1 * c * B + 2) ^ M' := by
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        have hrest : ∏ i : Fin M', (2 * ∑ j, (Bn j : ℝ) * |∑ k ∈ Finset.range (M' + 1 + 1),
            ((k.choose ((i.succ.succ : Fin (M' + 1 + 1)) : ℕ) : ℕ) : ℝ) *
              (((S j).coeff k : ℤ) : ℝ) * ξ ^ (k - ((i.succ.succ : Fin (M' + 1 + 1)) : ℕ))| + 2)
            ≤ (4 * m1 * c * B + 2) ^ M' := by
          have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin M')))
            (fun i _ => hnn i.succ.succ) (fun i _ => hrow2 i.succ.succ)
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
          exact this
        rw [mul_assoc]
        apply mul_le_mul hrow0 _ (mul_nonneg (hnn _) (Finset.prod_nonneg (fun i _ => hnn _)))
          (by have := hδ0; have := hν0; positivity)
        apply mul_le_mul hrow1 hrest (Finset.prod_nonneg (fun i _ => hnn _))
          (by positivity)
      linarith [hlow, hcount, hup]
    )
  have L_dim_aux : ∀ (m : ℕ), ∀ v : Fin (m + 1) → Polynomial ℚ,
      (∀ j k, m ≤ k → (v j).coeff k = 0) → ¬ LinearIndependent ℚ v :=
    (fun (m : ℕ) => by
      induction m with
      | zero =>
        intro v hv hli
        have h0 : v 0 = 0 := by
          ext k
          simpa using hv 0 k (Nat.zero_le k)
        exact hli.ne_zero 0 h0
      | succ m ih =>
        intro v hv hli
        by_cases hc : ∀ j, (v j).coeff m = 0
        · apply ih (fun i => v (Fin.castSucc i))
          · intro i k hk
            rcases Nat.eq_or_lt_of_le hk with h | h
            · subst h; exact hc _
            · exact hv _ k h
          · exact hli.comp _ (Fin.castSucc_injective _)
        · push_neg at hc
          obtain ⟨j0, hj0⟩ := hc
          set c : Fin (m + 2) → ℚ := fun j => (v j).coeff m with hcdef
          set w : Fin (m + 1) → Polynomial ℚ :=
            fun i => v (j0.succAbove i) - (c (j0.succAbove i) / c j0) • v j0 with hwdef
          apply ih w
          · intro i k hk
            rcases Nat.eq_or_lt_of_le hk with h | h
            · subst h
              simp only [hwdef, hcdef, Polynomial.coeff_sub, Polynomial.coeff_smul, smul_eq_mul]
              field_simp
              ring
            · simp only [hwdef, Polynomial.coeff_sub, Polynomial.coeff_smul, smul_eq_mul,
                hv _ k h, mul_zero, sub_zero]
          · rw [Fintype.linearIndependent_iff] at hli ⊢
            intro g hg
            set a : ℚ := -(∑ i, g i * (c (j0.succAbove i) / c j0)) with hadef
            set G : Fin (m + 2) → ℚ := Fin.insertNth (α := fun _ => ℚ) j0 a g with hGdef
            have hsum : ∑ j, G j • v j = 0 := by
              rw [Fin.sum_univ_succAbove _ j0]
              simp only [hGdef, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
              rw [← hg]
              simp only [hwdef, hadef, smul_sub, smul_smul, Finset.sum_sub_distrib, neg_smul,
                Finset.sum_smul]
              abel
            intro i
            have := hli G hsum (j0.succAbove i)
            simpa [hGdef, Fin.insertNth_apply_succAbove] using this
    )
  have L_dim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ) (hv : ∀ j, (v j).natDegree < m), ¬ LinearIndependent ℚ v :=
    (fun (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ) (hv : ∀ j, (v j).natDegree < m) => by
      apply L_dim_aux m v
      intro j k hk
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hv j) hk)
    )
  have L_final : ∀ (n : ℕ) (ξ : ℝ)
      (h : ∀ ω : ℝ≥0, 0 < (ω : ℝ) → (ω : ℝ) < 1 / (2 - Real.log 2) * n → ω ∈ ω_stars n ξ), (ω⋆ n ξ : EReal) ≥ ((1 / (2 - Real.log 2) : ℝ) : EReal) * (n : EReal) :=
    (fun (n : ℕ) (ξ : ℝ)
        (h : ∀ ω : ℝ≥0, 0 < (ω : ℝ) → (ω : ℝ) < 1 / (2 - Real.log 2) * n → ω ∈ ω_stars n ξ) => by
      have hlog : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (x := (2:ℝ)) (by norm_num)
        linarith
      have hpos : 0 < 2 - Real.log 2 := by linarith
      have hc0 : 0 ≤ 1 / (2 - Real.log 2) * (n : ℝ) := by positivity
      have key : ENNReal.ofReal (1 / (2 - Real.log 2) * (n : ℝ)) ≤ ω⋆ n ξ := by
        apply le_of_forall_lt
        intro y hy
        obtain ⟨r, hyr, hrc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hy
        have hr0 : 0 < (r : ℝ) := by
          have h0 : (0:ℝ≥0∞) < r := lt_of_le_of_lt (zero_le _) hyr
          have h1 : (0:ℝ≥0) < r := ENNReal.coe_pos.1 h0
          exact_mod_cast h1
        have hrc' : (r : ℝ) < 1 / (2 - Real.log 2) * (n : ℝ) := by
          have := (ENNReal.lt_ofReal_iff_toReal_lt ENNReal.coe_ne_top).1 hrc
          simpa using this
        have hmem := h r hr0 hrc'
        calc y < (r : ℝ≥0∞) := hyr
          _ ≤ ω⋆ n ξ := le_sSup ⟨r, hmem, rfl⟩
      have h1 : ((1 / (2 - Real.log 2) : ℝ) : EReal) * (n : EReal)
          = (((1 / (2 - Real.log 2) * (n : ℝ)) : ℝ) : EReal) := by
        rw [EReal.coe_mul]; norm_cast
      rw [ge_iff_le, h1]
      have h2 : (((1 / (2 - Real.log 2) * (n : ℝ)) : ℝ) : EReal)
          = ((ENNReal.ofReal (1 / (2 - Real.log 2) * (n : ℝ)) : ℝ≥0∞) : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left hc0]
      rw [h2]
      exact EReal.coe_ennreal_le_coe_ennreal_iff.2 key
    )
  have L_fta_cont : ∀ (p : Polynomial ℂ), Continuous fun z : ℂ => p.eval z :=
    (fun (p : Polynomial ℂ) => by
      have h : (fun z : ℂ => p.eval z) =
          fun z => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i := by
        funext z; exact Polynomial.eval_eq_sum_range z
      rw [h]
      exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_pow i))
    )
  have L_fta_lower : ∀ (n : ℕ), ∀ p : Polynomial ℂ, p.natDegree = n → p ≠ 0 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → δ ≤ ‖p.eval z‖ :=
    (fun (n : ℕ) => by
      induction n with
      | zero =>
        intro p hn hp
        have hpc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
        have hc : p.coeff 0 ≠ 0 := by
          intro h; apply hp; rw [hpc, h, map_zero]
        refine ⟨‖p.coeff 0‖, norm_pos_iff.mpr hc, 0, fun z _ => ?_⟩
        rw [hpc, Polynomial.eval_C, Polynomial.coeff_C_zero]
      | succ n ih =>
        intro p hn hp
        have hq : p.divX.natDegree = n := by
          rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hn]; simp
        have hq0 : p.divX ≠ 0 := by
          intro h
          rw [Polynomial.divX_eq_zero_iff] at h
          rw [h, Polynomial.natDegree_C] at hn
          exact Nat.succ_ne_zero n hn.symm
        obtain ⟨δ, hδ, R, hR⟩ := ih p.divX hq hq0
        refine ⟨1, one_pos, max R ((1 + ‖p.coeff 0‖) / δ), fun z hz => ?_⟩
        have hz1 : R ≤ ‖z‖ := le_trans (le_max_left _ _) hz
        have hz2 : (1 + ‖p.coeff 0‖) / δ ≤ ‖z‖ := le_trans (le_max_right _ _) hz
        have h1 := hR z hz1
        have h2 : 1 + ‖p.coeff 0‖ ≤ δ * ‖z‖ := by
          rw [div_le_iff₀ hδ] at hz2; linarith
        have heq : p.eval z = p.divX.eval z * z + p.coeff 0 := by
          conv_lhs => rw [← Polynomial.divX_mul_X_add p]
          simp
        have h3 : ‖p.divX.eval z * z‖ ≤ ‖p.divX.eval z * z + p.coeff 0‖ + ‖p.coeff 0‖ := by
          have := norm_sub_le (p.divX.eval z * z + p.coeff 0) (p.coeff 0)
          simpa using this
        rw [norm_mul] at h3
        have h4 : δ * ‖z‖ ≤ ‖p.divX.eval z‖ * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg z)
        rw [heq]; linarith
    )
  have L_fta_coercive : ∀ (p : Polynomial ℂ) (hp : 0 < p.natDegree) (M : ℝ), ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → M ≤ ‖p.eval z‖ :=
    (fun (p : Polynomial ℂ) (hp : 0 < p.natDegree) (M : ℝ) => by
      have hq0 : p.divX ≠ 0 := by
        intro h
        rw [Polynomial.divX_eq_zero_iff] at h
        rw [h, Polynomial.natDegree_C] at hp
        exact lt_irrefl 0 hp
      obtain ⟨δ, hδ, R, hR⟩ := L_fta_lower _ p.divX rfl hq0
      refine ⟨max R ((M + ‖p.coeff 0‖) / δ), fun z hz => ?_⟩
      have hz1 : R ≤ ‖z‖ := le_trans (le_max_left _ _) hz
      have hz2 : (M + ‖p.coeff 0‖) / δ ≤ ‖z‖ := le_trans (le_max_right _ _) hz
      have h1 := hR z hz1
      have h2 : M + ‖p.coeff 0‖ ≤ δ * ‖z‖ := by
        rw [div_le_iff₀ hδ] at hz2; linarith
      have heq : p.eval z = p.divX.eval z * z + p.coeff 0 := by
        conv_lhs => rw [← Polynomial.divX_mul_X_add p]
        simp
      have h3 : ‖p.divX.eval z * z‖ ≤ ‖p.divX.eval z * z + p.coeff 0‖ + ‖p.coeff 0‖ := by
        have := norm_sub_le (p.divX.eval z * z + p.coeff 0) (p.coeff 0)
        simpa using this
      rw [norm_mul] at h3
      have h4 : δ * ‖z‖ ≤ ‖p.divX.eval z‖ * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg z)
      rw [heq]; linarith
    )
  have L_fta_exists_min : ∀ (p : Polynomial ℂ), ∃ z0 : ℂ, ∀ z : ℂ, ‖p.eval z0‖ ≤ ‖p.eval z‖ :=
    (fun (p : Polynomial ℂ) => by
      rcases Nat.eq_zero_or_pos p.natDegree with h | h
      · refine ⟨0, fun z => ?_⟩
        rw [Polynomial.eq_C_of_natDegree_eq_zero h]; simp
      · obtain ⟨R, hR⟩ := L_fta_coercive p h (‖p.eval 0‖ + 1)
        have hK : IsCompact (Metric.closedBall (0:ℂ) (max R 0)) := isCompact_closedBall _ _
        have h0K : (0:ℂ) ∈ Metric.closedBall (0:ℂ) (max R 0) :=
          Metric.mem_closedBall_self (le_max_right _ _)
        obtain ⟨z0, _, hmin⟩ := hK.exists_isMinOn ⟨0, h0K⟩ ((L_fta_cont p).norm.continuousOn)
        rw [isMinOn_iff] at hmin
        refine ⟨z0, fun z => ?_⟩
        by_cases hz : z ∈ Metric.closedBall (0:ℂ) (max R 0)
        · exact hmin z hz
        · have h0 : ‖p.eval z0‖ ≤ ‖p.eval 0‖ := hmin 0 h0K
          rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
          have := hR z (le_trans (le_max_left _ _) hz.le)
          linarith
    )
  have L_fta_descent : ∀ (p : Polynomial ℂ) (hp : 0 < p.natDegree) (z0 : ℂ) (h0 : p.eval z0 ≠ 0), ∃ z : ℂ, ‖p.eval z‖ < ‖p.eval z0‖ :=
    (fun (p : Polynomial ℂ) (hp : 0 < p.natDegree) (z0 : ℂ) (h0 : p.eval z0 ≠ 0) => by
      set q : Polynomial ℂ := p.comp (Polynomial.X + Polynomial.C z0) with hqdef
      have hqe : ∀ z, q.eval z = p.eval (z + z0) := by
        intro z; simp [hqdef, Polynomial.eval_comp]
      have hqdeg : q.natDegree = p.natDegree := by
        rw [hqdef, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
      set c0 := p.eval z0 with hc0
      set g : Polynomial ℂ := q - Polynomial.C c0 with hgdef
      have hg0 : g ≠ 0 := by
        intro h
        have : q = Polynomial.C c0 := sub_eq_zero.mp h
        rw [this, Polynomial.natDegree_C] at hqdeg
        omega
      obtain ⟨r, hr, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd g hg0 0
      set m := Polynomial.rootMultiplicity 0 g with hmdef
      have hb : r.eval 0 ≠ 0 := by
        intro h; apply hndvd
        rw [Polynomial.dvd_iff_isRoot]; exact h
      have hgeval : ∀ z, g.eval z = z ^ m * r.eval z := by
        intro z; rw [hr]; simp
      have hm : m ≠ 0 := by
        intro hm0
        have h1 := hgeval 0
        rw [hm0, pow_zero, one_mul] at h1
        apply hb; rw [← h1, hgdef]; simp [hqe, hc0]
      have hqz : ∀ z, p.eval (z + z0) = c0 + z ^ m * r.eval z := by
        intro z
        rw [← hgeval z, hgdef, Polynomial.eval_sub, Polynomial.eval_C, hqe]; ring
      set b := r.eval 0 with hbdef
      have hcont := (L_fta_cont r).continuousAt (x := 0)
      rw [Metric.continuousAt_iff] at hcont
      obtain ⟨ε, hε, hεr⟩ := hcont ‖b‖ (norm_pos_iff.mpr hb)
      set w : ℂ := (-c0 / b) ^ ((m : ℂ)⁻¹) with hwdef
      have hw : w ^ m = -c0 / b := Complex.cpow_nat_inv_pow _ hm
      have hwb : w ^ m * b = -c0 := by rw [hw]; field_simp
      have hw0 : w ≠ 0 := by
        intro h; rw [h, zero_pow hm] at hw
        have : -c0 / b ≠ 0 := div_ne_zero (neg_ne_zero.mpr h0) hb
        exact this hw.symm
      set t : ℝ := min (1/2) (ε / (2 * (‖w‖ + 1))) with htdef
      have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
      have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have htw : t * ‖w‖ < ε := by
        have h1 : t ≤ ε / (2 * (‖w‖ + 1)) := min_le_right _ _
        have h2 : t * ‖w‖ ≤ ε / (2 * (‖w‖ + 1)) * ‖w‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
        have h3 : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg w]
        linarith
      refine ⟨(t:ℂ) * w + z0, ?_⟩
      rw [hqz]
      have hdist : dist ((t:ℂ) * w) 0 < ε := by
        rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        exact htw
      have hrb : ‖r.eval ((t:ℂ) * w) - b‖ < ‖b‖ := by
        have := hεr hdist
        rwa [dist_eq_norm] at this
      have hid : c0 + ((t:ℂ) * w) ^ m * r.eval ((t:ℂ) * w)
          = ((1 - t ^ m : ℝ) : ℂ) * c0 + (t:ℂ) ^ m * (w ^ m * (r.eval ((t:ℂ) * w) - b)) := by
        have : (t:ℂ) ^ m * (w ^ m * b) = (t:ℂ) ^ m * (-c0) := by rw [hwb]
        push_cast
        linear_combination this
      rw [hid]
      have htm0 : 0 < t ^ m := pow_pos ht0 m
      have htm1 : t ^ m < 1 := pow_lt_one₀ ht0.le ht1 hm
      have hwm : ‖w‖ ^ m * ‖b‖ = ‖c0‖ := by
        rw [← norm_pow, ← norm_mul, hwb, norm_neg]
      have hwpos : 0 < ‖w‖ ^ m := pow_pos (norm_pos_iff.mpr hw0) m
      calc ‖((1 - t ^ m : ℝ) : ℂ) * c0 + (t:ℂ) ^ m * (w ^ m * (r.eval ((t:ℂ) * w) - b))‖
          ≤ ‖((1 - t ^ m : ℝ) : ℂ) * c0‖ + ‖(t:ℂ) ^ m * (w ^ m * (r.eval ((t:ℂ) * w) - b))‖ :=
            norm_add_le _ _
        _ = (1 - t ^ m) * ‖c0‖ + t ^ m * (‖w‖ ^ m * ‖r.eval ((t:ℂ) * w) - b‖) := by
            rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
              Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos (by linarith : (0:ℝ) < 1 - t ^ m), abs_of_pos ht0]
        _ < (1 - t ^ m) * ‖c0‖ + t ^ m * (‖w‖ ^ m * ‖b‖) := by
            have h5 := mul_lt_mul_of_pos_left hrb hwpos
            have h6 := mul_lt_mul_of_pos_left h5 htm0
            linarith
        _ = ‖c0‖ := by rw [hwm]; ring
    )
  have L_fta_root : ∀ (p : Polynomial ℂ) (hp : 0 < p.natDegree), ∃ z, p.IsRoot z :=
    (fun (p : Polynomial ℂ) (hp : 0 < p.natDegree) => by
      obtain ⟨z0, hz0⟩ := L_fta_exists_min p
      refine ⟨z0, ?_⟩
      by_contra h
      obtain ⟨z, hz⟩ := L_fta_descent p hp z0 h
      exact absurd (hz0 z) (not_le.mpr hz)
    )
  have L_fta_split : ∀ (n : ℕ), ∀ p : Polynomial ℂ, p ≠ 0 → p.natDegree = n →
      ∃ r : Fin n → ℂ,
        p = Polynomial.C p.leadingCoeff * ∏ j, (Polynomial.X - Polynomial.C (r j)) :=
    (fun (n : ℕ) => by
      induction n with
      | zero =>
        intro p hp hn
        refine ⟨Fin.elim0, ?_⟩
        rw [Fin.prod_univ_zero, mul_one, Polynomial.leadingCoeff, hn]
        exact Polynomial.eq_C_of_natDegree_eq_zero hn
      | succ n ih =>
        intro p hp hn
        obtain ⟨a, ha⟩ := L_fta_root p (by omega)
        have hdiv := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
        set q := p /ₘ (Polynomial.X - Polynomial.C a) with hqdef
        have hq0 : q ≠ 0 := by
          intro h; rw [h, mul_zero] at hdiv; exact hp hdiv.symm
        have hqn : q.natDegree = n := by
          rw [hqdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C a),
            Polynomial.natDegree_X_sub_C, hn]
          simp
        obtain ⟨s, hs⟩ := ih q hq0 hqn
        refine ⟨Fin.cons a s, ?_⟩
        have hlc : p.leadingCoeff = q.leadingCoeff := by
          conv_lhs => rw [← hdiv]
          rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_sub_C, one_mul]
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hlc]
        conv_lhs => rw [← hdiv, hs]
        ring
    )
  have L_fta : ∀ (p : Polynomial ℂ) (hp : p ≠ 0), ∃ r : Fin p.natDegree → ℂ,
        p = Polynomial.C p.leadingCoeff * ∏ j, (Polynomial.X - Polynomial.C (r j)) :=
    (fun (p : Polynomial ℂ) (hp : p ≠ 0) => by
      exact L_fta_split p.natDegree p hp rfl
    )
  have L_gauss_clear : ∀ (T : Polynomial ℚ), ∃ d : ℕ, d ≠ 0 ∧ ∃ U : Polynomial ℤ, U.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * T :=
    (fun (T : Polynomial ℚ) => by
      induction T using Polynomial.induction_on' with
      | add T1 T2 h1 h2 =>
        obtain ⟨d1, hd1, U1, hU1⟩ := h1
        obtain ⟨d2, hd2, U2, hU2⟩ := h2
        refine ⟨d1 * d2, Nat.mul_ne_zero hd1 hd2, Polynomial.C (d2 : ℤ) * U1 + Polynomial.C (d1 : ℤ) * U2, ?_⟩
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, hU1, hU2]
        simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, Polynomial.C_mul]
        ring
      | monomial n q =>
        refine ⟨q.den, q.den_nz, Polynomial.monomial n q.num, ?_⟩
        rw [Polynomial.map_monomial, Polynomial.C_mul_monomial]
        congr 1
        rw [mul_comm, Rat.mul_den_eq_num]
        simp
    )
  have L_gauss_intprime : ∀ (p : ℕ) (hp : p.Prime), Prime (p : ℤ) :=
    (fun (p : ℕ) (hp : p.Prime) => by
      refine ⟨by exact_mod_cast hp.ne_zero, ?_, ?_⟩
      · intro hu
        rcases Int.isUnit_iff.mp hu with h | h
        · have : p = 1 := by exact_mod_cast h
          exact hp.ne_one this
        · omega
      · intro a b hab
        rw [Int.natCast_dvd, Int.natAbs_mul] at hab
        rcases (Nat.Prime.dvd_mul hp).mp hab with h | h
        · left; exact Int.natCast_dvd.mpr h
        · right; exact Int.natCast_dvd.mpr h
    )
  have L_gauss_prime : ∀ (P U : Polynomial ℤ) (p : ℕ) (hp : p.Prime)
      (hPU : ∀ i, (p : ℤ) ∣ (P * U).coeff i), (∀ i, (p : ℤ) ∣ P.coeff i) ∨ (∀ i, (p : ℤ) ∣ U.coeff i) :=
    (fun (P U : Polynomial ℤ) (p : ℕ) (hp : p.Prime)
        (hPU : ∀ i, (p : ℤ) ∣ (P * U).coeff i) => by
      have hpz : Prime (p : ℤ) := L_gauss_intprime p hp
      have hI : (Ideal.span {(p : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr hpz
      have hJ : (Ideal.map Polynomial.C (Ideal.span {(p : ℤ)})).IsPrime := Ideal.isPrime_map_C_of_isPrime
      have hmem : P * U ∈ Ideal.map Polynomial.C (Ideal.span {(p : ℤ)}) := by
        rw [Ideal.mem_map_C_iff]
        intro n
        exact Ideal.mem_span_singleton.mpr (hPU n)
      rcases hJ.mem_or_mem hmem with h | h
      · left
        intro i
        rw [Ideal.mem_map_C_iff] at h
        exact Ideal.mem_span_singleton.mp (h i)
      · right
        intro i
        rw [Ideal.mem_map_C_iff] at h
        exact Ideal.mem_span_singleton.mp (h i)
    )
  have L_gauss_ind : ∀ (P S : Polynomial ℤ) (hP : ∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d), ∀ d : ℕ, ∀ U : Polynomial ℤ, d ≠ 0 → P * U = Polynomial.C (d : ℤ) * S → P ∣ S :=
    (fun (P S : Polynomial ℤ) (hP : ∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) => by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro U hd hPU
        by_cases h1 : d = 1
        · subst h1
          refine ⟨U, ?_⟩
          rw [hPU]
          simp
        · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
          obtain ⟨d', rfl⟩ := hpd
          have hcoeff : ∀ i, (p : ℤ) ∣ (P * U).coeff i := by
            intro i
            rw [hPU, Polynomial.coeff_C_mul]
            push_cast
            exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
          rcases L_gauss_prime P U p hp hcoeff with hPp | hUp
          · exfalso
            exact (L_gauss_intprime p hp).not_unit (hP _ hPp)
          · obtain ⟨U', hU'⟩ := (Polynomial.C_dvd_iff_dvd_coeff (p : ℤ) U).mpr hUp
            have hd' : d' ≠ 0 := by
              rintro rfl
              simp at hd
            have hp0 : (Polynomial.C (p : ℤ)) ≠ 0 := by
              rw [Ne, Polynomial.C_eq_zero]
              exact_mod_cast hp.ne_zero
            have hPU' : P * U' = Polynomial.C (d' : ℤ) * S := by
              apply mul_left_cancel₀ hp0
              rw [hU'] at hPU
              calc Polynomial.C (p : ℤ) * (P * U') = P * (Polynomial.C (p : ℤ) * U') := by ring
                _ = Polynomial.C ((p * d' : ℕ) : ℤ) * S := hPU
                _ = Polynomial.C (p : ℤ) * (Polynomial.C (d' : ℤ) * S) := by
                  push_cast
                  rw [Polynomial.C_mul]
                  ring
            have hlt : d' < p * d' := by
              have := hp.two_le
              have : 0 < d' := Nat.pos_of_ne_zero hd'
              nlinarith
            exact ih d' hlt U' hd' hPU'
    )
  have L_gauss : ∀ (P S : Polynomial ℤ) (hP : ∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d)
      (hdvd : P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ)), P ∣ S :=
    (fun (P S : Polynomial ℤ) (hP : ∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d)
        (hdvd : P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ)) => by
      obtain ⟨T, hT⟩ := hdvd
      obtain ⟨d, hd, U, hU⟩ := L_gauss_clear T
      apply L_gauss_ind P S hP d U hd
      apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
      rw [Polynomial.map_mul, hU, Polynomial.map_mul, Polynomial.map_C, hT]
      simp only [eq_intCast, Int.cast_natCast]
      ring
    )
  have L_gelfond_coeff_mul : ∀ {R : Type} [CommRing R] (n : ℕ) (x y : Fin (n+1) → R) (k : ℕ), ((∑ i : Fin (n+1), Polynomial.C (x i) * Polynomial.X ^ (i:ℕ)) *
        (∑ j : Fin (n+1), Polynomial.C (y j) * Polynomial.X ^ (j:ℕ))).coeff k =
      ∑ i : Fin (n+1), ∑ j : Fin (n+1), if (i:ℕ) + (j:ℕ) = k then x i * y j else 0 :=
    (fun {R : Type} [CommRing R] (n : ℕ) (x y : Fin (n+1) → R) (k : ℕ) => by
      rw [Finset.sum_mul_sum, Polynomial.finset_sum_coeff]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.finset_sum_coeff]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show Polynomial.C (x i) * Polynomial.X ^ (i:ℕ) * (Polynomial.C (y j) * Polynomial.X ^ (j:ℕ))
          = Polynomial.C (x i * y j) * Polynomial.X ^ ((i:ℕ) + (j:ℕ)) by
            rw [Polynomial.C_mul, pow_add]; ring]
      rw [Polynomial.coeff_C_mul_X_pow]
      by_cases h : (i:ℕ) + (j:ℕ) = k
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]
    )
  have L_gelfond_coeff_single : ∀ {R : Type} [CommRing R] (n : ℕ) (x : Fin (n+1) → R)
      (i : Fin (n+1)), (∑ j : Fin (n+1), Polynomial.C (x j) * Polynomial.X ^ (j:ℕ)).coeff i = x i :=
    (fun {R : Type} [CommRing R] (n : ℕ) (x : Fin (n+1) → R)
        (i : Fin (n+1)) => by
      rw [Polynomial.finset_sum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [if_neg]
        intro h
        exact hj (Fin.ext h.symm)
      · intro h; exact absurd (Finset.mem_univ i) h
    )
  have L_gelfond_repr : ∀ {R : Type} [CommRing R] (n : ℕ) (p : Polynomial R) (hp : p.natDegree ≤ n), p = ∑ i : Fin (n+1), Polynomial.C (p.coeff i) * Polynomial.X ^ (i:ℕ) :=
    (fun {R : Type} [CommRing R] (n : ℕ) (p : Polynomial R) (hp : p.natDegree ≤ n) => by
      rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (p.coeff i) * Polynomial.X ^ i) (n+1)]
      conv_lhs => rw [Polynomial.as_sum_range' p (n+1) (by omega)]
      simp only [Polynomial.C_mul_X_pow_eq_monomial]
    )
  have L_gelfond_coeff_mul_int : ∀ (n : ℕ) (P Q : Polynomial ℤ) (hP : P.natDegree ≤ n)
      (hQ : Q.natDegree ≤ n) (k : ℕ), (P * Q).coeff k = ∑ i : Fin (n+1), ∑ j : Fin (n+1),
        if (i:ℕ) + (j:ℕ) = k then P.coeff i * Q.coeff j else 0 :=
    (fun (n : ℕ) (P Q : Polynomial ℤ) (hP : P.natDegree ≤ n)
        (hQ : Q.natDegree ≤ n) (k : ℕ) => by
      have h := L_gelfond_coeff_mul n (fun i : Fin (n+1) => P.coeff i) (fun j : Fin (n+1) => Q.coeff j) k
      rw [← L_gelfond_repr n P hP, ← L_gelfond_repr n Q hQ] at h
      exact h
    )
  have L_gelfond : ∀ (n : ℕ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hfta : ∀ p : Polynomial ℂ, p ≠ 0 → ∃ r : Fin p.natDegree → ℂ,
        p = Polynomial.C p.leadingCoeff * ∏ j, (Polynomial.X - Polynomial.C (r j))), ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
        N A * N B ≤ C * N (A * B) :=
    (fun (n : ℕ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hfta : ∀ p : Polynomial ℂ, p ≠ 0 → ∃ r : Fin p.natDegree → ℂ,
          p = Polynomial.C p.leadingCoeff * ∏ j, (Polynomial.X - Polynomial.C (r j))) => by
      classical
      obtain ⟨cv, hcv⟩ : ∃ cv : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) → (Fin (2*n+1) → ℝ),
          ∀ x y k, cv x y k = ∑ i : Fin (n+1), ∑ j : Fin (n+1),
            if (i:ℕ) + (j:ℕ) = (k:ℕ) then x i * y j else 0 := ⟨_, fun _ _ _ => rfl⟩
      have hcont : Continuous (fun p : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ) => ‖cv p.1 p.2‖) := by
        apply continuous_norm.comp
        apply continuous_pi
        intro k
        simp only [hcv]
        apply continuous_finset_sum
        intro i _
        apply continuous_finset_sum
        intro j _
        split_ifs
        · exact ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
        · exact continuous_const
      have hKc : IsCompact (Metric.sphere (0 : Fin (n+1) → ℝ) 1 ×ˢ Metric.sphere (0 : Fin (n+1) → ℝ) 1) :=
        (isCompact_sphere _ _).prod (isCompact_sphere _ _)
      have h1 : (fun _ : Fin (n+1) => (1:ℝ)) ∈ Metric.sphere (0 : Fin (n+1) → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, pi_norm_const]; simp
      have hKne : (Metric.sphere (0 : Fin (n+1) → ℝ) 1 ×ˢ Metric.sphere (0 : Fin (n+1) → ℝ) 1).Nonempty :=
        ⟨(_, _), Set.mk_mem_prod h1 h1⟩
      obtain ⟨p0, hp0K, hp0min⟩ := hKc.exists_isMinOn hKne hcont.continuousOn
      have hp0K' := Set.mem_prod.mp hp0K
      have hδpos : 0 < ‖cv p0.1 p0.2‖ := by
        rcases (norm_nonneg (cv p0.1 p0.2)).lt_or_eq with h | h
        · exact h
        exfalso
        have hz : cv p0.1 p0.2 = 0 := norm_eq_zero.mp h.symm
        have hpq : (∑ i : Fin (n+1), Polynomial.C (p0.1 i) * Polynomial.X ^ (i:ℕ)) *
            (∑ j : Fin (n+1), Polynomial.C (p0.2 j) * Polynomial.X ^ (j:ℕ)) = 0 := by
          ext k
          rw [L_gelfond_coeff_mul, Polynomial.coeff_zero]
          by_cases hk : k < 2*n+1
          · have := congrFun hz ⟨k, hk⟩
            rw [hcv] at this
            simpa using this
          · apply Finset.sum_eq_zero
            intro i _
            apply Finset.sum_eq_zero
            intro j _
            rw [if_neg]
            have := i.isLt; have := j.isLt; omega
        have hzero : ∀ v : Fin (n+1) → ℝ, v ∈ Metric.sphere (0 : Fin (n+1) → ℝ) 1 →
            (∑ i : Fin (n+1), Polynomial.C (v i) * Polynomial.X ^ (i:ℕ)) ≠ 0 := by
          intro v hv h0
          have : v = 0 := by
            funext i
            have := L_gelfond_coeff_single n v i
            rw [h0, Polynomial.coeff_zero] at this
            simpa using this.symm
          rw [mem_sphere_zero_iff_norm, this, norm_zero] at hv
          exact zero_ne_one hv
        rcases mul_eq_zero.mp hpq with h0 | h0
        · exact hzero _ hp0K'.1 h0
        · exact hzero _ hp0K'.2 h0
      set δ := ‖cv p0.1 p0.2‖ with hδ
      refine ⟨1/δ, by positivity, ?_⟩
      intro A B hA hB hAB
      have hdeg := Polynomial.natDegree_mul hA hB
      have hAn : A.natDegree ≤ n := by omega
      have hBn : B.natDegree ≤ n := by omega
      have hNle : ∀ (P : Polynomial ℤ) (v : Fin (n+1) → ℝ), P.natDegree ≤ n →
          (∀ i : Fin (n+1), v i = (P.coeff i : ℝ)) → N P ≤ ‖v‖ := by
        intro P v hP hv
        rw [hN]
        have hb : ∀ i ∈ P.support, (((P.coeff i).natAbs : ℕ) : ℝ) ≤ ‖v‖ := by
          intro i hi
          have hi' : i < n + 1 := by have := Polynomial.le_natDegree_of_mem_supp i hi; omega
          have := norm_le_pi_norm v ⟨i, hi'⟩
          rw [hv, Real.norm_eq_abs] at this
          simpa [Nat.cast_natAbs] using this
        rcases P.support.eq_empty_or_nonempty with he | hne
        · rw [he, Finset.sup_empty]; simp
        · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup P.support hne (fun i => (P.coeff i).natAbs)
          rw [heq]; exact hb i hi
      have hpos : ∀ (P : Polynomial ℤ) (v : Fin (n+1) → ℝ), P ≠ 0 → P.natDegree ≤ n →
          (∀ i : Fin (n+1), v i = (P.coeff i : ℝ)) → 0 < ‖v‖ := by
        intro P v hP0 hP hv
        apply norm_pos_iff.mpr
        intro h0
        have := congrFun h0 ⟨P.natDegree, by omega⟩
        rw [hv, Pi.zero_apply] at this
        have hl : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
        have h2 : P.coeff P.natDegree = 0 := by exact_mod_cast this
        exact hl h2
      set a : Fin (n+1) → ℝ := fun i => (A.coeff i : ℝ) with ha
      set b : Fin (n+1) → ℝ := fun i => (B.coeff i : ℝ) with hb
      have hNA : N A ≤ ‖a‖ := hNle A a hAn (fun i => rfl)
      have hNB : N B ≤ ‖b‖ := hNle B b hBn (fun i => rfl)
      have ha0 : 0 < ‖a‖ := hpos A a hA hAn (fun i => rfl)
      have hb0 : 0 < ‖b‖ := hpos B b hB hBn (fun i => rfl)
      have hNAB : ‖cv a b‖ ≤ N (A * B) := by
        have hN0 : 0 ≤ N (A * B) := by rw [hN]; positivity
        refine (pi_norm_le_iff_of_nonneg hN0).mpr fun k => ?_
        have hk : cv a b k = (((A * B).coeff k : ℤ) : ℝ) := by
          rw [hcv, L_gelfond_coeff_mul_int n A B hAn hBn k]
          simp only [Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_zero, a, b]
        rw [hk, Real.norm_eq_abs]
        by_cases hc : (A * B).coeff k = 0
        · rw [hc]; simpa using hN0
        · rw [hN]
          have hmem : (k:ℕ) ∈ (A * B).support := Polynomial.mem_support_iff.mpr hc
          have := Finset.le_sup (f := fun i => ((A * B).coeff i).natAbs) hmem
          have h3 : (((A * B).coeff k).natAbs : ℝ) ≤
              (((A * B).support.sup fun i => ((A * B).coeff i).natAbs : ℕ) : ℝ) := by
            exact_mod_cast this
          simpa [Nat.cast_natAbs] using h3
      have hs : ∀ v : Fin (n+1) → ℝ, 0 < ‖v‖ → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Fin (n+1) → ℝ) 1 := by
        intro v hv
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv.ne']
      have key : δ * (‖a‖ * ‖b‖) ≤ ‖cv a b‖ := by
        have hmem : (‖a‖⁻¹ • a, ‖b‖⁻¹ • b) ∈
            Metric.sphere (0 : Fin (n+1) → ℝ) 1 ×ˢ Metric.sphere (0 : Fin (n+1) → ℝ) 1 :=
          Set.mk_mem_prod (hs a ha0) (hs b hb0)
        have hle := isMinOn_iff.mp hp0min _ hmem
        simp only at hle
        have hscale : cv (‖a‖⁻¹ • a) (‖b‖⁻¹ • b) = (‖a‖⁻¹ * ‖b‖⁻¹) • cv a b := by
          funext k
          rw [hcv, Pi.smul_apply, hcv, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Pi.smul_apply, smul_eq_mul]
          split_ifs <;> ring
        rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hle
        calc δ * (‖a‖ * ‖b‖) ≤ (‖a‖⁻¹ * ‖b‖⁻¹ * ‖cv a b‖) * (‖a‖ * ‖b‖) := by
              apply mul_le_mul_of_nonneg_right hle; positivity
          _ = ‖cv a b‖ := by field_simp
      have hNA0 : 0 ≤ N A := by rw [hN]; positivity
      calc N A * N B ≤ ‖a‖ * ‖b‖ := mul_le_mul hNA hNB (by rw [hN]; positivity) (norm_nonneg _)
        _ ≤ ‖cv a b‖ / δ := by rw [le_div_iff₀ hδpos]; linarith
        _ ≤ N (A * B) / δ := by gcongr
        _ = 1/δ * N (A * B) := by ring
    )
  have L_good_lower_ne : ∀ (ξ : ℝ) (hξ : Transcendental ℚ ξ) (Q : Polynomial ℤ) (hQ : Q ≠ 0), Polynomial.aeval ξ Q ≠ 0 :=
    (fun (ξ : ℝ) (hξ : Transcendental ℚ ξ) (Q : Polynomial ℤ) (hQ : Q ≠ 0) => by
      intro h
      apply hξ
      refine ⟨Q.map (algebraMap ℤ ℚ), ?_, ?_⟩
      · intro h0
        apply hQ
        have hinj : Function.Injective (algebraMap ℤ ℚ) := (algebraMap ℤ ℚ).injective_int
        exact (Polynomial.map_injective _ hinj) (by rw [h0, Polynomial.map_zero])
      · rw [Polynomial.aeval_map_algebraMap]; exact h
    )
  have L_good_lower_coeff : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) (M : ℝ)
      (Q : Polynomial ℤ) (hQ : N Q ≤ M) (i : ℕ), ((Q.coeff i).natAbs : ℝ) ≤ M :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) (M : ℝ)
        (Q : Polynomial ℤ) (hQ : N Q ≤ M) (i : ℕ) => by
      have h0 : (0 : ℝ) ≤ N Q := by rw [hN Q]; exact Nat.cast_nonneg _
      by_cases hi : i ∈ Q.support
      · have h1 : (Q.coeff i).natAbs ≤ Q.support.sup fun i => (Q.coeff i).natAbs :=
          Finset.le_sup (f := fun i => (Q.coeff i).natAbs) hi
        have h2 : ((Q.coeff i).natAbs : ℝ) ≤ ((Q.support.sup fun i => (Q.coeff i).natAbs : ℕ) : ℝ) := by
          exact_mod_cast h1
        rw [← hN Q] at h2
        linarith
      · have : Q.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
        rw [this]
        simp only [Int.natAbs_zero, Nat.cast_zero]
        linarith
    )
  have L_good_lower_finite : ∀ (n : ℕ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) (M : ℝ), {Q : Polynomial ℤ | Q ≠ 0 ∧ Q.natDegree ≤ n ∧ N Q ≤ M}.Finite :=
    (fun (n : ℕ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) (M : ℝ) => by
      have hbd : ∀ Q : Polynomial ℤ, Q ∈ {Q : Polynomial ℤ | Q ≠ 0 ∧ Q.natDegree ≤ n ∧ N Q ≤ M} →
          ∀ i, -((Nat.ceil M : ℕ) : ℤ) ≤ Q.coeff i ∧ Q.coeff i ≤ ((Nat.ceil M : ℕ) : ℤ) := by
        intro Q hQ i
        have h := L_good_lower_coeff N hN M Q hQ.2.2 i
        have h2 : (Q.coeff i).natAbs ≤ Nat.ceil M := by
          have : ((Q.coeff i).natAbs : ℝ) ≤ (Nat.ceil M : ℝ) := le_trans h (Nat.le_ceil M)
          exact_mod_cast this
        omega
      let f : Polynomial ℤ → (Fin (n+1) → ℕ) := fun Q i => (Q.coeff i + ((Nat.ceil M : ℕ) : ℤ)).toNat
      have hinj : Set.InjOn f {Q : Polynomial ℤ | Q ≠ 0 ∧ Q.natDegree ≤ n ∧ N Q ≤ M} := by
        intro P hP Q hQ hPQ
        ext i
        by_cases hi : i ≤ n
        · have := congrFun hPQ ⟨i, Nat.lt_succ_of_le hi⟩
          simp only [f] at this
          have hP1 := (hbd P hP i).1
          have hQ1 := (hbd Q hQ i).1
          have e1 := Int.toNat_of_nonneg (show 0 ≤ P.coeff i + ((Nat.ceil M : ℕ) : ℤ) by omega)
          have e2 := Int.toNat_of_nonneg (show 0 ≤ Q.coeff i + ((Nat.ceil M : ℕ) : ℤ) by omega)
          rw [this] at e1
          omega
        · push_neg at hi
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP.2.1 hi),
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ.2.1 hi)]
      have himg : f '' {Q : Polynomial ℤ | Q ≠ 0 ∧ Q.natDegree ≤ n ∧ N Q ≤ M} ⊆
          Set.pi Set.univ (fun _ => {m : ℕ | m ≤ 2 * Nat.ceil M}) := by
        rintro _ ⟨Q, hQ, rfl⟩
        intro i _
        have h1 := (hbd Q hQ i).1
        have h2 := (hbd Q hQ i).2
        show (Q.coeff i + ((Nat.ceil M : ℕ) : ℤ)).toNat ≤ 2 * Nat.ceil M
        have e1 := Int.toNat_of_nonneg (show 0 ≤ Q.coeff i + ((Nat.ceil M : ℕ) : ℤ) by omega)
        omega
      have hfin : (Set.pi Set.univ (fun _ : Fin (n+1) => {m : ℕ | m ≤ 2 * Nat.ceil M})).Finite :=
        Set.Finite.pi (fun _ => Set.finite_le_nat _)
      exact Set.Finite.of_finite_image (hfin.subset himg) hinj
    )
  have L_good_lower : ∀ (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) (M : ℝ), ∃ c : ℝ, 0 < c ∧ ∀ Q : Polynomial ℤ, Q ≠ 0 → Q.natDegree ≤ n → N Q ≤ M →
        c ≤ |Polynomial.aeval ξ Q| :=
    (fun (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) (M : ℝ) => by
      have hS := L_good_lower_finite n N hN M
      by_cases hne : hS.toFinset.Nonempty
      · obtain ⟨Q0, hQ0, hmin⟩ :=
          Finset.exists_min_image hS.toFinset (fun Q => |Polynomial.aeval ξ Q|) hne
        have hQ0' := (Set.Finite.mem_toFinset hS).mp hQ0
        refine ⟨|Polynomial.aeval ξ Q0|, abs_pos.mpr (L_good_lower_ne ξ hξ Q0 hQ0'.1), ?_⟩
        intro Q hQ hdeg hNQ
        exact hmin Q ((Set.Finite.mem_toFinset hS).mpr ⟨hQ, hdeg, hNQ⟩)
      · refine ⟨1, one_pos, ?_⟩
        intro Q hQ hdeg hNQ
        exfalso
        exact hne ⟨Q, (Set.Finite.mem_toFinset hS).mpr ⟨hQ, hdeg, hNQ⟩⟩
    )
  have L_good_normprod : ∀ (n : ℕ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (C : ℝ) (hC : 1 ≤ C) (hgel : ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
        N A * N B ≤ C * N (A * B)), ∀ (L : List (Polynomial ℤ)) (c : ℤ), c ≠ 0 → (∀ F ∈ L, F ≠ 0) →
        (Polynomial.C c * L.prod).natDegree ≤ n →
        (L.map N).prod ≤ C ^ L.length * N (Polynomial.C c * L.prod) :=
    (fun (n : ℕ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (C : ℝ) (hC : 1 ≤ C) (hgel : ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
          N A * N B ≤ C * N (A * B)) => by
      intro L
      induction L with
      | nil =>
        intro c hc _ _
        simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero, one_mul, mul_one]
        rw [hN]
        have h0 : (0:ℕ) ∈ (Polynomial.C c).support := by
          rw [Polynomial.mem_support_iff, Polynomial.coeff_C_zero]; exact hc
        have h1 : ((Polynomial.C c).coeff 0).natAbs ≤
            (Polynomial.C c).support.sup fun i => ((Polynomial.C c).coeff i).natAbs :=
          Finset.le_sup (f := fun i => ((Polynomial.C c).coeff i).natAbs) h0
        rw [Polynomial.coeff_C_zero] at h1
        have h2 : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hc
        have h3 : (1:ℕ) ≤ (Polynomial.C c).support.sup fun i => ((Polynomial.C c).coeff i).natAbs :=
          le_trans h2 h1
        exact_mod_cast h3
      | cons F L ih =>
        intro c hc hL hdeg
        have hF : F ≠ 0 := hL F (List.mem_cons_self ..)
        have hL' : ∀ G ∈ L, G ≠ 0 := fun G hG => hL G (List.mem_cons_of_mem _ hG)
        have hprod : L.prod ≠ 0 := by
          intro h
          rw [List.prod_eq_zero_iff] at h
          exact hL' 0 h rfl
        have hCc : Polynomial.C c ≠ 0 := by
          intro h; exact hc (Polynomial.C_eq_zero.mp h)
        have hB : Polynomial.C c * L.prod ≠ 0 := mul_ne_zero hCc hprod
        have heq : Polynomial.C c * (F :: L).prod = F * (Polynomial.C c * L.prod) := by
          rw [List.prod_cons]; ring
        rw [heq] at hdeg ⊢
        have hdeg' : (Polynomial.C c * L.prod).natDegree ≤ n := by
          refine le_trans ?_ hdeg
          rw [Polynomial.natDegree_mul hF hB]
          omega
        have ih' := ih c hc hL' hdeg'
        have hg := hgel F (Polynomial.C c * L.prod) hF hB hdeg
        have hNF : 0 ≤ N F := by rw [hN]; exact Nat.cast_nonneg _
        have hCp : 0 ≤ C ^ L.length := pow_nonneg (by linarith) _
        simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
        calc N F * (L.map N).prod ≤ N F * (C ^ L.length * N (Polynomial.C c * L.prod)) :=
              mul_le_mul_of_nonneg_left ih' hNF
          _ = C ^ L.length * (N F * N (Polynomial.C c * L.prod)) := by ring
          _ ≤ C ^ L.length * (C * N (F * (Polynomial.C c * L.prod))) :=
              mul_le_mul_of_nonneg_left hg hCp
          _ = C ^ L.length * C * N (F * (Polynomial.C c * L.prod)) := by ring
    )
  have L_good_factor_clear : ∀ g : Polynomial ℚ, ∃ d : ℤ, d ≠ 0 ∧ ∃ G : Polynomial ℤ,
      G.map (Int.castRingHom ℚ) = Polynomial.C (d:ℚ) * g :=
    (by
      intro g
      induction g using Polynomial.induction_on' with
      | add p q hp hq =>
        obtain ⟨d1, hd1, G1, hG1⟩ := hp
        obtain ⟨d2, hd2, G2, hG2⟩ := hq
        refine ⟨d1 * d2, mul_ne_zero hd1 hd2, Polynomial.C d2 * G1 + Polynomial.C d1 * G2, ?_⟩
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hG1, hG2,
          Polynomial.map_C, Polynomial.map_C]
        simp only [eq_intCast, Int.cast_mul, Polynomial.C_mul]
        ring
      | monomial n a =>
        refine ⟨a.den, by exact_mod_cast a.den_nz, Polynomial.monomial n a.num, ?_⟩
        rw [Polynomial.map_monomial, Polynomial.C_mul_monomial]
        congr 1
        simp only [eq_intCast, Int.cast_natCast]
        rw [mul_comm]
        exact (Rat.mul_den_eq_num a).symm
    )
  have L_good_factor_exists_irred : ∀ (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
        P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S), ∀ P : Polynomial ℤ, 0 < P.natDegree → ∃ F : Polynomial ℤ, F ≠ 0 ∧
        Irreducible (F.map (Int.castRingHom ℚ)) ∧
        (∀ d : ℤ, (∀ i, d ∣ F.coeff i) → IsUnit d) ∧ F ∣ P :=
    (fun (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
          P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S) => by
      intro P hP
      classical
      have hinj : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
      have hdegmap : ∀ G : Polynomial ℤ, (G.map (Int.castRingHom ℚ)).natDegree = G.natDegree :=
        fun G => Polynomial.natDegree_map_eq_of_injective hinj G
      have hex : ∃ m : ℕ, ∃ F : Polynomial ℤ, F.natDegree = m ∧ 0 < m ∧
          F.map (Int.castRingHom ℚ) ∣ P.map (Int.castRingHom ℚ) := ⟨_, P, rfl, hP, dvd_refl _⟩
      obtain ⟨F0, hF0m, hm0, hF0P⟩ := Nat.find_spec hex
      have hmmin : ∀ G : Polynomial ℤ, 0 < G.natDegree →
          G.map (Int.castRingHom ℚ) ∣ P.map (Int.castRingHom ℚ) → Nat.find hex ≤ G.natDegree := by
        intro G hG hGP
        exact Nat.find_min' hex ⟨G, rfl, hG, hGP⟩
      have hex2 : ∃ k : ℕ, ∃ F : Polynomial ℤ, F.natDegree = Nat.find hex ∧
          F.map (Int.castRingHom ℚ) ∣ P.map (Int.castRingHom ℚ) ∧ F.leadingCoeff.natAbs = k :=
        ⟨_, F0, hF0m, hF0P, rfl⟩
      obtain ⟨F, hFm, hFP, hFk⟩ := Nat.find_spec hex2
      have hkmin : ∀ G : Polynomial ℤ, G.natDegree = Nat.find hex →
          G.map (Int.castRingHom ℚ) ∣ P.map (Int.castRingHom ℚ) →
          Nat.find hex2 ≤ G.leadingCoeff.natAbs := by
        intro G hG hGP
        exact Nat.find_min' hex2 ⟨G, hG, hGP, rfl⟩
      have hFpos : 0 < F.natDegree := hFm ▸ hm0
      have hF0 : F ≠ 0 := by rintro rfl; simp at hFpos
      have hprim : ∀ d : ℤ, (∀ i, d ∣ F.coeff i) → IsUnit d := by
        intro d hd
        by_contra hdu
        have hd0 : d ≠ 0 := by
          rintro rfl
          apply hF0
          ext i
          simpa using hd i
        obtain ⟨F', hF'⟩ : Polynomial.C d ∣ F := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hd
        have hF'0 : F' ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hF'
          exact hF0 hF'
        have hdeg' : F'.natDegree = F.natDegree := by
          rw [hF', Polynomial.natDegree_C_mul hd0]
        have hlead : F.leadingCoeff = d * F'.leadingCoeff := by
          rw [hF', Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
        have hF'P : F'.map (Int.castRingHom ℚ) ∣ P.map (Int.castRingHom ℚ) :=
          (Polynomial.map_dvd _ (Dvd.intro_left _ hF'.symm)).trans hFP
        have h1 := hkmin F' (hdeg'.trans hFm) hF'P
        rw [← hFk, hlead, Int.natAbs_mul] at h1
        have hd2 : 2 ≤ d.natAbs := by
          have hne : d.natAbs ≠ 1 := fun h => hdu (Int.isUnit_iff_natAbs_eq.mpr h)
          have hne0 : d.natAbs ≠ 0 := by simpa using hd0
          omega
        have hl0 : F'.leadingCoeff.natAbs ≠ 0 := by
          simpa using hF'0
        have h3 : 2 * F'.leadingCoeff.natAbs ≤ d.natAbs * F'.leadingCoeff.natAbs :=
          Nat.mul_le_mul_right _ hd2
        omega
      have hirr : Irreducible (F.map (Int.castRingHom ℚ)) := by
        refine ⟨?_, ?_⟩
        · intro hu
          have := Polynomial.natDegree_eq_zero_of_isUnit hu
          rw [hdegmap] at this
          omega
        · intro a b hab
          have hFm0 : F.map (Int.castRingHom ℚ) ≠ 0 := by
            intro h
            apply hF0
            apply Polynomial.map_injective _ hinj
            rw [h, Polynomial.map_zero]
          have ha0 : a ≠ 0 := by
            rintro rfl
            rw [zero_mul] at hab
            exact hFm0 hab
          have hb0 : b ≠ 0 := by
            rintro rfl
            rw [mul_zero] at hab
            exact hFm0 hab
          have hdab : a.natDegree + b.natDegree = F.natDegree := by
            rw [← hdegmap F, hab, Polynomial.natDegree_mul ha0 hb0]
          by_cases ha : a.natDegree = 0
          · left
            rw [Polynomial.eq_C_of_natDegree_eq_zero ha]
            apply Polynomial.isUnit_C.mpr
            apply Ne.isUnit
            intro hc
            apply ha0
            rw [Polynomial.eq_C_of_natDegree_eq_zero ha, hc, map_zero]
          by_cases hb : b.natDegree = 0
          · right
            rw [Polynomial.eq_C_of_natDegree_eq_zero hb]
            apply Polynomial.isUnit_C.mpr
            apply Ne.isUnit
            intro hc
            apply hb0
            rw [Polynomial.eq_C_of_natDegree_eq_zero hb, hc, map_zero]
          exfalso
          obtain ⟨d, hd, G, hG⟩ := L_good_factor_clear a
          have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
          have hGdeg : G.natDegree = a.natDegree := by
            rw [← hdegmap G, hG, Polynomial.natDegree_C_mul hdq]
          have hGP : G.map (Int.castRingHom ℚ) ∣ P.map (Int.castRingHom ℚ) := by
            rw [hG]
            have hu : IsUnit (Polynomial.C (d:ℚ)) := Polynomial.isUnit_C.mpr (Ne.isUnit hdq)
            rw [hu.mul_left_dvd]
            exact (Dvd.intro b hab.symm).trans hFP
          have := hmmin G (by omega) hGP
          omega
      exact ⟨F, hF0, hirr, hprim, hgauss F P hprim hFP⟩
    )
  have L_good_factor : ∀ (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
        P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S), ∀ P : Polynomial ℤ, P ≠ 0 → ∃ c : ℤ, c ≠ 0 ∧ ∃ L : List (Polynomial ℤ),
        P = Polynomial.C c * L.prod ∧ L.length ≤ P.natDegree ∧
        ∀ F ∈ L, F ≠ 0 ∧ Irreducible (F.map (Int.castRingHom ℚ)) ∧
          (∀ d : ℤ, (∀ i, d ∣ F.coeff i) → IsUnit d) :=
    (fun (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
          P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S) => by
      suffices hmain : ∀ n : ℕ, ∀ P : Polynomial ℤ, P.natDegree = n → P ≠ 0 → ∃ c : ℤ, c ≠ 0 ∧
          ∃ L : List (Polynomial ℤ), P = Polynomial.C c * L.prod ∧ L.length ≤ P.natDegree ∧
          ∀ F ∈ L, F ≠ 0 ∧ Irreducible (F.map (Int.castRingHom ℚ)) ∧
            (∀ d : ℤ, (∀ i, d ∣ F.coeff i) → IsUnit d) by
        intro P; exact hmain _ P rfl
      intro n
      refine Nat.strong_induction_on n ?_
      intro n ih P hn hP
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · have hPC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (hn.trans h0)
        refine ⟨P.coeff 0, ?_, [], ?_, ?_, ?_⟩
        · intro hc
          apply hP
          rw [hPC, hc, map_zero]
        · simp only [List.prod_nil, mul_one]
          exact hPC
        · simp
        · simp
      · obtain ⟨F, hF0, hFirr, hFprim, hFP⟩ := L_good_factor_exists_irred hgauss P (hn ▸ hpos)
        obtain ⟨T, rfl⟩ := hFP
        have hT0 : T ≠ 0 := by rintro rfl; simp at hP
        have hdeg : (F * T).natDegree = F.natDegree + T.natDegree := Polynomial.natDegree_mul hF0 hT0
        have hFpos : 0 < F.natDegree := by
          by_contra hcon
          have h0 : F.natDegree = 0 := by omega
          have hFC : F = Polynomial.C (F.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
          apply hFirr.not_isUnit
          rw [hFC, Polynomial.map_C]
          apply Polynomial.isUnit_C.mpr
          apply Ne.isUnit
          intro hc
          apply hF0
          rw [hFC]
          simpa using hc
        obtain ⟨c, hc, L, hTL, hlen, hL⟩ := ih T.natDegree (by omega) T rfl hT0
        refine ⟨c, hc, F :: L, ?_, ?_, ?_⟩
        · rw [List.prod_cons, hTL]; ring
        · simp only [List.length_cons]; omega
        · intro G hG
          rcases List.mem_cons.mp hG with rfl | hG
          · exact ⟨hF0, hFirr, hFprim⟩
          · exact hL G hG
    )
  have L_good_dirichlet_step : ∀ (ξ : ℝ) (m : ℕ) (i j : ℕ) (hij : i < j) (hj : j ≤ m)
      (h : |Int.fract ((j:ℝ) * ξ) - Int.fract ((i:ℝ) * ξ)| ≤ 1 / (m:ℝ)), ∃ p q : ℤ, 0 < q ∧ q ≤ m ∧ |(q : ℝ) * ξ - p| ≤ 1 / (m : ℝ) :=
    (fun (ξ : ℝ) (m : ℕ) (i j : ℕ) (hij : i < j) (hj : j ≤ m)
        (h : |Int.fract ((j:ℝ) * ξ) - Int.fract ((i:ℝ) * ξ)| ≤ 1 / (m:ℝ)) => by
      refine ⟨⌊(j:ℝ) * ξ⌋ - ⌊(i:ℝ) * ξ⌋, (j:ℤ) - i, by omega, by omega, ?_⟩
      have e : ((((j:ℤ) - i : ℤ)) : ℝ) * ξ - (((⌊(j:ℝ) * ξ⌋ - ⌊(i:ℝ) * ξ⌋ : ℤ)) : ℝ)
          = Int.fract ((j:ℝ) * ξ) - Int.fract ((i:ℝ) * ξ) := by
        rw [Int.fract, Int.fract]; push_cast; ring
      rw [e]; exact h
    )
  have L_good_dirichlet_core : ∀ (ξ : ℝ) (m : ℕ) (hm : 0 < m), ∃ p q : ℤ, 0 < q ∧ q ≤ m ∧ |(q : ℝ) * ξ - p| ≤ 1 / (m : ℝ) :=
    (fun (ξ : ℝ) (m : ℕ) (hm : 0 < m) => by
      have hmR : (0:ℝ) < m := by exact_mod_cast hm
      have hbd : ∀ k : ℕ, 0 ≤ ⌊Int.fract ((k:ℝ) * ξ) * m⌋ ∧ ⌊Int.fract ((k:ℝ) * ξ) * m⌋ < m := by
        intro k
        constructor
        · exact Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) hmR.le)
        · rw [Int.floor_lt]
          push_cast
          have := Int.fract_lt_one ((k:ℝ) * ξ)
          nlinarith
      let f : Fin (m+1) → Fin m := fun k =>
        ⟨min (⌊Int.fract (((k:ℕ):ℝ) * ξ) * m⌋.toNat) (m-1), by omega⟩
      have hcard : Fintype.card (Fin m) < Fintype.card (Fin (m+1)) := by simp
      obtain ⟨k1, k2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
      have key : ∀ k : Fin (m+1),
          (((f k : Fin m) : ℕ) : ℤ) = ⌊Int.fract (((k:ℕ):ℝ) * ξ) * m⌋ := by
        intro k
        obtain ⟨h0, h1⟩ := hbd k
        show ((min (⌊Int.fract (((k:ℕ):ℝ) * ξ) * m⌋.toNat) (m-1) : ℕ) : ℤ) = _
        omega
      have hfl : ⌊Int.fract (((k1:ℕ):ℝ) * ξ) * m⌋ = ⌊Int.fract (((k2:ℕ):ℝ) * ξ) * m⌋ := by
        rw [← key k1, ← key k2, heq]
      have hclose : |Int.fract (((k2:ℕ):ℝ) * ξ) - Int.fract (((k1:ℕ):ℝ) * ξ)| ≤ 1 / (m:ℝ) := by
        set a := Int.fract (((k1:ℕ):ℝ) * ξ)
        set b := Int.fract (((k2:ℕ):ℝ) * ξ)
        have ha1 := Int.floor_le (a * m)
        have ha2 := Int.lt_floor_add_one (a * m)
        have hb1 := Int.floor_le (b * m)
        have hb2 := Int.lt_floor_add_one (b * m)
        rw [hfl] at ha1 ha2
        have : |b - a| < 1 / (m:ℝ) := by
          rw [abs_sub_lt_iff]
          constructor <;> rw [lt_div_iff₀ hmR] <;> linarith
        exact this.le
      rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
      · exact L_good_dirichlet_step ξ m k1 k2 h (by have := k2.2; omega) hclose
      · exact L_good_dirichlet_step ξ m k2 k1 h (by have := k1.2; omega)
          (by rw [abs_sub_comm]; exact hclose)
    )
  have L_good_dirichlet : ∀ (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
      (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hlow : ∀ M : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ Q : Polynomial ℤ, Q ≠ 0 → Q.natDegree ≤ n → N Q ≤ M →
        c ≤ |Polynomial.aeval ξ Q|), ∀ B : ℝ, ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧ B ≤ N P ∧
        |Polynomial.aeval ξ P| ≤ N P ^ (-(1/2 : ℝ)) :=
    (fun (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
        (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hlow : ∀ M : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ Q : Polynomial ℤ, Q ≠ 0 → Q.natDegree ≤ n → N Q ≤ M →
          c ≤ |Polynomial.aeval ξ Q|) => by
      intro B
      obtain ⟨c, hc, hcQ⟩ := hlow (max B 1)
      obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = ⌈1/c⌉₊ + ⌈|ξ|⌉₊ + 2 := ⟨_, rfl⟩
      have hm : 0 < m := by omega
      have hmR : (0:ℝ) < m := by exact_mod_cast hm
      have hm1 : (1/c : ℝ) < m := by
        have h1 := Nat.le_ceil (1/c)
        have h3 := (Nat.cast_nonneg (α := ℝ) ⌈|ξ|⌉₊)
        have h2 : (m:ℝ) = (⌈1/c⌉₊ : ℝ) + (⌈|ξ|⌉₊ : ℝ) + 2 := by rw [hm_def]; push_cast; ring
        linarith
      have hmξ : |ξ| + 1 ≤ (m:ℝ) := by
        have h1 := Nat.le_ceil |ξ|
        have h3 := (Nat.cast_nonneg (α := ℝ) ⌈1/c⌉₊)
        have h2 : (m:ℝ) = (⌈1/c⌉₊ : ℝ) + (⌈|ξ|⌉₊ : ℝ) + 2 := by rw [hm_def]; push_cast; ring
        linarith
      obtain ⟨p, q, hq0, hqm, hpq⟩ := L_good_dirichlet_core ξ m hm
      have hlt : 1 / (m:ℝ) < c := by
        rw [div_lt_iff₀ hmR]; rw [div_lt_iff₀ hc] at hm1; linarith
      have hcoef : ∀ i, (Polynomial.C q * Polynomial.X - Polynomial.C p).coeff i
          = (if i = 1 then q else 0) - (if i = 0 then p else 0) := by
        intro i; rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
      have hev : Polynomial.aeval ξ (Polynomial.C q * Polynomial.X - Polynomial.C p)
          = (q:ℝ) * ξ - p := by simp
      have hP0 : Polynomial.C q * Polynomial.X - Polynomial.C p ≠ 0 := by
        intro h
        have h1 := hcoef 1
        rw [h, Polynomial.coeff_zero] at h1
        simp at h1
        omega
      have hdeg : (Polynomial.C q * Polynomial.X - Polynomial.C p).natDegree ≤ n := by
        refine le_trans ?_ hn
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro i hi
        have hi1 : i ≠ 1 := by intro h; subst h; exact absurd hi (by norm_num)
        have hi0 : i ≠ 0 := by intro h; subst h; exact absurd hi (by norm_num)
        rw [hcoef i]; simp [hi1, hi0]
      have hNP : max B 1 < N (Polynomial.C q * Polynomial.X - Polynomial.C p) := by
        by_contra hcon
        push_neg at hcon
        have h1 := hcQ _ hP0 hdeg hcon
        rw [hev] at h1
        linarith
      have hqR : (q:ℝ) ≤ m := by exact_mod_cast hqm
      have hq0R : (0:ℝ) < q := by exact_mod_cast hq0
      have hpR : |(p:ℝ)| ≤ (m:ℝ)^2 := by
        have h1 := abs_sub_abs_le_abs_sub (p:ℝ) ((q:ℝ)*ξ)
        rw [abs_sub_comm] at h1
        have h2 : |(q:ℝ) * ξ| ≤ m * |ξ| := by
          rw [abs_mul, abs_of_pos hq0R]
          exact mul_le_mul_of_nonneg_right hqR (abs_nonneg ξ)
        have h3 : 1 / (m:ℝ) ≤ 1 := by
          rw [div_le_one hmR]; exact_mod_cast hm
        have h4 : (1:ℝ) ≤ m := by exact_mod_cast hm
        nlinarith [abs_nonneg ξ]
      have hNup : N (Polynomial.C q * Polynomial.X - Polynomial.C p) ≤ (m:ℝ)^2 := by
        rw [hN]
        have hsup : ((Polynomial.C q * Polynomial.X - Polynomial.C p).support.sup
            fun i => ((Polynomial.C q * Polynomial.X - Polynomial.C p).coeff i).natAbs) ≤ m^2 := by
          apply Finset.sup_le
          intro i _
          rw [hcoef i]
          by_cases h1 : i = 1
          · subst h1
            simp
            have hmm : m ≤ m^2 := by nlinarith
            have : q.natAbs ≤ m := by omega
            omega
          · by_cases h0 : i = 0
            · subst h0
              simp
              have : ((p.natAbs : ℕ) : ℝ) ≤ ((m^2 : ℕ) : ℝ) := by
                rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; exact hpR
              exact_mod_cast this
            · simp [h1, h0]
        exact_mod_cast hsup
      refine ⟨Polynomial.C q * Polynomial.X - Polynomial.C p, hP0, hdeg, ?_, ?_⟩
      · exact le_trans (le_max_left B 1) hNP.le
      · rw [hev]
        have hNpos : 0 < N (Polynomial.C q * Polynomial.X - Polynomial.C p) := by
          linarith [le_max_right B 1]
        rw [Real.rpow_neg hNpos.le, ← Real.sqrt_eq_rpow]
        have hs : Real.sqrt (N (Polynomial.C q * Polynomial.X - Polynomial.C p)) ≤ m := by
          have := Real.sqrt_le_sqrt hNup
          rwa [Real.sqrt_sq hmR.le] at this
        have hspos : 0 < Real.sqrt (N (Polynomial.C q * Polynomial.X - Polynomial.C p)) :=
          Real.sqrt_pos.mpr hNpos
        calc |(q:ℝ) * ξ - p| ≤ 1 / (m:ℝ) := hpq
          _ ≤ _ := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hspos hs
    )
  have L_good_aeval : ∀ (ξ : ℝ), ∀ (L : List (Polynomial ℤ)) (c : ℤ),
        |Polynomial.aeval ξ (Polynomial.C c * L.prod)| =
          |(c : ℝ)| * (L.map fun F => |Polynomial.aeval ξ F|).prod :=
    (fun (ξ : ℝ) => by
      intro L c
      induction L with
      | nil => simp
      | cons F L ih =>
        have h : Polynomial.C c * (F :: L).prod = F * (Polynomial.C c * L.prod) := by
          simp only [List.prod_cons]; ring
        rw [h, map_mul, abs_mul, ih]
        simp only [List.map_cons, List.prod_cons]
        ring
    )
  have L_good_Ngeone : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (F : Polynomial ℤ) (hF : F ≠ 0), 1 ≤ N F :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (F : Polynomial ℤ) (hF : F ≠ 0) => by
      rw [hN F]
      have h1 : (F.coeff F.natDegree).natAbs ≤ F.support.sup fun i => (F.coeff i).natAbs :=
        Finset.le_sup (f := fun i => (F.coeff i).natAbs) (Polynomial.natDegree_mem_support_of_nonzero hF)
      have h2 : F.coeff F.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hF
      have h3 : 1 ≤ (F.coeff F.natDegree).natAbs := Int.natAbs_pos.mpr h2
      exact_mod_cast le_trans h3 h1
    )
  have L_good_prodbound : ∀ (ξ : ℝ) (N : Polynomial ℤ → ℝ) (κ w : ℝ) (hκ : 0 < κ), ∀ L : List (Polynomial ℤ), (∀ F ∈ L, 1 ≤ N F ∧ κ * N F ^ (-w) ≤ |Polynomial.aeval ξ F|) →
        1 ≤ (L.map N).prod ∧
        κ ^ L.length * ((L.map N).prod) ^ (-w) ≤ (L.map fun F => |Polynomial.aeval ξ F|).prod :=
    (fun (ξ : ℝ) (N : Polynomial ℤ → ℝ) (κ w : ℝ) (hκ : 0 < κ) => by
      intro L
      induction L with
      | nil => intro _; simp
      | cons F L ih =>
        intro h
        have hF := h F (by simp)
        have hL := ih (fun G hG => h G (by simp [hG]))
        simp only [List.map_cons, List.prod_cons, List.length_cons]
        refine ⟨?_, ?_⟩
        · nlinarith [hF.1, hL.1]
        · have hNF : 0 ≤ N F := by linarith [hF.1]
          have hP : 0 ≤ (L.map N).prod := by linarith [hL.1]
          rw [Real.mul_rpow hNF hP, pow_succ]
          have e : κ ^ L.length * κ * (N F ^ (-w) * (L.map N).prod ^ (-w)) =
              (κ * N F ^ (-w)) * (κ ^ L.length * (L.map N).prod ^ (-w)) := by ring
          rw [e]
          apply mul_le_mul hF.2 hL.2
          · exact mul_nonneg (pow_nonneg hκ.le _) (Real.rpow_nonneg hP _)
          · exact abs_nonneg _
    )
  have L_good_extract : ∀ (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
      (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
        N A * N B ≤ C * N (A * B))
      (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
        P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S)
      (w w' : ℝ) (hw : 0 ≤ w) (hww' : w < w')
      (hgood : ∀ B : ℝ, ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧ B ≤ N P ∧
        |Polynomial.aeval ξ P| ≤ N P ^ (-w')), ∀ B : ℝ, ∃ P : Polynomial ℤ, P.natDegree ≤ n ∧ Irreducible (P.map (Int.castRingHom ℚ)) ∧
            (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) ∧ B ≤ N P ∧
            |Polynomial.aeval ξ P| ≤ N P ^ (-w) :=
    (fun (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
        (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
          N A * N B ≤ C * N (A * B))
        (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
          P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S)
        (w w' : ℝ) (hw : 0 ≤ w) (hww' : w < w')
        (hgood : ∀ B : ℝ, ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧ B ≤ N P ∧
          |Polynomial.aeval ξ P| ≤ N P ^ (-w')) => by
      classical
      intro B
      by_contra hcon
      push_neg at hcon
      obtain ⟨C0, hC0, hgel0⟩ := hgel
      obtain ⟨C1, hC1def⟩ : ∃ C1 : ℝ, C1 = max C0 1 := ⟨_, rfl⟩
      have hC1one : 1 ≤ C1 := by rw [hC1def]; exact le_max_right _ _
      have hC01 : C0 ≤ C1 := by rw [hC1def]; exact le_max_left _ _
      have hgel1 : ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
          N A * N B ≤ C1 * N (A * B) := by
        intro A B' hA hB hd
        have h1 := hgel0 A B' hA hB hd
        have h2 : 0 ≤ N (A * B') := by rw [hN]; exact Nat.cast_nonneg _
        nlinarith
      obtain ⟨cB, hcB, hlow⟩ := L_good_lower n ξ hξ N hN B
      obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min cB 1 := ⟨_, rfl⟩
      have hκ : 0 < κ := by rw [hκdef]; exact lt_min hcB one_pos
      have hκ1 : κ ≤ 1 := by rw [hκdef]; exact min_le_right _ _
      have hκc : κ ≤ cB := by rw [hκdef]; exact min_le_left _ _
      obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = κ ^ n * (C1 ^ n) ^ (-w) := ⟨_, rfl⟩
      have hK : 0 < K := by
        rw [hKdef]
        exact mul_pos (pow_pos hκ n) (Real.rpow_pos_of_pos (pow_pos (by linarith) n) _)
      obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ, T0 = K ^ (-(1 / (w' - w))) := ⟨_, rfl⟩
      have hT0pos : 0 < T0 := by rw [hT0]; exact Real.rpow_pos_of_pos hK _
      obtain ⟨P, hP0, hPd, hPB, hPv⟩ := hgood (max 1 (T0 + 1))
      have hNP1 : 1 ≤ N P := le_trans (le_max_left _ _) hPB
      have hNPT : T0 < N P := by have := le_trans (le_max_right _ _) hPB; linarith
      obtain ⟨c, hc, L, hPL, hlen, hL⟩ := L_good_factor hgauss P hP0
      have hfac : ∀ F ∈ L, 1 ≤ N F ∧ κ * N F ^ (-w) ≤ |Polynomial.aeval ξ F| := by
        intro F hF
        obtain ⟨hF0, hFirr, hFprim⟩ := hL F hF
        have hFdvd : F ∣ P := by
          rw [hPL]; exact (List.dvd_prod hF).mul_left _
        have hFd : F.natDegree ≤ n := le_trans (Polynomial.natDegree_le_of_dvd hFdvd hP0) hPd
        have hNF := L_good_Ngeone N hN F hF0
        refine ⟨hNF, ?_⟩
        have hle1 : N F ^ (-w) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNF (by linarith)
        have hpos : 0 ≤ N F ^ (-w) := Real.rpow_nonneg (by linarith) _
        by_cases hBF : B ≤ N F
        · have := hcon F hFd hFirr hFprim hBF
          nlinarith
        · push_neg at hBF
          have := hlow F hF0 hFd hBF.le
          nlinarith
      obtain ⟨hprod1, hprodle⟩ := L_good_prodbound ξ N κ w hκ L hfac
      have hnorm := L_good_normprod n N hN C1 hC1one hgel1 L c hc (fun F hF => (hL F hF).1)
        (by rw [← hPL]; exact hPd)
      rw [← hPL] at hnorm
      have haeval := L_good_aeval ξ L c
      rw [← hPL] at haeval
      have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := by
        have := Int.one_le_abs hc
        exact_mod_cast this
      have hprodabs_nonneg : 0 ≤ (L.map fun F => |Polynomial.aeval ξ F|).prod := by
        have : 0 ≤ κ ^ L.length * ((L.map N).prod) ^ (-w) :=
          mul_nonneg (pow_nonneg hκ.le _) (Real.rpow_nonneg (by linarith) _)
        linarith
      have hge1 : (L.map fun F => |Polynomial.aeval ξ F|).prod ≤ |Polynomial.aeval ξ P| := by
        rw [haeval]; nlinarith
      have hlenn : L.length ≤ n := le_trans hlen hPd
      have hκpow : κ ^ n ≤ κ ^ L.length := pow_le_pow_of_le_one hκ.le hκ1 hlenn
      have hCpow : C1 ^ L.length ≤ C1 ^ n := pow_le_pow_right₀ hC1one hlenn
      have hprodN_le : (L.map N).prod ≤ C1 ^ n * N P := by
        have : C1 ^ L.length * N P ≤ C1 ^ n * N P := mul_le_mul_of_nonneg_right hCpow (by linarith)
        linarith
      have hrpow1 : (C1 ^ n * N P) ^ (-w) ≤ ((L.map N).prod) ^ (-w) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hprodN_le (by linarith)
      have hCnP : (C1 ^ n * N P) ^ (-w) = (C1 ^ n) ^ (-w) * N P ^ (-w) :=
        Real.mul_rpow (pow_nonneg (by linarith) _) (by linarith)
      have hchain : K * N P ^ (-w) ≤ N P ^ (-w') := by
        have h1 : κ ^ n * (C1 ^ n * N P) ^ (-w) ≤ κ ^ L.length * ((L.map N).prod) ^ (-w) := by
          apply mul_le_mul hκpow hrpow1
            (Real.rpow_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (by linarith)) _)
            (pow_nonneg hκ.le _)
        rw [hKdef, mul_assoc, ← hCnP]
        linarith
      have hsplit : N P ^ (-w') = N P ^ (-w) * N P ^ (-(w' - w)) := by
        rw [← Real.rpow_add (by linarith)]; congr 1; ring
      have hNPw : 0 < N P ^ (-w) := Real.rpow_pos_of_pos (by linarith) _
      have hK2 : K ≤ N P ^ (-(w' - w)) := by
        rw [hsplit] at hchain
        by_contra hlt
        push_neg at hlt
        have := mul_lt_mul_of_pos_left hlt hNPw
        linarith
      have hlt : N P ^ (-(w' - w)) < T0 ^ (-(w' - w)) :=
        Real.rpow_lt_rpow_of_neg hT0pos hNPT (by linarith)
      have hne : w' - w ≠ 0 := (sub_pos.mpr hww').ne'
      have hT0K : T0 ^ (-(w' - w)) = K := by
        rw [hT0, ← Real.rpow_mul hK.le, neg_mul_neg, one_div, inv_mul_cancel₀ hne, Real.rpow_one]
      linarith
    )
  have L_good : ∀ (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
        N A * N B ≤ C * N (A * B))
      (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
        P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S)
      (W ε : ℝ) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1), ∃ w : ℝ, 0 ≤ w ∧
        (∀ B : ℝ, ∃ P : Polynomial ℤ, P.natDegree ≤ n ∧ Irreducible (P.map (Int.castRingHom ℚ)) ∧
            (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) ∧ B ≤ N P ∧
            |Polynomial.aeval ξ P| ≤ N P ^ (-w)) ∧
        (W ≤ w ∨ ∃ B₀ : ℝ, ∀ R : Polynomial ℤ, R ≠ 0 → R.natDegree ≤ n → B₀ ≤ N R →
            N R ^ (-(w + ε)) ≤ |Polynomial.aeval ξ R|) :=
    (fun (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
          N A * N B ≤ C * N (A * B))
        (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
          P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S)
        (W ε : ℝ) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) => by
      classical
      set G : Set ℝ := {v | ∀ B : ℝ, ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧ B ≤ N P ∧
          |Polynomial.aeval ξ P| ≤ N P ^ (-v)} with hG
      have hhalf : (1/2 : ℝ) ∈ G := L_good_dirichlet n hn ξ hξ N hN (L_good_lower n ξ hξ N hN)
      by_cases hcase : ∃ v ∈ G, W < v
      · obtain ⟨v, hv, hWv⟩ := hcase
        exact ⟨W, hW, L_good_extract n hn ξ hξ N hN hgel hgauss W v hW hWv hv, Or.inl le_rfl⟩
      · push_neg at hcase
        have hbdd : BddAbove G := ⟨W, fun v hv => hcase v hv⟩
        have hne : G.Nonempty := ⟨1/2, hhalf⟩
        have hhalf_le : (1/2 : ℝ) ≤ sSup G := le_csSup hbdd hhalf
        refine ⟨sSup G - ε/2, by linarith, ?_, Or.inr ?_⟩
        · obtain ⟨v, hv, hlt⟩ := exists_lt_of_lt_csSup hne (show sSup G - ε/2 < sSup G by linarith)
          exact L_good_extract n hn ξ hξ N hN hgel hgauss (sSup G - ε/2) v (by linarith) hlt hv
        · have hnot : (sSup G + ε/2) ∉ G := fun h => by
            have := le_csSup hbdd h; linarith
          simp only [hG, Set.mem_setOf_eq, not_forall, not_exists, not_and] at hnot
          obtain ⟨B₀, hB₀⟩ := hnot
          refine ⟨B₀, fun R hR hRd hRB => ?_⟩
          have h1 := hB₀ R hR hRd hRB
          have h2 : sSup G - ε/2 + ε = sSup G + ε/2 := by ring
          rw [h2]
          exact le_of_lt (not_le.mp h1)
    )
  have L_height_int : ∀ (c : ℚ) (m : ℕ) (h : c.den ∣ m), ∃ z : ℤ, (m : ℚ) * c = z :=
    (fun (c : ℚ) (m : ℕ) (h : c.den ∣ m) => by
      obtain ⟨k, hk⟩ := h
      refine ⟨k * c.num, ?_⟩
      rw [hk]
      push_cast
      rw [← Rat.mul_den_eq_num]
      ring
    )
  have L_height_den : ∀ (c : ℚ) (m : ℕ) (hm : 0 < m) (z : ℤ) (h : (m : ℚ) * c = z), c.den ∣ m :=
    (fun (c : ℚ) (m : ℕ) (hm : 0 < m) (z : ℤ) (h : (m : ℚ) * c = z) => by
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      have hc : c = Rat.divInt z m := by
        rw [Rat.divInt_eq_div, ← h]
        push_cast
        field_simp
      have := Rat.den_dvd z m
      rw [← hc] at this
      exact_mod_cast this
    )
  have L_height_dvd : ∀ (α : ℂ) (q : Polynomial ℚ) (hint : IsIntegral ℚ α)
      (hq : Polynomial.aeval α q = 0), minpoly ℚ α ∣ q :=
    (fun (α : ℂ) (q : Polynomial ℚ) (hint : IsIntegral ℚ α)
        (hq : Polynomial.aeval α q = 0) => by
      have hmon := minpoly.monic hint
      have hdiv := Polynomial.modByMonic_add_div q hmon
      by_cases hr0 : Polynomial.modByMonic q (minpoly ℚ α) = 0
      · refine ⟨Polynomial.divByMonic q (minpoly ℚ α), ?_⟩
        rw [hr0, zero_add] at hdiv
        exact hdiv.symm
      · exfalso
        have hra : Polynomial.aeval α (Polynomial.modByMonic q (minpoly ℚ α)) = 0 := by
          have : Polynomial.aeval α (Polynomial.modByMonic q (minpoly ℚ α) +
              minpoly ℚ α * Polynomial.divByMonic q (minpoly ℚ α)) = 0 := by rw [hdiv]; exact hq
          simpa [minpoly.aeval] using this
        have hlt := Polynomial.degree_modByMonic_lt q hmon
        have hm1 := Polynomial.monic_mul_leadingCoeff_inv hr0
        have hm2 : Polynomial.aeval α (Polynomial.modByMonic q (minpoly ℚ α) *
            Polynomial.C (Polynomial.modByMonic q (minpoly ℚ α)).leadingCoeff⁻¹) = 0 := by
          simp [hra]
        have := minpoly.min ℚ α hm1 hm2
        rw [Polynomial.degree_mul_leadingCoeff_inv _ hr0] at this
        exact absurd hlt (not_lt.mpr this)
    )
  have L_height : ∀ (n : ℕ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
        N A * N B ≤ C * N (A * B))
      (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
        P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S), ∃ C : ℝ, 0 < C ∧ ∀ (S : Polynomial ℤ) (α : ℂ), S ≠ 0 → S.natDegree ≤ n →
        Polynomial.aeval α S = 0 → ∃ β : AlgebraicDegLE n, β.1 = α ∧ (height α : ℝ) ≤ C * N S :=
    (fun (n : ℕ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hgel : ∃ C : ℝ, 0 < C ∧ ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 → (A * B).natDegree ≤ n →
          N A * N B ≤ C * N (A * B))
        (hgauss : ∀ P S : Polynomial ℤ, (∀ d : ℤ, (∀ i, d ∣ P.coeff i) → IsUnit d) →
          P.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) → P ∣ S) => by
      obtain ⟨C, hC, hgel'⟩ := hgel
      refine ⟨C, hC, ?_⟩
      intro S α hS hdeg hroot
      have hq0 : S.map (Int.castRingHom ℚ) ≠ 0 := by
        intro h
        apply hS
        ext i
        have := congrArg (fun P => Polynomial.coeff P i) h
        simpa using this
      have hqa : Polynomial.aeval α (S.map (Int.castRingHom ℚ)) = 0 := by
        rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]
        exact hroot
      have halg : IsAlgebraic ℚ α := ⟨_, hq0, hqa⟩
      have hint : IsIntegral ℚ α := by
        refine ⟨_, Polynomial.monic_mul_leadingCoeff_inv hq0, ?_⟩
        rw [← Polynomial.aeval_def]
        simp [hqa]
      have hpq : minpoly ℚ α ∣ S.map (Int.castRingHom ℚ) := L_height_dvd α _ hint hqa
      have hpdeg : (minpoly ℚ α).natDegree ≤ n :=
        le_trans (Polynomial.natDegree_le_of_dvd hpq hq0)
          (le_trans (Polynomial.natDegree_map_le) hdeg)
      refine ⟨⟨α, halg, hpdeg⟩, rfl, ?_⟩
      have hmon := minpoly.monic hint
      set p := minpoly ℚ α with hp
      set D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val) with hD
      have hheight : height α = Finset.sup p.support (fun i ↦ ((D : ℚ) * p.coeff i).num.natAbs) := rfl
      have hDpos : 0 < D := by
        rw [Nat.pos_iff_ne_zero, hD, Ne, Multiset.lcm_eq_zero_iff]
        intro h
        rw [Multiset.mem_map] at h
        obtain ⟨i, -, hi⟩ := h
        exact (p.coeff i).den_ne_zero hi
      have hdenD : ∀ i ∈ p.support, (p.coeff i).den ∣ D := fun i hi =>
        Multiset.dvd_lcm (Multiset.mem_map_of_mem _ hi)
      have hintall : ∀ i, ∃ z : ℤ, (D : ℚ) * p.coeff i = z := by
        intro i
        by_cases hi : i ∈ p.support
        · exact L_height_int _ _ (hdenD i hi)
        · refine ⟨0, ?_⟩
          rw [Polynomial.notMem_support_iff.mp hi]
          simp
      have hnum : ∀ i, ((((D : ℚ) * p.coeff i).num : ℤ) : ℚ) = (D : ℚ) * p.coeff i := by
        intro i
        obtain ⟨z, hz⟩ := hintall i
        rw [hz, Rat.num_intCast]
      set P0 : Polynomial ℤ := ∑ i ∈ p.support, Polynomial.monomial i (((D : ℚ) * p.coeff i).num)
        with hP0
      have hP0coeff : ∀ i, P0.coeff i = ((D : ℚ) * p.coeff i).num := by
        intro i
        rw [hP0, Polynomial.finset_sum_coeff]
        by_cases h : i ∈ p.support
        · rw [Finset.sum_eq_single i]
          · simp
          · intro b _ hb
            simp [Polynomial.coeff_monomial, hb]
          · intro h'
            exact absurd h h'
        · rw [Finset.sum_eq_zero]
          · rw [Polynomial.notMem_support_iff.mp h]
            simp
          · intro b hb
            have : b ≠ i := fun e => h (e ▸ hb)
            simp [Polynomial.coeff_monomial, this]
      have hP0map : P0.map (Int.castRingHom ℚ) = Polynomial.C (D : ℚ) * p := by
        ext i
        rw [Polynomial.coeff_map, Polynomial.coeff_C_mul, hP0coeff]
        simpa using hnum i
      have hP0supp : P0.support = p.support := by
        ext i
        rw [Polynomial.mem_support_iff, Polynomial.mem_support_iff, hP0coeff]
        have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
        constructor
        · intro h h'
          apply h
          rw [h', mul_zero]
          rfl
        · intro h h'
          rw [Rat.num_eq_zero] at h'
          rcases mul_eq_zero.mp h' with h'' | h''
          · exact hD0 h''
          · exact h h''
      have hNP0 : N P0 = (height α : ℝ) := by
        rw [hN, hheight, hP0supp]
        simp only [hP0coeff]
      have hlead : P0.coeff p.natDegree = D := by
        rw [hP0coeff, hmon.coeff_natDegree, mul_one, Rat.num_natCast]
      have hprim : ∀ d : ℤ, (∀ i, d ∣ P0.coeff i) → IsUnit d := by
        intro d hd
        rw [Int.isUnit_iff_natAbs_eq]
        have hde : ∀ i, ((d.natAbs : ℕ) : ℤ) ∣ P0.coeff i := fun i => Int.natAbs_dvd.mpr (hd i)
        have heD : d.natAbs ∣ D := by
          have := hde p.natDegree
          rw [hlead] at this
          exact_mod_cast this
        have he0 : 0 < d.natAbs := Nat.pos_of_dvd_of_pos heD hDpos
        by_contra hne
        have he2 : 2 ≤ d.natAbs := by omega
        obtain ⟨D', hD'⟩ := heD
        have hD'pos : 0 < D' := by
          rcases Nat.eq_zero_or_pos D' with h | h
          · rw [h, mul_zero] at hD'
            omega
          · exact h
        have hdvd : D ∣ D' := by
          rw [hD]
          apply Multiset.lcm_dvd.mpr
          intro b hb
          rw [Multiset.mem_map] at hb
          obtain ⟨i, -, rfl⟩ := hb
          obtain ⟨w, hw⟩ := hde i
          rw [hP0coeff] at hw
          apply L_height_den _ D' hD'pos w
          have h1 := hnum i
          rw [hw] at h1
          have hDq : (D : ℚ) = (d.natAbs : ℚ) * D' := by exact_mod_cast hD'
          rw [hDq] at h1
          have he' : (d.natAbs : ℚ) ≠ 0 := by exact_mod_cast he0.ne'
          rw [Int.cast_mul, Int.cast_natCast] at h1
          apply mul_left_cancel₀ he'
          linear_combination -h1
        have hle : D ≤ D' := Nat.le_of_dvd hD'pos hdvd
        have : 2 * D' ≤ d.natAbs * D' := Nat.mul_le_mul_right _ he2
        omega
      have hdivq : P0.map (Int.castRingHom ℚ) ∣ S.map (Int.castRingHom ℚ) := by
        rw [hP0map]
        obtain ⟨T, hT⟩ := hpq
        refine ⟨Polynomial.C ((D : ℚ)⁻¹) * T, ?_⟩
        rw [hT]
        have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
        calc p * T = (Polynomial.C (D : ℚ) * Polynomial.C ((D : ℚ)⁻¹)) * (p * T) := by
              rw [← Polynomial.C_mul, mul_inv_cancel₀ hD0, Polynomial.C_1, one_mul]
          _ = _ := by ring
      obtain ⟨T, hT⟩ := hgauss P0 S hprim hdivq
      have hT0 : T ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hT
        exact hS hT
      have hP00 : P0 ≠ 0 := by
        intro h
        have := hlead
        rw [h, Polynomial.coeff_zero] at this
        omega
      have hg := hgel' P0 T hP00 hT0 (by rw [← hT]; exact hdeg)
      have hNT : 1 ≤ N T := by
        rw [hN]
        obtain ⟨i, hi⟩ := Polynomial.nonempty_support_iff.mpr hT0
        have h1 : 1 ≤ (T.coeff i).natAbs := Int.natAbs_pos.mpr (Polynomial.mem_support_iff.mp hi)
        have h2 : (T.coeff i).natAbs ≤ T.support.sup (fun i => (T.coeff i).natAbs) :=
          Finset.le_sup (f := fun i => (T.coeff i).natAbs) hi
        exact_mod_cast (le_trans h1 h2)
      have hNP0nn : 0 ≤ N P0 := by
        rw [hN]
        positivity
      rw [← hNP0, hT]
      calc N P0 = N P0 * 1 := (mul_one _).symm
        _ ≤ N P0 * N T := mul_le_mul_of_nonneg_left hNT hNP0nn
        _ ≤ C * N (P0 * T) := hg
    )
  have L_mii_poly_of_vec : ∀ (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (a : Fin (n + 1) → ℤ), ∃ p : Polynomial ℤ, p.natDegree ≤ n ∧ (∀ k : Fin (n + 1), p.coeff (k : ℕ) = a k) ∧
        N p = ((Finset.univ.sup fun k => (a k).natAbs : ℕ) : ℝ) ∧
        Polynomial.aeval ξ p = ∑ k : Fin (n + 1), (a k : ℝ) * ξ ^ (k : ℕ) :=
    (fun (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (a : Fin (n + 1) → ℤ) => by
      obtain ⟨p, hp⟩ : ∃ p : Polynomial ℤ,
          p = ∑ k : Fin (n + 1), Polynomial.C (a k) * Polynomial.X ^ (k : ℕ) := ⟨_, rfl⟩
      have hcoeff : ∀ i : ℕ, p.coeff i = ∑ k : Fin (n + 1), if i = (k : ℕ) then a k else 0 := by
        intro i
        rw [hp, Polynomial.finset_sum_coeff]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Polynomial.coeff_C_mul_X_pow]
      have hcoeffk : ∀ k : Fin (n + 1), p.coeff (k : ℕ) = a k := by
        intro k
        rw [hcoeff]
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb
          rw [if_neg]
          intro h
          exact hb (Fin.ext h.symm)
        · intro h
          exact absurd (Finset.mem_univ k) h
      have hcoeff_big : ∀ i : ℕ, n < i → p.coeff i = 0 := by
        intro i hi
        rw [hcoeff]
        refine Finset.sum_eq_zero ?_
        intro k _
        rw [if_neg]
        intro h
        have := k.isLt
        omega
      have hdeg : p.natDegree ≤ n := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        exact hcoeff_big
      refine ⟨p, hdeg, hcoeffk, ?_, ?_⟩
      · rw [hN]
        congr 1
        apply le_antisymm
        · apply Finset.sup_le
          intro i hi
          have hi' : i < n + 1 := by
            by_contra h
            push_neg at h
            have h0 := hcoeff_big i (by omega)
            rw [Polynomial.mem_support_iff] at hi
            exact hi h0
          have h2 : p.coeff i = a ⟨i, hi'⟩ := hcoeffk ⟨i, hi'⟩
          show (p.coeff i).natAbs ≤ _
          rw [h2]
          exact Finset.le_sup (f := fun k => (a k).natAbs) (Finset.mem_univ _)
        · apply Finset.sup_le
          intro k _
          by_cases hk : a k = 0
          · simp [hk]
          · have hmem : (k : ℕ) ∈ p.support := by
              rw [Polynomial.mem_support_iff, hcoeffk]
              exact hk
            calc (a k).natAbs = (p.coeff (k : ℕ)).natAbs := by rw [hcoeffk]
              _ ≤ _ := Finset.le_sup (f := fun i => (p.coeff i).natAbs) hmem
      · rw [hp, map_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        simp
    )
  have L_mii_linindep : ∀ (n : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℤ)
      (P : Fin (n + 1) → Polynomial ℤ)
      (hP : ∀ i, ∀ k : Fin (n + 1), (P i).coeff (k : ℕ) = x i k)
      (hdeg : ∀ i, (P i).natDegree ≤ n)
      (hx : LinearIndependent ℝ (fun i => fun k => (x i k : ℝ))), LinearIndependent ℚ (fun i => (P i).map (Int.castRingHom ℚ)) :=
    (fun (n : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℤ)
        (P : Fin (n + 1) → Polynomial ℤ)
        (hP : ∀ i, ∀ k : Fin (n + 1), (P i).coeff (k : ℕ) = x i k)
        (hdeg : ∀ i, (P i).natDegree ≤ n)
        (hx : LinearIndependent ℝ (fun i => fun k => (x i k : ℝ))) => by
      rw [Fintype.linearIndependent_iff] at hx ⊢
      intro g hg i
      have hcoef : ∀ k : Fin (n + 1), ∑ j, g j * (x j k : ℚ) = 0 := by
        intro k
        have h1 := congrArg (fun p => Polynomial.coeff p (k : ℕ)) hg
        simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul, Polynomial.coeff_map, hP,
          Polynomial.coeff_zero, smul_eq_mul, eq_intCast] at h1
        exact h1
      have hR : ∑ j, ((g j : ℚ) : ℝ) • (fun k => (x j k : ℝ)) = 0 := by
        funext k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have h2 := congrArg (fun q : ℚ => (q : ℝ)) (hcoef k)
        simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zero] at h2
        exact h2
      have h3 := hx (fun j => (g j : ℝ)) hR i
      exact_mod_cast h3
    )
  have L_mii_dep_drop : ∀ {n d : ℕ} (w : Fin n → Fin (d+1) → ℝ)
      (hw : ∀ j, w j (Fin.last d) = 0) (h : LinearIndependent ℝ w), LinearIndependent ℝ (fun j (k : Fin d) => w j (Fin.castSucc k)) :=
    (fun {n d : ℕ} (w : Fin n → Fin (d+1) → ℝ)
        (hw : ∀ j, w j (Fin.last d) = 0) (h : LinearIndependent ℝ w) => by
      rw [Fintype.linearIndependent_iff] at h ⊢
      intro g hg
      apply h g
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp [Finset.sum_apply, hw]
      · have := congrFun hg k
        simpa [Finset.sum_apply] using this
    )
  have L_mii_dep_elim : ∀ {n d : ℕ} (v : Fin (n+1) → Fin (d+1) → ℝ) (i0 : Fin (n+1))
      (h : LinearIndependent ℝ v), LinearIndependent ℝ (fun j => v (i0.succAbove j)
        - (v (i0.succAbove j) (Fin.last d) / v i0 (Fin.last d)) • v i0) :=
    (fun {n d : ℕ} (v : Fin (n+1) → Fin (d+1) → ℝ) (i0 : Fin (n+1))
        (h : LinearIndependent ℝ v) => by
      rw [Fintype.linearIndependent_iff] at h ⊢
      intro g hg j
      have key := h (Fin.insertNth i0
        (-(∑ j, g j * (v (i0.succAbove j) (Fin.last d) / v i0 (Fin.last d)))) g) (by
        rw [Fin.sum_univ_succAbove _ i0]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul] at hg
        rw [neg_smul, neg_add_eq_sub]
        exact hg) (i0.succAbove j)
      simpa [Fin.insertNth_apply_succAbove] using key
    )
  have L_mii_dep_aux : ∀ (d : ℕ), ∀ (m : ℕ), d < m → ∀ (v : Fin m → Fin d → ℝ),
      ¬ LinearIndependent ℝ v :=
    (fun (d : ℕ) => by
      induction d with
      | zero =>
        intro m hm v hv
        have h0 := hv.ne_zero ⟨0, hm⟩
        exact h0 (Subsingleton.elim _ _)
      | succ d ih =>
        intro m hm v hv
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        by_cases hall : ∀ i, v i (Fin.last d) = 0
        · exact ih (n+1) (by omega) _ (L_mii_dep_drop v hall hv)
        · push_neg at hall
          obtain ⟨i0, hi0⟩ := hall
          have hw := L_mii_dep_elim v i0 hv
          have hlast : ∀ j, (v (i0.succAbove j) - (v (i0.succAbove j) (Fin.last d)
              / v i0 (Fin.last d)) • v i0) (Fin.last d) = 0 := by
            intro j
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            rw [div_mul_cancel₀ _ hi0, sub_self]
          exact ih n (by omega) _ (L_mii_dep_drop _ hlast hw)
    )
  have L_mii_dep : ∀ (m d : ℕ) (hmd : d < m) (v : Fin m → Fin d → ℝ), ¬ LinearIndependent ℝ v :=
    (fun (m d : ℕ) (hmd : d < m) (v : Fin m → Fin d → ℝ) => by
      exact L_mii_dep_aux d m hmd v
    )
  have L_mii_limit : ∀ (d : ℕ) (A c E : ℝ) (hA : 0 < A) (hc : 0 < c) (hE : 0 < E)
      (lam : Fin d → ℝ) (hlam : ∀ j, 0 < lam j)
      (h : ∀ T : ℝ, 2 * E ≤ T → c * T ^ d / E ≤ ∏ j, (A * T / lam j + 2)), ∏ j, lam j ≤ A ^ d / c * E :=
    (fun (d : ℕ) (A c E : ℝ) (hA : 0 < A) (hc : 0 < c) (hE : 0 < E)
        (lam : Fin d → ℝ) (hlam : ∀ j, 0 < lam j)
        (h : ∀ T : ℝ, 2 * E ≤ T → c * T ^ d / E ≤ ∏ j, (A * T / lam j + 2)) => by
      have hP : 0 < ∏ j, lam j := Finset.prod_pos (fun j _ => hlam j)
      set f : ℝ → ℝ := fun s => ∏ j, (A / lam j + 2 * s) with hf
      have hfc : Continuous f := by
        apply continuous_finset_prod
        intro j _
        exact continuous_const.add (continuous_const.mul continuous_id)
      have hkey : ∀ s : ℝ, 0 < s → s ≤ 1 / (2 * E) → c / E ≤ f s := by
        intro s hs hsE
        have hT : 2 * E ≤ 1 / s := by
          rw [le_div_iff₀ hs]
          rw [le_div_iff₀ (by positivity)] at hsE
          linarith
        have h1 := h (1 / s) hT
        have h2 : ∏ j, (A * (1 / s) / lam j + 2) = (1 / s) ^ d * f s := by
          have e : ∀ j, A * (1 / s) / lam j + 2 = (1 / s) * (A / lam j + 2 * s) := by
            intro j
            have := (hlam j).ne'
            have := hs.ne'
            field_simp
          simp only [hf, e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
        rw [h2] at h1
        have hTd : 0 < (1 / s) ^ d := by positivity
        have h3 : (1 / s) ^ d * (c / E) ≤ (1 / s) ^ d * f s := by
          calc (1 / s) ^ d * (c / E) = c * (1 / s) ^ d / E := by ring
            _ ≤ (1 / s) ^ d * f s := h1
        exact le_of_mul_le_mul_left h3 hTd
      have hlim : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) :=
        (hfc.tendsto 0).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), c / E ≤ f s := by
        have : Set.Ioo (0:ℝ) (1 / (2 * E)) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
          Ioo_mem_nhdsGT (by positivity)
        filter_upwards [this] with s hs
        exact hkey s hs.1 hs.2.le
      have hle : c / E ≤ f 0 := ge_of_tendsto hlim hev
      have hf0 : f 0 = A ^ d / ∏ j, lam j := by
        simp only [hf, mul_zero, add_zero]
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hf0] at hle
      rw [div_le_div_iff₀ hE hP] at hle
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith
    )
  have L_mii_count_lower : ∀ (n : ℕ) (ξ : ℝ), ∃ c : ℝ, 0 < c ∧ ∀ q : ℝ, 0 ≤ q → ∀ T : ℝ, 2 * Real.exp q ≤ T →
        ∃ S : Finset (Fin (n + 1) → ℤ), c * T ^ (n + 1) / Real.exp q ≤ S.card ∧
          ∀ z ∈ S, (∀ k, |(z k : ℝ)| ≤ T) ∧
            Real.exp q * |∑ k : Fin (n + 1), (z k : ℝ) * ξ ^ (k : ℕ)| ≤ T :=
    (fun (n : ℕ) (ξ : ℝ) => by
      set A : ℝ := 1 + |ξ| with hA
      have hA1 : 1 ≤ A := by have := abs_nonneg ξ; linarith
      set K : ℝ := 2 * n * A ^ n + 2 with hK
      have hKpos : 0 < K := by positivity
      have hK2 : 2 * n * A ^ n ≤ K := by linarith
      have hK2' : (2:ℝ) ≤ K := by
        have : 0 ≤ 2 * (n:ℝ) * A ^ n := by positivity
        linarith
      refine ⟨1 / (2 * K ^ n), by positivity, ?_⟩
      intro q hq T hT
      have heq : 0 < Real.exp q := Real.exp_pos q
      have heq1 : 1 ≤ Real.exp q := Real.one_le_exp hq
      have hT0 : 0 < T := by linarith
      set R : ℝ := T / K with hR
      have hR0 : 0 ≤ R := by positivity
      have hRT : R ≤ T := by
        rw [hR, div_le_iff₀ hKpos]
        nlinarith
      set L : ℝ := T / Real.exp q with hL
      have hL2 : 2 ≤ L := by rw [hL, le_div_iff₀ heq]; linarith
      have hLT : L ≤ T := by rw [hL]; exact div_le_self hT0.le heq1
      let s : (Fin n → ℤ) → ℝ := fun t => ∑ i : Fin n, (t i : ℝ) * ξ ^ ((i : ℕ) + 1)
      let P : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-⌊R⌋) ⌊R⌋
      let I : (Fin n → ℤ) → Finset ℤ := fun t => Finset.Icc ⌈-s t - L / 2⌉ ⌊-s t + L / 2⌋
      let f : (Σ _ : (Fin n → ℤ), ℤ) → (Fin (n + 1) → ℤ) := fun p => Fin.cons p.2 p.1
      have hf : Function.Injective f := by
        rintro ⟨t, a⟩ ⟨t', a'⟩ h
        obtain ⟨rfl, rfl⟩ := Fin.cons_injective2 h
        rfl
      have hPmem : ∀ t ∈ P, ∀ i, |(t i : ℝ)| ≤ R := by
        intro t ht i
        have hti := Fintype.mem_piFinset.mp ht i
        rw [Finset.mem_Icc] at hti
        have h1 : ((-⌊R⌋ : ℤ) : ℝ) ≤ (t i : ℝ) := by exact_mod_cast hti.1
        have h2 : (t i : ℝ) ≤ ((⌊R⌋ : ℤ) : ℝ) := by exact_mod_cast hti.2
        have h3 : ((⌊R⌋ : ℤ) : ℝ) ≤ R := Int.floor_le R
        push_cast at h1
        rw [abs_le]; constructor <;> linarith
      have hs : ∀ t ∈ P, |s t| ≤ T / 2 := by
        intro t ht
        have hb : ∀ i : Fin n, |(t i : ℝ) * ξ ^ ((i : ℕ) + 1)| ≤ R * A ^ n := by
          intro i
          rw [abs_mul, abs_pow]
          have h1 : |ξ| ^ ((i : ℕ) + 1) ≤ A ^ ((i : ℕ) + 1) :=
            pow_le_pow_left₀ (abs_nonneg ξ) (by linarith) _
          have h2 : A ^ ((i : ℕ) + 1) ≤ A ^ n := pow_le_pow_right₀ hA1 (by omega)
          have h3 := hPmem t ht i
          have h4 : 0 ≤ |ξ| ^ ((i : ℕ) + 1) := by positivity
          calc |(t i : ℝ)| * |ξ| ^ ((i : ℕ) + 1) ≤ R * |ξ| ^ ((i : ℕ) + 1) :=
                mul_le_mul_of_nonneg_right h3 h4
            _ ≤ R * A ^ n := mul_le_mul_of_nonneg_left (h1.trans h2) hR0
        have hAn : 0 ≤ A ^ n := by positivity
        have hmain : (n:ℝ) * (R * A ^ n) ≤ T / 2 := by
          have e1 : (n:ℝ) * (R * A ^ n) = (2 * n * A ^ n) * T / (2 * K) := by
            rw [hR]; field_simp
          rw [e1, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        calc |s t| ≤ ∑ i : Fin n, |(t i : ℝ) * ξ ^ ((i : ℕ) + 1)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, R * A ^ n := Finset.sum_le_sum (fun i _ => hb i)
          _ = n * (R * A ^ n) := by simp
          _ ≤ T / 2 := hmain
      have hIcard : ∀ t, L / 2 ≤ ((I t).card : ℝ) := by
        intro t
        simp only [I]
        rw [Int.card_Icc]
        have h1 := Int.sub_one_lt_floor (-s t + L / 2)
        have h2 := Int.ceil_lt_add_one (-s t - L / 2)
        have h3 : (((⌊-s t + L / 2⌋ + 1 - ⌈-s t - L / 2⌉ : ℤ)) : ℝ) ≤
            (((⌊-s t + L / 2⌋ + 1 - ⌈-s t - L / 2⌉).toNat : ℕ) : ℝ) := by
          exact_mod_cast Int.self_le_toNat _
        push_cast at h3
        linarith
      have hPcard : R ^ n ≤ (P.card : ℝ) := by
        simp only [P]
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Int.card_Icc]
        push_cast
        apply pow_le_pow_left₀ hR0
        have h1 := Int.lt_floor_add_one R
        have h0 : (0:ℤ) ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR0
        have h3 : (((⌊R⌋ + 1 - -⌊R⌋ : ℤ)) : ℝ) ≤ (((⌊R⌋ + 1 - -⌊R⌋).toNat : ℕ) : ℝ) := by
          exact_mod_cast Int.self_le_toNat _
        have h0' : (0:ℝ) ≤ ((⌊R⌋ : ℤ) : ℝ) := by exact_mod_cast h0
        push_cast at h3
        linarith
      refine ⟨(P.sigma I).image f, ?_, ?_⟩
      · rw [Finset.card_image_of_injective _ hf, Finset.card_sigma]
        push_cast
        have hsum : (P.card : ℝ) * (L / 2) ≤ ∑ t ∈ P, ((I t).card : ℝ) := by
          have := Finset.sum_le_sum (s := P) (fun t _ => hIcard t)
          simpa [Finset.sum_const, nsmul_eq_mul] using this
        have heqn : 1 / (2 * K ^ n) * T ^ (n + 1) / Real.exp q = R ^ n * (L / 2) := by
          rw [hR, hL, div_pow, pow_succ]
          field_simp
        rw [heqn]
        calc R ^ n * (L / 2) ≤ (P.card : ℝ) * (L / 2) :=
              mul_le_mul_of_nonneg_right hPcard (by linarith)
          _ ≤ _ := hsum
      · intro z hz
        obtain ⟨⟨t, a⟩, hmem, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_sigma] at hmem
        obtain ⟨ht, ha⟩ := hmem
        have ha' : a ∈ Finset.Icc ⌈-s t - L / 2⌉ ⌊-s t + L / 2⌋ := ha
        rw [Finset.mem_Icc] at ha'
        have ha1 : -s t - L / 2 ≤ (a : ℝ) := Int.ceil_le.mp ha'.1
        have ha2 : (a : ℝ) ≤ -s t + L / 2 := Int.le_floor.mp ha'.2
        have has : |(a : ℝ) + s t| ≤ L / 2 := by rw [abs_le]; constructor <;> linarith
        have hst := hs t ht
        have hsum : ∑ k : Fin (n + 1), ((f ⟨t, a⟩ k : ℤ) : ℝ) * ξ ^ (k : ℕ) = (a : ℝ) + s t := by
          rw [Fin.sum_univ_succ]
          simp [f, s, Fin.cons_zero, Fin.cons_succ, Fin.val_succ]
        refine ⟨?_, ?_⟩
        · intro k
          refine Fin.cases ?_ (fun i => ?_) k
          · simp only [f, Fin.cons_zero]
            have habs : |(a : ℝ)| ≤ |(a : ℝ) + s t| + |s t| := by
              have := abs_sub ((a : ℝ) + s t) (s t)
              simpa using this
            linarith
          · simp only [f, Fin.cons_succ]
            exact (hPmem t ht i).trans hRT
        · rw [hsum]
          calc Real.exp q * |(a : ℝ) + s t| ≤ Real.exp q * (L / 2) :=
                mul_le_mul_of_nonneg_left has heq.le
            _ = T / 2 := by rw [hL]; field_simp
            _ ≤ T := by linarith
    )
  have L_mii_minima_avoid : ∀ (d i : ℕ) (hi : i < d) (y : Fin i → Fin d → ℝ), ∃ z : Fin d → ℤ, (fun k => (z k : ℝ)) ∉ Submodule.span ℝ (Set.range y) :=
    (fun (d i : ℕ) (hi : i < d) (y : Fin i → Fin d → ℝ) => by
      by_contra hcon
      push_neg at hcon
      have hc : ∀ k : Fin d, ∃ c : Fin i → ℝ, ∑ j, c j • y j = Pi.basisFun ℝ (Fin d) k := by
        intro k
        have h := hcon (Pi.single k 1)
        have he : (fun k' => ((Pi.single k (1:ℤ) : Fin d → ℤ) k' : ℝ)) = Pi.basisFun ℝ (Fin d) k := by
          funext k'
          rw [Pi.basisFun_apply]
          by_cases hk : k' = k
          · subst hk; simp
          · simp [hk]
        rw [he] at h
        exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp h
      choose c hc using hc
      apply L_mii_dep d i hi c
      apply LinearIndependent.of_comp (Fintype.linearCombination ℝ y)
      have : (Fintype.linearCombination ℝ y) ∘ c = Pi.basisFun ℝ (Fin d) := by
        funext k
        simp only [Function.comp_apply, Fintype.linearCombination_apply]
        exact hc k
      rw [this]
      exact (Pi.basisFun ℝ (Fin d)).linearIndependent
    )
  have L_mii_minima_step : ∀ (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
      (hfin : ∀ T : ℝ, Set.Finite {z : Fin d → ℤ | ν (fun k => (z k : ℝ)) ≤ T})
      (S : Submodule ℝ (Fin d → ℝ)) (z0 : Fin d → ℤ) (hz0 : (fun k => (z0 k : ℝ)) ∉ S), ∃ z : Fin d → ℤ, (fun k => (z k : ℝ)) ∉ S ∧ ∀ w : Fin d → ℤ, (fun k => (w k : ℝ)) ∉ S →
        ν (fun k => (z k : ℝ)) ≤ ν (fun k => (w k : ℝ)) :=
    (fun (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
        (hfin : ∀ T : ℝ, Set.Finite {z : Fin d → ℤ | ν (fun k => (z k : ℝ)) ≤ T})
        (S : Submodule ℝ (Fin d → ℝ)) (z0 : Fin d → ℤ) (hz0 : (fun k => (z0 k : ℝ)) ∉ S) => by
      have hF : Set.Finite {z : Fin d → ℤ | (fun k => (z k : ℝ)) ∉ S ∧
          ν (fun k => (z k : ℝ)) ≤ ν (fun k => (z0 k : ℝ))} :=
        (hfin _).subset (fun z hz => hz.2)
      obtain ⟨z, hz, hmin⟩ := Set.exists_min_image _ (fun z : Fin d → ℤ => ν (fun k => (z k : ℝ))) hF
        ⟨z0, hz0, le_rfl⟩
      refine ⟨z, hz.1, fun w hw => ?_⟩
      by_cases h : ν (fun k => (w k : ℝ)) ≤ ν (fun k => (z0 k : ℝ))
      · exact hmin w ⟨hw, h⟩
      · push_neg at h
        exact le_trans hz.2 h.le
    )
  have L_mii_minima_ind : ∀ (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
      (hfin : ∀ T : ℝ, Set.Finite {z : Fin d → ℤ | ν (fun k => (z k : ℝ)) ≤ T}), ∀ i : ℕ, i ≤ d → ∃ x : Fin i → Fin d → ℤ, LinearIndependent ℝ (fun j => fun k => (x j k : ℝ)) ∧
        (∀ a b : Fin i, a ≤ b → ν (fun k => (x a k : ℝ)) ≤ ν (fun k => (x b k : ℝ))) ∧
        ∀ a : Fin i, ∀ z : Fin d → ℤ,
          (fun k => (z k : ℝ)) ∉ Submodule.span ℝ
            (Set.range fun j : {j : Fin i // j < a} => fun k => (x j k : ℝ)) →
          ν (fun k => (x a k : ℝ)) ≤ ν (fun k => (z k : ℝ)) :=
    (fun (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
        (hfin : ∀ T : ℝ, Set.Finite {z : Fin d → ℤ | ν (fun k => (z k : ℝ)) ≤ T}) => by
      intro i
      induction i with
      | zero =>
        intro _
        exact ⟨fun j => Fin.elim0 j, linearIndependent_empty_type, fun a => Fin.elim0 a,
          fun a => Fin.elim0 a⟩
      | succ i ih =>
        intro hi
        obtain ⟨x, hli, hmono, hmin⟩ := ih (by omega)
        obtain ⟨z0, hz0⟩ := L_mii_minima_avoid d i (by omega) (fun j => fun k => (x j k : ℝ))
        obtain ⟨z, hz, hzmin⟩ := L_mii_minima_step d ν hfin _ z0 hz0
        refine ⟨Fin.snoc (α := fun _ => Fin d → ℤ) x z, ?_, ?_, ?_⟩
        · have heq : (fun j : Fin (i+1) => fun k =>
              ((Fin.snoc (α := fun _ => Fin d → ℤ) x z j) k : ℝ)) =
              Fin.snoc (α := fun _ => Fin d → ℝ) (fun j k => (x j k : ℝ)) (fun k => (z k : ℝ)) := by
            funext j
            induction j using Fin.lastCases with
            | last => simp
            | cast j' => simp
          rw [heq, linearIndependent_fin_snoc]
          exact ⟨hli, hz⟩
        · intro a b hab
          induction b using Fin.lastCases with
          | last =>
            induction a using Fin.lastCases with
            | last => exact le_rfl
            | cast a' =>
              simp only [Fin.snoc_castSucc, Fin.snoc_last]
              apply hmin a' z
              intro hmem
              apply hz
              refine Submodule.span_mono ?_ hmem
              rintro _ ⟨j, rfl⟩
              exact ⟨j.1, rfl⟩
          | cast b' =>
            induction a using Fin.lastCases with
            | last => exact absurd hab (not_le.mpr (Fin.castSucc_lt_last b'))
            | cast a' =>
              simp only [Fin.snoc_castSucc]
              exact hmono a' b' (Fin.castSucc_le_castSucc_iff.mp hab)
        · intro a w hw
          induction a using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_last]
            apply hzmin w
            intro hmem
            apply hw
            refine Submodule.span_mono ?_ hmem
            rintro _ ⟨j, rfl⟩
            exact ⟨⟨Fin.castSucc j, Fin.castSucc_lt_last j⟩, by simp⟩
          | cast a' =>
            simp only [Fin.snoc_castSucc]
            apply hmin a' w
            intro hmem
            apply hw
            refine Submodule.span_mono ?_ hmem
            rintro _ ⟨j, rfl⟩
            exact ⟨⟨Fin.castSucc j.1, Fin.castSucc_lt_castSucc_iff.mpr j.2⟩, by simp⟩
    )
  have L_mii_minima : ∀ (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
      (hfin : ∀ T : ℝ, Set.Finite {z : Fin d → ℤ | ν (fun k => (z k : ℝ)) ≤ T}), ∃ x : Fin d → Fin d → ℤ, LinearIndependent ℝ (fun i => fun k => (x i k : ℝ)) ∧
        Monotone (fun i => ν (fun k => (x i k : ℝ))) ∧
        ∀ i : Fin d, ∀ z : Fin d → ℤ,
          (fun k => (z k : ℝ)) ∉ Submodule.span ℝ
            (Set.range fun j : {j : Fin d // j < i} => fun k => (x j k : ℝ)) →
          ν (fun k => (x i k : ℝ)) ≤ ν (fun k => (z k : ℝ)) :=
    (fun (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
        (hfin : ∀ T : ℝ, Set.Finite {z : Fin d → ℤ | ν (fun k => (z k : ℝ)) ≤ T}) => by
      obtain ⟨x, hli, hmono, hmin⟩ := L_mii_minima_ind d ν hfin d le_rfl
      exact ⟨x, hli, fun a b hab => hmono a b hab, hmin⟩
    )
  have L_mii_nearorth_nonneg : ∀ (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
      (hsub : ∀ u v, ν (u + v) ≤ ν u + ν v) (hhom : ∀ (c : ℝ) v, ν (c • v) = |c| * ν v)
      (v : Fin d → ℝ), 0 ≤ ν v :=
    (fun (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
        (hsub : ∀ u v, ν (u + v) ≤ ν u + ν v) (hhom : ∀ (c : ℝ) v, ν (c • v) = |c| * ν v)
        (v : Fin d → ℝ) => by
      have h1 := hsub v ((-1 : ℝ) • v)
      have h2 := hhom (-1 : ℝ) v
      have h3 := hhom (0 : ℝ) v
      have h4 : v + (-1 : ℝ) • v = (0 : ℝ) • v := by
        ext k; simp
      rw [h4, h3, h2] at h1
      simp at h1
      linarith
    )
  have L_mii_nearorth_peel : ∀ (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
      (hsub : ∀ u v, ν (u + v) ≤ ν u + ν v) (hhom : ∀ (c : ℝ) v, ν (c • v) = |c| * ν v)
      (X : Fin d → Fin d → ℝ) (κ' : ℝ) (hκ' : 0 < κ')
      (htop : ∀ c : Fin d → ℝ, ∀ m : Fin d, (∀ i, m < i → c i = 0) →
          κ' * |c m| * ν (X m) ≤ ν (∑ i, c i • X i)), ∀ n : ℕ, ∀ c : Fin d → ℝ, (∀ i : Fin d, n ≤ i.val → c i = 0) → ∀ j : Fin d,
        (κ' / (1 + κ')) ^ (n + 1) * |c j| * ν (X j) ≤ ν (∑ i, c i • X i) :=
    (fun (d : ℕ) (ν : (Fin d → ℝ) → ℝ)
        (hsub : ∀ u v, ν (u + v) ≤ ν u + ν v) (hhom : ∀ (c : ℝ) v, ν (c • v) = |c| * ν v)
        (X : Fin d → Fin d → ℝ) (κ' : ℝ) (hκ' : 0 < κ')
        (htop : ∀ c : Fin d → ℝ, ∀ m : Fin d, (∀ i, m < i → c i = 0) →
            κ' * |c m| * ν (X m) ≤ ν (∑ i, c i • X i)) => by
      have hr0 : 0 < κ' / (1 + κ') := by positivity
      have hr1 : κ' / (1 + κ') ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      have hrk : κ' / (1 + κ') ≤ κ' := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      have hnn := L_mii_nearorth_nonneg d ν hsub hhom
      intro n
      induction n with
      | zero =>
        intro c hc j
        have h0 : c j = 0 := hc j (Nat.zero_le _)
        rw [h0, abs_zero, mul_zero, zero_mul]
        exact hnn _
      | succ n ih =>
        intro c hc j
        by_cases hnd : d ≤ n
        · have hc' : ∀ i : Fin d, n ≤ i.val → c i = 0 := by
            intro i hi
            exact absurd (lt_of_lt_of_le i.isLt hnd) (not_lt.mpr hi)
          have h1 := ih c hc' j
          have hpow : (κ' / (1 + κ')) ^ (n + 1 + 1) ≤ (κ' / (1 + κ')) ^ (n + 1) :=
            pow_le_pow_of_le_one hr0.le hr1 (by omega)
          have hcj : 0 ≤ |c j| * ν (X j) := mul_nonneg (abs_nonneg _) (hnn _)
          calc (κ' / (1 + κ')) ^ (n + 1 + 1) * |c j| * ν (X j)
              = (κ' / (1 + κ')) ^ (n + 1 + 1) * (|c j| * ν (X j)) := by ring
            _ ≤ (κ' / (1 + κ')) ^ (n + 1) * (|c j| * ν (X j)) :=
              mul_le_mul_of_nonneg_right hpow hcj
            _ = (κ' / (1 + κ')) ^ (n + 1) * |c j| * ν (X j) := by ring
            _ ≤ _ := h1
        · push_neg at hnd
          obtain ⟨m, hm⟩ : ∃ m : Fin d, m.val = n := ⟨⟨n, hnd⟩, rfl⟩
          have hmtop : ∀ i, m < i → c i = 0 := by
            intro i hi
            apply hc i
            have : m.val < i.val := hi
            omega
          have htm := htop c m hmtop
          obtain ⟨c', hc'def⟩ : ∃ c' : Fin d → ℝ, c' = Function.update c m 0 := ⟨_, rfl⟩
          have hc'm : c' m = 0 := by simp [hc'def]
          have hc'ne : ∀ i, i ≠ m → c' i = c i := by
            intro i hi
            rw [hc'def, Function.update_of_ne hi]
          have hc'supp : ∀ i : Fin d, n ≤ i.val → c' i = 0 := by
            intro i hi
            by_cases him : i = m
            · rw [him]; exact hc'm
            · rw [hc'ne i him]
              apply hc i
              have : i.val ≠ n := by
                intro h; apply him; ext; omega
              omega
          have ih' := ih c' hc'supp
          have hv : ∑ i, c i • X i = c m • X m + ∑ i, c' i • X i := by
            rw [← Finset.add_sum_erase Finset.univ (fun i => c i • X i) (Finset.mem_univ m),
              ← Finset.add_sum_erase Finset.univ (fun i => c' i • X i) (Finset.mem_univ m)]
            have h2 : ∑ x ∈ Finset.univ.erase m, c' x • X x
                = ∑ x ∈ Finset.univ.erase m, c x • X x := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [hc'ne x (Finset.ne_of_mem_erase hx)]
            rw [hc'm, h2, zero_smul, zero_add]
          have hv' : ∑ i, c' i • X i = ∑ i, c i • X i + (-c m) • X m := by
            rw [hv, neg_smul]; abel
          have hνv' : ν (∑ i, c' i • X i) ≤ ν (∑ i, c i • X i) + |c m| * ν (X m) := by
            rw [hv']
            have := hsub (∑ i, c i • X i) ((-c m) • X m)
            rw [hhom, abs_neg] at this
            exact this
          have hA : 0 ≤ |c m| * ν (X m) := mul_nonneg (abs_nonneg _) (hnn _)
          have hV : 0 ≤ ν (∑ i, c i • X i) := hnn _
          by_cases hjm : j = m
          · subst hjm
            have hp : (κ' / (1 + κ')) ^ (n + 1 + 1) ≤ κ' :=
              le_trans (pow_le_of_le_one hr0.le hr1 (by omega)) hrk
            calc (κ' / (1 + κ')) ^ (n + 1 + 1) * |c j| * ν (X j)
                = (κ' / (1 + κ')) ^ (n + 1 + 1) * (|c j| * ν (X j)) := by ring
              _ ≤ κ' * (|c j| * ν (X j)) := mul_le_mul_of_nonneg_right hp hA
              _ = κ' * |c j| * ν (X j) := by ring
              _ ≤ _ := htm
          · have h3 := ih' j
            rw [hc'ne j hjm] at h3
            have hkey : κ' / (1 + κ') * (ν (∑ i, c i • X i) + |c m| * ν (X m))
                ≤ ν (∑ i, c i • X i) := by
              rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
              nlinarith
            calc (κ' / (1 + κ')) ^ (n + 1 + 1) * |c j| * ν (X j)
                = κ' / (1 + κ') * ((κ' / (1 + κ')) ^ (n + 1) * |c j| * ν (X j)) := by ring
              _ ≤ κ' / (1 + κ') * (ν (∑ i, c i • X i) + |c m| * ν (X m)) :=
                mul_le_mul_of_nonneg_left (le_trans h3 hνv') hr0.le
              _ ≤ _ := hkey
    )
  have L_mii_nearorth_pigeon_box : ∀ (d D : ℕ) (hD : 0 < D) (t : Fin d → ℝ), ∃ m m' : ℕ, m < m' ∧ m' ≤ D ^ d ∧
        ∀ j, |Int.fract ((m' : ℝ) * t j) - Int.fract ((m : ℝ) * t j)| < 1 / D :=
    (fun (d D : ℕ) (hD : 0 < D) (t : Fin d → ℝ) => by
      have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
      let f : ℕ → Fin d → Fin D := fun m j =>
        ⟨(⌊(D : ℝ) * Int.fract ((m : ℝ) * t j)⌋).toNat, by
          have h1 : (D : ℝ) * Int.fract ((m : ℝ) * t j) < D := by
            have := Int.fract_lt_one ((m : ℝ) * t j)
            nlinarith
          have h2 : ⌊(D : ℝ) * Int.fract ((m : ℝ) * t j)⌋ < D := by
            rw [Int.floor_lt]; exact_mod_cast h1
          omega⟩
      have hcard : (Finset.univ : Finset (Fin d → Fin D)).card
          < (Finset.range (D ^ d + 1)).card := by
        simp
      obtain ⟨a, ha, b, hb, hab, hfab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
        (f := f) (fun m _ => Finset.mem_univ _)
      have key : ∀ a b : ℕ, f a = f b →
          ∀ j, |Int.fract ((b : ℝ) * t j) - Int.fract ((a : ℝ) * t j)| < 1 / D := by
        intro a b hfab j
        have hj := congrArg (fun g => (g j : ℕ)) hfab
        simp only [f] at hj
        have n1 : 0 ≤ ⌊(D : ℝ) * Int.fract ((a : ℝ) * t j)⌋ :=
          Int.floor_nonneg.mpr (mul_nonneg hDpos.le (Int.fract_nonneg _))
        have n2 : 0 ≤ ⌊(D : ℝ) * Int.fract ((b : ℝ) * t j)⌋ :=
          Int.floor_nonneg.mpr (mul_nonneg hDpos.le (Int.fract_nonneg _))
        have heq : ⌊(D : ℝ) * Int.fract ((b : ℝ) * t j)⌋
            = ⌊(D : ℝ) * Int.fract ((a : ℝ) * t j)⌋ := by
          omega
        have := Int.abs_sub_lt_one_of_floor_eq_floor heq
        rw [← mul_sub, abs_mul, abs_of_pos hDpos] at this
        rw [lt_div_iff₀ hDpos]; linarith
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a, b, h, by simp at hb; omega, key a b hfab⟩
      · exact ⟨b, a, h, by simp at ha; omega, key b a hfab.symm⟩
    )
  have L_mii_nearorth_pigeon_notmem : ∀ (d : ℕ) (x : Fin d → Fin d → ℤ)
      (hli : LinearIndependent ℝ (fun i => fun k => (x i k : ℝ))) (i : Fin d) (r : ℤ)
      (hr : r ≠ 0) (w : Fin d → ℤ) (hw : ∀ j, i ≤ j → w j = 0), (fun k => ((r * x i k - ∑ j, w j * x j k : ℤ) : ℝ)) ∉ Submodule.span ℝ
        (Set.range fun j : {j : Fin d // j < i} => fun k => (x j k : ℝ)) :=
    (fun (d : ℕ) (x : Fin d → Fin d → ℤ)
        (hli : LinearIndependent ℝ (fun i => fun k => (x i k : ℝ))) (i : Fin d) (r : ℤ)
        (hr : r ≠ 0) (w : Fin d → ℤ) (hw : ∀ j, i ≤ j → w j = 0) => by
      intro hmem
      set X : Fin d → Fin d → ℝ := fun i k => (x i k : ℝ) with hX
      have hrange : (Set.range fun j : {j : Fin d // j < i} => fun k => (x j k : ℝ))
          = X '' {j | j < i} := by
        ext v; simp [hX]
      rw [hrange] at hmem
      have hsum : (∑ j, (w j : ℝ) • X j) ∈ Submodule.span ℝ (X '' {j | j < i}) := by
        apply Submodule.sum_mem
        intro j _
        by_cases hj : j < i
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
        · rw [hw j (not_lt.mp hj)]; simp
      have heq : (fun k => ((r * x i k - ∑ j, w j * x j k : ℤ) : ℝ))
          = (r : ℝ) • X i - ∑ j, (w j : ℝ) • X j := by
        ext k; simp [hX, Finset.sum_apply]
      rw [heq] at hmem
      have h2 : (r : ℝ) • X i ∈ Submodule.span ℝ (X '' {j | j < i}) := by
        have := Submodule.add_mem _ hmem hsum
        simpa using this
      have h3 : X i ∈ Submodule.span ℝ (X '' {j | j < i}) := by
        have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
        have := Submodule.smul_mem _ ((r : ℝ)⁻¹) h2
        rwa [smul_smul, inv_mul_cancel₀ hr', one_smul] at this
      exact hli.notMem_span_image (by simp) h3
    )
  have L_mii_nearorth_pigeon : ∀ (d : ℕ), ∃ κ' : ℝ, 0 < κ' ∧ ∀ ν : (Fin d → ℝ) → ℝ,
        (∀ u v, ν (u + v) ≤ ν u + ν v) → (∀ (c : ℝ) v, ν (c • v) = |c| * ν v) →
        ∀ x : Fin d → Fin d → ℤ,
        LinearIndependent ℝ (fun i => fun k => (x i k : ℝ)) →
        Monotone (fun i => ν (fun k => (x i k : ℝ))) →
        (∀ i : Fin d, ∀ z : Fin d → ℤ,
          (fun k => (z k : ℝ)) ∉ Submodule.span ℝ
            (Set.range fun j : {j : Fin d // j < i} => fun k => (x j k : ℝ)) →
          ν (fun k => (x i k : ℝ)) ≤ ν (fun k => (z k : ℝ))) →
        ∀ i : Fin d, ∀ t : Fin d → ℝ, (∀ j, i ≤ j → t j = 0) →
          κ' * ν (fun k => (x i k : ℝ)) ≤
            ν ((fun k => (x i k : ℝ)) + ∑ j, t j • fun k => (x j k : ℝ)) :=
    (fun (d : ℕ) => by
      refine ⟨1 / (2 * ((2 * d + 1 : ℕ) : ℝ) ^ d), by positivity, ?_⟩
      intro ν hsub hhom x hli hmono hmin i t ht
      have hnn := L_mii_nearorth_nonneg d ν hsub hhom
      obtain ⟨m, m', hmm', hm'le, hbox⟩ := L_mii_nearorth_pigeon_box d (2 * d + 1) (by omega) t
      set X : Fin d → Fin d → ℝ := fun i k => (x i k : ℝ) with hX
      set V : Fin d → ℝ := X i + ∑ j, t j • X j with hV
      set r : ℤ := (m' : ℤ) - m with hr_def
      have hr : r ≠ 0 := by omega
      set w : Fin d → ℤ := fun j => -(⌊(m' : ℝ) * t j⌋ - ⌊(m : ℝ) * t j⌋) with hw_def
      have hw : ∀ j, i ≤ j → w j = 0 := by intro j hj; simp [w, ht j hj]
      have hnot := L_mii_nearorth_pigeon_notmem d x hli i r hr w hw
      have hle := hmin i _ hnot
      set e : Fin d → ℝ := fun j => Int.fract ((m' : ℝ) * t j) - Int.fract ((m : ℝ) * t j) with he
      have he' : ∀ j, e j = (r : ℝ) * t j + (w j : ℝ) := by
        intro j
        simp only [he, hr_def, hw_def, Int.fract]
        push_cast
        ring
      have hz : (fun k => ((r * x i k - ∑ j, w j * x j k : ℤ) : ℝ))
          = (r : ℝ) • V + (-1 : ℝ) • ∑ j, e j • X j := by
        funext k
        simp only [hV, hX, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, he']
        push_cast
        simp only [add_mul, Finset.sum_add_distrib]
        rw [mul_add, Finset.mul_sum]
        have hcg : ∑ j, (r : ℝ) * (t j * (x j k : ℝ)) = ∑ j, (r : ℝ) * t j * (x j k : ℝ) :=
          Finset.sum_congr rfl (fun j _ => by ring)
        rw [hcg]; ring
      rw [hz] at hle
      have h1 := hsub ((r : ℝ) • V) ((-1 : ℝ) • ∑ j, e j • X j)
      rw [hhom, hhom] at h1
      have h0 : ν 0 = 0 := by simpa using hhom 0 0
      have h2 : ν (∑ j, e j • X j) ≤ ∑ j, ν (e j • X j) :=
        Finset.le_sum_of_subadditive ν h0.le hsub _ _
      have hD : (0 : ℝ) < ((2 * d + 1 : ℕ) : ℝ) := by positivity
      have h3 : ∀ j, ν (e j • X j) ≤ (1 / ((2 * d + 1 : ℕ) : ℝ)) * ν (X i) := by
        intro j
        rw [hhom]
        by_cases hj : i ≤ j
        · have : e j = 0 := by simp [he, ht j hj]
          rw [this, abs_zero, zero_mul]
          exact mul_nonneg (by positivity) (hnn _)
        · have hlam : ν (X j) ≤ ν (X i) := hmono (le_of_lt (not_le.mp hj))
          have hb := hbox j
          have hnj := hnn (X j)
          calc |e j| * ν (X j) ≤ (1 / ((2 * d + 1 : ℕ) : ℝ)) * ν (X j) :=
                mul_le_mul_of_nonneg_right hb.le hnj
            _ ≤ _ := mul_le_mul_of_nonneg_left hlam (by positivity)
      have h4 : ∑ j, ν (e j • X j) ≤ d * ((1 / ((2 * d + 1 : ℕ) : ℝ)) * ν (X i)) := by
        have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h3 j)
        simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
      have h5 : (d : ℝ) * ((1 / ((2 * d + 1 : ℕ) : ℝ)) * ν (X i)) ≤ ν (X i) / 2 := by
        have hni := hnn (X i)
        rw [show (d : ℝ) * ((1 / ((2 * d + 1 : ℕ) : ℝ)) * ν (X i))
            = (d : ℝ) / ((2 * d + 1 : ℕ) : ℝ) * ν (X i) by ring]
        have hq : (d : ℝ) / ((2 * d + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
          rw [div_le_iff₀ hD]; push_cast; linarith
        nlinarith
      have hrabs : |(r : ℝ)| ≤ ((2 * d + 1 : ℕ) : ℝ) ^ d := by
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := by
          have : (0 : ℤ) ≤ r := by omega
          exact_mod_cast this
        rw [abs_of_nonneg hr0]
        have : r ≤ ((2 * d + 1) ^ d : ℕ) := by omega
        have := (Int.cast_le (R := ℝ)).2 this
        simpa using this
      have hVnn := hnn V
      have habs1 : |(-1 : ℝ)| = 1 := by norm_num
      rw [habs1, one_mul] at h1
      have hP : (0 : ℝ) < ((2 * d + 1 : ℕ) : ℝ) ^ d := by positivity
      have key : ν (X i) ≤ ((2 * d + 1 : ℕ) : ℝ) ^ d * ν V + ν (X i) / 2 := by
        calc ν (X i) ≤ |(r : ℝ)| * ν V + ν (∑ j, e j • X j) := hle.trans h1
          _ ≤ ((2 * d + 1 : ℕ) : ℝ) ^ d * ν V + ν (X i) / 2 := by
            have := mul_le_mul_of_nonneg_right hrabs hVnn
            linarith
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith
    )
  have L_mii_nearorth_top : ∀ (d : ℕ) (κ' : ℝ) (hκ' : 0 < κ')
      (ν : (Fin d → ℝ) → ℝ)
      (hsub : ∀ u v, ν (u + v) ≤ ν u + ν v) (hhom : ∀ (c : ℝ) v, ν (c • v) = |c| * ν v)
      (X : Fin d → Fin d → ℝ)
      (hA : ∀ i : Fin d, ∀ t : Fin d → ℝ, (∀ j, i ≤ j → t j = 0) →
          κ' * ν (X i) ≤ ν (X i + ∑ j, t j • X j)), ∀ c : Fin d → ℝ, ∀ m : Fin d, (∀ i, m < i → c i = 0) →
          κ' * |c m| * ν (X m) ≤ ν (∑ i, c i • X i) :=
    (fun (d : ℕ) (κ' : ℝ) (hκ' : 0 < κ')
        (ν : (Fin d → ℝ) → ℝ)
        (hsub : ∀ u v, ν (u + v) ≤ ν u + ν v) (hhom : ∀ (c : ℝ) v, ν (c • v) = |c| * ν v)
        (X : Fin d → Fin d → ℝ)
        (hA : ∀ i : Fin d, ∀ t : Fin d → ℝ, (∀ j, i ≤ j → t j = 0) →
            κ' * ν (X i) ≤ ν (X i + ∑ j, t j • X j)) => by
      intro c m hc
      have hnn := L_mii_nearorth_nonneg d ν hsub hhom
      by_cases hcm : c m = 0
      · rw [hcm]; simp only [abs_zero, mul_zero, zero_mul]; exact hnn _
      · set t : Fin d → ℝ := fun j => if j < m then c j / c m else 0 with ht
        have hsum : ∑ i, c i • X i = c m • (X m + ∑ j, t j • X j) := by
          rw [smul_add, Finset.smul_sum]
          have key : ∀ i, c i • X i = (if i = m then c m else 0) • X i + c m • (t i • X i) := by
            intro i
            rw [smul_smul]
            rcases lt_trichotomy i m with h | h | h
            · have e : c m * (c i / c m) = c i := by field_simp
              simp [ht, h, h.ne, e]
            · subst h; simp [ht]
            · simp [ht, hc i h, h.ne', not_lt.mpr h.le]
          rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
          simp [ite_smul]
        rw [hsum, hhom]
        have hA' := hA m t (fun j hj => by simp [ht, not_lt.mpr hj])
        have habs : 0 ≤ |c m| := abs_nonneg _
        calc κ' * |c m| * ν (X m) = |c m| * (κ' * ν (X m)) := by ring
          _ ≤ |c m| * ν (X m + ∑ j, t j • X j) := mul_le_mul_of_nonneg_left hA' habs
    )
  have L_mii_nearorth : ∀ (d : ℕ), ∃ κ : ℝ, 0 < κ ∧ ∀ ν : (Fin d → ℝ) → ℝ,
        (∀ u v, ν (u + v) ≤ ν u + ν v) → (∀ (c : ℝ) v, ν (c • v) = |c| * ν v) →
        ∀ x : Fin d → Fin d → ℤ,
        LinearIndependent ℝ (fun i => fun k => (x i k : ℝ)) →
        Monotone (fun i => ν (fun k => (x i k : ℝ))) →
        (∀ i : Fin d, ∀ z : Fin d → ℤ,
          (fun k => (z k : ℝ)) ∉ Submodule.span ℝ
            (Set.range fun j : {j : Fin d // j < i} => fun k => (x j k : ℝ)) →
          ν (fun k => (x i k : ℝ)) ≤ ν (fun k => (z k : ℝ))) →
        ∀ c : Fin d → ℝ, ∀ j : Fin d,
          κ * |c j| * ν (fun k => (x j k : ℝ)) ≤ ν (∑ i, c i • fun k => (x i k : ℝ)) :=
    (fun (d : ℕ) => by
      obtain ⟨κ', hκ', hA⟩ := L_mii_nearorth_pigeon d
      refine ⟨(κ' / (1 + κ')) ^ (d + 1), by positivity, ?_⟩
      intro ν hsub hhom x hli hmono hmin c j
      have htop := L_mii_nearorth_top d κ' hκ' ν hsub hhom (fun i k => (x i k : ℝ))
        (hA ν hsub hhom x hli hmono hmin)
      exact L_mii_nearorth_peel d ν hsub hhom (fun i k => (x i k : ℝ)) κ' hκ' htop d c
        (fun i hi => absurd i.isLt (by omega)) j
    )
  have L_mii_count_upper : ∀ (d : ℕ) (κ : ℝ) (hκ : 0 < κ) (ν : (Fin d → ℝ) → ℝ)
      (hadd : ∀ u v, ν (u + v) ≤ ν u + ν v) (hsmul : ∀ (c : ℝ) v, ν (c • v) = |c| * ν v)
      (x : Fin d → Fin d → ℤ)
      (hli : LinearIndependent ℝ (fun i => fun k => (x i k : ℝ)))
      (hmono : Monotone (fun i => ν (fun k => (x i k : ℝ))))
      (hpos : ∀ i, 0 < ν (fun k => (x i k : ℝ)))
      (hmin : ∀ i : Fin d, ∀ z : Fin d → ℤ,
          (fun k => (z k : ℝ)) ∉ Submodule.span ℝ
            (Set.range fun j : {j : Fin d // j < i} => fun k => (x j k : ℝ)) →
          ν (fun k => (x i k : ℝ)) ≤ ν (fun k => (z k : ℝ)))
      (hnear : ∀ c : Fin d → ℝ, ∀ j : Fin d,
          κ * |c j| * ν (fun k => (x j k : ℝ)) ≤ ν (∑ i, c i • fun k => (x i k : ℝ)))
      (S : Finset (Fin d → ℤ)) (T : ℝ) (hS : ∀ z ∈ S, ν (fun k => (z k : ℝ)) ≤ T) (hT0 : 0 ≤ T), (S.card : ℝ) ≤ ∏ j, (2 * d * T / (κ * ν (fun k => (x j k : ℝ))) + 2) :=
    (fun (d : ℕ) (κ : ℝ) (hκ : 0 < κ) (ν : (Fin d → ℝ) → ℝ)
        (hadd : ∀ u v, ν (u + v) ≤ ν u + ν v) (hsmul : ∀ (c : ℝ) v, ν (c • v) = |c| * ν v)
        (x : Fin d → Fin d → ℤ)
        (hli : LinearIndependent ℝ (fun i => fun k => (x i k : ℝ)))
        (hmono : Monotone (fun i => ν (fun k => (x i k : ℝ))))
        (hpos : ∀ i, 0 < ν (fun k => (x i k : ℝ)))
        (hmin : ∀ i : Fin d, ∀ z : Fin d → ℤ,
            (fun k => (z k : ℝ)) ∉ Submodule.span ℝ
              (Set.range fun j : {j : Fin d // j < i} => fun k => (x j k : ℝ)) →
            ν (fun k => (x i k : ℝ)) ≤ ν (fun k => (z k : ℝ)))
        (hnear : ∀ c : Fin d → ℝ, ∀ j : Fin d,
            κ * |c j| * ν (fun k => (x j k : ℝ)) ≤ ν (∑ i, c i • fun k => (x i k : ℝ)))
        (S : Finset (Fin d → ℤ)) (T : ℝ) (hS : ∀ z ∈ S, ν (fun k => (z k : ℝ)) ≤ T) (hT0 : 0 ≤ T) => by
      classical
      have hT : 0 ≤ T := hT0
      have huniq : ∀ c c' : Fin d → ℝ, ∑ j, c j • (fun k => (x j k : ℝ)) =
          ∑ j, c' j • (fun k => (x j k : ℝ)) → c = c' := by
        intro c c' h
        have := Fintype.linearIndependent_iff.1 hli (c - c')
          (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]; exact sub_eq_zero.2 h)
        funext j; have := this j; simp only [Pi.sub_apply] at this; linarith
      have hspan : ∀ v : Fin d → ℝ, ∃ c : Fin d → ℝ, v = ∑ j, c j • (fun k => (x j k : ℝ)) := by
        intro v
        by_contra hne
        have hnot : v ∉ Submodule.span ℝ (Set.range (fun i => fun k => (x i k : ℝ))) := by
          intro hv
          rw [Submodule.mem_span_range_iff_exists_fun] at hv
          obtain ⟨c, hc⟩ := hv
          exact hne ⟨c, hc.symm⟩
        exact L_mii_dep (d+1) d (Nat.lt_succ_self d) _ (linearIndependent_fin_cons.2 ⟨hli, hnot⟩)
      choose C hC using hspan
      set a : Fin d → ℝ := fun j => d * T / (κ * ν (fun k => (x j k : ℝ))) with ha
      let f : (Fin d → ℤ) → (Fin d → ℤ) := fun z j => ⌊(d:ℝ) * C (fun k => (z k : ℝ)) j⌋
      have hmaps : ∀ z ∈ S, f z ∈ Fintype.piFinset (fun j => Finset.Icc ⌊-a j⌋ ⌊a j⌋) := by
        intro z hz
        rw [Fintype.mem_piFinset]
        intro j
        have h1 := hnear (C (fun k => (z k : ℝ))) j
        rw [← hC (fun k => (z k : ℝ))] at h1
        have h2 := hS z hz
        have hl := hpos j
        have hcj : |C (fun k => (z k : ℝ)) j| ≤ T / (κ * ν (fun k => (x j k : ℝ))) := by
          rw [le_div_iff₀ (mul_pos hκ hl)]
          nlinarith
        have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
        have hab : |(d:ℝ) * C (fun k => (z k : ℝ)) j| ≤ a j := by
          show _ ≤ (d:ℝ) * T / (κ * ν (fun k => (x j k : ℝ)))
          rw [abs_mul, abs_of_nonneg hd, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hcj hd
        rw [Finset.mem_Icc]
        constructor
        · exact Int.floor_mono (by linarith [neg_abs_le ((d:ℝ) * C (fun k => (z k : ℝ)) j)])
        · exact Int.floor_mono (le_trans (le_abs_self _) hab)
      have hinj : Set.InjOn f S := by
        intro z hz z' hz' hfz
        by_contra hne
        set Z : Fin d → ℝ := fun k => (z k : ℝ) with hZ
        set Z' : Fin d → ℝ := fun k => (z' k : ℝ) with hZ'
        set w : Fin d → ℤ := z - z' with hw
        have hW : (fun k => (w k : ℝ)) = Z - Z' := by
          funext k; simp [hw, hZ, hZ']
        set c : Fin d → ℝ := C Z - C Z' with hc
        have hWc : (fun k => (w k : ℝ)) = ∑ j, c j • (fun k => (x j k : ℝ)) := by
          have e1 := hC Z
          have e2 := hC Z'
          rw [hW]
          simp only [hc, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
          rw [← e1, ← e2]
        have hcbound : ∀ j, (d:ℝ) * |c j| < 1 := by
          intro j
          have h1 : ⌊(d:ℝ) * C Z j⌋ = ⌊(d:ℝ) * C Z' j⌋ := congrFun hfz j
          have h2 := Int.abs_sub_lt_one_of_floor_eq_floor h1
          have h3 : (d:ℝ) * C Z j - (d:ℝ) * C Z' j = (d:ℝ) * c j := by
            rw [hc, Pi.sub_apply]; ring
          rw [h3, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)] at h2
          exact h2
        have hc0 : ∃ j, c j ≠ 0 := by
          by_contra hall
          push_neg at hall
          apply hne
          have h0 : (fun k => (w k : ℝ)) = 0 := by
            rw [hWc]; simp [hall]
          funext k
          have h5 := congrFun h0 k
          have h6 : ((z k : ℤ) : ℝ) = (z' k : ℝ) := by
            simp only [hw, Pi.sub_apply, Int.cast_sub, Pi.zero_apply] at h5
            linarith
          exact_mod_cast h6
        let P := Finset.univ.filter (fun j => c j ≠ 0)
        have hPne : P.Nonempty := by
          obtain ⟨j, hj⟩ := hc0
          exact ⟨j, by simp [P, hj]⟩
        let i := P.max' hPne
        have hci : c i ≠ 0 := by
          have := P.max'_mem hPne
          simpa [P] using this
        have hgt : ∀ j, i < j → c j = 0 := by
          intro j hij
          by_contra hcj
          have : j ≤ i := P.le_max' j (by simp [P, hcj])
          exact absurd hij (not_lt.2 this)
        have hnotspan : (fun k => (w k : ℝ)) ∉ Submodule.span ℝ
              (Set.range fun j : {j : Fin d // j < i} => fun k => (x j k : ℝ)) := by
          intro hmem
          rw [Submodule.mem_span_range_iff_exists_fun] at hmem
          obtain ⟨b, hb⟩ := hmem
          let b' : Fin d → ℝ := fun j => if h : j < i then b ⟨j, h⟩ else 0
          have hb' : ∑ j, b' j • (fun k => (x j k : ℝ)) = ∑ j, c j • (fun k => (x j k : ℝ)) := by
            rw [← hWc, ← hb]
            rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j < i)]
            have h1 : ∑ j : {j : Fin d // j < i}, b' j • (fun k => (x j k : ℝ)) =
                ∑ j : {j : Fin d // j < i}, b j • (fun k => (x j k : ℝ)) := by
              apply Finset.sum_congr rfl
              intro j _
              simp [b', j.2]
            have h2 : ∑ j : {j : Fin d // ¬ j < i}, b' j • (fun k => (x j k : ℝ)) = 0 := by
              apply Finset.sum_eq_zero
              intro j _
              simp [b', j.2]
            rw [h1, h2, add_zero]
          have h7 := congrFun (huniq _ _ hb') i
          simp [b'] at h7
          exact hci h7.symm
        have hmi := hmin i w hnotspan
        have h0 : ν 0 = 0 := by
          have := hsmul 0 0
          simpa using this
        have hsub : ν (∑ j, c j • (fun k => (x j k : ℝ))) ≤
            ∑ j, ν (c j • (fun k => (x j k : ℝ))) :=
          Finset.le_sum_of_subadditive ν h0.le hadd _ _
        have hle : ∀ j, ν (c j • (fun k => (x j k : ℝ))) ≤ |c j| * ν (fun k => (x i k : ℝ)) := by
          intro j
          rw [hsmul]
          by_cases hji : j ≤ i
          · exact mul_le_mul_of_nonneg_left (hmono hji) (abs_nonneg _)
          · rw [hgt j (not_le.1 hji)]; simp
        have hd1 : 0 < d := by have := i.2; omega
        have hsum : ∑ j, |c j| < 1 := by
          calc ∑ j, |c j| < ∑ j : Fin d, (1 / (d:ℝ)) := by
                apply Finset.sum_lt_sum_of_nonempty ⟨i, Finset.mem_univ i⟩
                intro j _
                rw [lt_div_iff₀ (by exact_mod_cast hd1)]
                have := hcbound j
                linarith
            _ = 1 := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                have hd' : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
                field_simp
        have hlp := hpos i
        have hfin : ν (fun k => (w k : ℝ)) ≤ (∑ j, |c j|) * ν (fun k => (x i k : ℝ)) := by
          rw [hWc, Finset.sum_mul]
          exact le_trans hsub (Finset.sum_le_sum (fun j _ => hle j))
        nlinarith
      have hcard := Finset.card_le_card_of_injOn f (fun z hz => hmaps z hz) hinj
      have hbox : ((Fintype.piFinset (fun j => Finset.Icc ⌊-a j⌋ ⌊a j⌋)).card : ℝ) ≤
          ∏ j, (2 * d * T / (κ * ν (fun k => (x j k : ℝ))) + 2) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
        apply Finset.prod_le_prod
        · intro j _; positivity
        · intro j _
          rw [Int.card_Icc]
          have hl := hpos j
          have ha0 : 0 ≤ a j := by
            show 0 ≤ (d:ℝ) * T / (κ * ν (fun k => (x j k : ℝ)))
            exact div_nonneg (mul_nonneg (Nat.cast_nonneg d) hT) (le_of_lt (mul_pos hκ hl))
          have hfl : ⌊-a j⌋ ≤ ⌊a j⌋ := Int.floor_mono (by linarith)
          have hb : 0 ≤ ⌊a j⌋ + 1 - ⌊-a j⌋ := by omega
          have hcast : ((⌊a j⌋ + 1 - ⌊-a j⌋).toNat : ℝ) = ((⌊a j⌋ + 1 - ⌊-a j⌋ : ℤ) : ℝ) := by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg hb]
          rw [hcast]
          push_cast
          have e1 := Int.floor_le (a j)
          have e2 := Int.lt_floor_add_one (-a j)
          have e3 : 2 * (d:ℝ) * T / (κ * ν (fun k => (x j k : ℝ))) = 2 * a j := by
            show _ = 2 * ((d:ℝ) * T / (κ * ν (fun k => (x j k : ℝ))))
            ring
          rw [e3]
          linarith
      calc (S.card : ℝ) ≤ ((Fintype.piFinset (fun j => Finset.Icc ⌊-a j⌋ ⌊a j⌋)).card : ℝ) := by
            exact_mod_cast hcard
        _ ≤ _ := hbox
    )
  have L_mii_norm_int : ∀ (d : ℕ) (z : Fin d → ℤ), ‖(fun k => (z k : ℝ))‖ = ((Finset.univ.sup fun k => (z k).natAbs : ℕ) : ℝ) :=
    (fun (d : ℕ) (z : Fin d → ℤ) => by
      apply le_antisymm
      · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
        have hk : (z k).natAbs ≤ Finset.univ.sup fun k => (z k).natAbs :=
          Finset.le_sup (f := fun k => (z k).natAbs) (Finset.mem_univ k)
        rw [Real.norm_eq_abs, ← Int.cast_abs, ← Nat.cast_natAbs]
        exact_mod_cast hk
      · refine Finset.sup_induction (p := fun m : ℕ => (m : ℝ) ≤ ‖(fun k => (z k : ℝ))‖)
          (by simp) (fun a ha b hb => ?_) (fun k _ => ?_)
        · show ((max a b : ℕ) : ℝ) ≤ _
          rw [Nat.cast_max]; exact max_le ha hb
        · have := norm_le_pi_norm (fun k => (z k : ℝ)) k
          rw [Real.norm_eq_abs, ← Int.cast_abs, ← Nat.cast_natAbs] at this
          exact this
    )
  have L_mii_finite : ∀ (d : ℕ) (ν : (Fin d → ℝ) → ℝ) (hν : ∀ v, ‖v‖ ≤ ν v) (T : ℝ), Set.Finite {z : Fin d → ℤ | ν (fun k => (z k : ℝ)) ≤ T} :=
    (fun (d : ℕ) (ν : (Fin d → ℝ) → ℝ) (hν : ∀ v, ‖v‖ ≤ ν v) (T : ℝ) => by
      refine Set.Finite.subset (Fintype.piFinset fun _ : Fin d => Finset.Icc (-⌈T⌉) ⌈T⌉).finite_toSet ?_
      intro z hz
      simp only [Set.mem_setOf_eq] at hz
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro k
      rw [Finset.mem_Icc]
      have h1 := norm_le_pi_norm (fun k => (z k : ℝ)) k
      have h2 := hν (fun k => (z k : ℝ))
      rw [Real.norm_eq_abs] at h1
      have h3 : |(z k : ℝ)| ≤ T := by simpa using h1.trans (h2.trans hz)
      have h4 : (T : ℝ) ≤ ⌈T⌉ := Int.le_ceil T
      have h5 : ((z k : ℤ) : ℝ) ≤ ⌈T⌉ := by linarith [le_abs_self (z k : ℝ)]
      have h6 : -((⌈T⌉ : ℤ) : ℝ) ≤ (z k : ℝ) := by linarith [neg_abs_le (z k : ℝ)]
      constructor
      · exact_mod_cast h6
      · exact_mod_cast h5
    )
  have L_mii_core : ∀ (n : ℕ) (ξ : ℝ), ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∃ x : Fin (n + 1) → Fin (n + 1) → ℤ,
        LinearIndependent ℝ (fun i => fun k => (x i k : ℝ)) ∧
        ∏ i, max ((Finset.univ.sup fun k => (x i k).natAbs : ℕ) : ℝ)
          (Real.exp q * |∑ k : Fin (n + 1), (x i k : ℝ) * ξ ^ (k : ℕ)|) ≤ C * Real.exp q :=
    (fun (n : ℕ) (ξ : ℝ) => by
      obtain ⟨κ, hκ, hnear⟩ := L_mii_nearorth (n + 1)
      obtain ⟨c, hc, hlow⟩ := L_mii_count_lower n ξ
      set A : ℝ := 2 * ((n + 1 : ℕ) : ℝ) / κ with hA_def
      have hA : 0 < A := by positivity
      refine ⟨A ^ (n + 1) / c, by positivity, fun q hq => ?_⟩
      set E := Real.exp q with hE_def
      have hE : 0 < E := Real.exp_pos q
      set ν : (Fin (n + 1) → ℝ) → ℝ := fun v => max ‖v‖ (E * |∑ k : Fin (n + 1), v k * ξ ^ (k : ℕ)|)
        with hν_def
      have hνnorm : ∀ v, ‖v‖ ≤ ν v := fun v => le_max_left _ _
      have hadd : ∀ u v, ν (u + v) ≤ ν u + ν v := by
        intro u v
        simp only [hν_def, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        refine max_le ((norm_add_le u v).trans (add_le_add (le_max_left _ _) (le_max_left _ _))) ?_
        calc E * |∑ k : Fin (n + 1), u k * ξ ^ (k : ℕ) + ∑ k : Fin (n + 1), v k * ξ ^ (k : ℕ)|
            ≤ E * (|∑ k : Fin (n + 1), u k * ξ ^ (k : ℕ)| + |∑ k : Fin (n + 1), v k * ξ ^ (k : ℕ)|) :=
              mul_le_mul_of_nonneg_left (abs_add_le _ _) hE.le
          _ = E * |∑ k : Fin (n + 1), u k * ξ ^ (k : ℕ)| + E * |∑ k : Fin (n + 1), v k * ξ ^ (k : ℕ)| :=
              by ring
          _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)
      have hsmul : ∀ (a : ℝ) v, ν (a • v) = |a| * ν v := by
        intro a v
        simp only [hν_def, Pi.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_assoc,
          ← Finset.mul_sum, abs_mul]
        rw [mul_left_comm E |a|, ← mul_max_of_nonneg _ _ (abs_nonneg a)]
      obtain ⟨x, hli, hmono, hmin⟩ := L_mii_minima (n + 1) ν (L_mii_finite (n + 1) ν hνnorm)
      have hpos : ∀ i, 0 < ν (fun k => (x i k : ℝ)) := by
        intro i
        have hne := hli.ne_zero i
        exact lt_of_lt_of_le (norm_pos_iff.2 hne) (hνnorm _)
      have hnear' := hnear ν hadd hsmul x hli hmono hmin
      have hbound : ∀ T : ℝ, 2 * E ≤ T →
          c * T ^ (n + 1) / E ≤ ∏ j, (A * T / ν (fun k => (x j k : ℝ)) + 2) := by
        intro T hT
        obtain ⟨S, hScard, hS⟩ := hlow q hq T hT
        have hSν : ∀ z ∈ S, ν (fun k => (z k : ℝ)) ≤ T := by
          intro z hz
          obtain ⟨h1, h2⟩ := hS z hz
          refine max_le ?_ h2
          have hT0 : 0 ≤ T := le_trans (by positivity) hT
          refine (pi_norm_le_iff_of_nonneg hT0).2 fun k => ?_
          rw [Real.norm_eq_abs]; exact h1 k
        have hup := L_mii_count_upper (n + 1) κ hκ ν hadd hsmul x hli hmono hpos hmin hnear' S T hSν
          (le_trans (by positivity) hT)
        refine hScard.trans (hup.trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_)))
        rw [hA_def]
        have := hpos j
        field_simp
      have hlim := L_mii_limit (n + 1) A c E hA hc hE (fun j => ν (fun k => (x j k : ℝ))) hpos hbound
      refine ⟨x, hli, le_of_eq_of_le ?_ hlim⟩
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hν_def]
      rw [L_mii_norm_int]
    )
  have L_mii : ∀ (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)), ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∃ P : Fin (n + 1) → Polynomial ℤ,
        (∀ i, (P i).natDegree ≤ n) ∧
        LinearIndependent ℚ (fun i => (P i).map (Int.castRingHom ℚ)) ∧
        ∏ i, max (N (P i)) (Real.exp q * |Polynomial.aeval ξ (P i)|) ≤ C * Real.exp q :=
    (fun (n : ℕ) (hn : 1 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) => by
      obtain ⟨C, hC, hcore⟩ := L_mii_core n ξ
      refine ⟨C, hC, fun q hq => ?_⟩
      obtain ⟨x, hxli, hxprod⟩ := hcore q hq
      choose P hPdeg hPcoeff hPN hPev using fun i => L_mii_poly_of_vec n ξ N hN (x i)
      refine ⟨P, hPdeg, L_mii_linindep n x P hPcoeff hPdeg hxli, ?_⟩
      calc ∏ i, max (N (P i)) (Real.exp q * |Polynomial.aeval ξ (P i)|)
          = ∏ i, max ((Finset.univ.sup fun k => (x i k).natAbs : ℕ) : ℝ)
              (Real.exp q * |∑ k : Fin (n + 1), (x i k : ℝ) * ξ ^ (k : ℕ)|) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [hPN i, hPev i]
        _ ≤ C * Real.exp q := hxprod
    )
  have L_opt_step : ∀ (M t G G' : ℝ) (hM : 0 < M)
      (hG : (if t ≤ 0 then M - t else M * Real.exp (-t / M)) ≤ G)
      (h1 : G - 1 ≤ G') (h2 : M * G ≤ (M + 1) * G'), (if t + 1 ≤ 0 then M - (t + 1) else M * Real.exp (-(t + 1) / M)) ≤ G' :=
    (fun (M t G G' : ℝ) (hM : 0 < M)
        (hG : (if t ≤ 0 then M - t else M * Real.exp (-t / M)) ≤ G)
        (h1 : G - 1 ≤ G') (h2 : M * G ≤ (M + 1) * G') => by
      by_cases ht1 : t + 1 ≤ 0
      · have ht : t ≤ 0 := by linarith
        rw [if_pos ht] at hG
        rw [if_pos ht1]
        linarith
      · rw [if_neg ht1]
        by_cases ht : t ≤ 0
        · rw [if_pos ht] at hG
          have hpos : 0 < (t + 1) / M := div_pos (by linarith) hM
          have hE1 : Real.exp (-(t + 1) / M) * Real.exp ((t + 1) / M) = 1 := by
            rw [← Real.exp_add, show -(t + 1) / M + (t + 1) / M = 0 by ring, Real.exp_zero]
          have hexp : (t + 1) / M + 1 ≤ Real.exp ((t + 1) / M) := Real.add_one_le_exp _
          have hE0 : 0 < Real.exp (-(t + 1) / M) := Real.exp_pos _
          have hA : Real.exp (-(t + 1) / M) * ((t + 1) / M + 1) ≤ 1 := by
            calc Real.exp (-(t + 1) / M) * ((t + 1) / M + 1)
                ≤ Real.exp (-(t + 1) / M) * Real.exp ((t + 1) / M) :=
                  mul_le_mul_of_nonneg_left hexp hE0.le
              _ = 1 := hE1
          have hEle : Real.exp (-(t + 1) / M) ≤ 1 := by
            have : Real.exp (-(t + 1) / M) * 1 ≤ Real.exp (-(t + 1) / M) * ((t + 1) / M + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) hE0.le
            linarith
          have hMi : M * M⁻¹ = 1 := mul_inv_cancel₀ hM.ne'
          have e : M * (Real.exp (-(t + 1) / M) * ((t + 1) / M + 1))
              = Real.exp (-(t + 1) / M) * (M + t + 1) := by
            rw [div_eq_mul_inv]
            linear_combination (Real.exp (-(t + 1) * M⁻¹) * (t + 1)) * hMi
          have hB : Real.exp (-(t + 1) / M) * (M + t + 1) ≤ M := by
            have := mul_le_mul_of_nonneg_left hA hM.le
            linarith
          have h3 : (M + 1) * Real.exp (-(t + 1) / M) ≤ M - t := by
            nlinarith [mul_nonneg (neg_nonneg.mpr ht) (sub_nonneg.mpr hEle)]
          have h4 : M * ((M + 1) * Real.exp (-(t + 1) / M)) ≤ M * (M - t) :=
            mul_le_mul_of_nonneg_left h3 hM.le
          have h5 : M * (M - t) ≤ M * G := mul_le_mul_of_nonneg_left hG hM.le
          nlinarith
        · rw [if_neg ht] at hG
          have hsplit : Real.exp (-(t + 1) / M) = Real.exp (-t / M) * Real.exp (-1 / M) := by
            rw [← Real.exp_add]; congr 1; ring
          have hE1 : Real.exp (-1 / M) * Real.exp (1 / M) = 1 := by
            rw [← Real.exp_add, show -1 / M + 1 / M = 0 by ring, Real.exp_zero]
          have hexp : 1 / M + 1 ≤ Real.exp (1 / M) := Real.add_one_le_exp _
          have hE0 : 0 < Real.exp (-1 / M) := Real.exp_pos _
          have hA : Real.exp (-1 / M) * (1 / M + 1) ≤ 1 := by
            calc Real.exp (-1 / M) * (1 / M + 1)
                ≤ Real.exp (-1 / M) * Real.exp (1 / M) := mul_le_mul_of_nonneg_left hexp hE0.le
              _ = 1 := hE1
          have hMi : M * M⁻¹ = 1 := mul_inv_cancel₀ hM.ne'
          have e : M * (Real.exp (-1 / M) * (1 / M + 1)) = Real.exp (-1 / M) * (1 + M) := by
            rw [one_div]
            linear_combination (Real.exp (-1 / M)) * hMi
          have hB : Real.exp (-1 / M) * (1 + M) ≤ M := by
            have := mul_le_mul_of_nonneg_left hA hM.le
            linarith
          have hF0 : 0 < Real.exp (-t / M) := Real.exp_pos _
          rw [hsplit]
          have h4 : (M + 1) * (M * (Real.exp (-t / M) * Real.exp (-1 / M)))
              ≤ M * (M * Real.exp (-t / M)) := by
            have := mul_le_mul_of_nonneg_left hB (mul_pos hM hF0).le
            nlinarith
          have h5 : M * (M * Real.exp (-t / M)) ≤ M * G := mul_le_mul_of_nonneg_left hG hM.le
          nlinarith
    )
  have L_opt : ∀ (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : (n : ℝ) ≤ x) (a : ℕ → ℝ) (ha2 : a 2 = 1)
      (hmono : ∀ i, 2 ≤ i → i ≤ n → a i ≤ a (i + 1))
      (hsum : ∑ i ∈ Finset.Icc 2 (n + 1), a i = x), ∃ k ∈ Finset.Icc 2 (n + 1),
        1 / (2 - Real.log 2) * n ≤ (2 * x - 2 * ((n : ℝ) + 1 - k) - ∑ i ∈ Finset.Icc 2 k, a i) / a k :=
    (fun (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : (n : ℝ) ≤ x) (a : ℕ → ℝ) (ha2 : a 2 = 1)
        (hmono : ∀ i, 2 ≤ i → i ≤ n → a i ≤ a (i + 1))
        (hsum : ∑ i ∈ Finset.Icc 2 (n + 1), a i = x) => by
      have ha1 : ∀ k, 2 ≤ k → k ≤ n + 1 → 1 ≤ a k := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => intro _; rw [ha2]
        | succ k hk ih =>
          intro hk1
          have := hmono k hk (by omega)
          linarith [ih (by omega)]
      set A : ℕ → ℝ := fun k => 2 * x - 2 * ((n : ℝ) + 1 - k) - ∑ i ∈ Finset.Icc 2 k, a i with hAdef
      have hne : (Finset.Icc 2 (n + 1)).Nonempty := ⟨2, by simp; omega⟩
      obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image (Finset.Icc 2 (n + 1)) (fun k => A k / a k) hne
      refine ⟨k0, hk0, ?_⟩
      show 1 / (2 - Real.log 2) * n ≤ A k0 / a k0
      set M := A k0 / a k0 with hMdef
      have hle : ∀ k, 2 ≤ k → k ≤ n + 1 → A k ≤ M * a k := by
        intro k h1 h2
        have := hmax k (Finset.mem_Icc.mpr ⟨h1, h2⟩)
        have hak : 0 < a k := by linarith [ha1 k h1 h2]
        rwa [div_le_iff₀ hak] at this
      have hA2 : A 2 = 2 * (x - n) + 1 := by
        simp only [hAdef, Finset.Icc_self, Finset.sum_singleton, ha2]; push_cast; ring
      have hAn : A (n + 1) = x := by
        simp only [hAdef, hsum]; push_cast; ring
      have hArec : ∀ k, 2 ≤ k → A (k + 1) = A k + 2 - a (k + 1) := by
        intro k hk
        simp only [hAdef]
        rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1)]
        push_cast; ring
      have hM2 : A 2 ≤ M := by have := hle 2 le_rfl (by omega); rw [ha2] at this; linarith
      have hM1 : 1 ≤ M := by rw [hA2] at hM2; linarith
      have hMpos : 0 < M := by linarith
      have hinv : ∀ k, 2 ≤ k → k ≤ n + 1 →
          (if ((k : ℝ) - 2 - (M - A 2)) ≤ 0 then M - ((k : ℝ) - 2 - (M - A 2))
            else M * Real.exp (-((k : ℝ) - 2 - (M - A 2)) / M)) ≤ 2 * M - A k := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base =>
          intro _
          rw [if_pos (by push_cast; linarith)]
          push_cast; linarith
        | succ k hk ih =>
          intro hk1
          have ih' := ih (by omega)
          have hrec := hArec k hk
          have hak1 := ha1 (k + 1) (by omega) hk1
          have hle1 := hle (k + 1) (by omega) hk1
          have h1 : (2 * M - A k) - 1 ≤ 2 * M - A (k + 1) := by linarith
          have h2 : M * (2 * M - A k) ≤ (M + 1) * (2 * M - A (k + 1)) := by
            have e : a (k + 1) = A k + 2 - A (k + 1) := by linarith
            rw [e] at hle1; nlinarith
          have := L_opt_step M ((k : ℝ) - 2 - (M - A 2)) _ _ hMpos ih' h1 h2
          have e : ((k + 1 : ℕ) : ℝ) - 2 - (M - A 2) = ((k : ℝ) - 2 - (M - A 2)) + 1 := by
            push_cast; ring
          rw [e]; exact this
      have hfin := hinv (n + 1) (by omega) le_rfl
      rw [hAn] at hfin
      have hlog2 : Real.log 2 < 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
        have h2 : Real.log 2 < 2 - 1 := by
          have hlt := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num)
          linarith
        linarith
      have hden : 0 < 2 - Real.log 2 := by linarith
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
      by_cases hT : ((n + 1 : ℕ) : ℝ) - 2 - (M - A 2) ≤ 0
      · have hnM : (n : ℝ) ≤ M := by
          rw [hA2] at hT; push_cast at hT; linarith
        nlinarith
      · rw [if_neg hT] at hfin
        have hT' : ((n + 1 : ℕ) : ℝ) - 2 - (M - A 2) = 2 * x - n - M := by
          rw [hA2]; push_cast; ring
        rw [hT'] at hfin
        have hEpos : 0 < Real.exp (-(2 * x - n - M) / M) := Real.exp_pos _
        have hw : 0 < 2 * M - x := by nlinarith
        set θ := (2 * M - x) / M with hθdef
        have hθM : θ * M = 2 * M - x := by rw [hθdef]; field_simp
        have hθpos : 0 < θ := div_pos hw hMpos
        have hEθ : Real.exp (-(2 * x - n - M) / M) ≤ θ := by
          by_contra hc
          push_neg at hc
          have := mul_lt_mul_of_pos_left hc hMpos
          nlinarith
        have hlogθ : -(2 * x - n - M) / M ≤ Real.log θ := by
          have := Real.log_le_log hEpos hEθ
          rwa [Real.log_exp] at this
        have hlogθ' : -(2 * x - n - M) ≤ Real.log θ * M := (div_le_iff₀ hMpos).mp hlogθ
        have hl2 : Real.log (2 * θ) ≤ 2 * θ - 1 := Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_mul two_ne_zero hθpos.ne'] at hl2
        have hl3 := mul_le_mul_of_nonneg_right hl2 hMpos.le
        nlinarith
    )
  have L_res_coeff_le : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (p : Polynomial ℤ) (i : ℕ), |((p.coeff i : ℤ) : ℝ)| ≤ N p :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (p : Polynomial ℤ) (i : ℕ) => by
      rw [hN p]
      have h1 : |((p.coeff i : ℤ) : ℝ)| = (((p.coeff i).natAbs : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [h1]
      by_cases hi : i ∈ p.support
      · exact_mod_cast Finset.le_sup (f := fun i => (p.coeff i).natAbs) hi
      · have : p.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
        rw [this]; simp
    )
  have L_res_N_le : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (p : Polynomial ℤ) (K : ℝ) (hK : 0 ≤ K) (h : ∀ i, |((p.coeff i : ℤ) : ℝ)| ≤ K), N p ≤ K :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (p : Polynomial ℤ) (K : ℝ) (hK : 0 ≤ K) (h : ∀ i, |((p.coeff i : ℤ) : ℝ)| ≤ K) => by
      rw [hN p]
      rcases Finset.eq_empty_or_nonempty p.support with hs | hs
      · rw [hs]; simpa using hK
      · obtain ⟨i, _, heq⟩ := Finset.exists_mem_eq_sup p.support hs (fun i => (p.coeff i).natAbs)
        rw [heq]
        have h1 : |((p.coeff i : ℤ) : ℝ)| = (((p.coeff i).natAbs : ℕ) : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [← h1]
        exact h i
    )
  have L_res_N_pos : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (Q : Polynomial ℤ) (hQ : Q ≠ 0), 1 ≤ N Q :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (Q : Polynomial ℤ) (hQ : Q ≠ 0) => by
      have h1 := L_res_coeff_le N hN Q Q.natDegree
      have h2 : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
      have h3 : (1 : ℤ) ≤ |Q.coeff Q.natDegree| := Int.one_le_abs h2
      have h4 : (1 : ℝ) ≤ |((Q.coeff Q.natDegree : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast h3
      linarith
    )
  have L_res_N_small : ∀ (n : ℕ) (hn : 2 ≤ n) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) (c : ℕ)
      (hc : c ≤ n), N (Polynomial.X - Polynomial.C (c : ℤ)) ≤ n ∧ N (Polynomial.X : Polynomial ℤ) ≤ n :=
    (fun (n : ℕ) (hn : 2 ≤ n) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) (c : ℕ)
        (hc : c ≤ n) => by
      have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
      constructor
      · apply L_res_N_le N hN _ _ (by linarith)
        intro i
        rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
        split_ifs with h1 h2
        · omega
        · norm_num; linarith
        · norm_num; exact_mod_cast hc
        · norm_num
      · apply L_res_N_le N hN _ _ (by linarith)
        intro i
        rw [Polynomial.coeff_X]
        split_ifs with h1
        · norm_num; linarith
        · norm_num
    )
  have L_res_B_nonneg : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (p : Polynomial ℤ), 0 ≤ N p :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (p : Polynomial ℤ) => le_trans (abs_nonneg _) (L_res_coeff_le N hN p 0)
    )
  have L_res_B_Xpow : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (R : Polynomial ℤ) (t : ℕ), N (Polynomial.X ^ t * R) ≤ N R :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (R : Polynomial ℤ) (t : ℕ) => by
      apply L_res_N_le N hN _ _ (L_res_B_nonneg N hN R)
      intro i
      rw [Polynomial.coeff_X_pow_mul']
      split_ifs
      · exact L_res_coeff_le N hN R _
      · simp only [Int.cast_zero, abs_zero]
        exact L_res_B_nonneg N hN R
    )
  have L_res_B_lin : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (R : Polynomial ℤ) (c : ℕ), N ((Polynomial.X - Polynomial.C (c : ℤ)) * R) ≤ ((c : ℝ) + 1) * N R :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (R : Polynomial ℤ) (c : ℕ) => by
      have h0 := L_res_B_nonneg N hN R
      have hc : (0:ℝ) ≤ (c:ℝ) := Nat.cast_nonneg c
      apply L_res_N_le N hN _ _ (by positivity)
      intro i
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      cases i with
      | zero =>
        rw [Polynomial.coeff_X_mul_zero]
        have h1 := abs_le.mp (L_res_coeff_le N hN R 0)
        push_cast
        rw [abs_le]
        constructor <;> nlinarith [h1.1, h1.2]
      | succ k =>
        rw [Polynomial.coeff_X_mul]
        have h1 := abs_le.mp (L_res_coeff_le N hN R k)
        have h2 := abs_le.mp (L_res_coeff_le N hN R (k+1))
        push_cast
        rw [abs_le]
        constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    )
  have L_res_B_pow : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (Q : Polynomial ℤ) (c e : ℕ), N ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) ≤ ((c : ℝ) + 1) ^ e * N Q :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (Q : Polynomial ℤ) (c e : ℕ) => by
      induction e with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_assoc]
        calc N ((Polynomial.X - Polynomial.C (c : ℤ)) * ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q))
            ≤ ((c : ℝ) + 1) * N ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q) :=
              L_res_B_lin N hN _ c
          _ ≤ ((c : ℝ) + 1) * (((c : ℝ) + 1) ^ k * N Q) := by
              apply mul_le_mul_of_nonneg_left ih
              positivity
          _ = ((c : ℝ) + 1) ^ (k+1) * N Q := by ring
    )
  have L_res_norm_upper : ∀ (n : ℕ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (Q : Polynomial ℤ) (t c e : ℕ) (hc : c ≤ n) (he : e ≤ n), N (Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) ≤
        ((n : ℝ) + 1) ^ n * N Q :=
    (fun (n : ℕ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (Q : Polynomial ℤ) (t c e : ℕ) (hc : c ≤ n) (he : e ≤ n) => by
      rw [mul_assoc]
      have h0 := L_res_B_nonneg N hN Q
      have hcn : (c:ℝ) ≤ n := by exact_mod_cast hc
      have hc0 : (0:ℝ) ≤ (c:ℝ) := Nat.cast_nonneg c
      calc N (Polynomial.X ^ t * ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q))
          ≤ N ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) := L_res_B_Xpow N hN _ t
        _ ≤ ((c : ℝ) + 1) ^ e * N Q := L_res_B_pow N hN Q c e
        _ ≤ ((n : ℝ) + 1) ^ e * N Q := by
            apply mul_le_mul_of_nonneg_right _ h0
            exact pow_le_pow_left₀ (by linarith) (by linarith) e
        _ ≤ ((n : ℝ) + 1) ^ n * N Q := by
            apply mul_le_mul_of_nonneg_right _ h0
            exact pow_le_pow_right₀ (by linarith) he
    )
  have L_res_value : ∀ (n : ℕ) (ξ : ℝ), ∃ B : ℝ, 0 < B ∧ ∀ (Q : Polynomial ℤ) (t c e : ℕ) (δ : ℝ), t ≤ 2 * n + 1 → c ≤ n → e ≤ n →
        |Polynomial.aeval ξ Q| ≤ δ →
        |Polynomial.aeval ξ (Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q)| ≤
          B * δ :=
    (fun (n : ℕ) (ξ : ℝ) => by
      refine ⟨(1 + |ξ|) ^ (2 * n + 1) * (|ξ| + n + 1) ^ n, ?_, ?_⟩
      · have h1 : (0:ℝ) < 1 + |ξ| := by positivity
        have h2 : (0:ℝ) < |ξ| + n + 1 := by positivity
        positivity
      · intro Q t c e δ ht hc he hQ
        have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hQ
        have hval : Polynomial.aeval ξ (Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q)
            = ξ ^ t * (ξ - (c : ℝ)) ^ e * Polynomial.aeval ξ Q := by
          simp [map_mul, map_pow, Polynomial.aeval_X, map_sub]
        rw [hval, abs_mul, abs_mul, abs_pow, abs_pow]
        have hx : 0 ≤ |ξ| := abs_nonneg ξ
        have hA : |ξ| ^ t ≤ (1 + |ξ|) ^ (2 * n + 1) := by
          calc |ξ| ^ t ≤ (1 + |ξ|) ^ t := pow_le_pow_left₀ hx (by linarith) t
            _ ≤ (1 + |ξ|) ^ (2 * n + 1) := pow_le_pow_right₀ (by linarith) ht
        have hcn : (c : ℝ) ≤ n := by exact_mod_cast hc
        have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
        have hd : |ξ - (c : ℝ)| ≤ |ξ| + n + 1 := by
          calc |ξ - (c : ℝ)| ≤ |ξ| + |(c : ℝ)| := abs_sub _ _
            _ = |ξ| + (c : ℝ) := by rw [abs_of_nonneg hc0]
            _ ≤ |ξ| + n + 1 := by linarith
        have hB : |ξ - (c : ℝ)| ^ e ≤ (|ξ| + n + 1) ^ n := by
          calc |ξ - (c : ℝ)| ^ e ≤ (|ξ| + n + 1) ^ e := pow_le_pow_left₀ (abs_nonneg _) hd e
            _ ≤ (|ξ| + n + 1) ^ n := pow_le_pow_right₀ (by
                have : (0:ℝ) ≤ n := Nat.cast_nonneg n
                linarith) he
        have hP1 : 0 ≤ |ξ| ^ t := pow_nonneg hx t
        have hP2 : 0 ≤ |ξ - (c : ℝ)| ^ e := pow_nonneg (abs_nonneg _) e
        have hP3 : (0:ℝ) ≤ (1 + |ξ|) ^ (2 * n + 1) := pow_nonneg (by linarith) _
        have hP4 : (0:ℝ) ≤ (|ξ| + n + 1) ^ n := pow_nonneg (by positivity) _
        calc |ξ| ^ t * |ξ - (c : ℝ)| ^ e * |Polynomial.aeval ξ Q|
            ≤ (1 + |ξ|) ^ (2 * n + 1) * (|ξ| + n + 1) ^ n * δ := by
              apply mul_le_mul (mul_le_mul hA hB hP2 hP3) hQ (abs_nonneg _) (mul_nonneg hP3 hP4)
    )
  have L_res_C_nonneg : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (p : Polynomial ℤ), 0 ≤ N p :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (p : Polynomial ℤ) => by
      rw [hN p]; exact Nat.cast_nonneg _
    )
  have L_res_C_shift : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (P : Polynomial ℤ) (t : ℕ), N P ≤ N (Polynomial.X ^ t * P) :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (P : Polynomial ℤ) (t : ℕ) => by
      apply L_res_N_le N hN P _ (L_res_C_nonneg N hN _)
      intro i
      have h := L_res_coeff_le N hN (Polynomial.X ^ t * P) (i + t)
      rw [Polynomial.coeff_X_pow_mul] at h
      exact h
    )
  have L_res_C_div : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (Q : Polynomial ℤ) (c D : ℕ) (hQ : Q.natDegree ≤ D), N Q ≤ ((D : ℝ) + 1) * N ((Polynomial.X - Polynomial.C (c : ℤ)) * Q) :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (Q : Polynomial ℤ) (c D : ℕ) (hQ : Q.natDegree ≤ D) => by
      set R := (Polynomial.X - Polynomial.C (c : ℤ)) * Q with hR
      have hNR : 0 ≤ N R := L_res_C_nonneg N hN R
      have hcoef : ∀ i : ℕ, |((Q.coeff i : ℤ) : ℝ)| ≤ ((i : ℝ) + 1) * N R := by
        rcases Nat.eq_zero_or_pos c with hc | hc
        · intro i
          have h1 : R.coeff (i + 1) = Q.coeff i := by
            rw [hR, hc]; simp [Polynomial.coeff_X_mul]
          have h2 := L_res_coeff_le N hN R (i + 1)
          rw [h1] at h2
          have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
          nlinarith
        · have hc0 : 1 ≤ c := hc
          have hc1 : (1 : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hc0
          intro i
          induction i with
          | zero =>
            have h1 : R.coeff 0 = -((c : ℤ) * Q.coeff 0) := by
              rw [hR, Polynomial.mul_coeff_zero]; simp
            have h2 := L_res_coeff_le N hN R 0
            rw [h1] at h2
            have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc0
            have h2' : (c : ℝ) * |((Q.coeff 0 : ℤ) : ℝ)| ≤ N R := by
              have e1 : |(((-((c : ℤ) * Q.coeff 0)) : ℤ) : ℝ)|
                  = (c : ℝ) * |((Q.coeff 0 : ℤ) : ℝ)| := by
                push_cast
                rw [abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg c)]
              linarith
            have h3 : |((Q.coeff 0 : ℤ) : ℝ)| ≤ (c : ℝ) * |((Q.coeff 0 : ℤ) : ℝ)| := by
              nlinarith [abs_nonneg ((Q.coeff 0 : ℤ) : ℝ)]
            simp only [Nat.cast_zero, zero_add, one_mul]
            linarith
          | succ k ih =>
            have h1 : R.coeff (k + 1) = Q.coeff k - Q.coeff (k + 1) * (c : ℤ) := by
              rw [hR, mul_comm, Polynomial.coeff_mul_X_sub_C]
            have h2 := L_res_coeff_le N hN R (k + 1)
            have h3 : ((Q.coeff (k + 1) : ℤ) : ℝ) * ((c : ℤ) : ℝ)
                = ((Q.coeff k : ℤ) : ℝ) - ((R.coeff (k + 1) : ℤ) : ℝ) := by
              rw [h1]; push_cast; ring
            have h4 : |((Q.coeff (k + 1) : ℤ) : ℝ)|
                ≤ |((Q.coeff (k + 1) : ℤ) : ℝ) * ((c : ℤ) : ℝ)| := by
              rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < ((c:ℤ):ℝ))]
              nlinarith [abs_nonneg ((Q.coeff (k + 1) : ℤ) : ℝ)]
            rw [h3] at h4
            have h5 : |((Q.coeff k : ℤ) : ℝ) - ((R.coeff (k + 1) : ℤ) : ℝ)|
                ≤ |((Q.coeff k : ℤ) : ℝ)| + |((R.coeff (k + 1) : ℤ) : ℝ)| := by
              rw [abs_le]
              constructor
              · linarith [le_abs_self ((Q.coeff k : ℤ) : ℝ), neg_abs_le ((Q.coeff k : ℤ) : ℝ),
                  le_abs_self ((R.coeff (k + 1) : ℤ) : ℝ), neg_abs_le ((R.coeff (k + 1) : ℤ) : ℝ)]
              · linarith [le_abs_self ((Q.coeff k : ℤ) : ℝ), neg_abs_le ((Q.coeff k : ℤ) : ℝ),
                  le_abs_self ((R.coeff (k + 1) : ℤ) : ℝ), neg_abs_le ((R.coeff (k + 1) : ℤ) : ℝ)]
            push_cast
            push_cast at ih h4 h5
            linarith
      apply L_res_N_le N hN Q _ (by positivity)
      intro i
      by_cases hi : i ≤ D
      · calc |((Q.coeff i : ℤ) : ℝ)| ≤ ((i : ℝ) + 1) * N R := hcoef i
          _ ≤ ((D : ℝ) + 1) * N R := by
            apply mul_le_mul_of_nonneg_right _ hNR
            have : (i : ℝ) ≤ D := by exact_mod_cast hi
            linarith
      · have : Q.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [this]; simp; positivity
    )
  have L_res_C_iter : ∀ (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (n : ℕ) (Q : Polynomial ℤ) (c : ℕ) (hQ : Q.natDegree ≤ n), ∀ e : ℕ, e ≤ n → N Q ≤ (2 * (n : ℝ) + 1) ^ e *
        N ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) :=
    (fun (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (n : ℕ) (Q : Polynomial ℤ) (c : ℕ) (hQ : Q.natDegree ≤ n) => by
      intro e
      induction e with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have ih' := ih (by omega)
        have h1 : ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q).natDegree
            ≤ ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k).natDegree + Q.natDegree :=
          Polynomial.natDegree_mul_le
        have h2 : ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k).natDegree
            ≤ k * (Polynomial.X - Polynomial.C (c : ℤ)).natDegree := Polynomial.natDegree_pow_le
        have h3 : (Polynomial.X - Polynomial.C (c : ℤ)).natDegree ≤ 1 :=
          Polynomial.natDegree_X_sub_C_le _
        have h4 : k * (Polynomial.X - Polynomial.C (c : ℤ)).natDegree ≤ k := by
          simpa using Nat.mul_le_mul_left k h3
        have hdeg : ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q).natDegree ≤ 2 * n := by
          calc ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q).natDegree
              ≤ ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k).natDegree + Q.natDegree := h1
            _ ≤ k * (Polynomial.X - Polynomial.C (c : ℤ)).natDegree + n := Nat.add_le_add h2 hQ
            _ ≤ k + n := Nat.add_le_add_right h4 n
            _ ≤ 2 * n := by omega
        have hstep := L_res_C_div N hN ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q) c (2 * n) hdeg
        have heq : (Polynomial.X - Polynomial.C (c : ℤ)) ^ (k + 1) * Q
            = (Polynomial.X - Polynomial.C (c : ℤ)) * ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q) := by
          ring
        rw [heq]
        push_cast at hstep
        have hM : (0:ℝ) ≤ (2 * (n:ℝ) + 1) ^ k := by positivity
        calc N Q ≤ (2 * (n : ℝ) + 1) ^ k * N ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q) := ih'
          _ ≤ (2 * (n : ℝ) + 1) ^ k * ((2 * (n:ℝ) + 1) * N ((Polynomial.X - Polynomial.C (c : ℤ))
                * ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q))) :=
              mul_le_mul_of_nonneg_left hstep hM
          _ = (2 * (n : ℝ) + 1) ^ (k + 1) * N ((Polynomial.X - Polynomial.C (c : ℤ))
                * ((Polynomial.X - Polynomial.C (c : ℤ)) ^ k * Q)) := by ring
    )
  have L_res_norm_lower : ∀ (n : ℕ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)), ∃ a : ℝ, 0 < a ∧ ∀ (Q : Polynomial ℤ) (t c e : ℕ), Q.natDegree ≤ n → c ≤ n → e ≤ n →
        a * N Q ≤ N (Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) :=
    (fun (n : ℕ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ)) => by
      refine ⟨1 / (2 * (n : ℝ) + 1) ^ n, by positivity, ?_⟩
      intro Q t c e hQ hc he
      have hit := L_res_C_iter N hN n Q c hQ e he
      have hsh := L_res_C_shift N hN ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) t
      have heq : Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q
          = Polynomial.X ^ t * ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) := mul_assoc _ _ _
      rw [heq]
      have hpos : (0:ℝ) < (2 * (n : ℝ) + 1) ^ n := by positivity
      have hle : (2 * (n : ℝ) + 1) ^ e ≤ (2 * (n : ℝ) + 1) ^ n := by
        apply pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) he
      have hNP := L_res_C_nonneg N hN ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q)
      have key : N Q ≤ (2 * (n : ℝ) + 1) ^ n *
          N (Polynomial.X ^ t * ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q)) := by
        calc N Q ≤ (2 * (n : ℝ) + 1) ^ e * N ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) := hit
          _ ≤ (2 * (n : ℝ) + 1) ^ n * N ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) :=
              mul_le_mul_of_nonneg_right hle hNP
          _ ≤ (2 * (n : ℝ) + 1) ^ n *
              N (Polynomial.X ^ t * ((Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q)) :=
              mul_le_mul_of_nonneg_left hsh hpos.le
      have h := mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ 1 / (2 * (n : ℝ) + 1) ^ n)
      rw [← mul_assoc, one_div_mul_cancel hpos.ne', one_mul] at h
      exact h
    )
  have L_res_root_factor : ∀ (Q : Polynomial ℤ) (t c e : ℕ) (α : ℂ)
      (h : Polynomial.aeval α
        (Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) = 0), Polynomial.aeval α (Polynomial.X : Polynomial ℤ) = 0 ∨
      Polynomial.aeval α (Polynomial.X - Polynomial.C (c : ℤ)) = 0 ∨ Polynomial.aeval α Q = 0 :=
    (fun (Q : Polynomial ℤ) (t c e : ℕ) (α : ℂ)
        (h : Polynomial.aeval α
          (Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℤ)) ^ e * Q) = 0) => by
      simp only [map_mul, map_pow, mul_eq_zero] at h
      rcases h with (h | h) | h
      · exact Or.inl (eq_zero_of_pow_eq_zero h)
      · exact Or.inr (Or.inl (eq_zero_of_pow_eq_zero h))
      · exact Or.inr (Or.inr h)
    )
  have L_res_lab_lt : ∀ (n k : ℕ) (hk : 2 ≤ k) (lab : Fin (2 * n + 1 - k + 1) → ℕ)
      (hlab : Multiset.map lab Finset.univ.val =
        Multiset.replicate (n + 2 - k) 0 + Multiset.replicate (n + 2 - k) 1 +
          (Multiset.range k).filter (fun i => 2 ≤ i)) (j : Fin (2 * n + 1 - k + 1)), lab j < k :=
    (fun (n k : ℕ) (hk : 2 ≤ k) (lab : Fin (2 * n + 1 - k + 1) → ℕ)
        (hlab : Multiset.map lab Finset.univ.val =
          Multiset.replicate (n + 2 - k) 0 + Multiset.replicate (n + 2 - k) 1 +
            (Multiset.range k).filter (fun i => 2 ≤ i)) (j : Fin (2 * n + 1 - k + 1)) => by
      have hmem : lab j ∈ Multiset.map lab Finset.univ.val :=
        Multiset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
      rw [hlab] at hmem
      simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_filter,
        Multiset.mem_range] at hmem
      omega
    )
  have L_res_lab_prod : ∀ (n k : ℕ) (f : ℕ → ℝ) (lab : Fin (2 * n + 1 - k + 1) → ℕ)
      (hlab : Multiset.map lab Finset.univ.val =
        Multiset.replicate (n + 2 - k) 0 + Multiset.replicate (n + 2 - k) 1 +
          (Multiset.range k).filter (fun i => 2 ≤ i)), ∏ j, f (lab j) = f 0 ^ (n + 2 - k) * f 1 ^ (n + 2 - k) * ∏ i ∈ Finset.Ico 2 k, f i :=
    (fun (n k : ℕ) (f : ℕ → ℝ) (lab : Fin (2 * n + 1 - k + 1) → ℕ)
        (hlab : Multiset.map lab Finset.univ.val =
          Multiset.replicate (n + 2 - k) 0 + Multiset.replicate (n + 2 - k) 1 +
            (Multiset.range k).filter (fun i => 2 ≤ i)) => by
      have h1 : ∏ j, f (lab j) = ((Multiset.map lab Finset.univ.val).map f).prod := by
        rw [Multiset.map_map]; rfl
      rw [h1, hlab]
      simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
      congr 1
      have hf : (Multiset.range k).filter (fun i => 2 ≤ i) = (Finset.Ico 2 k).val := by
        have : (Finset.range k).filter (fun i => 2 ≤ i) = Finset.Ico 2 k := by
          ext i; simp [Finset.mem_Ico]; omega
        rw [← this]; rfl
      rw [hf]; rfl
    )
  have L_res_unif : ∀ (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
      (hdet : ∀ M : ℕ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ S : Fin (M + 1) → Polynomial ℤ,
        (∀ j, (S j).natDegree ≤ M) →
        LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)) →
        ∀ δ μ ν : ℝ, (∀ j, |Polynomial.aeval ξ (S j)| ≤ δ) →
          (∀ j, |Polynomial.aeval ξ (Polynomial.derivative (S j))| ≤ μ * N (S j)) →
          (∀ j, ν ≤ N (S j)) → 0 < ν →
          1 ≤ C * δ * μ * (∏ j, N (S j)) / ν), ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → M ≤ 2 * n + 1 → ∃ C' : ℝ, 0 < C' ∧ C' ≤ C ∧
        ∀ S : Fin (M + 1) → Polynomial ℤ,
        (∀ j, (S j).natDegree ≤ M) →
        LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)) →
        ∀ δ μ ν : ℝ, (∀ j, |Polynomial.aeval ξ (S j)| ≤ δ) →
          (∀ j, |Polynomial.aeval ξ (Polynomial.derivative (S j))| ≤ μ * N (S j)) →
          (∀ j, ν ≤ N (S j)) → 0 < ν →
          1 ≤ C' * δ * μ * (∏ j, N (S j)) / ν :=
    (fun (n : ℕ) (ξ : ℝ) (N : Polynomial ℤ → ℝ)
        (hdet : ∀ M : ℕ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ S : Fin (M + 1) → Polynomial ℤ,
          (∀ j, (S j).natDegree ≤ M) →
          LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)) →
          ∀ δ μ ν : ℝ, (∀ j, |Polynomial.aeval ξ (S j)| ≤ δ) →
            (∀ j, |Polynomial.aeval ξ (Polynomial.derivative (S j))| ≤ μ * N (S j)) →
            (∀ j, ν ≤ N (S j)) → 0 < ν →
            1 ≤ C * δ * μ * (∏ j, N (S j)) / ν) => by
      choose Cd hCd0 hCd using hdet
      refine ⟨1 + ∑ M ∈ Finset.range (2 * n + 2), (if h : 1 ≤ M then Cd M h else 0), ?_, ?_⟩
      · have : 0 ≤ ∑ M ∈ Finset.range (2 * n + 2), (if h : 1 ≤ M then Cd M h else 0) := by
          apply Finset.sum_nonneg
          intro M _
          split_ifs with h
          · exact (hCd0 M h).le
          · exact le_rfl
        linarith
      · intro M hM hM2
        refine ⟨Cd M hM, hCd0 M hM, ?_, hCd M hM⟩
        have hle : (if h : 1 ≤ M then Cd M h else 0) ≤
            ∑ M ∈ Finset.range (2 * n + 2), (if h : 1 ≤ M then Cd M h else 0) := by
          apply Finset.single_le_sum (f := fun M => if h : 1 ≤ M then Cd M h else 0)
          · intro M _
            show 0 ≤ (if h : 1 ≤ M then Cd M h else 0)
            split_ifs with h
            · exact (hCd0 M h).le
            · exact le_rfl
          · simp only [Finset.mem_range]; omega
        rw [dif_pos hM] at hle
        linarith
    )
  have L_res_combine : ∀ (d B δ μ NS Cd Pi ν a N0 Nm R M0 U : ℝ)
      (hd : d ≤ M0 * (B * δ) / (μ * NS))
      (hdet : 1 ≤ Cd * (B * δ) * μ * Pi / ν)
      (hPi : Pi ≤ U * (R * N0)) (hν : ν = a * N0) (hNS : a * Nm ≤ NS)
      (hμ : 0 < μ) (ha : 0 < a) (hN0 : 0 < N0) (hNm : 0 < Nm) (hR : 0 ≤ R)
      (hBδ : 0 ≤ B * δ) (hCd : 0 < Cd) (hM0 : 0 ≤ M0) (hU : 0 ≤ U), d ≤ (M0 * B ^ 2 * Cd * U / a ^ 2) * δ ^ 2 * R / Nm :=
    (fun (d B δ μ NS Cd Pi ν a N0 Nm R M0 U : ℝ)
        (hd : d ≤ M0 * (B * δ) / (μ * NS))
        (hdet : 1 ≤ Cd * (B * δ) * μ * Pi / ν)
        (hPi : Pi ≤ U * (R * N0)) (hν : ν = a * N0) (hNS : a * Nm ≤ NS)
        (hμ : 0 < μ) (ha : 0 < a) (hN0 : 0 < N0) (hNm : 0 < Nm) (hR : 0 ≤ R)
        (hBδ : 0 ≤ B * δ) (hCd : 0 < Cd) (hM0 : 0 ≤ M0) (hU : 0 ≤ U) => by
      subst hν
      have hNSpos : 0 < NS := lt_of_lt_of_le (mul_pos ha hNm) hNS
      have hX : 0 ≤ M0 * (B * δ) / (μ * NS) :=
        div_nonneg (mul_nonneg hM0 hBδ) (mul_pos hμ hNSpos).le
      have h1 : d ≤ M0 * (B * δ) / (μ * NS) * (Cd * (B * δ) * μ * Pi / (a * N0)) := by
        calc d ≤ M0 * (B * δ) / (μ * NS) := hd
          _ = M0 * (B * δ) / (μ * NS) * 1 := by ring
          _ ≤ M0 * (B * δ) / (μ * NS) * (Cd * (B * δ) * μ * Pi / (a * N0)) :=
            mul_le_mul_of_nonneg_left hdet hX
      have hK : 0 ≤ M0 * Cd * (B * δ) ^ 2 := by positivity
      have h2 : M0 * (B * δ) / (μ * NS) * (Cd * (B * δ) * μ * Pi / (a * N0))
          = M0 * Cd * (B * δ) ^ 2 * Pi / (NS * a * N0) := by
        field_simp
      have h3 : M0 * Cd * (B * δ) ^ 2 * Pi / (NS * a * N0)
          ≤ M0 * Cd * (B * δ) ^ 2 * (U * (R * N0)) / (NS * a * N0) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hPi hK
      have h4 : M0 * Cd * (B * δ) ^ 2 * (U * (R * N0)) / (NS * a * N0)
          = M0 * Cd * (B * δ) ^ 2 * U * R / (NS * a) := by
        field_simp
      have hK2 : 0 ≤ M0 * Cd * (B * δ) ^ 2 * U * R := by positivity
      have h5 : M0 * Cd * (B * δ) ^ 2 * U * R / (NS * a)
          ≤ M0 * Cd * (B * δ) ^ 2 * U * R / (a * Nm * a) := by
        apply div_le_div_of_nonneg_left hK2 (by positivity)
        exact mul_le_mul_of_nonneg_right hNS ha.le
      have h6 : M0 * Cd * (B * δ) ^ 2 * U * R / (a * Nm * a)
          = (M0 * B ^ 2 * Cd * U / a ^ 2) * δ ^ 2 * R / Nm := by
        field_simp
      linarith [h1, h2, h3, h4, h5, h6]
    )
  have L_res : ∀ (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
      (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
      (hspan : ∀ (k : ℕ), 2 ≤ k → k ≤ n + 1 → ∀ (P : ℕ → Polynomial ℚ),
        (∀ i, (P i).natDegree ≤ n) → LinearIndependent ℚ (fun i : Fin k => P i) →
        IsCoprime (P 0) (P 1) →
        ∃ (S : Fin (2 * n + 1 - k + 1) → Polynomial ℚ) (ι lab : Fin (2 * n + 1 - k + 1) → ℕ),
          LinearIndependent ℚ S ∧
          (∀ j, (S j).natDegree ≤ 2 * n + 1 - k) ∧
          (∀ j, ι j < k ∧ ι j ≤ lab j ∧ ∃ t ≤ 2 * n + 1 - k, ∃ c ∈ Finset.range (n + 1), ∃ e ≤ n,
              S j = Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℚ)) ^ e * P (ι j)) ∧
          Multiset.map lab Finset.univ.val =
            Multiset.replicate (n + 2 - k) 0 + Multiset.replicate (n + 2 - k) 1 +
              (Multiset.range k).filter (fun i => 2 ≤ i))
      (hdet : ∀ M : ℕ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ S : Fin (M + 1) → Polynomial ℤ,
        (∀ j, (S j).natDegree ≤ M) →
        LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)) →
        ∀ δ μ ν : ℝ, (∀ j, |Polynomial.aeval ξ (S j)| ≤ δ) →
          (∀ j, |Polynomial.aeval ξ (Polynomial.derivative (S j))| ≤ μ * N (S j)) →
          (∀ j, ν ≤ N (S j)) → 0 < ν →
          1 ≤ C * δ * μ * (∏ j, N (S j)) / ν)
      (hroot : ∀ (M : ℕ) (S : Polynomial ℤ), S ≠ 0 → S.natDegree ≤ M →
        Polynomial.aeval ξ (Polynomial.derivative S) ≠ 0 →
        ∃ α : ℂ, Polynomial.aeval α S = 0 ∧
          ‖(ξ : ℂ) - α‖ ≤ M * |Polynomial.aeval ξ S| / |Polynomial.aeval ξ (Polynomial.derivative S)|)
      (hheight : ∃ C : ℝ, 0 < C ∧ ∀ (S : Polynomial ℤ) (α : ℂ), S ≠ 0 → S.natDegree ≤ n →
        Polynomial.aeval α S = 0 → ∃ β : AlgebraicDegLE n, β.1 = α ∧ (height α : ℝ) ≤ C * N S), ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (P : ℕ → Polynomial ℤ) (δ : ℝ), 2 ≤ k → k ≤ n + 1 →
        (∀ i, (P i).natDegree ≤ n) →
        LinearIndependent ℚ (fun i : Fin k => (P i).map (Int.castRingHom ℚ)) →
        IsCoprime ((P 0).map (Int.castRingHom ℚ)) ((P 1).map (Int.castRingHom ℚ)) →
        (∀ i j, i ≤ j → j < k → N (P i) ≤ N (P j)) →
        (∀ i, i < k → |Polynomial.aeval ξ (P i)| ≤ δ) →
        ∃ α : AlgebraicDegLE n, ∃ m, m < k ∧ (height α.1 : ℝ) ≤ C * N (P m) ∧
          ‖(ξ : ℂ) - α.1‖ ≤ C * δ ^ 2 * N (P 0) ^ (n + 1 - k) * N (P 1) ^ (n + 2 - k) *
            (∏ i ∈ Finset.Ico 2 k, N (P i)) / N (P m) :=
    (fun (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ) (N : Polynomial ℤ → ℝ)
        (hN : ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ))
        (hspan : ∀ (k : ℕ), 2 ≤ k → k ≤ n + 1 → ∀ (P : ℕ → Polynomial ℚ),
          (∀ i, (P i).natDegree ≤ n) → LinearIndependent ℚ (fun i : Fin k => P i) →
          IsCoprime (P 0) (P 1) →
          ∃ (S : Fin (2 * n + 1 - k + 1) → Polynomial ℚ) (ι lab : Fin (2 * n + 1 - k + 1) → ℕ),
            LinearIndependent ℚ S ∧
            (∀ j, (S j).natDegree ≤ 2 * n + 1 - k) ∧
            (∀ j, ι j < k ∧ ι j ≤ lab j ∧ ∃ t ≤ 2 * n + 1 - k, ∃ c ∈ Finset.range (n + 1), ∃ e ≤ n,
                S j = Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℚ)) ^ e * P (ι j)) ∧
            Multiset.map lab Finset.univ.val =
              Multiset.replicate (n + 2 - k) 0 + Multiset.replicate (n + 2 - k) 1 +
                (Multiset.range k).filter (fun i => 2 ≤ i))
        (hdet : ∀ M : ℕ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ S : Fin (M + 1) → Polynomial ℤ,
          (∀ j, (S j).natDegree ≤ M) →
          LinearIndependent ℚ (fun j => (S j).map (Int.castRingHom ℚ)) →
          ∀ δ μ ν : ℝ, (∀ j, |Polynomial.aeval ξ (S j)| ≤ δ) →
            (∀ j, |Polynomial.aeval ξ (Polynomial.derivative (S j))| ≤ μ * N (S j)) →
            (∀ j, ν ≤ N (S j)) → 0 < ν →
            1 ≤ C * δ * μ * (∏ j, N (S j)) / ν)
        (hroot : ∀ (M : ℕ) (S : Polynomial ℤ), S ≠ 0 → S.natDegree ≤ M →
          Polynomial.aeval ξ (Polynomial.derivative S) ≠ 0 →
          ∃ α : ℂ, Polynomial.aeval α S = 0 ∧
            ‖(ξ : ℂ) - α‖ ≤ M * |Polynomial.aeval ξ S| / |Polynomial.aeval ξ (Polynomial.derivative S)|)
        (hheight : ∃ C : ℝ, 0 < C ∧ ∀ (S : Polynomial ℤ) (α : ℂ), S ≠ 0 → S.natDegree ≤ n →
          Polynomial.aeval α S = 0 → ∃ β : AlgebraicDegLE n, β.1 = α ∧ (height α : ℝ) ≤ C * N S) => by
      obtain ⟨a, ha0, ha⟩ := L_res_norm_lower n N hN
      obtain ⟨B, hB0, hB⟩ := L_res_value n ξ
      obtain ⟨Cu, hCu0, hCu⟩ := L_res_unif n ξ N hdet
      obtain ⟨Ch, hCh0, hCh⟩ := hheight
      have hNn : ∀ p, 0 ≤ N p := L_res_B_nonneg N hN
      have hU1 : (1:ℝ) ≤ (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) :=
        one_le_pow₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]))
      refine ⟨Ch * n + (2 * n + 1) * B ^ 2 * Cu * (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) / a ^ 2 + 1,
        by positivity, ?_⟩
      intro k P δ hk2 hkn hdeg hli hcop hmono hval
      have hM1 : 1 ≤ 2 * n + 1 - k := by omega
      have hM2 : 2 * n + 1 - k ≤ 2 * n + 1 := by omega
      obtain ⟨S, ι, lab, hSli, hSdeg, hSι, hlab⟩ := hspan k hk2 hkn
        (fun i => (P i).map (Int.castRingHom ℚ))
        (fun i => Polynomial.natDegree_map_le.trans (hdeg i)) hli hcop
      choose hιk hιlab t ht c hc e he hSeq using hSι
      have hPne : ∀ i, i < k → P i ≠ 0 := by
        intro i hi h0
        have := hli.ne_zero ⟨i, hi⟩
        simp [h0] at this
      have hNP : ∀ i, i < k → 1 ≤ N (P i) := fun i hi => L_res_N_pos N hN _ (hPne i hi)
      have hcn : ∀ j, c j ≤ n := fun j => by have := Finset.mem_range.mp (hc j); omega
      set T : Fin (2 * n + 1 - k + 1) → Polynomial ℤ := fun j =>
        Polynomial.X ^ t j * (Polynomial.X - Polynomial.C ((c j : ℕ) : ℤ)) ^ e j * P (ι j) with hT
      have hTmap : ∀ j, (T j).map (Int.castRingHom ℚ) = S j := by
        intro j; rw [hSeq j]; simp [T, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub]
      have hTli : LinearIndependent ℚ (fun j => (T j).map (Int.castRingHom ℚ)) := by
        have : (fun j => (T j).map (Int.castRingHom ℚ)) = S := funext hTmap
        rw [this]; exact hSli
      have hTdeg : ∀ j, (T j).natDegree ≤ 2 * n + 1 - k := by
        intro j
        have := hSdeg j
        rw [← hTmap j, Polynomial.natDegree_map_eq_of_injective
          (RingHom.injective_int (Int.castRingHom ℚ))] at this
        exact this
      have hTne : ∀ j, T j ≠ 0 := by
        intro j h
        have := hSli.ne_zero j
        rw [← hTmap j, h, Polynomial.map_zero] at this
        exact this rfl
      have hNT : ∀ j, 0 < N (T j) := fun j => lt_of_lt_of_le one_pos (L_res_N_pos N hN _ (hTne j))
      have hTval : ∀ j, |Polynomial.aeval ξ (T j)| ≤ B * δ := by
        intro j
        exact hB (P (ι j)) (t j) (c j) (e j) δ (by have := ht j; omega) (hcn j) (he j)
          (hval _ (hιk j))
      obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_max_image Finset.univ
        (fun j => |Polynomial.aeval ξ (Polynomial.derivative (T j))| / N (T j)) Finset.univ_nonempty
      set μ := |Polynomial.aeval ξ (Polynomial.derivative (T ℓ))| / N (T ℓ) with hμ
      have hμj : ∀ j, |Polynomial.aeval ξ (Polynomial.derivative (T j))| ≤ μ * N (T j) := by
        intro j
        have := hℓ j (Finset.mem_univ _)
        rw [div_le_iff₀ (hNT j)] at this
        exact this
      have hN0 : 1 ≤ N (P 0) := hNP 0 (by omega)
      have hν0 : 0 < a * N (P 0) := mul_pos ha0 (by linarith)
      have hνj : ∀ j, a * N (P 0) ≤ N (T j) := by
        intro j
        have h1 := ha (P (ι j)) (t j) (c j) (e j) (hdeg _) (hcn j) (he j)
        have h2 := hmono 0 (ι j) (Nat.zero_le _) (hιk j)
        calc a * N (P 0) ≤ a * N (P (ι j)) := mul_le_mul_of_nonneg_left h2 ha0.le
          _ ≤ _ := h1
      obtain ⟨Cd, hCd0, hCdle, hCd⟩ := hCu (2 * n + 1 - k) hM1 hM2
      have hdetT := hCd T hTdeg hTli (B * δ) μ (a * N (P 0)) hTval hμj hνj hν0
      have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hval 0 (by omega))
      have hμ0 : 0 < μ := by
        rcases (div_nonneg (abs_nonneg _) (hNT ℓ).le : 0 ≤ μ).lt_or_eq with h | h
        · exact h
        · exfalso
          have h' : μ = 0 := h.symm
          rw [h', mul_zero, zero_mul, zero_div] at hdetT
          linarith
      have hder : Polynomial.aeval ξ (Polynomial.derivative (T ℓ)) ≠ 0 := by
        intro h0
        have : μ = 0 := by rw [hμ, h0]; simp
        linarith
      obtain ⟨α, hαroot, hαdist⟩ := hroot (2 * n + 1 - k) (T ℓ) (hTne ℓ) (hTdeg ℓ) hder
      have hderEq : |Polynomial.aeval ξ (Polynomial.derivative (T ℓ))| = μ * N (T ℓ) := by
        rw [hμ, div_mul_cancel₀ _ (hNT ℓ).ne']
      have hd : ‖(ξ:ℂ) - α‖ ≤ ((2 * n + 1 - k : ℕ) : ℝ) * (B * δ) / (μ * N (T ℓ)) := by
        rw [hderEq] at hαdist
        refine hαdist.trans ?_
        apply div_le_div_of_nonneg_right _ (mul_pos hμ0 (hNT ℓ)).le
        exact mul_le_mul_of_nonneg_left (hTval ℓ) (Nat.cast_nonneg _)
      have hR0 : 0 ≤ N (P 0) ^ (n + 1 - k) * N (P 1) ^ (n + 2 - k) *
          ∏ i ∈ Finset.Ico 2 k, N (P i) :=
        mul_nonneg (mul_nonneg (pow_nonneg (hNn _) _) (pow_nonneg (hNn _) _))
          (Finset.prod_nonneg fun i _ => hNn _)
      have hPi : ∏ j, N (T j) ≤ (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) *
          ((N (P 0) ^ (n + 1 - k) * N (P 1) ^ (n + 2 - k) * ∏ i ∈ Finset.Ico 2 k, N (P i)) *
            N (P 0)) := by
        have h1 : ∀ j, N (T j) ≤ ((n:ℝ) + 1) ^ n * N (P (lab j)) := by
          intro j
          refine (L_res_norm_upper n N hN (P (ι j)) (t j) (c j) (e j) (hcn j) (he j)).trans ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hmono _ _ (hιlab j) (L_res_lab_lt n k hk2 lab hlab j)
        have hlp := L_res_lab_prod n k (fun i => N (P i)) lab hlab
        simp only at hlp
        calc ∏ j, N (T j) ≤ ∏ j, (((n:ℝ) + 1) ^ n * N (P (lab j))) := by
              apply Finset.prod_le_prod
              · intro j _; exact (hNT j).le
              · intro j _; exact h1 j
          _ = (((n:ℝ) + 1) ^ n) ^ (2 * n + 1 - k + 1) * ∏ j, N (P (lab j)) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) * ∏ j, N (P (lab j)) := by
              apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun j _ => hNn _)
              exact pow_le_pow_right₀
                (one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])) (by omega)
          _ = _ := by
              rw [hlp]
              have hk' : n + 2 - k = (n + 1 - k) + 1 := by omega
              rw [hk', pow_succ]
              ring
      have hS0 : ∃ S0 : Polynomial ℤ, S0 ≠ 0 ∧ S0.natDegree ≤ n ∧ Polynomial.aeval α S0 = 0 ∧
          N S0 ≤ n * N (P (ι ℓ)) := by
        have hNl := hNP (ι ℓ) (hιk ℓ)
        have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        obtain ⟨hs1, hs2⟩ := L_res_N_small n hn N hN (c ℓ) (hcn ℓ)
        rcases L_res_root_factor (P (ι ℓ)) (t ℓ) (c ℓ) (e ℓ) α hαroot with h | h | h
        · refine ⟨Polynomial.X, Polynomial.X_ne_zero, ?_, h, ?_⟩
          · rw [Polynomial.natDegree_X]; omega
          · nlinarith
        · refine ⟨Polynomial.X - Polynomial.C ((c ℓ : ℕ) : ℤ), Polynomial.X_sub_C_ne_zero _, ?_, h, ?_⟩
          · rw [Polynomial.natDegree_X_sub_C]; omega
          · nlinarith
        · refine ⟨P (ι ℓ), hPne _ (hιk ℓ), hdeg _, h, ?_⟩
          nlinarith
      obtain ⟨S0, hS0ne, hS0deg, hS0root, hS0N⟩ := hS0
      obtain ⟨β, hβ, hβh⟩ := hCh S0 α hS0ne hS0deg hS0root
      have hKpos : 0 ≤ (2 * n + 1) * B ^ 2 * Cu * (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) / a ^ 2 := by
        positivity
      refine ⟨β, ι ℓ, hιk ℓ, ?_, ?_⟩
      · rw [hβ]
        have hNl := hNP (ι ℓ) (hιk ℓ)
        calc (height α : ℝ) ≤ Ch * N S0 := hβh
          _ ≤ Ch * (n * N (P (ι ℓ))) := mul_le_mul_of_nonneg_left hS0N hCh0.le
          _ = (Ch * n) * N (P (ι ℓ)) := by ring
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            linarith
      · rw [hβ]
        have hNl := hNP (ι ℓ) (hιk ℓ)
        have hνT : a * N (P (ι ℓ)) ≤ N (T ℓ) :=
          ha (P (ι ℓ)) (t ℓ) (c ℓ) (e ℓ) (hdeg _) (hcn ℓ) (he ℓ)
        have hcomb := L_res_combine ‖(ξ:ℂ) - α‖ B δ μ (N (T ℓ)) Cd (∏ j, N (T j)) (a * N (P 0)) a
          (N (P 0)) (N (P (ι ℓ)))
          (N (P 0) ^ (n + 1 - k) * N (P 1) ^ (n + 2 - k) * ∏ i ∈ Finset.Ico 2 k, N (P i))
          ((2 * n + 1 - k : ℕ) : ℝ) ((((n:ℝ) + 1) ^ n) ^ (2 * n + 2))
          hd hdetT hPi rfl hνT hμ0 ha0 (by linarith) (by linarith) hR0 (by positivity) hCd0
          (Nat.cast_nonneg _) (by linarith)
        refine hcomb.trans ?_
        have hK : ((2 * n + 1 - k : ℕ) : ℝ) * B ^ 2 * Cd * (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) / a ^ 2 ≤
            Ch * n + (2 * n + 1) * B ^ 2 * Cu * (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) / a ^ 2 + 1 := by
          have hM' : ((2 * n + 1 - k : ℕ) : ℝ) ≤ 2 * n + 1 := by exact_mod_cast hM2
          have : ((2 * n + 1 - k : ℕ) : ℝ) * B ^ 2 * Cd * (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) / a ^ 2 ≤
              (2 * n + 1) * B ^ 2 * Cu * (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) / a ^ 2 := by
            gcongr
          have : 0 ≤ Ch * n := by positivity
          linarith
        have hNl0 : 0 < N (P (ι ℓ)) := by linarith
        rw [div_le_div_iff_of_pos_right hNl0]
        calc ((2 * n + 1 - k : ℕ) : ℝ) * B ^ 2 * Cd * (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) / a ^ 2 *
              δ ^ 2 * (N (P 0) ^ (n + 1 - k) * N (P 1) ^ (n + 2 - k) * ∏ i ∈ Finset.Ico 2 k, N (P i))
            ≤ (Ch * n + (2 * n + 1) * B ^ 2 * Cu * (((n:ℝ) + 1) ^ n) ^ (2 * n + 2) / a ^ 2 + 1) *
              δ ^ 2 * (N (P 0) ^ (n + 1 - k) * N (P 1) ^ (n + 2 - k) *
                ∏ i ∈ Finset.Ico 2 k, N (P i)) := by
              apply mul_le_mul_of_nonneg_right _ hR0
              exact mul_le_mul_of_nonneg_right hK (sq_nonneg _)
          _ = _ := by ring
    )
  have L_root : ∀ (hfta : ∀ p : Polynomial ℂ, p ≠ 0 → ∃ r : Fin p.natDegree → ℂ,
        p = Polynomial.C p.leadingCoeff * ∏ j, (Polynomial.X - Polynomial.C (r j)))
      (M : ℕ) (S : Polynomial ℤ) (hS : S ≠ 0) (hdeg : S.natDegree ≤ M) (ξ : ℝ)
      (hd : Polynomial.aeval ξ (Polynomial.derivative S) ≠ 0), ∃ α : ℂ, Polynomial.aeval α S = 0 ∧
        ‖(ξ : ℂ) - α‖ ≤ M * |Polynomial.aeval ξ S| / |Polynomial.aeval ξ (Polynomial.derivative S)| :=
    (fun (hfta : ∀ p : Polynomial ℂ, p ≠ 0 → ∃ r : Fin p.natDegree → ℂ,
          p = Polynomial.C p.leadingCoeff * ∏ j, (Polynomial.X - Polynomial.C (r j)))
        (M : ℕ) (S : Polynomial ℤ) (hS : S ≠ 0) (hdeg : S.natDegree ≤ M) (ξ : ℝ)
        (hd : Polynomial.aeval ξ (Polynomial.derivative S) ≠ 0) => by
      classical
      have hcast : ∀ (T : Polynomial ℤ) (x : ℝ),
          Polynomial.aeval (x : ℂ) T = ((Polynomial.aeval x T : ℝ) : ℂ) := by
        intro T x
        have := Polynomial.aeval_algebraMap_apply (R := ℤ) (A := ℝ) ℂ x T
        simpa using this
      have hmap : ∀ (T : Polynomial ℤ) (z : ℂ),
          Polynomial.aeval z T = (T.map (Int.castRingHom ℂ)).eval z := by
        intro T z
        rw [Polynomial.aeval_def, Polynomial.eval_map, algebraMap_int_eq]
      have hRnn : 0 ≤ (M : ℝ) * |Polynomial.aeval ξ S| /
          |Polynomial.aeval ξ (Polynomial.derivative S)| := by positivity
      by_cases h0 : Polynomial.aeval ξ S = 0
      · refine ⟨ξ, ?_, ?_⟩
        · rw [hcast, h0]; simp
        · simpa using hRnn
      set P : Polynomial ℂ := S.map (Int.castRingHom ℂ) with hP
      have hinj : Function.Injective (Int.castRingHom ℂ) := (Int.castRingHom ℂ).injective_int
      have hP0 : P ≠ 0 := by
        intro h
        exact hS ((Polynomial.map_eq_zero_iff hinj).1 h)
      have hPdeg : P.natDegree = S.natDegree := Polynomial.natDegree_map_eq_of_injective hinj S
      obtain ⟨r, hr⟩ := hfta P hP0
      have hPz' : P.eval (ξ : ℂ) = ((Polynomial.aeval ξ S : ℝ) : ℂ) := by
        rw [hP, ← hmap, hcast]
      have hdPz' : (Polynomial.derivative P).eval (ξ : ℂ) =
          ((Polynomial.aeval ξ (Polynomial.derivative S) : ℝ) : ℂ) := by
        rw [hP, Polynomial.derivative_map, ← hmap, hcast]
      have hroot : ∀ j, Polynomial.aeval (r j) S = 0 := by
        intro j
        rw [hmap, ← hP, hr]
        simp [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ j)]
      set z : ℂ := (ξ : ℂ) with hz
      have hPz : P.eval z = P.leadingCoeff * ∏ j, (z - r j) := by
        conv_lhs => rw [hr]
        simp [Polynomial.eval_prod]
      have hPz0 : P.eval z ≠ 0 := by
        rw [hPz']; exact_mod_cast h0
      have hw0 : ∀ j, z - r j ≠ 0 := by
        intro j hj
        apply hPz0
        rw [hPz, Finset.prod_eq_zero (Finset.mem_univ j) hj, mul_zero]
      have hdP : (Polynomial.derivative P).eval z = P.eval z * ∑ j, (z - r j)⁻¹ := by
        have h1 : Polynomial.derivative P = Polynomial.C P.leadingCoeff *
            Polynomial.derivative (∏ j, (Polynomial.X - Polynomial.C (r j))) := by
          conv_lhs => rw [hr]
          rw [Polynomial.derivative_C_mul]
        have hsumeq : Polynomial.eval z (∑ i, (∏ b ∈ Finset.univ.erase i,
            (Polynomial.X - Polynomial.C (r b))) *
              Polynomial.derivative (Polynomial.X - Polynomial.C (r i))) =
            (∏ j, (z - r j)) * ∑ j, (z - r j)⁻¹ := by
          rw [Polynomial.eval_finset_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
            sub_zero, mul_one, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
          rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_inv_cancel_right₀ (hw0 j)]
        rw [h1, Polynomial.derivative_prod_finset, Polynomial.eval_mul, Polynomial.eval_C,
          hsumeq, hPz, mul_assoc]
      by_contra hcon
      push_neg at hcon
      set R : ℝ := M * |Polynomial.aeval ξ S| / |Polynomial.aeval ξ (Polynomial.derivative S)|
        with hR
      have hlt : ∀ j, R < ‖z - r j‖ := fun j => hcon (r j) (hroot j)
      have hdpos : 0 < P.natDegree := by
        rcases Nat.eq_zero_or_pos P.natDegree with h | h
        · exfalso
          apply hd
          rw [hPdeg] at h
          rw [Polynomial.derivative_of_natDegree_zero h]; simp
        · exact h
      have hMpos : (0:ℝ) < M := by
        have : 0 < M := lt_of_lt_of_le (hPdeg ▸ hdpos) hdeg
        exact_mod_cast this
      have ha : 0 < |Polynomial.aeval ξ S| := abs_pos.2 h0
      have hb : 0 < |Polynomial.aeval ξ (Polynomial.derivative S)| := abs_pos.2 hd
      have hRpos : 0 < R := by rw [hR]; positivity
      have hsum : ∑ j, ‖z - r j‖⁻¹ < ∑ _j : Fin P.natDegree, R⁻¹ := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact Finset.univ_nonempty_iff.2 ⟨⟨0, hdpos⟩⟩
        · intro j _
          exact inv_strictAnti₀ hRpos (hlt j)
      have hsum2 : ∑ _j : Fin P.natDegree, R⁻¹ ≤ M * R⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 hRpos.le)
        exact_mod_cast (hPdeg ▸ hdeg)
      have key : |Polynomial.aeval ξ (Polynomial.derivative S)| ≤
          |Polynomial.aeval ξ S| * ∑ j, ‖z - r j‖⁻¹ := by
        have e1 : ‖(Polynomial.derivative P).eval z‖ =
            |Polynomial.aeval ξ (Polynomial.derivative S)| := by
          rw [hdPz', Complex.norm_real, Real.norm_eq_abs]
        have e2 : ‖P.eval z‖ = |Polynomial.aeval ξ S| := by
          rw [hPz', Complex.norm_real, Real.norm_eq_abs]
        rw [← e1, ← e2, hdP, norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        refine (norm_sum_le _ _).trans ?_
        simp [norm_inv]
      have heq : |Polynomial.aeval ξ S| * (M * R⁻¹) =
          |Polynomial.aeval ξ (Polynomial.derivative S)| := by
        rw [hR]; field_simp
      have hfin : |Polynomial.aeval ξ (Polynomial.derivative S)| <
          |Polynomial.aeval ξ (Polynomial.derivative S)| := by
        calc |Polynomial.aeval ξ (Polynomial.derivative S)|
            ≤ |Polynomial.aeval ξ S| * ∑ j, ‖z - r j‖⁻¹ := key
          _ < |Polynomial.aeval ξ S| * (M * R⁻¹) :=
              mul_lt_mul_of_pos_left (lt_of_lt_of_le hsum hsum2) ha
          _ = _ := heq
      exact lt_irrefl _ hfin
    )
  have L_span_steinitz : ∀ (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (p m : ℕ) (v : Fin p → Polynomial ℚ) (w : Fin m → Polynomial ℚ)
      (hv : LinearIndependent ℚ v) (hsub : ∀ i, v i ∈ Submodule.span ℚ (Set.range w)), p ≤ m :=
    (fun (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (p m : ℕ) (v : Fin p → Polynomial ℚ) (w : Fin m → Polynomial ℚ)
        (hv : LinearIndependent ℚ v) (hsub : ∀ i, v i ∈ Submodule.span ℚ (Set.range w)) => by
      by_contra hpm
      push_neg at hpm
      have ha : ∀ i, ∃ c : Fin m → ℚ, ∑ j, c j • w j = v i := fun i =>
        (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hsub i)
      choose a ha using ha
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        have h0 : v ⟨0, hpm⟩ = 0 := by rw [← ha]; simp
        exact hv.ne_zero ⟨0, hpm⟩ h0
      set u : Fin p → Polynomial ℚ := fun i =>
        ∑ j : Fin m, Polynomial.C (a i j) * Polynomial.X ^ (j : ℕ) with hu
      have hcoef : ∀ i (j : Fin m), (u i).coeff j = a i j := by
        intro i j
        simp only [hu, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h.symm)
        · simp
      have hui : LinearIndependent ℚ u := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hsum : ∀ j : Fin m, ∑ i, g i * a i j = 0 := by
          intro j
          have := congrArg (fun q => Polynomial.coeff q (j : ℕ)) hg
          simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul, hcoef, smul_eq_mul,
            Polynomial.coeff_zero] at this
          exact this
        have hv0 : ∑ i, g i • v i = 0 := by
          calc ∑ i, g i • v i = ∑ i, g i • ∑ j, a i j • w j := by simp only [ha]
            _ = ∑ j, (∑ i, g i * a i j) • w j := by
              simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
              rw [Finset.sum_comm]
            _ = 0 := by simp [hsum]
        exact (Fintype.linearIndependent_iff.mp hv) g hv0
      apply hdim m (fun j : Fin (m + 1) => u (Fin.castLE hpm j))
      · intro j
        by_cases hz : u (Fin.castLE hpm j) = 0
        · rw [hz, Polynomial.natDegree_zero]; exact hm0
        · rw [Polynomial.natDegree_lt_iff_degree_lt hz]
          exact Polynomial.degree_sum_fin_lt _
      · exact hui.comp _ (Fin.castLE_injective hpm)
    )
  have L_span_nonroot : ∀ (p : Polynomial ℚ) (hp : p ≠ 0) (T : Finset ℕ) (hT : p.natDegree < T.card), ∃ c ∈ T, p.eval (c : ℚ) ≠ 0 :=
    (fun (p : Polynomial ℚ) (hp : p ≠ 0) (T : Finset ℕ) (hT : p.natDegree < T.card) => by
      induction T using Finset.induction_on generalizing p with
      | empty => simp at hT
      | insert a T haT ih =>
        by_cases ha : p.eval (a : ℚ) = 0
        · have hroot : p.IsRoot (a : ℚ) := ha
          have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
          set q := p /ₘ (Polynomial.X - Polynomial.C (a : ℚ)) with hq
          have hq0 : q ≠ 0 := by
            intro h0; apply hp; rw [← hfac, h0, mul_zero]
          have hdeg : p.natDegree = q.natDegree + 1 := by
            rw [← hfac, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
              Polynomial.natDegree_X_sub_C]; ring
          rw [Finset.card_insert_of_notMem haT] at hT
          obtain ⟨c, hcT, hc⟩ := ih q hq0 (by omega)
          refine ⟨c, Finset.mem_insert_of_mem hcT, ?_⟩
          rw [← hfac, Polynomial.eval_mul]
          refine mul_ne_zero ?_ hc
          rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
          intro hca
          apply haT
          have : c = a := by exact_mod_cast hca
          rw [← this]; exact hcT
        · exact ⟨a, Finset.mem_insert_self a T, ha⟩
    )
  have L_span_coprime_X_sub_C : ∀ (a : ℚ) (p : Polynomial ℚ) (h : p.eval a ≠ 0), IsCoprime (Polynomial.X - Polynomial.C a) p :=
    (fun (a : ℚ) (p : Polynomial ℚ) (h : p.eval a ≠ 0) => by
      have key := Polynomial.modByMonic_add_div p (Polynomial.monic_X_sub_C a)
      rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at key
      have he : Polynomial.C (p.eval a)⁻¹ * Polynomial.C (p.eval a) = 1 := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ h, Polynomial.C_1]
      refine ⟨-(Polynomial.C (p.eval a)⁻¹) * (p /ₘ (Polynomial.X - Polynomial.C a)),
        Polynomial.C (p.eval a)⁻¹, ?_⟩
      linear_combination (-Polynomial.C (p.eval a)⁻¹) * key + he
    )
  have L_span_choose : ∀ (n : ℕ) (P0 P1 : Polynomial ℚ) (h0 : P0 ≠ 0) (h1 : P1 ≠ 0)
      (hd0 : P0.natDegree ≤ n) (hd1 : P1.natDegree ≤ n) (hcop : IsCoprime P0 P1), ∃ c0 ∈ Finset.range (n + 1), ∃ c1 ∈ Finset.range (n + 1),
        IsCoprime ((Polynomial.X - Polynomial.C (c0 : ℚ)) ^ (n - P0.natDegree) * P0)
          ((Polynomial.X - Polynomial.C (c1 : ℚ)) ^ (n - P1.natDegree) * P1) ∧
        ((Polynomial.X - Polynomial.C (c0 : ℚ)) ^ (n - P0.natDegree) * P0).natDegree = n ∧
        ((Polynomial.X - Polynomial.C (c1 : ℚ)) ^ (n - P1.natDegree) * P1).natDegree = n :=
    (fun (n : ℕ) (P0 P1 : Polynomial ℚ) (h0 : P0 ≠ 0) (h1 : P1 ≠ 0)
        (hd0 : P0.natDegree ≤ n) (hd1 : P1.natDegree ≤ n) (hcop : IsCoprime P0 P1) => by
      have hdegQ : ∀ (c : ℚ) (P : Polynomial ℚ), P ≠ 0 → P.natDegree ≤ n →
          ((Polynomial.X - Polynomial.C c) ^ (n - P.natDegree) * P).natDegree = n := by
        intro c P hP hPd
        rw [Polynomial.natDegree_mul (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c)) hP,
          Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
        omega
      obtain ⟨c0, hc0, hP1c0⟩ := L_span_nonroot P1 h1 (Finset.range (n + 1))
        (by rw [Finset.card_range]; omega)
      have hQ0ne : (Polynomial.X - Polynomial.C (c0 : ℚ)) ^ (n - P0.natDegree) * P0 ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)) h0
      obtain ⟨c1, hc1, hQ0c1⟩ := L_span_nonroot
        ((Polynomial.X - Polynomial.C (c0 : ℚ)) ^ (n - P0.natDegree) * P0) hQ0ne (Finset.range (n + 1))
        (by rw [Finset.card_range, hdegQ _ _ h0 hd0]; omega)
      refine ⟨c0, hc0, c1, hc1, ?_, hdegQ _ _ h0 hd0, hdegQ _ _ h1 hd1⟩
      apply IsCoprime.mul_right
      · exact ((L_span_coprime_X_sub_C _ _ hQ0c1).pow_left).symm
      · exact IsCoprime.mul_left (L_span_coprime_X_sub_C _ _ hP1c0).pow_left hcop
    )
  have L_span_coeffs_zero : ∀ (m : ℕ) (f : Fin m → ℚ)
      (h : (∑ i : Fin m, Polynomial.C (f i) * Polynomial.X ^ (i : ℕ)) = 0), ∀ i, f i = 0 :=
    (fun (m : ℕ) (f : Fin m → ℚ)
        (h : (∑ i : Fin m, Polynomial.C (f i) * Polynomial.X ^ (i : ℕ)) = 0) => by
      intro i
      have := congrArg (fun p => Polynomial.coeff p (i : ℕ)) h
      simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hb
        rw [if_neg]
        intro hib; exact hb (Fin.ext hib.symm)
      · simp
    )
  have L_span_sylvester : ∀ (n m : ℕ) (hm : m ≤ n) (Q0 Q1 : Polynomial ℚ) (hcop : IsCoprime Q0 Q1)
      (hd0 : Q0.natDegree = n) (hd1 : Q1.natDegree = n), LinearIndependent ℚ (fun i : Fin (m + m) =>
        if (i : ℕ) < m then Polynomial.X ^ (i : ℕ) * Q0 else Polynomial.X ^ ((i : ℕ) - m) * Q1) :=
    (fun (n m : ℕ) (hm : m ≤ n) (Q0 Q1 : Polynomial ℚ) (hcop : IsCoprime Q0 Q1)
        (hd0 : Q0.natDegree = n) (hd1 : Q1.natDegree = n) => by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · intro i; exact absurd i.2 (by omega)
      rw [Fin.sum_univ_add] at hg
      simp only [Fin.val_castAdd, Fin.is_lt, if_true, Fin.val_natAdd, Polynomial.smul_eq_C_mul] at hg
      have hn : ∀ i : Fin m, ¬ (m + (i : ℕ) < m) := fun i => by omega
      simp only [hn, if_false, Nat.add_sub_cancel_left] at hg
      set A := ∑ i : Fin m, Polynomial.C (g (Fin.castAdd m i)) * Polynomial.X ^ (i : ℕ) with hA
      set B := ∑ i : Fin m, Polynomial.C (g (Fin.natAdd m i)) * Polynomial.X ^ (i : ℕ) with hB
      have hAB : A * Q0 + B * Q1 = 0 := by
        rw [hA, hB, Finset.sum_mul, Finset.sum_mul]
        rw [← hg]; congr 1 <;> (apply Finset.sum_congr rfl; intro i _; ring)
      have hQ1 : Q1 ≠ 0 := by
        intro h0; rw [h0, Polynomial.natDegree_zero] at hd1; omega
      have hQ0 : Q0 ≠ 0 := by
        intro h0; rw [h0, Polynomial.natDegree_zero] at hd0; omega
      have hdvd : Q1 ∣ A * Q0 := ⟨-B, by linear_combination hAB⟩
      have hA0 : A = 0 := by
        apply Polynomial.eq_zero_of_dvd_of_degree_lt (hcop.symm.dvd_of_dvd_mul_right hdvd)
        rw [Polynomial.degree_eq_natDegree hQ1, hd1]
        exact lt_of_lt_of_le (Polynomial.degree_sum_fin_lt _) (by exact_mod_cast hm)
      have hB0 : B = 0 := by
        rw [hA0, zero_mul, zero_add] at hAB
        exact (mul_eq_zero.mp hAB).resolve_right hQ1
      have h1 := L_span_coeffs_zero m _ hA0
      have h2 := L_span_coeffs_zero m _ hB0
      intro i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i
      · exact h1 a
      · exact h2 a
    )
  have L_span_V_natDegree : ∀ {j : ℕ} (A : Fin j → Polynomial ℚ) (M : ℕ) (q : Polynomial ℚ)
      (hq : q ∈ Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M ∧
        q = Polynomial.X ^ t * A i}), q.natDegree ≤ M :=
    (fun {j : ℕ} (A : Fin j → Polynomial ℚ) (M : ℕ) (q : Polynomial ℚ)
        (hq : q ∈ Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M ∧
          q = Polynomial.X ^ t * A i}) => by
      induction hq using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, t, ht, rfl⟩ := hx
        calc (Polynomial.X ^ t * A i).natDegree ≤ (Polynomial.X ^ t : Polynomial ℚ).natDegree + (A i).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ t + (A i).natDegree := by
              have := Polynomial.natDegree_X_pow_le (R := ℚ) t
              omega
          _ ≤ M := ht
      | zero => simp
      | add x y _ _ hx hy =>
        exact le_trans (Polynomial.natDegree_add_le x y) (max_le hx hy)
      | smul a x _ hx =>
        exact le_trans (Polynomial.natDegree_smul_le a x) hx
    )
  have L_span_mem_span_X_pow : ∀ (M : ℕ) (q : Polynomial ℚ) (hq : q.natDegree ≤ M), q ∈ Submodule.span ℚ (Set.range (fun i : Fin (M + 1) => (Polynomial.X : Polynomial ℚ) ^ (i : ℕ))) :=
    (fun (M : ℕ) (q : Polynomial ℚ) (hq : q.natDegree ≤ M) => by
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => q.coeff i, ?_⟩
      conv_rhs => rw [q.as_sum_range' (M + 1) (by omega)]
      rw [Fin.sum_univ_eq_sum_range (fun i => q.coeff i • (Polynomial.X : Polynomial ℚ) ^ i) (M + 1)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
    )
  have L_span_concave_step : ∀ {j : ℕ} (n : ℕ) (A : Fin j → Polynomial ℚ)
      (hdeg : ∀ i, (A i).natDegree ≤ n) (M : ℕ) (hM : n ≤ M) (a b : ℕ)
      (u : Fin a → Polynomial ℚ) (w : Fin b → Polynomial ℚ)
      (hu : ∀ i, u i ∈ Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M ∧
        q = Polynomial.X ^ t * A i})
      (hspan0 : Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M ∧
        q = Polynomial.X ^ t * A i} ≤ Submodule.span ℚ (Set.range u))
      (hspan1 : Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M + 1 ∧
        q = Polynomial.X ^ t * A i} = Submodule.span ℚ (Set.range (Fin.append u w))), Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M + 2 ∧
        q = Polynomial.X ^ t * A i} ≤
        Submodule.span ℚ (Set.range (Fin.append (Fin.append u w) (fun i => Polynomial.X * w i))) :=
    (fun {j : ℕ} (n : ℕ) (A : Fin j → Polynomial ℚ)
        (hdeg : ∀ i, (A i).natDegree ≤ n) (M : ℕ) (hM : n ≤ M) (a b : ℕ)
        (u : Fin a → Polynomial ℚ) (w : Fin b → Polynomial ℚ)
        (hu : ∀ i, u i ∈ Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M ∧
          q = Polynomial.X ^ t * A i})
        (hspan0 : Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M ∧
          q = Polynomial.X ^ t * A i} ≤ Submodule.span ℚ (Set.range u))
        (hspan1 : Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M + 1 ∧
          q = Polynomial.X ^ t * A i} = Submodule.span ℚ (Set.range (Fin.append u w))) => by
      set T := Submodule.span ℚ (Set.range (Fin.append (Fin.append u w) (fun i => Polynomial.X * w i)))
        with hT
      have hsub1 : Submodule.span ℚ (Set.range (Fin.append u w)) ≤ T := by
        apply Submodule.span_mono
        rintro _ ⟨k, rfl⟩
        exact ⟨Fin.castAdd b k, by simp⟩
      -- X maps V_M into V_{M+1}
      have hXV : ∀ y ∈ Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M ∧
          q = Polynomial.X ^ t * A i}, Polynomial.X * y ∈ Submodule.span ℚ
            {q | ∃ (i : Fin j) (t : ℕ), t + (A i).natDegree ≤ M + 1 ∧ q = Polynomial.X ^ t * A i} := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, t, ht, rfl⟩ := hx
          apply Submodule.subset_span
          exact ⟨i, t + 1, by omega, by ring⟩
        | zero => simp
        | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
      have hX : ∀ y ∈ Submodule.span ℚ (Set.range (Fin.append u w)), Polynomial.X * y ∈ T := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, rfl⟩ := hx
          refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
          · rw [Fin.append_left]
            apply hsub1
            rw [← hspan1]
            exact hXV _ (hu k')
          · rw [Fin.append_right]
            apply Submodule.subset_span
            exact ⟨Fin.natAdd (a + b) k', by simp⟩
        | zero => simp
        | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
      rw [Submodule.span_le]
      rintro _ ⟨i, t, ht, rfl⟩
      by_cases h1 : t + (A i).natDegree ≤ M + 1
      · apply hsub1
        rw [← hspan1]
        exact Submodule.subset_span ⟨i, t, h1, rfl⟩
      · have ht1 : 1 ≤ t := by have := hdeg i; omega
        have hmem : Polynomial.X ^ (t - 1) * A i ∈ Submodule.span ℚ (Set.range (Fin.append u w)) := by
          rw [← hspan1]
          exact Submodule.subset_span ⟨i, t - 1, by omega, rfl⟩
        have := hX _ hmem
        have heq : Polynomial.X * (Polynomial.X ^ (t - 1) * A i) = Polynomial.X ^ t * A i := by
          rw [← mul_assoc, ← pow_succ']
          congr 2; omega
        rw [heq] at this
        exact this
    )
  have L_span_card_bound : ∀ (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (M p : ℕ) (v : Fin p → Polynomial ℚ) (hv : LinearIndependent ℚ v)
      (hdeg : ∀ i, (v i).natDegree ≤ M), p ≤ M + 1 :=
    (fun (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (M p : ℕ) (v : Fin p → Polynomial ℚ) (hv : LinearIndependent ℚ v)
        (hdeg : ∀ i, (v i).natDegree ≤ M) => L_span_steinitz hdim p (M + 1) v (fun i : Fin (M + 1) => Polynomial.X ^ (i : ℕ)) hv
        (fun i => L_span_mem_span_X_pow M (v i) (hdeg i))
    )
  have L_span_extend_basis : ∀ (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (M : ℕ) (W : Submodule ℚ (Polynomial ℚ)) (hW : ∀ q ∈ W, q.natDegree ≤ M)
      (a : ℕ) (u : Fin a → Polynomial ℚ) (hu : LinearIndependent ℚ u) (huW : ∀ i, u i ∈ W), ∃ (b : ℕ) (w : Fin b → Polynomial ℚ), LinearIndependent ℚ (Fin.append u w) ∧
        (∀ i, w i ∈ W) ∧ W ≤ Submodule.span ℚ (Set.range (Fin.append u w)) :=
    (fun (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (M : ℕ) (W : Submodule ℚ (Polynomial ℚ)) (hW : ∀ q ∈ W, q.natDegree ≤ M)
        (a : ℕ) (u : Fin a → Polynomial ℚ) (hu : LinearIndependent ℚ u) (huW : ∀ i, u i ∈ W) => by
      classical
      let Pb : ℕ → Prop := fun b => ∃ w : Fin b → Polynomial ℚ,
        LinearIndependent ℚ (Fin.append u w) ∧ ∀ i, w i ∈ W
      have hP0 : Pb 0 := ⟨Fin.elim0, by rw [Fin.append_elim0]; exact hu.comp _ (Fin.cast_injective _),
        fun i => i.elim0⟩
      have hbound : ∀ b, Pb b → b ≤ M + 1 := by
        rintro b ⟨w, hw, hwW⟩
        have := L_span_card_bound hdim M (a + b) _ hw (fun i => hW _ (by
          refine Fin.addCases (fun k => ?_) (fun k => ?_) i
          · rw [Fin.append_left]; exact huW k
          · rw [Fin.append_right]; exact hwW k))
        omega
      obtain ⟨w, hw, hwW⟩ : Pb (Nat.findGreatest Pb (M + 1)) :=
        Nat.findGreatest_spec (P := Pb) (m := 0) (Nat.zero_le _) hP0
      refine ⟨_, w, hw, hwW, ?_⟩
      intro q hq
      by_contra hqn
      have hli : LinearIndependent ℚ (Fin.append u (Fin.snoc w q)) := by
        rw [Fin.append_snoc, linearIndependent_fin_snoc]
        exact ⟨hw, hqn⟩
      have hPb1 : Pb (Nat.findGreatest Pb (M + 1) + 1) := ⟨Fin.snoc w q, hli, fun i => by
        refine Fin.lastCases ?_ (fun k => ?_) i
        · rw [Fin.snoc_last]; exact hq
        · rw [Fin.snoc_castSucc]; exact hwW k⟩
      have := Nat.le_findGreatest (hbound _ hPb1) hPb1
      omega
    )
  have L_span_arith : ∀ (g : ℕ → ℕ) (n j s : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n + 1) (hs : s ≤ n + 1 - j)
      (hconc : ∀ M, n ≤ M → g (M + 2) + g M ≤ 2 * g (M + 1))
      (h0 : j ≤ g n) (h1 : g (n + s) < 2 * s + j) (h2 : 2 * n ≤ g (2 * n - 1)), False :=
    (fun (g : ℕ → ℕ) (n j s : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n + 1) (hs : s ≤ n + 1 - j)
        (hconc : ∀ M, n ≤ M → g (M + 2) + g M ≤ 2 * g (M + 1))
        (h0 : j ≤ g n) (h1 : g (n + s) < 2 * s + j) (h2 : 2 * n ≤ g (2 * n - 1)) => by
      have hs1 : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h | h
        · subst h; simp at h1; omega
        · exact h
      by_cases hA : g (n + (s - 1)) + 2 ≤ g (n + s)
      · have c1 : ∀ t, t < s → g (n + (s - t) - 1) + 2 ≤ g (n + (s - t)) := by
          intro t
          induction t with
          | zero =>
            intro _
            have e : n + (s - 0) - 1 = n + (s - 1) := by omega
            rw [e, Nat.sub_zero]; exact hA
          | succ t ih =>
            intro ht
            have ih' := ih (by omega)
            have hc := hconc (n + (s - (t+1)) - 1) (by omega)
            have e1 : n + (s - (t + 1)) - 1 + 2 = n + (s - t) := by omega
            have e2 : n + (s - (t + 1)) - 1 + 1 = n + (s - (t + 1)) := by omega
            have e3 : n + (s - t) - 1 = n + (s - (t + 1)) := by omega
            rw [e1, e2] at hc
            rw [e3] at ih'
            omega
        have c2 : ∀ t, t ≤ s → g n + 2 * t ≤ g (n + t) := by
          intro t
          induction t with
          | zero => intro _; simp
          | succ t ih =>
            intro ht
            have ih' := ih (by omega)
            have h := c1 (s - (t + 1)) (by omega)
            have e1 : n + (s - (s - (t + 1))) = n + (t + 1) := by omega
            have e2 : n + (t + 1) - 1 = n + t := by omega
            rw [e1, e2] at h
            omega
        have := c2 s le_rfl
        omega
      · push_neg at hA
        have c3 : ∀ t, g (n + s + t) ≤ g (n + s + t - 1) + 1 := by
          intro t
          induction t with
          | zero =>
            have e : n + s + 0 - 1 = n + (s - 1) := by omega
            rw [e, Nat.add_zero]; omega
          | succ t ih =>
            have hc := hconc (n + s + t - 1) (by omega)
            have e1 : n + s + t - 1 + 2 = n + s + (t + 1) := by omega
            have e2 : n + s + t - 1 + 1 = n + s + t := by omega
            have e3 : n + s + (t + 1) - 1 = n + s + t := by omega
            rw [e1, e2] at hc
            rw [e3]
            omega
        have c4 : ∀ t, g (n + s + t) ≤ g (n + s) + t := by
          intro t
          induction t with
          | zero => simp
          | succ t ih =>
            have h := c3 (t + 1)
            have e3 : n + s + (t + 1) - 1 = n + s + t := by omega
            rw [e3] at h
            omega
        have := c4 (n - 1 - s)
        have e : n + s + (n - 1 - s) = 2 * n - 1 := by omega
        rw [e] at this
        omega
    )
  have L_span_lemma51 : ∀ (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (n j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n + 1) (A : Fin j → Polynomial ℚ)
      (hA : LinearIndependent ℚ A) (hdeg : ∀ i, (A i).natDegree ≤ n) (i0 i1 : Fin j)
      (hcop : IsCoprime (A i0) (A i1)) (hd0 : (A i0).natDegree = n) (hd1 : (A i1).natDegree = n)
      (s : ℕ) (hs : s ≤ n + 1 - j)
      (r : ℕ) (w : Fin r → Polynomial ℚ) (hr : r < 2 * s + j), ¬ (∀ i t, t + (A i).natDegree ≤ n + s →
          Polynomial.X ^ t * A i ∈ Submodule.span ℚ (Set.range w)) :=
    (fun (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (n j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n + 1) (A : Fin j → Polynomial ℚ)
        (hA : LinearIndependent ℚ A) (hdeg : ∀ i, (A i).natDegree ≤ n) (i0 i1 : Fin j)
        (hcop : IsCoprime (A i0) (A i1)) (hd0 : (A i0).natDegree = n) (hd1 : (A i1).natDegree = n)
        (s : ℕ) (hs : s ≤ n + 1 - j)
        (r : ℕ) (w : Fin r → Polynomial ℚ) (hr : r < 2 * s + j) => by
      intro hB
      classical
      set V : ℕ → Submodule ℚ (Polynomial ℚ) := fun M => Submodule.span ℚ {q | ∃ (i : Fin j) (t : ℕ),
        t + (A i).natDegree ≤ M ∧ q = Polynomial.X ^ t * A i} with hVdef
      have hVdeg : ∀ M q, q ∈ V M → q.natDegree ≤ M := fun M q hq => L_span_V_natDegree A M q hq
      have hbasis : ∀ M, ∃ (p : ℕ) (v : Fin p → Polynomial ℚ), LinearIndependent ℚ v ∧
          (∀ i, v i ∈ V M) ∧ V M ≤ Submodule.span ℚ (Set.range v) := by
        intro M
        obtain ⟨b, w, hw, hwV, hVw⟩ := L_span_extend_basis hdim M (V M) (hVdeg M) 0 Fin.elim0
          (linearIndependent_empty_type) (fun i => i.elim0)
        refine ⟨0 + b, Fin.append Fin.elim0 w, hw, ?_, hVw⟩
        intro i
        refine Fin.addCases (fun k => k.elim0) (fun k => ?_) i
        rw [Fin.append_right]; exact hwV k
      choose g v hv hvV hVv using hbasis
      have hi : ∀ M p (x : Fin p → Polynomial ℚ), LinearIndependent ℚ x → (∀ i, x i ∈ V M) → p ≤ g M :=
        fun M p x hx hxV => L_span_steinitz hdim p (g M) x (v M) hx (fun i => hVv M (hxV i))
      have hii : ∀ M r (y : Fin r → Polynomial ℚ), V M ≤ Submodule.span ℚ (Set.range y) → g M ≤ r :=
        fun M r y hy => L_span_steinitz hdim (g M) r (v M) y (hv M) (fun i => hy (hvV M i))
      have hmono : ∀ M, V M ≤ V (M + 1) := by
        intro M
        refine Submodule.span_mono ?_
        rintro _ ⟨i, t, ht, rfl⟩
        exact ⟨i, t, by omega, rfl⟩
      have hconc : ∀ M, n ≤ M → g (M + 2) + g M ≤ 2 * g (M + 1) := by
        intro M hM
        obtain ⟨b, w, hw, hwV, hVw⟩ := L_span_extend_basis hdim (M + 1) (V (M + 1)) (hVdeg (M + 1))
          (g M) (v M) (hv M) (fun i => hmono M (hvV M i))
        have hmem : ∀ i, Fin.append (v M) w i ∈ V (M + 1) := by
          intro i
          refine Fin.addCases (fun k => ?_) (fun k => ?_) i
          · rw [Fin.append_left]; exact hmono M (hvV M k)
          · rw [Fin.append_right]; exact hwV k
        have h1 : g M + b ≤ g (M + 1) := hi (M + 1) _ _ hw hmem
        have hspan1 : V (M + 1) = Submodule.span ℚ (Set.range (Fin.append (v M) w)) := by
          apply le_antisymm hVw
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact hmem i
        have hst := L_span_concave_step n A hdeg M hM (g M) b (v M) w (hvV M) (hVv M) hspan1
        have h2 := hii (M + 2) _ _ hst
        omega
      have hstart : j ≤ g n := hi n j A hA (fun i => Submodule.subset_span
        ⟨i, 0, by simpa using hdeg i, by simp⟩)
      have hmid : g (n + s) ≤ r := hii (n + s) r w (by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, t, ht, rfl⟩
        exact hB i t ht)
      have hn1 : 1 ≤ n := by omega
      have hend : 2 * n ≤ g (2 * n - 1) := by
        have := hi (2 * n - 1) (n + n) _ (L_span_sylvester n n le_rfl (A i0) (A i1) hcop hd0 hd1) (by
          intro i
          by_cases hin : (i : ℕ) < n
          · simp only [if_pos hin]
            exact Submodule.subset_span ⟨i0, i, by omega, rfl⟩
          · simp only [if_neg hin]
            exact Submodule.subset_span ⟨i1, (i : ℕ) - n, by omega, rfl⟩)
        omega
      exact L_span_arith g n j s hj2 hjn hs hconc hstart (by omega) hend
    )
  have L_span_subseq_aux : ∀ (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (k : ℕ) (P : ℕ → Polynomial ℚ)
      (hind : LinearIndependent ℚ (fun i : Fin k => P i)) (Q0 Q1 : Polynomial ℚ)
      (hQ : LinearIndependent ℚ ![Q0, Q1]), ∀ m, m ≤ k → ∃ (c : ℕ) (κ : Fin c → ℕ), (∀ i, κ i ≤ (i : ℕ) + 2) ∧
        LinearIndependent ℚ (Fin.append ![Q0, Q1] (fun i => P (κ i))) ∧
        (∀ l, l < m → P l ∈ Submodule.span ℚ (Set.range (Fin.append ![Q0, Q1] (fun i => P (κ i))))) ∧
        m ≤ c + 2 :=
    (fun (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (k : ℕ) (P : ℕ → Polynomial ℚ)
        (hind : LinearIndependent ℚ (fun i : Fin k => P i)) (Q0 Q1 : Polynomial ℚ)
        (hQ : LinearIndependent ℚ ![Q0, Q1]) => by
      intro m
      induction m with
      | zero =>
        intro _
        refine ⟨0, Fin.elim0, fun i => i.elim0, ?_, fun l hl => absurd hl (Nat.not_lt_zero _), by omega⟩
        have : (fun i : Fin 0 => P (Fin.elim0 i : ℕ)) = Fin.elim0 := funext (fun i => i.elim0)
        rw [this, Fin.append_elim0]
        exact hQ.comp _ (Fin.cast_injective _)
      | succ m ih =>
        intro hm
        obtain ⟨c, κ, hκ, hli, hsp, hmc⟩ := ih (by omega)
        by_cases hPm : P m ∈ Submodule.span ℚ (Set.range (Fin.append ![Q0, Q1] (fun i => P (κ i))))
        · have hsp' : ∀ l, l < m + 1 → P l ∈ Submodule.span ℚ
              (Set.range (Fin.append ![Q0, Q1] (fun i => P (κ i)))) := by
            intro l hl
            rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h | h
            · exact hsp l h
            · rw [h]; exact hPm
          refine ⟨c, κ, hκ, hli, hsp', ?_⟩
          have hli' : LinearIndependent ℚ (fun l : Fin (m + 1) => P l) :=
            hind.comp (Fin.castLE hm) (Fin.castLE_injective hm)
          have := L_span_steinitz hdim (m + 1) (2 + c) _ _ hli' (fun l => hsp' l l.2)
          omega
        · refine ⟨c + 1, Fin.snoc κ m, ?_, ?_, ?_, by omega⟩
          · intro i
            refine Fin.lastCases ?_ (fun i => ?_) i
            · rw [Fin.snoc_last]; simp; omega
            · rw [Fin.snoc_castSucc]; simpa using hκ i
          · have : (fun i => P ((Fin.snoc κ m : Fin (c + 1) → ℕ) i)) =
                Fin.snoc (fun i => P (κ i)) (P m) := by
              funext i
              refine Fin.lastCases ?_ (fun i => ?_) i
              · simp
              · simp
            rw [this, Fin.append_snoc, linearIndependent_fin_snoc]
            exact ⟨hli, hPm⟩
          · have : (fun i => P ((Fin.snoc κ m : Fin (c + 1) → ℕ) i)) =
                Fin.snoc (fun i => P (κ i)) (P m) := by
              funext i
              refine Fin.lastCases ?_ (fun i => ?_) i
              · simp
              · simp
            rw [this, Fin.append_snoc]
            have hle : Submodule.span ℚ (Set.range (Fin.append ![Q0, Q1] (fun i => P (κ i)))) ≤
                Submodule.span ℚ (Set.range (Fin.snoc (Fin.append ![Q0, Q1] (fun i => P (κ i))) (P m) :
                  Fin (2 + c + 1) → Polynomial ℚ)) := by
              refine Submodule.span_mono ?_
              rintro _ ⟨i, rfl⟩
              exact ⟨Fin.castSucc i, by simp⟩
            intro l hl
            rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h | h
            · exact hle (hsp l h)
            · rw [h]
              exact Submodule.subset_span ⟨Fin.last _, by simp⟩
    )
  have L_span_subseq : ∀ (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (k : ℕ) (hk2 : 2 ≤ k) (P : ℕ → Polynomial ℚ)
      (hind : LinearIndependent ℚ (fun i : Fin k => P i)) (Q0 Q1 : Polynomial ℚ)
      (hQ : LinearIndependent ℚ ![Q0, Q1]), ∃ σ : Fin (k - 2) → ℕ, (∀ i, σ i ≤ (i : ℕ) + 2) ∧
        LinearIndependent ℚ (Fin.append ![Q0, Q1] (fun i => P (σ i))) :=
    (fun (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (k : ℕ) (hk2 : 2 ≤ k) (P : ℕ → Polynomial ℚ)
        (hind : LinearIndependent ℚ (fun i : Fin k => P i)) (Q0 Q1 : Polynomial ℚ)
        (hQ : LinearIndependent ℚ ![Q0, Q1]) => by
      obtain ⟨c, κ, hκ, hli, -, hkc⟩ := L_span_subseq_aux hdim k P hind Q0 Q1 hQ k le_rfl
      have hle : k - 2 ≤ c := by omega
      refine ⟨fun i => κ (Fin.castLE hle i), fun i => by simpa using hκ (Fin.castLE hle i), ?_⟩
      have hle2 : 2 + (k - 2) ≤ 2 + c := by omega
      have : Fin.append ![Q0, Q1] (fun i => P (κ (Fin.castLE hle i))) =
          Fin.append ![Q0, Q1] (fun i => P (κ i)) ∘ Fin.castLE hle2 := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simp only [Fin.append_left, Function.comp_apply]
          have : Fin.castLE hle2 (Fin.castAdd (k - 2) i) = Fin.castAdd c i := Fin.ext (by simp)
          rw [this, Fin.append_left]
        · simp only [Fin.append_right, Function.comp_apply]
          have : Fin.castLE hle2 (Fin.natAdd 2 i) = Fin.natAdd 2 (Fin.castLE hle i) := Fin.ext (by simp)
          rw [this, Fin.append_right]
      rw [this]
      exact hli.comp _ (Fin.castLE_injective hle2)
    )
  have L_span_append_castLE : ∀ (a c d : ℕ) (h : d ≤ c) (u : Fin a → Polynomial ℚ)
      (v : Fin c → Polynomial ℚ) (hli : LinearIndependent ℚ (Fin.append u v)), LinearIndependent ℚ (Fin.append u (fun i : Fin d => v (Fin.castLE h i))) :=
    (fun (a c d : ℕ) (h : d ≤ c) (u : Fin a → Polynomial ℚ)
        (v : Fin c → Polynomial ℚ) (hli : LinearIndependent ℚ (Fin.append u v)) => by
      have hle2 : a + d ≤ a + c := by omega
      have : Fin.append u (fun i : Fin d => v (Fin.castLE h i)) = Fin.append u v ∘ Fin.castLE hle2 := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simp only [Fin.append_left, Function.comp_apply]
          have : Fin.castLE hle2 (Fin.castAdd d i) = Fin.castAdd c i := Fin.ext (by simp)
          rw [this, Fin.append_left]
        · simp only [Fin.append_right, Function.comp_apply]
          have : Fin.castLE hle2 (Fin.natAdd a i) = Fin.natAdd a (Fin.castLE h i) := Fin.ext (by simp)
          rw [this, Fin.append_right]
      rw [this]
      exact hli.comp _ (Fin.castLE_injective hle2)
    )
  have L_span_greedy : ∀ (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v)
      (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) (P : ℕ → Polynomial ℚ)
      (hdeg : ∀ i, (P i).natDegree ≤ n) (Q0 Q1 : Polynomial ℚ) (hcop : IsCoprime Q0 Q1)
      (hd0 : Q0.natDegree = n) (hd1 : Q1.natDegree = n)
      (σ : Fin (k - 2) → ℕ) (hσ : ∀ i, σ i ≤ (i : ℕ) + 2)
      (hli : LinearIndependent ℚ (Fin.append ![Q0, Q1] (fun i => P (σ i))))
      (F : Fin (n + 2 - k + (n + 2 - k)) → Polynomial ℚ) (hF : LinearIndependent ℚ F)
      (hFspan : ∀ t, t ≤ n + 1 - k → Polynomial.X ^ t * Q0 ∈ Submodule.span ℚ (Set.range F) ∧
        Polynomial.X ^ t * Q1 ∈ Submodule.span ℚ (Set.range F)), ∀ m, m ≤ k - 2 → ∃ (R : Fin m → Polynomial ℚ) (ιR : Fin m → ℕ),
        LinearIndependent ℚ (Fin.append F R) ∧
        ∀ i, ιR i ≤ (i : ℕ) + 2 ∧ ∃ t, t + (P (ιR i)).natDegree ≤ 2 * n + 1 - k ∧
          R i = Polynomial.X ^ t * P (ιR i) :=
    (fun (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v)
        (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) (P : ℕ → Polynomial ℚ)
        (hdeg : ∀ i, (P i).natDegree ≤ n) (Q0 Q1 : Polynomial ℚ) (hcop : IsCoprime Q0 Q1)
        (hd0 : Q0.natDegree = n) (hd1 : Q1.natDegree = n)
        (σ : Fin (k - 2) → ℕ) (hσ : ∀ i, σ i ≤ (i : ℕ) + 2)
        (hli : LinearIndependent ℚ (Fin.append ![Q0, Q1] (fun i => P (σ i))))
        (F : Fin (n + 2 - k + (n + 2 - k)) → Polynomial ℚ) (hF : LinearIndependent ℚ F)
        (hFspan : ∀ t, t ≤ n + 1 - k → Polynomial.X ^ t * Q0 ∈ Submodule.span ℚ (Set.range F) ∧
          Polynomial.X ^ t * Q1 ∈ Submodule.span ℚ (Set.range F)) => by
      intro m
      induction m with
      | zero =>
        intro _
        refine ⟨Fin.elim0, Fin.elim0, ?_, fun i => i.elim0⟩
        rw [Fin.append_elim0]
        exact hF.comp _ (Fin.cast_injective _)
      | succ m ih =>
        intro hm
        obtain ⟨R, ιR, hR, hιR⟩ := ih (by omega)
        have hA := L_span_append_castLE 2 (k - 2) (m + 1) hm ![Q0, Q1] _ hli
        set A := Fin.append ![Q0, Q1] (fun i : Fin (m + 1) => P (σ (Fin.castLE hm i))) with hAdef
        have hA0 : A (Fin.castAdd (m + 1) 0) = Q0 := by rw [hAdef, Fin.append_left]; simp
        have hA1 : A (Fin.castAdd (m + 1) 1) = Q1 := by rw [hAdef, Fin.append_left]; simp
        have hAd : ∀ i, (A i).natDegree ≤ n := by
          intro i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i
          · rw [hAdef, Fin.append_left]
            fin_cases i
            · simp [hd0]
            · simp [hd1]
          · rw [hAdef, Fin.append_right]; exact hdeg _
        have h51 := L_span_lemma51 hdim n (2 + (m + 1)) (by omega) (by omega) A hA hAd
          (Fin.castAdd (m + 1) 0) (Fin.castAdd (m + 1) 1) (by rw [hA0, hA1]; exact hcop)
          (by rw [hA0]; exact hd0) (by rw [hA1]; exact hd1) (n + 1 - k) (by omega)
          (n + 2 - k + (n + 2 - k) + m) (Fin.append F R) (by omega)
        push_neg at h51
        obtain ⟨i, t, ht, hnot⟩ := h51
        have hFle : Submodule.span ℚ (Set.range F) ≤ Submodule.span ℚ (Set.range (Fin.append F R)) := by
          refine Submodule.span_mono ?_
          rintro _ ⟨i, rfl⟩
          exact ⟨Fin.castAdd m i, by simp⟩
        revert ht hnot
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · intro ht hnot
          exfalso
          apply hnot
          rw [hAdef, Fin.append_left] at *
          fin_cases i
          · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at ht ⊢
            exact hFle (hFspan t (by omega)).1
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at ht ⊢
            exact hFle (hFspan t (by omega)).2
        · intro ht hnot
          rw [hAdef, Fin.append_right] at ht hnot
          refine ⟨Fin.snoc R (Polynomial.X ^ t * P (σ (Fin.castLE hm i))),
            Fin.snoc ιR (σ (Fin.castLE hm i)), ?_, ?_⟩
          · rw [Fin.append_snoc, linearIndependent_fin_snoc]
            exact ⟨hR, hnot⟩
          · intro l
            refine Fin.lastCases ?_ (fun l => ?_) l
            · simp only [Fin.snoc_last, Fin.val_last]
              refine ⟨?_, t, ?_, rfl⟩
              · have := hσ (Fin.castLE hm i)
                have := i.2
                simp at *; omega
              · omega
            · simp only [Fin.snoc_castSucc, Fin.val_castSucc]
              exact hιR l
    )
  have L_span_ofFn_add_two : ∀ (m : ℕ), List.ofFn (fun i : Fin m => (i : ℕ) + 2) = (List.range m).map (· + 2) :=
    (fun (m : ℕ) => by
      rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]; rfl
    )
  have L_span_filter_range : ∀ (k : ℕ), (Multiset.range k).filter (fun i => 2 ≤ i) = (Multiset.range (k - 2)).map (· + 2) :=
    (fun (k : ℕ) => by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Multiset.range_succ, Multiset.filter_cons, ih]
        by_cases hk : 2 ≤ k
        · rw [if_pos hk]
          obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
          simp only [show m + 2 + 1 - 2 = m + 1 by omega, Nat.add_sub_cancel, Multiset.range_succ,
            Multiset.map_cons]
          rfl
        · rw [if_neg hk, show k + 1 - 2 = 0 by omega, show k - 2 = 0 by omega]; rfl
    )
  have L_span : ∀ (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) (P : ℕ → Polynomial ℚ)
      (hdeg : ∀ i, (P i).natDegree ≤ n)
      (hind : LinearIndependent ℚ (fun i : Fin k => P i))
      (hcop : IsCoprime (P 0) (P 1))
      (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
        ¬ LinearIndependent ℚ v), ∃ (S : Fin (2 * n + 1 - k + 1) → Polynomial ℚ) (ι lab : Fin (2 * n + 1 - k + 1) → ℕ),
        LinearIndependent ℚ S ∧
        (∀ j, (S j).natDegree ≤ 2 * n + 1 - k) ∧
        (∀ j, ι j < k ∧ ι j ≤ lab j ∧ ∃ t ≤ 2 * n + 1 - k, ∃ c ∈ Finset.range (n + 1), ∃ e ≤ n,
            S j = Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℚ)) ^ e * P (ι j)) ∧
        Multiset.map lab Finset.univ.val =
          Multiset.replicate (n + 2 - k) 0 + Multiset.replicate (n + 2 - k) 1 +
            (Multiset.range k).filter (fun i => 2 ≤ i) :=
    (fun (n k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) (P : ℕ → Polynomial ℚ)
        (hdeg : ∀ i, (P i).natDegree ≤ n)
        (hind : LinearIndependent ℚ (fun i : Fin k => P i))
        (hcop : IsCoprime (P 0) (P 1))
        (hdim : ∀ (m : ℕ) (v : Fin (m + 1) → Polynomial ℚ), (∀ j, (v j).natDegree < m) →
          ¬ LinearIndependent ℚ v) => by
      classical
      have hk0 : 0 < k := by omega
      have hk1 : 1 < k := by omega
      have hP0 : P 0 ≠ 0 := by simpa using hind.ne_zero (⟨0, hk0⟩ : Fin k)
      have hP1 : P 1 ≠ 0 := by simpa using hind.ne_zero (⟨1, hk1⟩ : Fin k)
      obtain ⟨c0, hc0, c1, hc1, hQcop, hQd0, hQd1⟩ :=
        L_span_choose n (P 0) (P 1) hP0 hP1 (hdeg 0) (hdeg 1) hcop
      set Q0 := (Polynomial.X - Polynomial.C (c0 : ℚ)) ^ (n - (P 0).natDegree) * P 0 with hQ0
      set Q1 := (Polynomial.X - Polynomial.C (c1 : ℚ)) ^ (n - (P 1).natDegree) * P 1 with hQ1
      have hn1 : 1 ≤ n := by omega
      have hQ : LinearIndependent ℚ ![Q0, Q1] := by
        have h := L_span_sylvester n 1 hn1 Q0 Q1 hQcop hQd0 hQd1
        have : (fun i : Fin (1 + 1) =>
            if (i : ℕ) < 1 then Polynomial.X ^ (i : ℕ) * Q0 else Polynomial.X ^ ((i : ℕ) - 1) * Q1) =
            ![Q0, Q1] := by
          funext i
          fin_cases i <;> simp
        rwa [this] at h
      obtain ⟨σ, hσ, hli⟩ := L_span_subseq hdim k hk2 P hind Q0 Q1 hQ
      set a := n + 2 - k with ha
      have han : a ≤ n := by omega
      set F : Fin (a + a) → Polynomial ℚ := Fin.append (fun i : Fin a => Polynomial.X ^ (i : ℕ) * Q0)
        (fun i : Fin a => Polynomial.X ^ (i : ℕ) * Q1) with hFdef
      have hF : LinearIndependent ℚ F := by
        have h := L_span_sylvester n a han Q0 Q1 hQcop hQd0 hQd1
        have : (fun i : Fin (a + a) =>
            if (i : ℕ) < a then Polynomial.X ^ (i : ℕ) * Q0 else Polynomial.X ^ ((i : ℕ) - a) * Q1) =
            F := by
          funext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i
          · rw [hFdef, Fin.append_left]; simp
          · rw [hFdef, Fin.append_right]; simp
        rwa [this] at h
      have hFspan : ∀ t, t ≤ n + 1 - k → Polynomial.X ^ t * Q0 ∈ Submodule.span ℚ (Set.range F) ∧
          Polynomial.X ^ t * Q1 ∈ Submodule.span ℚ (Set.range F) := by
        intro t ht
        have hta : t < a := by omega
        constructor
        · refine Submodule.subset_span ⟨Fin.castAdd a ⟨t, hta⟩, ?_⟩
          rw [hFdef, Fin.append_left]
        · refine Submodule.subset_span ⟨Fin.natAdd a ⟨t, hta⟩, ?_⟩
          rw [hFdef, Fin.append_right]
      obtain ⟨R, ιR, hR, hιR⟩ := L_span_greedy hdim n k hk2 hkn P hdeg Q0 Q1 hQcop hQd0 hQd1 σ hσ hli
        F hF hFspan (k - 2) le_rfl
      have hcard : 2 * n + 1 - k + 1 = a + a + (k - 2) := by omega
      set S' := Fin.append F R with hS'
      set ι' : Fin (a + a + (k - 2)) → ℕ :=
        Fin.append (Fin.append (fun _ : Fin a => 0) (fun _ : Fin a => 1)) ιR with hι'
      set lab' : Fin (a + a + (k - 2)) → ℕ :=
        Fin.append (Fin.append (fun _ : Fin a => 0) (fun _ : Fin a => 1)) (fun i : Fin (k - 2) => (i : ℕ) + 2)
        with hlab'
      have hprop : ∀ j, (S' j).natDegree ≤ 2 * n + 1 - k ∧ ι' j < k ∧ ι' j ≤ lab' j ∧
          ∃ t ≤ 2 * n + 1 - k, ∃ c ∈ Finset.range (n + 1), ∃ e ≤ n,
            S' j = Polynomial.X ^ t * (Polynomial.X - Polynomial.C (c : ℚ)) ^ e * P (ι' j) := by
        intro j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [hS', hι', hlab', Fin.append_left]
          refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simp only [hFdef, Fin.append_left]
            refine ⟨?_, hk0, le_rfl, j, by omega, c0, hc0, n - (P 0).natDegree, Nat.sub_le _ _,
              by rw [hQ0, mul_assoc]⟩
            refine (Polynomial.natDegree_mul_le).trans ?_
            rw [Polynomial.natDegree_X_pow, hQd0]; omega
          · simp only [hFdef, Fin.append_right]
            refine ⟨?_, hk1, le_rfl, j, by omega, c1, hc1, n - (P 1).natDegree, Nat.sub_le _ _,
              by rw [hQ1, mul_assoc]⟩
            refine (Polynomial.natDegree_mul_le).trans ?_
            rw [Polynomial.natDegree_X_pow, hQd1]; omega
        · simp only [hS', hι', hlab', Fin.append_right]
          obtain ⟨hle, t, ht, hRj⟩ := hιR j
          have hj := j.2
          refine ⟨?_, by omega, hle, t, by omega, 0, by simp, 0, Nat.zero_le _, by rw [hRj]; simp⟩
          rw [hRj]
          refine (Polynomial.natDegree_mul_le).trans ?_
          rw [Polynomial.natDegree_X_pow]; omega
      refine ⟨S' ∘ Fin.cast hcard, ι' ∘ Fin.cast hcard, lab' ∘ Fin.cast hcard,
        hR.comp _ (Fin.cast_injective hcard), fun j => (hprop _).1,
        fun j => (hprop _).2, ?_⟩
      have hc : ∀ {N M : ℕ} (h : N = M) (f : Fin M → ℕ), List.ofFn (f ∘ Fin.cast h) = List.ofFn f := by
        intro N M h f; subst h; rfl
      rw [hlab', Fin.univ_val_map, hc, List.ofFn_fin_append, List.ofFn_fin_append, List.ofFn_const,
        List.ofFn_const, L_span_ofFn_add_two, L_span_filter_range, ← Multiset.coe_add, ← Multiset.coe_add,
        Multiset.coe_replicate, Multiset.coe_replicate]
      rfl
    )
  have hNex : ∃ N : Polynomial ℤ → ℝ,
      ∀ p, N p = ((p.support.sup fun i => (p.coeff i).natAbs : ℕ) : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ := hNex
  have hgel := L_gelfond n N hN L_fta
  have hdim := L_dim
  have hheight := L_height n N hN hgel L_gauss
  have hres := L_res n hn ξ hξ N hN
    (fun k hk2 hkn P hdeg hind hcop => L_span n k hk2 hkn P hdeg hind hcop hdim)
    (fun M hM => L_det2 M hM ξ N hN)
    (fun M S hS hdeg hd => L_root L_fta M S hS hdeg ξ hd) hheight
  have hmii := L_mii n (by omega) ξ hξ N hN
  have hconfig := fun ε hε hε1 => L_config n hn ξ hξ N hN hmii
    (fun W ε hW hε hε1 => L_good n (by omega) ξ hξ N hN hgel L_gauss W ε hW hε hε1)
    hgel L_gauss hdim ε hε hε1
  apply L_final n ξ
  intro ω hω0 hωc
  obtain ⟨K, hK, hKη⟩ := L_approx n hn ξ hξ N hN hconfig hres
    (fun x hx a ha2 hmono hsum => L_opt n hn x hx a ha2 hmono hsum)
    (((ω : ℝ) + 1 / (2 - Real.log 2) * n) / 2) (by linarith)
  exact L_absorb n ξ hξ ω hω0 _ K (by linarith) hK hKη)")
    withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0, maxRecDepth := 100000 })
      (do Lean.Elab.Tactic.evalTactic stx; Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing)

end Submission
