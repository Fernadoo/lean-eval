import ChallengeDeps
import Submission.Helpers
import Lean

open EquiangularLinesFixedAngle
open Filter
open scoped RealInnerProductSpace

set_option autoImplicit false

namespace Submission

theorem theorem_1_2 (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    let k := spectralRadiusOrder ((1 - α) / (2 * α))
    (k < ⊤ → ∀ᶠ d in atTop, N α d = ⌊(k.toNat * (d - 1) : ℝ) / (k.toNat - 1 : ℝ)⌋₊) ∧
    (k = ⊤ → ∃ e : ℕ → ℝ, e =o[atTop] (Nat.cast : ℕ → ℝ) ∧ ∀ d, N α d = d + e d) := by
  run_tac do
    let stx ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "(
  open Matrix in
  have L_spec_mem : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (r : ℝ), r ∈ spectrum ℝ A ↔ ∃ x : Fin m → ℝ, x ≠ 0 ∧ A *ᵥ x = r • x :=
    fun {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (r : ℝ) => by
      rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det,
        isUnit_iff_ne_zero, not_not, ← Matrix.exists_mulVec_eq_zero_iff]
      constructor
      · rintro ⟨x, hx, h⟩
        refine ⟨x, hx, ?_⟩
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
        exact h.symm
      · rintro ⟨x, hx, h⟩
        refine ⟨x, hx, ?_⟩
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
        exact h.symm
  open Matrix in
  have L_spec_abs : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i j, 0 ≤ A i j)
      (x : Fin m → ℝ), |x ⬝ᵥ (A *ᵥ x)| ≤ (fun i => |x i|) ⬝ᵥ (A *ᵥ (fun i => |x i|)) :=
    fun {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i j, 0 ≤ A i j)
        (x : Fin m → ℝ) => by
      simp only [dotProduct, mulVec]
      calc |∑ i, x i * ∑ j, A i j * x j| ≤ ∑ i, |x i * ∑ j, A i j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |x i| * ∑ j, A i j * |x j| := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc |∑ j, A i j * x j| ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ j, A i j * |x j| := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_mul, abs_of_nonneg (hA i j)]
  open Matrix in
  have L_spec_absdot : ∀ {m : ℕ} (x : Fin m → ℝ), (fun i => |x i|) ⬝ᵥ (fun i => |x i|) = x ⬝ᵥ x :=
    fun {m : ℕ} (x : Fin m → ℝ) => by
      simp only [dotProduct, abs_mul_abs_self]
  open Matrix in
  have L_spec_self_nonneg : ∀ {m : ℕ} (x : Fin m → ℝ), 0 ≤ x ⬝ᵥ x :=
    fun {m : ℕ} (x : Fin m → ℝ) => by
      simp only [dotProduct]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  open Matrix in
  have L_spec_self_eq_zero : ∀ {m : ℕ} (x : Fin m → ℝ) (h : x ⬝ᵥ x = 0), x = 0 :=
    fun {m : ℕ} (x : Fin m → ℝ) (h : x ⬝ᵥ x = 0) => by
      simp only [dotProduct] at h
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).mp h i
        (Finset.mem_univ i)
      exact mul_self_eq_zero.mp this
  open Matrix in
  have L_spec_self_pos : ∀ {m : ℕ} (x : Fin m → ℝ) (hx : x ≠ 0), 0 < x ⬝ᵥ x :=
    fun {m : ℕ} (x : Fin m → ℝ) (hx : x ≠ 0) => by
      rcases (L_spec_self_nonneg x).lt_or_eq with h | h
      · exact h
      · exact absurd (L_spec_self_eq_zero x h.symm) hx
  open Matrix in
  have L_spec_eig_le : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i j, 0 ≤ A i j)
      (μ : ℝ) (hR : ∀ x : Fin m → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ μ * (x ⬝ᵥ x))
      (r : ℝ) (x : Fin m → ℝ) (hx : x ≠ 0) (hr : A *ᵥ x = r • x), |r| ≤ μ :=
    fun {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i j, 0 ≤ A i j)
        (μ : ℝ) (hR : ∀ x : Fin m → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ μ * (x ⬝ᵥ x))
        (r : ℝ) (x : Fin m → ℝ) (hx : x ≠ 0) (hr : A *ᵥ x = r • x) => by
      have hpos := L_spec_self_pos x hx
      have h1 : x ⬝ᵥ (A *ᵥ x) = r * (x ⬝ᵥ x) := by
        rw [hr, dotProduct_smul, smul_eq_mul]
      have h2 := L_spec_abs A hA x
      have h3 := hR (fun i => |x i|)
      rw [L_spec_absdot] at h3
      rw [h1, abs_mul, abs_of_pos hpos] at h2
      have h4 : |r| * (x ⬝ᵥ x) ≤ μ * (x ⬝ᵥ x) := le_trans h2 h3
      exact le_of_mul_le_mul_right h4 hpos
  open Matrix in
  have L_spec_quad : ∀ (c d : ℝ) (hd : 0 ≤ d) (h : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * d), c = 0 :=
    fun (c d : ℝ) (hd : 0 ≤ d) (h : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * d) => by
      have hd1 : 0 < d + 1 := by linarith
      set t := -c / (d + 1) with ht
      have htc : c = -(t * (d + 1)) := by
        rw [ht]; field_simp
      have h0 := h t
      rw [htc] at h0
      have hsq : t ^ 2 ≤ 0 := by nlinarith [sq_nonneg t]
      have ht0 : t = 0 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hsq (sq_nonneg t))
      rw [htc, ht0]; ring
  open Matrix in
  have L_spec_symm : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hS : Aᵀ = A) (x y : Fin m → ℝ), x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) :=
    fun {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hS : Aᵀ = A) (x y : Fin m → ℝ) => by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, dotProduct_comm]
  open Matrix in
  have L_spec_eigvec : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hS : Aᵀ = A)
      (μ : ℝ) (hR : ∀ x : Fin m → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ μ * (x ⬝ᵥ x))
      (x₀ : Fin m → ℝ) (h0 : x₀ ⬝ᵥ (A *ᵥ x₀) = μ * (x₀ ⬝ᵥ x₀)), A *ᵥ x₀ = μ • x₀ :=
    fun {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hS : Aᵀ = A)
        (μ : ℝ) (hR : ∀ x : Fin m → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ μ * (x ⬝ᵥ x))
        (x₀ : Fin m → ℝ) (h0 : x₀ ⬝ᵥ (A *ᵥ x₀) = μ * (x₀ ⬝ᵥ x₀)) => by
      set v := μ • x₀ - A *ᵥ x₀ with hv
      have hvv : v ⬝ᵥ v = 0 := by
        apply L_spec_quad (v ⬝ᵥ v) (μ * (v ⬝ᵥ v) - v ⬝ᵥ (A *ᵥ v))
        · linarith [hR v]
        · intro t
          have h := hR (x₀ + t • v)
          have e1 : (x₀ + t • v) ⬝ᵥ (A *ᵥ (x₀ + t • v)) =
              x₀ ⬝ᵥ (A *ᵥ x₀) + 2 * t * (v ⬝ᵥ (A *ᵥ x₀)) + t ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
              dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
              L_spec_symm A hS x₀ v]
            simp only [smul_eq_mul]; ring
          have e2 : (x₀ + t • v) ⬝ᵥ (x₀ + t • v) =
              x₀ ⬝ᵥ x₀ + 2 * t * (v ⬝ᵥ x₀) + t ^ 2 * (v ⬝ᵥ v) := by
            rw [add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, smul_dotProduct,
              dotProduct_smul, dotProduct_smul, dotProduct_comm x₀ v]
            simp only [smul_eq_mul]; ring
          have e3 : v ⬝ᵥ v = μ * (v ⬝ᵥ x₀) - v ⬝ᵥ (A *ᵥ x₀) := by
            conv_lhs => rw [hv]
            rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
          rw [e1, e2] at h
          have e3' : t * (v ⬝ᵥ v) = t * (μ * (v ⬝ᵥ x₀) - v ⬝ᵥ (A *ᵥ x₀)) := by rw [e3]
          linarith [h, h0, e3']
      have := L_spec_self_eq_zero v hvv
      rw [hv, sub_eq_zero] at this
      exact this.symm
  open Matrix in
  have L_spec_max : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hm : 0 < m), ∃ μ : ℝ, (∀ x : Fin m → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ μ * (x ⬝ᵥ x)) ∧
        ∃ x₀ : Fin m → ℝ, x₀ ≠ 0 ∧ x₀ ⬝ᵥ (A *ᵥ x₀) = μ * (x₀ ⬝ᵥ x₀) :=
    fun {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hm : 0 < m) => by
      let S := {x : Fin m → ℝ | x ⬝ᵥ x = 1}
      have hcont1 : Continuous (fun x : Fin m → ℝ => x ⬝ᵥ x) := by
        simp only [dotProduct]; fun_prop
      have hcont2 : Continuous (fun x : Fin m → ℝ => x ⬝ᵥ (A *ᵥ x)) := by
        simp only [dotProduct, mulVec]; fun_prop
      have hclosed : IsClosed S := isClosed_eq hcont1 continuous_const
      have hsub : S ⊆ Metric.closedBall 0 1 := by
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
        intro i
        rw [Real.norm_eq_abs]
        have hx' : x ⬝ᵥ x = 1 := hx
        have hi : x i * x i ≤ x ⬝ᵥ x := by
          simp only [dotProduct]
          exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
            (Finset.mem_univ i)
        rw [hx'] at hi
        rw [abs_le]; constructor <;> nlinarith
      have hcpt : IsCompact S := (isCompact_closedBall 0 1).of_isClosed_subset hclosed hsub
      have hne : S.Nonempty := by
        refine ⟨Pi.single ⟨0, hm⟩ 1, ?_⟩
        show Pi.single _ 1 ⬝ᵥ Pi.single _ 1 = 1
        rw [dotProduct_single]
        simp
      obtain ⟨x₀, hx₀S, hmax⟩ := hcpt.exists_isMaxOn hne hcont2.continuousOn
      have hx₀1 : x₀ ⬝ᵥ x₀ = 1 := hx₀S
      refine ⟨x₀ ⬝ᵥ (A *ᵥ x₀), ?_, x₀, ?_, ?_⟩
      · intro y
        by_cases hy : y = 0
        · subst hy; simp
        · have hpos := L_spec_self_pos y hy
          set s := Real.sqrt (y ⬝ᵥ y) with hs
          have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
          have hss : s * s = y ⬝ᵥ y := Real.mul_self_sqrt hpos.le
          have hz : (s⁻¹ • y) ∈ S := by
            show (s⁻¹ • y) ⬝ᵥ (s⁻¹ • y) = 1
            rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
            field_simp
          have hle : (s⁻¹ • y) ⬝ᵥ (A *ᵥ (s⁻¹ • y)) ≤ x₀ ⬝ᵥ (A *ᵥ x₀) := hmax hz
          rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hle
          rw [← hss]
          have h2 : y ⬝ᵥ (A *ᵥ y) = (s * s) * (s⁻¹ * (s⁻¹ * y ⬝ᵥ (A *ᵥ y))) := by
            field_simp
          have hss0 : 0 ≤ s * s := (mul_pos hs0 hs0).le
          calc y ⬝ᵥ (A *ᵥ y) = (s * s) * (s⁻¹ * (s⁻¹ * y ⬝ᵥ (A *ᵥ y))) := h2
            _ ≤ (s * s) * (x₀ ⬝ᵥ (A *ᵥ x₀)) := mul_le_mul_of_nonneg_left hle hss0
            _ = x₀ ⬝ᵥ (A *ᵥ x₀) * (s * s) := by ring
      · intro h
        rw [h] at hx₀1
        simp at hx₀1
      · rw [hx₀1, mul_one]
  open Matrix in
  have L_spec : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (lam : ℝ) (hlam : 0 < lam), spectralRadius ℝ (H.adjMatrix ℝ) = ENNReal.ofReal lam ↔
        ((∀ x : Fin m → ℝ, x ⬝ᵥ (H.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) ∧
          ∃ x : Fin m → ℝ, x ≠ 0 ∧ H.adjMatrix ℝ *ᵥ x = lam • x) :=
    fun (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (lam : ℝ) (hlam : 0 < lam) => by
      set A := H.adjMatrix ℝ with hAdef
      have hS : Aᵀ = A := H.transpose_adjMatrix
      have hnn : ∀ i j, 0 ≤ A i j := by
        intro i j
        rw [hAdef, SimpleGraph.adjMatrix_apply]
        split_ifs <;> norm_num
      have hsr : ∀ μ : ℝ, 0 ≤ μ → (∀ x : Fin m → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ μ * (x ⬝ᵥ x)) →
          (∃ x : Fin m → ℝ, x ≠ 0 ∧ A *ᵥ x = μ • x) → spectralRadius ℝ A = ENNReal.ofReal μ := by
        rintro μ hμ hR ⟨x, hx, hxe⟩
        apply le_antisymm
        · apply iSup₂_le
          intro k hk
          obtain ⟨y, hy, hye⟩ := (L_spec_mem A k).mp hk
          have hk' := L_spec_eig_le A hnn μ hR k y hy hye
          rw [← enorm_eq_nnnorm, Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal hk'
        · apply le_iSup₂_of_le μ ((L_spec_mem A μ).mpr ⟨x, hx, hxe⟩)
          rw [← enorm_eq_nnnorm, Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self μ)
      constructor
      · intro h
        have hne : (spectrum ℝ A).Nonempty := by
          by_contra hc
          rw [Set.not_nonempty_iff_eq_empty] at hc
          have h0 : spectralRadius ℝ A = 0 := by simp [spectralRadius, hc]
          rw [h0] at h
          have hp := ENNReal.ofReal_pos.mpr hlam
          rw [← h] at hp
          exact lt_irrefl _ hp
        obtain ⟨r, hr⟩ := hne
        obtain ⟨y, hy, _⟩ := (L_spec_mem A r).mp hr
        have hm : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · exfalso
            apply hy
            funext i
            exfalso
            have := i.2
            omega
          · exact h0
        obtain ⟨μ, hR, x₀, hx₀, hx₀e⟩ := L_spec_max A hm
        have hev := L_spec_eigvec A hS μ hR x₀ hx₀e
        have hμ : 0 ≤ μ := le_trans (abs_nonneg μ) (L_spec_eig_le A hnn μ hR μ x₀ hx₀ hev)
        have h2 := hsr μ hμ hR ⟨x₀, hx₀, hev⟩
        rw [h2, ENNReal.ofReal_eq_ofReal_iff hμ hlam.le] at h
        subst h
        exact ⟨hR, x₀, hx₀, hev⟩
      · rintro ⟨hR, x, hx, hxe⟩
        exact hsr lam hlam.le hR ⟨x, hx, hxe⟩
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_psd_ker : ∀ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.transpose = B)
      (hpsd : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ (B *ᵥ y)) (x : Fin n → ℝ) (hx : x ⬝ᵥ (B *ᵥ x) = 0), B *ᵥ x = 0 :=
    fun {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.transpose = B)
        (hpsd : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ (B *ᵥ y)) (x : Fin n → ℝ) (hx : x ⬝ᵥ (B *ᵥ x) = 0) => by
      have hsymm : ∀ y : Fin n → ℝ, x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
        intro y
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB, dotProduct_comm]
      have hexp : ∀ t : ℝ, (x + t • (B *ᵥ x)) ⬝ᵥ (B *ᵥ (x + t • (B *ᵥ x))) =
          2 * t * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x)) + t ^ 2 * ((B *ᵥ x) ⬝ᵥ (B *ᵥ (B *ᵥ x))) := by
        intro t
        have h1 : x ⬝ᵥ (B *ᵥ (B *ᵥ x)) = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := hsymm (B *ᵥ x)
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
          dotProduct_smul, smul_dotProduct, smul_eq_mul]
        rw [hx, h1]
        ring
      have key : ∀ t : ℝ,
          0 ≤ 2 * t * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x)) + t ^ 2 * ((B *ᵥ x) ⬝ᵥ (B *ᵥ (B *ᵥ x))) := by
        intro t
        rw [← hexp t]
        exact hpsd _
      have hb : 0 ≤ (B *ᵥ x) ⬝ᵥ (B *ᵥ (B *ᵥ x)) := hpsd (B *ᵥ x)
      have ha0 : (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = 0 := by
        generalize (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = a at key ⊢
        generalize (B *ᵥ x) ⬝ᵥ (B *ᵥ (B *ᵥ x)) = b at key hb
        have hb1 : (0 : ℝ) < b + 1 := by linarith
        have h := key (-a / (b + 1))
        have e : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b
            = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
          field_simp
          ring
        rw [e, le_div_iff₀ (by positivity)] at h
        have h2 : a ^ 2 * (b + 2) ≤ 0 := by linarith
        have h3 : a ^ 2 ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos hc (show (0 : ℝ) < b + 2 by linarith)
          linarith
        have h4 : a ^ 2 = 0 := le_antisymm h3 (sq_nonneg a)
        exact (pow_eq_zero_iff two_ne_zero).mp h4
      funext i
      have hsum : ∑ j, (B *ᵥ x) j * (B *ᵥ x) j = 0 := ha0
      have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (B *ᵥ x) j * (B *ᵥ x) j :=
        fun j _ => mul_self_nonneg _
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
      have : (B *ᵥ x) i = 0 := mul_self_eq_zero.mp hi
      simpa using this
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_abs_dot_self : ∀ {n : ℕ} (x : Fin n → ℝ), (fun i => |x i|) ⬝ᵥ (fun i => |x i|) = x ⬝ᵥ x :=
    fun {n : ℕ} (x : Fin n → ℝ) => by
      simp only [dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact abs_mul_abs_self (x i)
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_abs_quad_le : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x : Fin n → ℝ), x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ (fun i => |x i|) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (fun i => |x i|)) :=
    fun (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (x : Fin n → ℝ) => by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
      rw [SimpleGraph.adjMatrix_apply]
      split_ifs with h
      · simp only [one_mul]
        calc x i * x j ≤ |x i * x j| := le_abs_self _
          _ = |x i| * |x j| := abs_mul _ _
      · simp
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_abs_mem : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x))
      (x : Fin n → ℝ) (hx : G.adjMatrix ℝ *ᵥ x = lam • x), G.adjMatrix ℝ *ᵥ (fun i => |x i|) = lam • (fun i => |x i|) :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x))
        (x : Fin n → ℝ) (hx : G.adjMatrix ℝ *ᵥ x = lam • x) => by
      set y : Fin n → ℝ := fun i => |x i| with hy
      set A := G.adjMatrix ℝ with hAdef
      set B : Matrix (Fin n) (Fin n) ℝ := lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A with hBdef
      have hBv : ∀ v : Fin n → ℝ, B *ᵥ v = lam • v - A *ᵥ v := by
        intro v
        rw [hBdef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      have hBq : ∀ v : Fin n → ℝ, v ⬝ᵥ (B *ᵥ v) = lam * (v ⬝ᵥ v) - v ⬝ᵥ (A *ᵥ v) := by
        intro v
        rw [hBv, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      have hBT : B.transpose = B := by
        rw [hBdef, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hAdef,
          SimpleGraph.transpose_adjMatrix]
      have hpsd : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (B *ᵥ v) := by
        intro v
        rw [hBq]
        have := hA v
        linarith
      have hxx : x ⬝ᵥ (A *ᵥ x) = lam * (x ⬝ᵥ x) := by
        rw [hx, dotProduct_smul, smul_eq_mul]
      have hyy : y ⬝ᵥ y = x ⬝ᵥ x := L_case1_abs_dot_self x
      have hle : x ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ (A *ᵥ y) := L_case1_abs_quad_le n G x
      have hz : y ⬝ᵥ (B *ᵥ y) = 0 := by
        have h1 := hpsd y
        have h2 := hA y
        rw [hBq]
        rw [hBq] at h1
        rw [hyy] at h1 h2 ⊢
        linarith
      have hker := L_case1_psd_ker B hBT hpsd y hz
      rw [hBv, sub_eq_zero] at hker
      exact hker.symm
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_hyperplane : ∀ {n : ℕ} (K : Submodule ℝ (Fin n → ℝ)) (v : Fin n → ℝ) (hv : v ∈ K)
      (hs : ∑ i, v i ≠ 0), Module.finrank ℝ ↥(K ⊓ LinearMap.ker (Matrix.toLin'
        (Matrix.of (fun (_ : Fin n) (_ : Fin n) => (1 : ℝ))))) + 1 = Module.finrank ℝ K :=
    fun {n : ℕ} (K : Submodule ℝ (Fin n → ℝ)) (v : Fin n → ℝ) (hv : v ∈ K)
        (hs : ∑ i, v i ≠ 0) => by
      classical
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h
          exact absurd (by simp) hs
        · exact h
      set φ : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i with hφ
      have hφapp : ∀ x : Fin n → ℝ, φ x = ∑ i, x i := by
        intro x
        simp [hφ]
      have hker : LinearMap.ker (Matrix.toLin'
          (Matrix.of (fun (_ : Fin n) (_ : Fin n) => (1 : ℝ)))) = LinearMap.ker φ := by
        ext x
        simp only [LinearMap.mem_ker, Matrix.toLin'_apply, hφapp]
        constructor
        · intro h
          have := congrFun h ⟨0, hn⟩
          simpa [Matrix.mulVec, dotProduct] using this
        · intro h
          funext i
          simp [Matrix.mulVec, dotProduct, h]
      rw [hker]
      have hsv : φ v ≠ 0 := by rw [hφapp]; exact hs
      have hsurj : Function.Surjective φ := by
        intro c
        refine ⟨(c / φ v) • v, ?_⟩
        rw [LinearMap.map_smul, smul_eq_mul]
        field_simp
      have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
      have hrn := LinearMap.finrank_range_add_finrank_ker φ
      rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hrn
      have hsup : K ⊔ LinearMap.ker φ = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : x = (φ x / φ v) • v + (x - (φ x / φ v) • v) := by abel
        rw [hx]
        refine Submodule.add_mem_sup (K.smul_mem _ hv) ?_
        rw [LinearMap.mem_ker, map_sub, LinearMap.map_smul, smul_eq_mul]
        field_simp
        ring
      have hfi := Submodule.finrank_sup_add_finrank_inf_eq K (LinearMap.ker φ)
      rw [hsup, finrank_top, Module.finrank_fin_fun] at hfi
      omega
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_order_le : ∀ (lam : ℝ) (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
      (hH : spectralRadius ℝ (H.adjMatrix ℝ) = ENNReal.ofReal lam), spectralRadiusOrder lam < ⊤ ∧ (spectralRadiusOrder lam).toNat ≤ m :=
    fun (lam : ℝ) (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
        (hH : spectralRadius ℝ (H.adjMatrix ℝ) = ENNReal.ofReal lam) => by
      have hle : spectralRadiusOrder lam ≤ (m : ℕ∞) := by
        unfold spectralRadiusOrder
        refine iInf₂_le m ?_
        refine ⟨H, ?_⟩
        convert hH using 3
      refine ⟨lt_of_le_of_lt hle (ENat.coe_lt_top m), ?_⟩
      exact ENat.toNat_le_of_le_coe hle
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_eig_sum : ∀ (n : ℕ) (S : Finset (Fin n)) (g : Fin n → ℝ)
      (hg : ∀ i, i ∉ S → g i = 0), ∑ i, g i = ∑ a : Fin S.card, g ((S.equivFin.symm a).1) :=
    fun (n : ℕ) (S : Finset (Fin n)) (g : Fin n → ℝ)
        (hg : ∀ i, i ∉ S → g i = 0) => by
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hg i hi)]
      rw [← Finset.sum_coe_sort S g]
      exact (Equiv.sum_comp S.equivFin.symm (fun i : S => g i.1)).symm
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_eigen_order : ∀ (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj]
      (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x))
      (S : Finset (Fin n)) (x : Fin n → ℝ) (hx0 : x ≠ 0) (hxS : ∀ i, i ∉ S → x i = 0)
      (hx : G.adjMatrix ℝ *ᵥ x = lam • x), spectralRadiusOrder lam < ⊤ ∧ (spectralRadiusOrder lam).toNat ≤ S.card :=
    fun (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (G : SimpleGraph (Fin n))
        [DecidableRel G.Adj]
        (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x))
        (S : Finset (Fin n)) (x : Fin n → ℝ) (hx0 : x ≠ 0) (hxS : ∀ i, i ∉ S → x i = 0)
        (hx : G.adjMatrix ℝ *ᵥ x = lam • x) => by
      classical
      set e : Fin S.card ≃ S := S.equivFin.symm with he
      set f : Fin S.card → Fin n := fun a => (e a).1 with hf
      have hsum : ∀ g : Fin n → ℝ, (∀ i, i ∉ S → g i = 0) → ∑ i, g i = ∑ a, g (f a) :=
        fun g hg => L_case1_eig_sum n S g hg
      have hfe : ∀ i (hi : i ∈ S), f (e.symm ⟨i, hi⟩) = i := by
        intro i hi
        simp only [hf, Equiv.apply_symm_apply]
      let H : SimpleGraph (Fin S.card) := G.comap f
      have hHA : ∀ a b, H.adjMatrix ℝ a b = G.adjMatrix ℝ (f a) (f b) := by
        intro a b
        rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
        by_cases h : G.Adj (f a) (f b)
        · have h' : H.Adj a b := h
          rw [if_pos h, if_pos h']
        · have h' : ¬ H.Adj a b := h
          rw [if_neg h, if_neg h']
      refine L_case1_order_le lam S.card H ((L_spec S.card H lam hlam).mpr ⟨?_, ?_⟩)
      · intro y
        let yt : Fin n → ℝ := fun i => if h : i ∈ S then y (e.symm ⟨i, h⟩) else 0
        have hyt0 : ∀ i, i ∉ S → yt i = 0 := by
          intro i hi
          show (if h : i ∈ S then y (e.symm ⟨i, h⟩) else 0) = 0
          rw [dif_neg hi]
        have hytf : ∀ a, yt (f a) = y a := by
          intro a
          show (if h : f a ∈ S then y (e.symm ⟨f a, h⟩) else 0) = y a
          rw [dif_pos (e a).2]
          simp only [hf, Subtype.coe_eta, Equiv.symm_apply_apply]
        have h1 := hA yt
        have h2 : yt ⬝ᵥ yt = y ⬝ᵥ y := by
          simp only [dotProduct]
          have h := hsum (fun i => yt i * yt i) (fun i hi => by beta_reduce; rw [hyt0 i hi, zero_mul])
          simp only at h
          rw [h]
          simp only [hytf]
        have h3 : yt ⬝ᵥ (G.adjMatrix ℝ *ᵥ yt) = y ⬝ᵥ (H.adjMatrix ℝ *ᵥ y) := by
          simp only [dotProduct, Matrix.mulVec]
          have h := hsum (fun i => yt i * ∑ j, G.adjMatrix ℝ i j * yt j)
            (fun i hi => by beta_reduce; rw [hyt0 i hi, zero_mul])
          simp only at h
          rw [h]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          have h' := hsum (fun j => G.adjMatrix ℝ (f a) j * yt j)
            (fun j hj => by beta_reduce; rw [hyt0 j hj, mul_zero])
          simp only at h'
          rw [h', hytf]
          refine congrArg (fun t => y a * t) (Finset.sum_congr rfl (fun b _ => ?_))
          rw [hytf, hHA]
        rw [← h2, ← h3]
        exact h1
      · refine ⟨fun a => x (f a), ?_, ?_⟩
        · intro h0
          apply hx0
          funext i
          by_cases hi : i ∈ S
          · have h1 := congrFun h0 (e.symm ⟨i, hi⟩)
            simp only [Pi.zero_apply] at h1
            rw [hfe i hi] at h1
            exact h1
          · exact hxS i hi
        · funext a
          have h1 := congrFun hx (f a)
          simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1 ⊢
          rw [← h1]
          have h2 := hsum (fun j => G.adjMatrix ℝ (f a) j * x j)
            (fun j hj => by beta_reduce; rw [hxS j hj, mul_zero])
          simp only at h2
          rw [h2]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [hHA]
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_closed : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x : Fin n → ℝ) (hnn : ∀ i, 0 ≤ x i) (hx : G.adjMatrix ℝ *ᵥ x = lam • x)
      (u v : Fin n) (hu : x u ≠ 0) (hv : x v = 0), ¬ G.Adj v u :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (x : Fin n → ℝ) (hnn : ∀ i, 0 ≤ x i) (hx : G.adjMatrix ℝ *ᵥ x = lam • x)
        (u v : Fin n) (hu : x u ≠ 0) (hv : x v = 0) => by
      intro hadj
      have h1 := congrFun hx v
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hv, mul_zero] at h1
      have hnn' : ∀ w ∈ (Finset.univ : Finset (Fin n)), 0 ≤ G.adjMatrix ℝ v w * x w := by
        intro w _
        rw [SimpleGraph.adjMatrix_apply]
        split_ifs
        · rw [one_mul]; exact hnn w
        · rw [zero_mul]
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn').mp h1 u (Finset.mem_univ u)
      rw [SimpleGraph.adjMatrix_apply, if_pos hadj, one_mul] at h2
      exact hu h2
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_restrict_mem : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (S : Finset (Fin n)) (hcl : ∀ u ∈ S, ∀ v ∉ S, ¬ G.Adj v u)
      (y : Fin n → ℝ) (hy : G.adjMatrix ℝ *ᵥ y = lam • y), G.adjMatrix ℝ *ᵥ (fun i => if i ∈ S then y i else 0) =
        lam • (fun i => if i ∈ S then y i else 0) :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (S : Finset (Fin n)) (hcl : ∀ u ∈ S, ∀ v ∉ S, ¬ G.Adj v u)
        (y : Fin n → ℝ) (hy : G.adjMatrix ℝ *ᵥ y = lam • y) => by
      funext v
      have h1 := congrFun hy v
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      by_cases hvS : v ∈ S
      · rw [if_pos hvS, ← h1]
        apply Finset.sum_congr rfl
        intro w _
        by_cases hwS : w ∈ S
        · rw [if_pos hwS]
        · rw [if_neg hwS, SimpleGraph.adjMatrix_apply,
            if_neg (fun h => hcl v hvS w hwS (G.symm h)), zero_mul, zero_mul]
      · rw [if_neg hvS, mul_zero]
        apply Finset.sum_eq_zero
        intro w _
        by_cases hwS : w ∈ S
        · rw [if_pos hwS, SimpleGraph.adjMatrix_apply, if_neg (hcl w hwS v hvS), zero_mul]
        · rw [if_neg hwS, mul_zero]
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_min_support : ∀ {n : ℕ} (W : Submodule ℝ (Fin n → ℝ))
      (hW : Module.finrank ℝ W ≠ 0), ∃ x ∈ W, x ≠ 0 ∧ ∀ y ∈ W, y ≠ 0 →
        (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ (Finset.univ.filter (fun i => y i ≠ 0)).card :=
    fun {n : ℕ} (W : Submodule ℝ (Fin n → ℝ))
        (hW : Module.finrank ℝ W ≠ 0) => by
      classical
      have hne : W ≠ ⊥ := by
        intro h
        apply hW
        rw [h]
        simp
      obtain ⟨y0, hy0W, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hex : ∃ c : ℕ, ∃ y ∈ W, y ≠ 0 ∧ (Finset.univ.filter (fun i => y i ≠ 0)).card = c :=
        ⟨_, y0, hy0W, hy0, rfl⟩
      obtain ⟨x, hxW, hx0, hxc⟩ := Nat.find_spec hex
      refine ⟨x, hxW, hx0, ?_⟩
      intro y hyW hy0'
      rw [hxc]
      exact Nat.find_min' hex ⟨y, hyW, hy0', rfl⟩
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_dim_drop : ∀ {n : ℕ} (W W' : Submodule ℝ (Fin n → ℝ)) (i : Fin n)
      (h : ∀ y ∈ W, y i = 0 → y ∈ W'), Module.finrank ℝ W ≤ Module.finrank ℝ W' + 1 :=
    fun {n : ℕ} (W W' : Submodule ℝ (Fin n → ℝ)) (i : Fin n)
        (h : ∀ y ∈ W, y i = 0 → y ∈ W') => by
      classical
      have hle : W ⊓ LinearMap.ker (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) ≤ W' := by
        intro y hy
        rw [Submodule.mem_inf] at hy
        exact h y hy.1 (by simpa using hy.2)
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W
        (LinearMap.ker (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ))
      have h2 : Module.finrank ℝ ↥(W ⊔ LinearMap.ker (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)) ≤ n := by
        have := Submodule.finrank_le (W ⊔ LinearMap.ker (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ))
        simpa using this
      have h3 := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)
      have h4 : Module.finrank ℝ (LinearMap.range (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)) ≤ 1 := by
        have := Submodule.finrank_le (LinearMap.range (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ))
        simpa using this
      have h5 : Module.finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
      rw [h5] at h3
      have h6 := Submodule.finrank_mono hle
      omega
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_mem_ker_iff : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x : Fin n → ℝ), x ∈ LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ)) ↔
        G.adjMatrix ℝ *ᵥ x = lam • x :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (x : Fin n → ℝ) => by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_eq_zero, eq_comm]
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_mem_supp : ∀ {n : ℕ} (T : Finset (Fin n)) (x : Fin n → ℝ), x ∈ LinearMap.ker (Matrix.toLin' (Matrix.diagonal (fun i => if i ∈ T then (0 : ℝ) else 1)))
        ↔ ∀ i, i ∉ T → x i = 0 :=
    fun {n : ℕ} (T : Finset (Fin n)) (x : Fin n → ℝ) => by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      constructor
      · intro h i hi
        have := congrFun h i
        simpa [Matrix.mulVec_diagonal, hi] using this
      · intro h
        funext i
        rw [Matrix.mulVec_diagonal]
        by_cases hi : i ∈ T
        · simp [hi]
        · simp [hi, h i hi]
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_count_T : ∀ (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj]
      (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) (T : Finset (Fin n)), Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin'
        (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ)) ⊓
        LinearMap.ker (Matrix.toLin' (Matrix.diagonal (fun i => if i ∈ T then (0 : ℝ) else 1)))) = 0 ∨
      (spectralRadiusOrder lam < ⊤ ∧
        (spectralRadiusOrder lam).toNat * Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin'
        (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ)) ⊓
        LinearMap.ker (Matrix.toLin' (Matrix.diagonal (fun i => if i ∈ T then (0 : ℝ) else 1))))
          ≤ T.card) :=
    fun (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (G : SimpleGraph (Fin n))
        [DecidableRel G.Adj]
        (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) (T : Finset (Fin n)) => by
      induction T using Finset.strongInduction with
      | H T ih =>
      set K := LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ))
        with hK
      by_cases hW : Module.finrank ℝ ↥(K ⊓ LinearMap.ker (Matrix.toLin'
          (Matrix.diagonal (fun i => if i ∈ T then (0 : ℝ) else 1)))) = 0
      · exact Or.inl hW
      right
      obtain ⟨x0, hx0W, hx0ne, hmin⟩ := L_case1_min_support _ hW
      have hx0K : x0 ∈ K := (Submodule.mem_inf.mp hx0W).1
      have hx0T : ∀ i, i ∉ T → x0 i = 0 := (L_case1_mem_supp T x0).mp (Submodule.mem_inf.mp hx0W).2
      have hx0e : G.adjMatrix ℝ *ᵥ x0 = lam • x0 := (L_case1_mem_ker_iff lam n G x0).mp hx0K
      have hxe := L_case1_abs_mem lam n G hA x0 hx0e
      set S := Finset.univ.filter (fun i => x0 i ≠ 0) with hS
      have hmemS : ∀ i, i ∈ S ↔ x0 i ≠ 0 := fun i => by simp [hS]
      have hST : S ⊆ T := by
        intro i hi
        by_contra hiT
        exact (hmemS i).mp hi (hx0T i hiT)
      obtain ⟨i0, hi0⟩ : ∃ i, x0 i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hx0ne (funext hcon)
      have hi0S : i0 ∈ S := (hmemS i0).mpr hi0
      have hcl : ∀ u ∈ S, ∀ v ∉ S, ¬ G.Adj v u := by
        intro u hu v hv
        refine L_case1_closed lam n G (fun i => |x0 i|) (fun i => abs_nonneg _) hxe u v ?_ ?_
        · exact abs_ne_zero.mpr ((hmemS u).mp hu)
        · have : x0 v = 0 := by
            by_contra h
            exact hv ((hmemS v).mpr h)
          simp [this]
      have hxne : (fun i => |x0 i|) ≠ 0 := by
        intro h
        have := congrFun h i0
        simp only [Pi.zero_apply, abs_eq_zero] at this
        exact hi0 this
      have hxS : ∀ i, i ∉ S → (fun i => |x0 i|) i = 0 := by
        intro i hi
        have : x0 i = 0 := by
          by_contra h
          exact hi ((hmemS i).mpr h)
        simp [this]
      obtain ⟨hlt, hkS⟩ := L_case1_eigen_order lam hlam n G hA S _ hxne hxS hxe
      have hdrop := L_case1_dim_drop (K ⊓ LinearMap.ker (Matrix.toLin'
          (Matrix.diagonal (fun i => if i ∈ T then (0 : ℝ) else 1))))
        (K ⊓ LinearMap.ker (Matrix.toLin'
          (Matrix.diagonal (fun i => if i ∈ T \\ S then (0 : ℝ) else 1)))) i0 (by
        intro y hyW hyi
        have hyK : y ∈ K := (Submodule.mem_inf.mp hyW).1
        have hyT : ∀ i, i ∉ T → y i = 0 := (L_case1_mem_supp T y).mp (Submodule.mem_inf.mp hyW).2
        have hye : G.adjMatrix ℝ *ᵥ y = lam • y := (L_case1_mem_ker_iff lam n G y).mp hyK
        have hy'e := L_case1_restrict_mem lam n G S hcl y hye
        have hy'W : (fun i => if i ∈ S then y i else 0) ∈ K ⊓ LinearMap.ker (Matrix.toLin'
            (Matrix.diagonal (fun i => if i ∈ T then (0 : ℝ) else 1))) := by
          refine Submodule.mem_inf.mpr ⟨(L_case1_mem_ker_iff lam n G _).mpr hy'e, ?_⟩
          refine (L_case1_mem_supp T _).mpr ?_
          intro i hi
          have : i ∉ S := fun h => hi (hST h)
          simp [this]
        have hy'0 : (fun i => if i ∈ S then y i else 0) = 0 := by
          by_contra hne
          have h1 := hmin _ hy'W hne
          have h2 : (Finset.univ.filter (fun i => (if i ∈ S then y i else 0) ≠ 0)) ⊆
              S.erase i0 := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            by_cases hiS : i ∈ S
            · refine Finset.mem_erase.mpr ⟨?_, hiS⟩
              rintro rfl
              simp [hiS, hyi] at hi
            · simp [hiS] at hi
          have h3 := Finset.card_le_card h2
          rw [Finset.card_erase_of_mem hi0S] at h3
          have h4 : 0 < S.card := Finset.card_pos.mpr ⟨i0, hi0S⟩
          omega
        refine Submodule.mem_inf.mpr ⟨hyK, (L_case1_mem_supp (T \\ S) y).mpr ?_⟩
        intro i hi
        by_cases hiS : i ∈ S
        · have := congrFun hy'0 i
          simpa [hiS] using this
        · have hiT : i ∉ T := by
            intro h
            exact hi (Finset.mem_sdiff.mpr ⟨h, hiS⟩)
          exact hyT i hiT)
      have hss : T \\ S ⊂ T := Finset.sdiff_ssubset hST ⟨i0, hi0S⟩
      have hcard := Finset.card_sdiff_add_card_eq_card hST
      refine ⟨hlt, ?_⟩
      rcases ih (T \\ S) hss with h0 | ⟨_, hle⟩
      · rw [h0] at hdrop
        have hST' := Finset.card_le_card hST
        calc (spectralRadiusOrder lam).toNat * _ ≤ (spectralRadiusOrder lam).toNat * 1 :=
              Nat.mul_le_mul_left _ hdrop
          _ ≤ T.card := by omega
      · calc (spectralRadiusOrder lam).toNat * _ ≤ (spectralRadiusOrder lam).toNat * (_ + 1) :=
              Nat.mul_le_mul_left _ hdrop
          _ ≤ T.card := by rw [Nat.mul_add, Nat.mul_one]; omega
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_J_mulVec : ∀ {n : ℕ} (x : Fin n → ℝ), Matrix.of (fun (_ : Fin n) (_ : Fin n) => (1 : ℝ)) *ᵥ x = fun _ => ∑ j, x j :=
    fun {n : ℕ} (x : Fin n → ℝ) => by
      funext i
      simp [Matrix.mulVec, dotProduct]
  open Matrix EquiangularLinesFixedAngle in
  have L_case1_ker_eq : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x)), LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin n) (Fin n) ℝ)
          - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)))) =
      LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ)) ⊓
        LinearMap.ker (Matrix.toLin' (Matrix.of (fun (_ : Fin n) (_ : Fin n) => (1 : ℝ)))) :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) => by
      ext x
      simp only [Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply]
      have hBsym : (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ).transpose =
          lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ := by
        rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
          SimpleGraph.transpose_adjMatrix]
      have hBpsd : ∀ y : Fin n → ℝ,
          0 ≤ y ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ y) := by
        intro y
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
          dotProduct_smul, smul_eq_mul]
        linarith [hA y]
      constructor
      · intro h
        rw [Matrix.add_mulVec, Matrix.smul_mulVec] at h
        have h1 : x ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ x) +
            (1 / 2 : ℝ) * ((∑ j, x j) * (∑ j, x j)) = 0 := by
          have := congrArg (fun v => x ⬝ᵥ v) h
          simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
            L_case1_J_mulVec] at this
          have hs : x ⬝ᵥ (fun _ => ∑ j, x j) = (∑ j, x j) * (∑ j, x j) := by
            simp only [dotProduct, Finset.sum_mul]
          rw [hs] at this
          exact this
        have h2 := hBpsd x
        have h3 : 0 ≤ (∑ j, x j) * (∑ j, x j) := mul_self_nonneg _
        have h4 : x ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ x) = 0 := by
          linarith
        have h5 : (∑ j, x j) = 0 := by
          have : (∑ j, x j) * (∑ j, x j) = 0 := by linarith
          exact mul_self_eq_zero.mp this
        refine ⟨L_case1_psd_ker _ hBsym hBpsd x h4, ?_⟩
        rw [L_case1_J_mulVec, h5]
        rfl
      · rintro ⟨h1, h2⟩
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, h1, h2, smul_zero, add_zero]
  open Matrix EquiangularLinesFixedAngle in
  have L_case1 : ∀ (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x)), Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin n) (Fin n) ℝ)
          - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))))) = 0 ∨
      (spectralRadiusOrder lam < ⊤ ∧
        (spectralRadiusOrder lam).toNat * (Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
            + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))))) + 1) ≤ n) :=
    fun (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (hA : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x)) => by
      rw [L_case1_ker_eq lam n G hA]
      set K := LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ))
        with hK
      have hKT : K ⊓ LinearMap.ker (Matrix.toLin' (Matrix.diagonal
          (fun i => if i ∈ (Finset.univ : Finset (Fin n)) then (0 : ℝ) else 1))) = K := by
        have : Matrix.diagonal (fun i => if i ∈ (Finset.univ : Finset (Fin n)) then (0 : ℝ) else 1)
            = 0 := by
          ext i j
          simp [Matrix.diagonal]
        rw [this, map_zero, LinearMap.ker_zero, inf_top_eq]
      have hcount := L_case1_count_T lam hlam n G hA Finset.univ
      rw [hKT, Finset.card_univ, Fintype.card_fin] at hcount
      by_cases hj : Module.finrank ℝ K = 0
      · left
        have hle := Submodule.finrank_mono (inf_le_left :
          K ⊓ LinearMap.ker (Matrix.toLin' (Matrix.of (fun (_ : Fin n) (_ : Fin n) => (1 : ℝ)))) ≤ K)
        omega
      · right
        rcases hcount with h0 | ⟨hlt, hle⟩
        · exact absurd h0 hj
        refine ⟨hlt, ?_⟩
        have hKbot : K ≠ ⊥ := by
          intro h
          apply hj
          rw [h]
          exact finrank_bot ℝ (Fin n → ℝ)
        obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKbot
        have hxe : G.adjMatrix ℝ *ᵥ x = lam • x := (L_case1_mem_ker_iff lam n G x).mp hxK
        have habs := L_case1_abs_mem lam n G hA x hxe
        have habsK : (fun i => |x i|) ∈ K := (L_case1_mem_ker_iff lam n G _).mpr habs
        have hsum : ∑ i, |x i| ≠ 0 := by
          intro hs
          apply hx0
          funext i
          have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (x j))).mp hs i
            (Finset.mem_univ i)
          simpa using h
        have hh := L_case1_hyperplane K (fun i => |x i|) habsK hsum
        rw [hh]
        exact hle
  open Matrix in
  have L_mult_net_geo : ∀ {V : Type} (G : SimpleGraph V) (v₀ : V) (δ : V → ℕ)
      (h1 : ∀ v, ∃ p : G.Walk v₀ v, p.length = δ v)
      (h2 : ∀ v (p : G.Walk v₀ v), δ v ≤ p.length), ∀ (n : ℕ) (v : V), δ v = n → ∀ j ≤ n, ∃ w, δ w = j ∧
        ∃ q : G.Walk w v, q.length = n - j :=
    fun {V : Type} (G : SimpleGraph V) (v₀ : V) (δ : V → ℕ)
        (h1 : ∀ v, ∃ p : G.Walk v₀ v, p.length = δ v)
        (h2 : ∀ v (p : G.Walk v₀ v), δ v ≤ p.length) => by
      intro n
      induction n with
      | zero =>
        intro v hv j hj
        exact ⟨v, by omega, SimpleGraph.Walk.nil, by simp⟩
      | succ n ih =>
        intro v hv j hj
        rcases Nat.lt_or_ge n j with h | h
        · exact ⟨v, by omega, SimpleGraph.Walk.nil, by simp; omega⟩
        · obtain ⟨p, hp⟩ := h1 v
          have hp' : p.reverse.length = n + 1 := by simp [hp, hv]
          generalize p.reverse = p' at hp'
          cases p' with
          | nil => simp at hp'
          | @cons _ x _ hadj q =>
            simp only [SimpleGraph.Walk.length_cons] at hp'
            have e1 : δ x ≤ n := by
              have := h2 x q.reverse
              simp only [SimpleGraph.Walk.length_reverse] at this
              omega
            have e2 : δ v ≤ δ x + 1 := by
              obtain ⟨px, hpx⟩ := h1 x
              have := h2 v (px.concat hadj.symm)
              simp only [SimpleGraph.Walk.length_concat] at this
              omega
            have hx : δ x = n := by omega
            obtain ⟨w, hw, q', hq'⟩ := ih x hx j h
            exact ⟨w, hw, q'.concat hadj.symm, by simp only [SimpleGraph.Walk.length_concat]; omega⟩
  open Matrix in
  have L_mult_net : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (hconn : G.Connected) (r : ℕ), ∃ N : Finset V, (N.card : ℝ) ≤ Fintype.card V / ((r : ℝ) + 1) + 1 ∧
        ∀ v, ∃ u ∈ N, ∃ p : G.Walk u v, p.length ≤ r :=
    fun {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (hconn : G.Connected) (r : ℕ) => by
      classical
      obtain ⟨v₀⟩ := hconn.nonempty
      have hex : ∀ v, ∃ k, ∃ p : G.Walk v₀ v, p.length = k := by
        intro v
        obtain ⟨p⟩ := hconn.preconnected v₀ v
        exact ⟨_, p, rfl⟩
      obtain ⟨δ, hδ1, hδ2⟩ : ∃ δ : V → ℕ, (∀ v, ∃ p : G.Walk v₀ v, p.length = δ v) ∧
          (∀ v (p : G.Walk v₀ v), δ v ≤ p.length) :=
        ⟨fun v => Nat.find (hex v), fun v => Nat.find_spec (hex v),
          fun v p => Nat.find_min' (hex v) ⟨p, rfl⟩⟩
      have hpos : (0:ℝ) < (r:ℝ) + 1 := by positivity
      have hsum : ∑ c ∈ Finset.range (r+1),
          ((Finset.univ.filter (fun v => δ v % (r+1) = c)).card : ℝ) = Fintype.card V := by
        rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise
          (fun v _ => Finset.mem_range.mpr (Nat.mod_lt (δ v) (Nat.succ_pos r)))]
        simp
      obtain ⟨c, hc, hcard⟩ : ∃ c ∈ Finset.range (r+1),
          ((Finset.univ.filter (fun v => δ v % (r+1) = c)).card : ℝ) ≤ Fintype.card V / ((r:ℝ)+1) := by
        by_contra hne
        push_neg at hne
        have := Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ hne
        rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
        push_cast at this
        rw [mul_div_cancel₀ _ (ne_of_gt hpos)] at this
        exact lt_irrefl _ this
      have hcr : c < r + 1 := Finset.mem_range.mp hc
      refine ⟨insert v₀ (Finset.univ.filter (fun v => δ v % (r+1) = c)), ?_, ?_⟩
      · have h1 := Finset.card_insert_le v₀ (Finset.univ.filter (fun v => δ v % (r+1) = c))
        have h2 : ((insert v₀ (Finset.univ.filter (fun v => δ v % (r+1) = c))).card : ℝ) ≤
            ((Finset.univ.filter (fun v => δ v % (r+1) = c)).card : ℝ) + 1 := by
          exact_mod_cast h1
        linarith
      · intro v
        by_cases hkc : c ≤ δ v
        · obtain ⟨w, hw, q, hq⟩ := L_mult_net_geo G v₀ δ hδ1 hδ2 (δ v) v rfl
            (δ v - ((δ v - c) % (r+1))) (Nat.sub_le _ _)
          refine ⟨w, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩), q, ?_⟩
          · rw [hw]
            have hm := Nat.mod_add_div (δ v - c) (r+1)
            have e : δ v - (δ v - c) % (r + 1) = c + (r+1) * ((δ v - c) / (r+1)) := by
              generalize (r+1) * ((δ v - c) / (r+1)) = t at hm ⊢
              generalize (δ v - c) % (r + 1) = m at hm ⊢
              omega
            rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcr]
          · rw [hq]
            have := Nat.mod_lt (δ v - c) (Nat.succ_pos r)
            generalize (δ v - c) % (r + 1) = m at this ⊢
            omega
        · obtain ⟨p, hp⟩ := hδ1 v
          exact ⟨v₀, Finset.mem_insert_self _ _, p, by omega⟩
  open Matrix in
  have L_mult_ball_last : ∀ {V : Type} {G : SimpleGraph V} {u v : V} (R : ℕ), ∀ (q : G.Walk u v), q.length = R + 1 → ∃ w, G.Adj u w ∧ ∃ q' : G.Walk w v, q'.length = R :=
    fun {V : Type} {G : SimpleGraph V} {u v : V} (R : ℕ) => by
      intro q
      cases q with
      | nil => intro hq; simp only [SimpleGraph.Walk.length_nil] at hq; omega
      | cons h q' => intro hq; simp only [SimpleGraph.Walk.length_cons] at hq; exact ⟨_, h, q', by omega⟩
  open Matrix in
  have L_mult_ball_aux : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (Δ : ℕ) (hdeg : ∀ v, (Finset.univ.filter (G.Adj v)).card ≤ Δ) (v : V) (R : ℕ), ∀ (B : Finset V), (∀ u ∈ B, ∃ p : G.Walk v u, p.length ≤ R) → B.card ≤ (Δ + 1) ^ R :=
    fun {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (Δ : ℕ) (hdeg : ∀ v, (Finset.univ.filter (G.Adj v)).card ≤ Δ) (v : V) (R : ℕ) => by
      classical
      induction R with
      | zero =>
        intro B hB
        have hsub : B ⊆ {v} := by
          intro u hu
          obtain ⟨p, hp⟩ := hB u hu
          have h0 : p.length = 0 := by omega
          have := SimpleGraph.Walk.eq_of_length_eq_zero h0
          simp [this]
        calc B.card ≤ ({v} : Finset V).card := Finset.card_le_card hsub
          _ = (Δ + 1) ^ 0 := by simp
      | succ R ih =>
        intro B hB
        have hSc : (Finset.univ.filter (fun u => ∃ p : G.Walk v u, p.length ≤ R)).card ≤ (Δ + 1) ^ R :=
          ih _ (by
            intro u hu
            simpa using hu)
        have hsub : B ⊆ (Finset.univ.filter (fun u => ∃ p : G.Walk v u, p.length ≤ R)) ∪
            (Finset.univ.filter (fun u => ∃ p : G.Walk v u, p.length ≤ R)).biUnion
              (fun w => Finset.univ.filter (G.Adj w)) := by
          intro u hu
          obtain ⟨p, hp⟩ := hB u hu
          by_cases hle : p.length ≤ R
          · apply Finset.mem_union_left
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨p, hle⟩
          · have hlen : p.reverse.length = R + 1 := by
              rw [SimpleGraph.Walk.length_reverse]; omega
            obtain ⟨w, huw, q', hq'⟩ := L_mult_ball_last R p.reverse hlen
            apply Finset.mem_union_right
            rw [Finset.mem_biUnion]
            refine ⟨w, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨q'.reverse, by rw [SimpleGraph.Walk.length_reverse]; omega⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact huw.symm
        set S := Finset.univ.filter (fun u => ∃ p : G.Walk v u, p.length ≤ R) with hS
        calc B.card ≤ (S ∪ S.biUnion (fun w => Finset.univ.filter (G.Adj w))).card :=
              Finset.card_le_card hsub
          _ ≤ S.card + (S.biUnion (fun w => Finset.univ.filter (G.Adj w))).card :=
              Finset.card_union_le _ _
          _ ≤ S.card + S.card * Δ := by
            have h1 : (S.biUnion (fun w => Finset.univ.filter (G.Adj w))).card ≤
                ∑ w ∈ S, (Finset.univ.filter (G.Adj w)).card := Finset.card_biUnion_le
            have h2 : ∑ w ∈ S, (Finset.univ.filter (G.Adj w)).card ≤ ∑ w ∈ S, Δ :=
              Finset.sum_le_sum (fun w _ => by convert hdeg w)
            have h3 : ∑ w ∈ S, Δ = S.card * Δ := by simp
            omega
          _ = S.card * (Δ + 1) := by ring
          _ ≤ (Δ + 1) ^ R * (Δ + 1) := Nat.mul_le_mul_right _ hSc
          _ = (Δ + 1) ^ (R + 1) := by ring
  open Matrix in
  have L_mult_ball : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (Δ : ℕ) (hdeg : ∀ v, (Finset.univ.filter (G.Adj v)).card ≤ Δ) (v : V) (R : ℕ)
      (B : Finset V) (hB : ∀ u ∈ B, ∃ p : G.Walk v u, p.length ≤ R), (B.card : ℝ) ≤ ((Δ : ℝ) + 1) ^ R :=
    fun {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (Δ : ℕ) (hdeg : ∀ v, (Finset.univ.filter (G.Adj v)).card ≤ Δ) (v : V) (R : ℕ)
        (B : Finset V) (hB : ∀ u ∈ B, ∃ p : G.Walk v u, p.length ≤ R) => by
      have h := L_mult_ball_aux G Δ hdeg v R B hB
      exact_mod_cast h
  open Matrix in
  have L_mult_U : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (lam : ℝ) (r : ℕ) (hconn : G.Connected)
      (hP2 : ∀ x y : V → ℝ, ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
          (a • x + b • y) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (a • x + b • y)) ≤
            lam * ((a • x + b • y) ⬝ᵥ (a • x + b • y)))
      (U : Finset V)
      (hU : ∀ u ∈ U, ∃ x : V → ℝ, (∀ w, (¬ ∃ p : G.Walk u w, p.length ≤ r) → x w = 0) ∧
          lam * (x ⬝ᵥ x) < x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)), ∃ u₀ : V, ∀ u ∈ U, ∃ p : G.Walk u₀ u, p.length ≤ 2 * r + 1 :=
    fun {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (lam : ℝ) (r : ℕ) (hconn : G.Connected)
        (hP2 : ∀ x y : V → ℝ, ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
            (a • x + b • y) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (a • x + b • y)) ≤
              lam * ((a • x + b • y) ⬝ᵥ (a • x + b • y)))
        (U : Finset V)
        (hU : ∀ u ∈ U, ∃ x : V → ℝ, (∀ w, (¬ ∃ p : G.Walk u w, p.length ≤ r) → x w = 0) ∧
            lam * (x ⬝ᵥ x) < x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)) => by
      classical
      rcases U.eq_empty_or_nonempty with hU0 | ⟨u₀, hu₀⟩
      · obtain ⟨v⟩ := hconn.nonempty
        exact ⟨v, by simp [hU0]⟩
      · refine ⟨u₀, fun u hu => ?_⟩
        by_contra hcon
        push_neg at hcon
        obtain ⟨x, hxs, hx⟩ := hU u₀ hu₀
        obtain ⟨y, hys, hy⟩ := hU u hu
        have hdisj : ∀ w, x w * y w = 0 := by
          intro w
          by_contra hne
          have hxw : x w ≠ 0 := left_ne_zero_of_mul hne
          have hyw : y w ≠ 0 := right_ne_zero_of_mul hne
          obtain ⟨p, hp⟩ : ∃ p : G.Walk u₀ w, p.length ≤ r := by
            by_contra h; exact hxw (hxs w h)
          obtain ⟨q, hq⟩ : ∃ p : G.Walk u w, p.length ≤ r := by
            by_contra h; exact hyw (hys w h)
          have := hcon (p.append q.reverse)
          rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at this
          omega
        have hnadj : ∀ i j, x i * G.adjMatrix ℝ i j * y j = 0 := by
          intro i j
          by_contra hne
          have hxi : x i ≠ 0 := by intro h; apply hne; simp [h]
          have hyj : y j ≠ 0 := by intro h; apply hne; simp [h]
          have hadj : G.Adj i j := by
            by_contra h; apply hne; simp [SimpleGraph.adjMatrix_apply, h]
          obtain ⟨p, hp⟩ : ∃ p : G.Walk u₀ i, p.length ≤ r := by
            by_contra h; exact hxi (hxs i h)
          obtain ⟨q, hq⟩ : ∃ p : G.Walk u j, p.length ≤ r := by
            by_contra h; exact hyj (hys j h)
          have := hcon (p.append (SimpleGraph.Walk.cons hadj q.reverse))
          rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
            SimpleGraph.Walk.length_reverse] at this
          omega
        have hsymm : ∀ i j, G.adjMatrix ℝ i j = G.adjMatrix ℝ j i := by
          intro i j; simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
        have hxAy : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) = 0 := by
          simp only [dotProduct, mulVec, Finset.mul_sum]
          apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _
          rw [← mul_assoc]; exact hnadj i j
        have hyAx : y ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = 0 := by
          simp only [dotProduct, mulVec, Finset.mul_sum]
          apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _
          have h := hnadj j i
          rw [hsymm i j]
          linear_combination h
        have hxy : x ⬝ᵥ y = 0 := by
          simp only [dotProduct]
          apply Finset.sum_eq_zero; intro i _; exact hdisj i
        have hyx : y ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact hxy
        obtain ⟨a, b, hab, hle⟩ := hP2 x y
        have hexp1 : (a • x + b • y) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (a • x + b • y)) =
            a ^ 2 * (x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)) + b ^ 2 * (y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y)) := by
          simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
            dotProduct_smul, smul_dotProduct, smul_eq_mul, hxAy, hyAx]
          ring
        have hexp2 : (a • x + b • y) ⬝ᵥ (a • x + b • y) =
            a ^ 2 * (x ⬝ᵥ x) + b ^ 2 * (y ⬝ᵥ y) := by
          simp only [dotProduct_add, add_dotProduct,
            dotProduct_smul, smul_dotProduct, smul_eq_mul, hxy, hyx]
          ring
        rw [hexp1, hexp2] at hle
        have h1 : 0 < x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) - lam * (x ⬝ᵥ x) := sub_pos.mpr hx
        have h2 : 0 < y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) - lam * (y ⬝ᵥ y) := sub_pos.mpr hy
        rcases hab with ha | hb
        · have ha2 : 0 < a ^ 2 := by positivity
          nlinarith [mul_pos ha2 h1, mul_nonneg (sq_nonneg b) h2.le]
        · have hb2 : 0 < b ^ 2 := by positivity
          nlinarith [mul_pos hb2 h2, mul_nonneg (sq_nonneg a) h1.le]
  open Matrix in
  have L_mult_delete : ∀ {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
      [DecidableRel G.Adj] [DecidableRel H.Adj] (lam : ℝ) (S : Finset V)
      (hH : ∀ a b, H.Adj a b ↔ G.Adj a b ∧ a ∉ S ∧ b ∉ S), (Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix V V ℝ)))) : ℝ) ≤
        Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (H.adjMatrix ℝ - lam • (1 : Matrix V V ℝ))))
          + S.card :=
    fun {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
        [DecidableRel G.Adj] [DecidableRel H.Adj] (lam : ℝ) (S : Finset V)
        (hH : ∀ a b, H.Adj a b ↔ G.Adj a b ∧ a ∉ S ∧ b ∉ S) => by
      classical
      let f : (V → ℝ) →ₗ[ℝ] (↥S → ℝ) := LinearMap.funLeft ℝ ℝ (Subtype.val : ↥S → V)
      have hle : LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix V V ℝ))) ⊓ LinearMap.ker f ≤
          LinearMap.ker (Matrix.toLin' (H.adjMatrix ℝ - lam • (1 : Matrix V V ℝ))) := by
        intro x hx
        rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hx
        obtain ⟨h1, h2⟩ := hx
        have hS : ∀ s ∈ S, x s = 0 := by
          intro s hs
          have := congrFun h2 ⟨s, hs⟩
          simpa [f, LinearMap.funLeft_apply] using this
        rw [Matrix.toLin'_apply] at h1
        rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        funext v
        have h1v := congrFun h1 v
        simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1v ⊢
        by_cases hv : v ∈ S
        · have : (H.adjMatrix ℝ *ᵥ x) v = 0 := by
            simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
            apply Finset.sum_eq_zero
            intro u _
            rw [if_neg]
            · ring
            · rw [hH]; tauto
          rw [this, hS v hv]; ring
        · have : (H.adjMatrix ℝ *ᵥ x) v = (G.adjMatrix ℝ *ᵥ x) v := by
            simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
            apply Finset.sum_congr rfl
            intro u _
            by_cases hu : u ∈ S
            · rw [hS u hu]; ring
            · have hiff : H.Adj v u ↔ G.Adj v u := by rw [hH]; tauto
              simp only [hiff]
          rw [this]; exact h1v
      have e1 := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix V V ℝ)))) (LinearMap.ker f)
      have e2 := Submodule.finrank_le
        (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix V V ℝ))) ⊔ LinearMap.ker f)
      have e3 := LinearMap.finrank_range_add_finrank_ker f
      have e4 := Submodule.finrank_le (LinearMap.range f)
      have e5 := Submodule.finrank_mono hle
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at e4
      have key : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix V V ℝ)))) ≤
          Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (H.adjMatrix ℝ - lam • (1 : Matrix V V ℝ)))) + S.card := by
        omega
      exact_mod_cast key
  open Matrix in
  have L_mult_trace : ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj] (lam : ℝ) (p : ℕ), (Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (H.adjMatrix ℝ - lam • (1 : Matrix V V ℝ)))) : ℝ)
          * lam ^ (2 * p) ≤ ∑ v, (H.adjMatrix ℝ ^ (2 * p)) v v :=
    fun {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
        [DecidableRel H.Adj] (lam : ℝ) (p : ℕ) => by
      classical
      set A := H.adjMatrix ℝ with hA
      set K := LinearMap.ker (Matrix.toLin' (A - lam • (1 : Matrix V V ℝ))) with hK
      have hAw : ∀ w ∈ K, ∀ n : ℕ, (A ^ n) *ᵥ w = lam ^ n • w := by
        intro w hw n
        have h1 : A *ᵥ w = lam • w := by
          rw [hK, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
            Matrix.one_mulVec, sub_eq_zero] at hw
          exact hw
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
      set M := A ^ p with hM
      have hMt : Mᵀ = M := by rw [hM, Matrix.transpose_pow, hA, SimpleGraph.transpose_adjMatrix]
      have hMs : ∀ u v, M u v = M v u := by
        intro u v
        rw [← Matrix.transpose_apply M v u, hMt]
      have htr : ∑ v, (A ^ (2 * p)) v v = ∑ v, ∑ u, M v u ^ 2 := by
        rw [two_mul, pow_add, ← hM]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [hMs u v, sq]
      rw [htr]
      let e : (V → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ V := (EuclideanSpace.equiv V ℝ).symm.toLinearEquiv
      let K' : Submodule ℝ (EuclideanSpace ℝ V) := K.map e.toLinearMap
      have hdim : Module.finrank ℝ K' = Module.finrank ℝ K := LinearEquiv.finrank_map_eq e K
      let b := stdOrthonormalBasis ℝ K'
      let w : Fin (Module.finrank ℝ K') → EuclideanSpace ℝ V := fun i => (b i : EuclideanSpace ℝ V)
      have hw : Orthonormal ℝ w := b.orthonormal.comp_linearIsometry K'.subtypeₗᵢ
      have hwK : ∀ i, e.symm (w i) ∈ K := by
        intro i
        have : w i ∈ K' := (b i).2
        obtain ⟨y, hy, hye⟩ := Submodule.mem_map.1 this
        rw [← hye]
        simpa using hy
      have hinner : ∀ (i) (v : V), inner ℝ (w i) (e (fun u => M v u)) = lam ^ p * (w i) v := by
        intro i v
        have h := congrFun (hAw _ (hwK i) p) v
        rw [← hM] at h
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
        rw [PiLp.inner_apply]
        simp only [e, RCLike.inner_apply, conj_trivial] at h ⊢
        simpa [mul_comm] using h
      have hrow : ∀ v, ∑ i, (lam ^ p * (w i) v) ^ 2 ≤ ∑ u, M v u ^ 2 := by
        intro v
        have hb := hw.sum_inner_products_le (e (fun u => M v u)) (s := Finset.univ)
        have hx : ‖e (fun u => M v u)‖ ^ 2 = ∑ u, M v u ^ 2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
          simp [e, Real.norm_eq_abs, sq_abs]
        rw [hx] at hb
        simp only [hinner, Real.norm_eq_abs, sq_abs] at hb
        exact hb
      have hnorm : ∀ i, ∑ v, ((w i) v) ^ 2 = 1 := by
        intro i
        have h1 : ‖w i‖ = 1 := hw.1 i
        have h2 : ‖w i‖ ^ 2 = ∑ v, ((w i) v) ^ 2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
          simp [Real.norm_eq_abs, sq_abs]
        rw [← h2, h1, one_pow]
      calc (Module.finrank ℝ K : ℝ) * lam ^ (2 * p)
          = ∑ i, ∑ v, (lam ^ p * (w i) v) ^ 2 := by
            have hi : ∀ i, ∑ v, (lam ^ p * (w i) v) ^ 2 = lam ^ (2 * p) := by
              intro i
              calc ∑ v, (lam ^ p * (w i) v) ^ 2 = lam ^ (2 * p) * ∑ v, ((w i) v) ^ 2 := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl (fun v _ => by ring)
                _ = lam ^ (2 * p) := by rw [hnorm i, mul_one]
            rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, hdim, nsmul_eq_mul]
        _ = ∑ v, ∑ i, (lam ^ p * (w i) v) ^ 2 := Finset.sum_comm
        _ ≤ ∑ v, ∑ u, M v u ^ 2 := Finset.sum_le_sum (fun v _ => hrow v)
  open Matrix in
  have L_mult_local_quad : ∀ {V : Type} [Fintype V] (P : Matrix V V ℝ) (x : V → ℝ), x ⬝ᵥ (P *ᵥ x) = ∑ a, ∑ b, x a * P a b * x b :=
    fun {V : Type} [Fintype V] (P : Matrix V V ℝ) (x : V → ℝ) => by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  open Matrix in
  have L_mult_local_abs_quad : ∀ {V : Type} [Fintype V] (P : Matrix V V ℝ) (hP : ∀ a b, 0 ≤ P a b)
      (x : V → ℝ), |x ⬝ᵥ (P *ᵥ x)| ≤ (fun w => |x w|) ⬝ᵥ (P *ᵥ (fun w => |x w|)) :=
    fun {V : Type} [Fintype V] (P : Matrix V V ℝ) (hP : ∀ a b, 0 ≤ P a b)
        (x : V → ℝ) => by
      rw [L_mult_local_quad, L_mult_local_quad]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (hP a b)]
  open Matrix in
  have L_mult_local_diag_quad : ∀ {V : Type} [Fintype V] (P : Matrix V V ℝ) (hP : ∀ a b, 0 ≤ P a b)
      (x : V → ℝ) (hx : ∀ a, 0 ≤ x a) (hd : ∀ a, x a ≠ 0 → 1 ≤ P a a), x ⬝ᵥ x ≤ x ⬝ᵥ (P *ᵥ x) :=
    fun {V : Type} [Fintype V] (P : Matrix V V ℝ) (hP : ∀ a b, 0 ≤ P a b)
        (x : V → ℝ) (hx : ∀ a, 0 ≤ x a) (hd : ∀ a, x a ≠ 0 → 1 ≤ P a a) => by
      rw [L_mult_local_quad]
      simp only [dotProduct]
      refine Finset.sum_le_sum fun a _ => ?_
      have h1 : x a * P a a * x a ≤ ∑ b, x a * P a b * x b :=
        Finset.single_le_sum (f := fun b => x a * P a b * x b)
          (fun b _ => mul_nonneg (mul_nonneg (hx a) (hP a b)) (hx b)) (Finset.mem_univ a)
      by_cases h : x a = 0
      · rw [h, mul_zero]
        exact Finset.sum_nonneg fun b _ => by simp
      · have h2 := hd a h
        have h3 : x a * x a ≤ x a * P a a * x a := by
          nlinarith [mul_nonneg (sub_nonneg.2 h2) (mul_self_nonneg (x a))]
        linarith
  open Matrix in
  have L_mult_local_sym_sq : ∀ {V : Type} [Fintype V] (S : Matrix V V ℝ) (hS : Sᵀ = S) (x : V → ℝ), x ⬝ᵥ ((S * S) *ᵥ x) = (S *ᵥ x) ⬝ᵥ (S *ᵥ x) :=
    fun {V : Type} [Fintype V] (S : Matrix V V ℝ) (hS : Sᵀ = S) (x : V → ℝ) => by
      have h : x ᵥ* S = S *ᵥ x := by simpa [hS] using vecMul_transpose S x
      rw [← mulVec_mulVec, dotProduct_mulVec, h]
  open Matrix in
  have L_mult_local_sym_norm : ∀ {V : Type} [Fintype V] (S : Matrix V V ℝ) (hS : Sᵀ = S) (μ : ℝ)
      (hμ : 0 < μ) (h : ∀ x : V → ℝ, |x ⬝ᵥ (S *ᵥ x)| ≤ μ * (x ⬝ᵥ x)) (x : V → ℝ), (S *ᵥ x) ⬝ᵥ (S *ᵥ x) ≤ μ ^ 2 * (x ⬝ᵥ x) :=
    fun {V : Type} [Fintype V] (S : Matrix V V ℝ) (hS : Sᵀ = S) (μ : ℝ)
        (hμ : 0 < μ) (h : ∀ x : V → ℝ, |x ⬝ᵥ (S *ᵥ x)| ≤ μ * (x ⬝ᵥ x)) (x : V → ℝ) => by
      have hsym : ∀ u w : V → ℝ, u ⬝ᵥ (S *ᵥ w) = w ⬝ᵥ (S *ᵥ u) := by
        intro u w
        have h' : u ᵥ* S = S *ᵥ u := by simpa [hS] using vecMul_transpose S u
        rw [dotProduct_mulVec, h', dotProduct_comm]
      set y := S *ᵥ x with hy
      have h1 := (abs_le.1 (h (μ • x + y))).2
      have h2 := (abs_le.1 (h (μ • x - y))).1
      simp only [mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_sub,
        sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 h2
      rw [← hy] at h1 h2
      have e1 := hsym x y
      rw [← hy] at e1
      have e2 : x ⬝ᵥ y = y ⬝ᵥ x := dotProduct_comm _ _
      have key : 2 * μ * (y ⬝ᵥ y) ≤ 2 * μ * (μ ^ 2 * (x ⬝ᵥ x)) := by nlinarith
      exact le_of_mul_le_mul_left key (by positivity)
  open Matrix in
  have L_mult_local_pow_nonneg : ∀ {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
      (hA : ∀ a b, 0 ≤ A a b) (n : ℕ), ∀ a b, 0 ≤ (A ^ n) a b :=
    fun {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
        (hA : ∀ a b, 0 ≤ A a b) (n : ℕ) => by
      induction n with
      | zero => intro a b; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
      | succ n ih =>
        intro a b; rw [pow_succ', Matrix.mul_apply]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (hA a j) (ih j b)
  open Matrix in
  have L_mult_local_mul_nonneg : ∀ {V : Type} [Fintype V] (A B : Matrix V V ℝ)
      (hA : ∀ a b, 0 ≤ A a b) (hB : ∀ a b, 0 ≤ B a b), ∀ a b, 0 ≤ (A * B) a b :=
    fun {V : Type} [Fintype V] (A B : Matrix V V ℝ)
        (hA : ∀ a b, 0 ≤ A a b) (hB : ∀ a b, 0 ≤ B a b) => by
      intro a b; rw [Matrix.mul_apply]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hA a j) (hB j b)
  open Matrix in
  have L_mult_local_mul_ge : ∀ {V : Type} [Fintype V] (A B : Matrix V V ℝ)
      (hA : ∀ a b, 0 ≤ A a b) (hB : ∀ a b, 0 ≤ B a b) (x z y : V), A x z * B z y ≤ (A * B) x y :=
    fun {V : Type} [Fintype V] (A B : Matrix V V ℝ)
        (hA : ∀ a b, 0 ≤ A a b) (hB : ∀ a b, 0 ≤ B a b) (x z y : V) => by
      rw [Matrix.mul_apply]
      exact Finset.single_le_sum (f := fun j => A x j * B j y)
        (fun j _ => mul_nonneg (hA x j) (hB j y)) (Finset.mem_univ z)
  open Matrix in
  have L_mult_local_pow_mono : ∀ {V : Type} [Fintype V] [DecidableEq V] (M K : Matrix V V ℝ)
      (hM : ∀ a b, 0 ≤ M a b) (hMK : ∀ a b, M a b ≤ K a b) (n : ℕ), ∀ a b, (M ^ n) a b ≤ (K ^ n) a b :=
    fun {V : Type} [Fintype V] [DecidableEq V] (M K : Matrix V V ℝ)
        (hM : ∀ a b, 0 ≤ M a b) (hMK : ∀ a b, M a b ≤ K a b) (n : ℕ) => by
      induction n with
      | zero => intro a b; exact le_rfl
      | succ n ih =>
        intro a b; rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
        exact Finset.sum_le_sum fun j _ => mul_le_mul (hMK a j) (ih j b)
          (L_mult_local_pow_nonneg M hM n j b) (le_trans (hM a j) (hMK a j))
  open Matrix in
  have L_mult_local_diff : ∀ {V : Type} [Fintype V] [DecidableEq V] (M K : Matrix V V ℝ)
      (hM : ∀ a b, 0 ≤ M a b) (hMK : ∀ a b, M a b ≤ K a b) (a b : ℕ) (x y : V), (M ^ (a + 1 + b)) x y + (K ^ a * (K - M) * M ^ b) x y ≤ (K ^ (a + 1 + b)) x y :=
    fun {V : Type} [Fintype V] [DecidableEq V] (M K : Matrix V V ℝ)
        (hM : ∀ a b, 0 ≤ M a b) (hMK : ∀ a b, M a b ≤ K a b) (a b : ℕ) (x y : V) => by
      have hK : ∀ i j, 0 ≤ K i j := fun i j => le_trans (hM i j) (hMK i j)
      have hid : K ^ a * K * K ^ b = M ^ a * M * M ^ b + K ^ a * (K - M) * M ^ b +
          (K ^ a * K * (K ^ b - M ^ b) + (K ^ a - M ^ a) * M * M ^ b) := by noncomm_ring
      have hKp : K ^ (a + 1 + b) = K ^ a * K * K ^ b := by rw [pow_add, pow_succ]
      have hMp : M ^ (a + 1 + b) = M ^ a * M * M ^ b := by rw [pow_add, pow_succ]
      rw [hKp, hMp, hid, Matrix.add_apply, Matrix.add_apply]
      have hb : ∀ i j, 0 ≤ (K ^ b - M ^ b) i j := fun i j =>
        sub_nonneg.2 (L_mult_local_pow_mono M K hM hMK b i j)
      have ha : ∀ i j, 0 ≤ (K ^ a - M ^ a) i j := fun i j =>
        sub_nonneg.2 (L_mult_local_pow_mono M K hM hMK a i j)
      have t1 := L_mult_local_mul_nonneg _ _ (L_mult_local_mul_nonneg _ _
        (L_mult_local_pow_nonneg K hK a) hK) hb x y
      have t2 := L_mult_local_mul_nonneg _ _ (L_mult_local_mul_nonneg _ _ ha hM)
        (L_mult_local_pow_nonneg M hM b) x y
      rw [Matrix.add_apply]
      linarith
  open Matrix in
  have L_mult_local_walk_entry : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (A : Matrix V V ℝ) (hA : ∀ a b, 0 ≤ A a b) (S : Finset V)
      (hadj : ∀ a b, G.Adj a b → a ∈ S → b ∈ S → 1 ≤ A a b)
      (x y : V) (p : G.Walk x y) (hp : ∀ z ∈ p.support, z ∈ S), 1 ≤ (A ^ p.length) x y :=
    fun {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (A : Matrix V V ℝ) (hA : ∀ a b, 0 ≤ A a b) (S : Finset V)
        (hadj : ∀ a b, G.Adj a b → a ∈ S → b ∈ S → 1 ≤ A a b)
        (x y : V) (p : G.Walk x y) (hp : ∀ z ∈ p.support, z ∈ S) => by
      induction p with
      | nil => simp
      | @cons a b c h p ih =>
        have hp' : ∀ z ∈ p.support, z ∈ S := fun z hz => hp z (by simp [hz])
        have ha : a ∈ S := hp a (by simp)
        have hb : b ∈ S := hp' b p.start_mem_support
        rw [SimpleGraph.Walk.length_cons, pow_succ']
        have h1 := hadj a b h ha hb
        have h2 := ih hp'
        have h3 := L_mult_local_mul_ge A (A ^ p.length) hA (L_mult_local_pow_nonneg A hA _) a b c
        nlinarith
  open Matrix in
  have L_mult_local_pad : ∀ {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
      (hA : ∀ a b, 0 ≤ A a b) (x z : V) (hz : 1 ≤ (A ^ 2) z z) (m k : ℕ), (A ^ m) x z ≤ (A ^ (m + 2 * k)) x z :=
    fun {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
        (hA : ∀ a b, 0 ≤ A a b) (x z : V) (hz : 1 ≤ (A ^ 2) z z) (m k : ℕ) => by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show m + 2 * (k + 1) = (m + 2 * k) + 2 by ring, pow_add]
        have h0 := L_mult_local_pow_nonneg A hA (m + 2 * k) x z
        have h1 := L_mult_local_mul_ge _ _ (L_mult_local_pow_nonneg A hA (m + 2 * k))
          (L_mult_local_pow_nonneg A hA 2) x z z
        nlinarith
  open Matrix in
  have L_mult_local_path : ∀ {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
      (S B : Finset V) (hH : ∀ a b, H.Adj a b ↔ G.Adj a b ∧ a ∉ S ∧ b ∉ S) (w u : V)
      (p : G.Walk w u) (hu : u ∈ S) (hw : w ∉ S) (hp : ∀ z ∈ p.support, z ∈ B), ∃ z z' : V, ∃ j : ℕ, 1 ≤ j ∧ j ≤ p.length ∧ z ∈ S ∧ G.Adj z' z ∧
        (∃ q₁ : G.Walk w z, q₁.length = j ∧ ∀ t ∈ q₁.support, t ∈ B) ∧
        (∃ q₂ : H.Walk z' w, q₂.length = j - 1 ∧ ∀ t ∈ q₂.support, t ∈ B) :=
    fun {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
        (S B : Finset V) (hH : ∀ a b, H.Adj a b ↔ G.Adj a b ∧ a ∉ S ∧ b ∉ S) (w u : V)
        (p : G.Walk w u) (hu : u ∈ S) (hw : w ∉ S) (hp : ∀ z ∈ p.support, z ∈ B) => by
      induction p with
      | nil => exact absurd hu hw
      | @cons a b c h p ih =>
        have hp' : ∀ z ∈ p.support, z ∈ B := fun z hz => hp z (by simp [hz])
        have haB : a ∈ B := hp a (by simp)
        have hbB : b ∈ B := hp' b p.start_mem_support
        by_cases hb : b ∈ S
        · refine ⟨b, a, 1, le_rfl, by simp, hb, h,
            ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil, by simp, ?_⟩, ⟨SimpleGraph.Walk.nil, by simp, ?_⟩⟩
          · intro t ht; simp at ht; rcases ht with rfl | rfl <;> assumption
          · intro t ht; simp at ht; subst ht; exact haB
        · obtain ⟨z, z', j, hj1, hjl, hz, hadj, ⟨q₁, hq₁, hq₁B⟩, ⟨q₂, hq₂, hq₂B⟩⟩ := ih hu hb hp'
          have hba : H.Adj b a := (hH b a).2 ⟨h.symm, hb, hw⟩
          refine ⟨z, z', j + 1, by omega, by simp; omega, hz, hadj,
            ⟨SimpleGraph.Walk.cons h q₁, by simp [hq₁], ?_⟩,
            ⟨q₂.concat hba, by simp [hq₂]; omega, ?_⟩⟩
          · intro t ht; simp at ht; rcases ht with rfl | ht
            · exact haB
            · exact hq₁B t ht
          · intro t ht; simp [SimpleGraph.Walk.support_concat] at ht; rcases ht with ht | rfl
            · exact hq₂B t ht
            · exact haB
  open Matrix in
  have L_mult_local : ∀ {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
      [DecidableRel G.Adj] [DecidableRel H.Adj] (lam : ℝ) (hlam : 0 < lam) (r₁ q : ℕ)
      (hr₁ : 1 ≤ r₁) (N U : Finset V)
      (hN : ∀ v, ∃ u ∈ N, ∃ p : G.Walk u v, p.length ≤ r₁)
      (hU : ∀ v, v ∉ U → ∀ x : V → ℝ, (∀ w, (¬ ∃ p : G.Walk v w, p.length ≤ r₁ + q * r₁) → x w = 0) →
          x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x))
      (hH : ∀ a b, H.Adj a b ↔ G.Adj a b ∧ a ∉ N ∪ U ∧ b ∉ N ∪ U)
      (v : V) (hv : v ∉ N ∪ U), 1 ≤ lam ^ (2 * r₁) ∧ (H.adjMatrix ℝ ^ (2 * (q * r₁))) v v ≤ (lam ^ (2 * r₁) - 1) ^ q :=
    fun {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
        [DecidableRel G.Adj] [DecidableRel H.Adj] (lam : ℝ) (hlam : 0 < lam) (r₁ q : ℕ)
        (hr₁ : 1 ≤ r₁) (N U : Finset V)
        (hN : ∀ v, ∃ u ∈ N, ∃ p : G.Walk u v, p.length ≤ r₁)
        (hU : ∀ v, v ∉ U → ∀ x : V → ℝ, (∀ w, (¬ ∃ p : G.Walk v w, p.length ≤ r₁ + q * r₁) → x w = 0) →
            x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x))
        (hH : ∀ a b, H.Adj a b ↔ G.Adj a b ∧ a ∉ N ∪ U ∧ b ∉ N ∪ U)
        (v : V) (hv : v ∉ N ∪ U) => by
      classical
      have hvU : v ∉ U := fun h => hv (Finset.mem_union_right _ h)
      obtain ⟨B, hB⟩ : ∃ B : Finset V, ∀ w, w ∈ B ↔ ∃ p : G.Walk v w, p.length ≤ r₁ + q * r₁ :=
        ⟨Finset.univ.filter (fun w => ∃ p : G.Walk v w, p.length ≤ r₁ + q * r₁),
          fun w => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))⟩
      obtain ⟨K, hK⟩ : ∃ K : Matrix V V ℝ, ∀ a b,
          K a b = if a ∈ B ∧ b ∈ B then G.adjMatrix ℝ a b else 0 := ⟨fun a b => _, fun a b => rfl⟩
      obtain ⟨M, hM⟩ : ∃ M : Matrix V V ℝ, ∀ a b,
          M a b = if a ∈ B ∧ b ∈ B then H.adjMatrix ℝ a b else 0 := ⟨fun a b => _, fun a b => rfl⟩
      have hK0 : ∀ a b, 0 ≤ K a b := by
        intro a b; rw [hK]; split_ifs
        · rw [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num
        · exact le_rfl
      have hM0 : ∀ a b, 0 ≤ M a b := by
        intro a b; rw [hM]; split_ifs
        · rw [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num
        · exact le_rfl
      have hMK : ∀ a b, M a b ≤ K a b := by
        intro a b; rw [hM, hK]; split_ifs
        · rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
          by_cases h : H.Adj a b
          · rw [if_pos h, if_pos ((hH a b).1 h).1]
          · rw [if_neg h]; split_ifs <;> norm_num
        · exact le_rfl
      have hKs : Kᵀ = K := by
        ext a b; rw [transpose_apply, hK, hK, SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
        simp only [and_comm, G.adj_comm]
      have hMs : Mᵀ = M := by
        ext a b; rw [transpose_apply, hM, hM, SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
        simp only [and_comm, H.adj_comm]
      have hKadj : ∀ a b, G.Adj a b → a ∈ B → b ∈ B → K a b = 1 := by
        intro a b h ha hb; rw [hK, if_pos ⟨ha, hb⟩, SimpleGraph.adjMatrix_apply, if_pos h]
      have hMadj : ∀ a b, H.Adj a b → a ∈ B → b ∈ B → M a b = 1 := by
        intro a b h ha hb; rw [hM, if_pos ⟨ha, hb⟩, SimpleGraph.adjMatrix_apply, if_pos h]
      have hdd : ∀ x : V → ℝ, (fun w => |x w|) ⬝ᵥ (fun w => |x w|) = x ⬝ᵥ x := by
        intro x; simp only [dotProduct, abs_mul_abs_self]
      have hKq : ∀ x : V → ℝ, |x ⬝ᵥ (K *ᵥ x)| ≤ lam * (x ⬝ᵥ x) := by
        intro x
        have h1 := L_mult_local_abs_quad K hK0 x
        set D : V → ℝ := fun w => if w ∈ B then |x w| else 0 with hD
        have h2 := hU v hvU D (fun w hw => by
          have : w ∉ B := fun h => hw ((hB w).1 h)
          simp [hD, this])
        have h3 : (fun w => |x w|) ⬝ᵥ (K *ᵥ (fun w => |x w|)) = D ⬝ᵥ (G.adjMatrix ℝ *ᵥ D) := by
          rw [L_mult_local_quad, L_mult_local_quad]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [hK]
          by_cases ha : a ∈ B <;> by_cases hb : b ∈ B <;> simp [hD, ha, hb]
        have h4 : D ⬝ᵥ D ≤ x ⬝ᵥ x := by
          rw [← hdd x]; simp only [dotProduct]
          refine Finset.sum_le_sum fun a _ => ?_
          by_cases ha : a ∈ B
          · simp [hD, ha]
          · simp only [hD, if_neg ha, mul_zero]; exact mul_self_nonneg _
        have h5 : lam * (D ⬝ᵥ D) ≤ lam * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left h4 hlam.le
        linarith
      have hKn := L_mult_local_sym_norm K hKs lam hlam hKq
      have hKpow : ∀ m (x : V → ℝ), (K ^ m *ᵥ x) ⬝ᵥ (K ^ m *ᵥ x) ≤ (lam ^ 2) ^ m * (x ⬝ᵥ x) := by
        intro m x
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ', ← mulVec_mulVec]
          calc (K *ᵥ (K ^ m *ᵥ x)) ⬝ᵥ (K *ᵥ (K ^ m *ᵥ x)) ≤ lam ^ 2 * ((K ^ m *ᵥ x) ⬝ᵥ (K ^ m *ᵥ x)) :=
                hKn _
            _ ≤ lam ^ 2 * ((lam ^ 2) ^ m * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left ih (by positivity)
            _ = (lam ^ 2) ^ (m + 1) * (x ⬝ᵥ x) := by ring
      have hdiag : ∀ w, w ∉ N ∪ U → (∃ p : G.Walk v w, p.length ≤ q * r₁) →
          1 + (M ^ (2 * r₁)) w w ≤ (K ^ (2 * r₁)) w w := by
        intro w hwS hw
        obtain ⟨p₀, hp₀⟩ := hw
        obtain ⟨u, huN, p, hp⟩ := hN w
        have hpB : ∀ z ∈ p.reverse.support, z ∈ B := by
          intro z hz
          rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
          refine (hB z).2 ⟨p₀.append (p.dropUntil z hz).reverse, ?_⟩
          have := SimpleGraph.Walk.length_dropUntil_le p hz
          simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
          omega
        obtain ⟨z, z', j, hj1, hjl, hzS, hadj, ⟨q₁, hq₁, hq₁B⟩, ⟨q₂, hq₂, hq₂B⟩⟩ :=
          L_mult_local_path G H (N ∪ U) B hH w u p.reverse (Finset.mem_union_left _ huN) hwS hpB
        rw [SimpleGraph.Walk.length_reverse] at hjl
        have hzB : z ∈ B := hq₁B z q₁.end_mem_support
        have hz'B : z' ∈ B := hq₂B z' q₂.start_mem_support
        have h1 : 1 ≤ (K ^ j) w z := by
          have := L_mult_local_walk_entry G K hK0 B (fun a b h ha hb => (hKadj a b h ha hb).ge) w z q₁ hq₁B
          rwa [hq₁] at this
        have h2 : 1 ≤ (K ^ 2) z z := by
          rw [sq]
          have := L_mult_local_mul_ge K K hK0 hK0 z z' z
          rw [hKadj z z' hadj.symm hzB hz'B, hKadj z' z hadj hz'B hzB] at this
          linarith
        have h3 : 1 ≤ (K ^ (j + 2 * (r₁ - j))) w z := le_trans h1 (L_mult_local_pad K hK0 w z h2 j (r₁ - j))
        have h4 : 1 ≤ (M ^ (j - 1)) z' w := by
          have := L_mult_local_walk_entry H M hM0 B (fun a b h ha hb => (hMadj a b h ha hb).ge) z' w q₂ hq₂B
          rwa [hq₂] at this
        have h5 : (K - M) z z' = 1 := by
          rw [Matrix.sub_apply, hKadj z z' hadj.symm hzB hz'B, hM, if_pos ⟨hzB, hz'B⟩,
            SimpleGraph.adjMatrix_apply, if_neg (fun h => ((hH z z').1 h).2.1 hzS)]
          norm_num
        have hKM0 : ∀ a b, 0 ≤ (K - M) a b := fun a b => by rw [Matrix.sub_apply]; linarith [hMK a b]
        have h6 := L_mult_local_diff M K hM0 hMK (j + 2 * (r₁ - j)) (j - 1) w w
        have hidx : j + 2 * (r₁ - j) + 1 + (j - 1) = 2 * r₁ := by omega
        rw [hidx] at h6
        have h7 : 1 ≤ (K ^ (j + 2 * (r₁ - j)) * (K - M) * M ^ (j - 1)) w w := by
          have e1 := L_mult_local_mul_ge (K ^ (j + 2 * (r₁ - j))) (K - M)
            (L_mult_local_pow_nonneg K hK0 _) hKM0 w z z'
          have e2 := L_mult_local_mul_ge (K ^ (j + 2 * (r₁ - j)) * (K - M)) (M ^ (j - 1))
            (L_mult_local_mul_nonneg _ _ (L_mult_local_pow_nonneg K hK0 _) hKM0)
            (L_mult_local_pow_nonneg M hM0 (j - 1)) w z' w
          rw [h5, mul_one] at e1
          have e3 : 0 ≤ (M ^ (j - 1)) z' w := L_mult_local_pow_nonneg M hM0 _ z' w
          nlinarith
        linarith
      have hMB : ∀ x : V → ℝ, (∀ w, x w ≠ 0 → w ∉ N ∪ U ∧ ∃ p : G.Walk v w, p.length ≤ q * r₁) →
          (M ^ r₁ *ᵥ x) ⬝ᵥ (M ^ r₁ *ᵥ x) ≤ (lam ^ (2 * r₁) - 1) * (x ⬝ᵥ x) := by
        intro x hx
        set ax : V → ℝ := fun w => |x w| with hax
        have hpow2 : ∀ A : Matrix V V ℝ, A ^ (2 * r₁) = A ^ r₁ * A ^ r₁ := fun A => by
          rw [← pow_add, two_mul]
        have hMrs : (M ^ r₁)ᵀ = M ^ r₁ := by rw [transpose_pow, hMs]
        have hKrs : (K ^ r₁)ᵀ = K ^ r₁ := by rw [transpose_pow, hKs]
        have e1 : (M ^ r₁ *ᵥ x) ⬝ᵥ (M ^ r₁ *ᵥ x) = x ⬝ᵥ (M ^ (2 * r₁) *ᵥ x) := by
          rw [hpow2, L_mult_local_sym_sq _ hMrs]
        have e2 := L_mult_local_abs_quad _ (L_mult_local_pow_nonneg M hM0 (2 * r₁)) x
        have e3 := L_mult_local_diag_quad (K ^ (2 * r₁) - M ^ (2 * r₁))
          (fun a b => by rw [Matrix.sub_apply]; linarith [L_mult_local_pow_mono M K hM0 hMK (2 * r₁) a b])
          ax (fun a => abs_nonneg _) (fun a ha => by
            have hxa : x a ≠ 0 := fun h => ha (by simp [hax, h])
            obtain ⟨h1, h2⟩ := hx a hxa
            have := hdiag a h1 h2
            rw [Matrix.sub_apply]; linarith)
        rw [sub_mulVec, dotProduct_sub] at e3
        have e4 : ax ⬝ᵥ (K ^ (2 * r₁) *ᵥ ax) ≤ lam ^ (2 * r₁) * (ax ⬝ᵥ ax) := by
          rw [hpow2, L_mult_local_sym_sq _ hKrs, pow_mul]
          exact hKpow r₁ ax
        have e5 := hdd x
        rw [← hax] at e5
        rw [e5] at e3 e4
        have e6 := (abs_le.1 e2).2
        linarith
      have hsupp : ∀ j w, (H.adjMatrix ℝ ^ j) w v ≠ 0 → w ∉ N ∪ U ∧ ∃ p : G.Walk v w, p.length ≤ j := by
        intro j
        induction j with
        | zero =>
          intro w hw
          rw [pow_zero, Matrix.one_apply] at hw
          have : w = v := by by_contra h; exact hw (if_neg h)
          subst this
          exact ⟨hv, SimpleGraph.Walk.nil, by simp⟩
        | succ j ih =>
          intro w hw
          rw [pow_succ', Matrix.mul_apply] at hw
          obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
          have hadj : H.Adj w b := by
            by_contra h
            apply hb
            rw [SimpleGraph.adjMatrix_apply, if_neg h, zero_mul]
          obtain ⟨_, p, hp⟩ := ih b (fun h => hb (by rw [h, mul_zero]))
          have hG := (hH w b).1 hadj
          exact ⟨hG.2.1, p.concat hG.1.symm, by simp; omega⟩
      have hloc : ∀ j, j ≤ r₁ + q * r₁ → ∀ w, (M ^ j) w v = (H.adjMatrix ℝ ^ j) w v := by
        intro j
        induction j with
        | zero => intro _ w; simp
        | succ j ih =>
          intro hj w
          rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [ih (by omega) b]
          by_cases h0 : (H.adjMatrix ℝ ^ j) b v = 0
          · rw [h0, mul_zero, mul_zero]
          obtain ⟨_, p, hp⟩ := hsupp j b h0
          have hbB : b ∈ B := (hB b).2 ⟨p, by omega⟩
          rw [hM]
          by_cases hwB : w ∈ B
          · rw [if_pos ⟨hwB, hbB⟩]
          · rw [if_neg (fun h => hwB h.1)]
            have : ¬ H.Adj w b := by
              intro h
              exact hwB ((hB w).2 ⟨p.concat ((hH w b).1 h).1.symm, by simp; omega⟩)
            rw [SimpleGraph.adjMatrix_apply, if_neg this]
      set c := lam ^ (2 * r₁) - 1 with hc
      set y : ℕ → V → ℝ := fun k w => (M ^ (k * r₁)) w v with hy
      have hy_succ : ∀ k, y (k + 1) = M ^ r₁ *ᵥ y k := by
        intro k; funext w
        simp only [hy, mulVec, dotProduct]
        rw [show (k + 1) * r₁ = r₁ + k * r₁ by ring, pow_add, Matrix.mul_apply]
      have hy_supp : ∀ k, k ≤ q → ∀ w, y k w ≠ 0 → w ∉ N ∪ U ∧ ∃ p : G.Walk v w, p.length ≤ q * r₁ := by
        intro k hk w hw
        have hkr : k * r₁ ≤ q * r₁ := Nat.mul_le_mul_right _ hk
        simp only [hy] at hw
        rw [hloc (k * r₁) (by omega) w] at hw
        obtain ⟨h1, p, hp⟩ := hsupp _ w hw
        exact ⟨h1, p, le_trans hp hkr⟩
      have hy0 : y 0 ⬝ᵥ y 0 = 1 := by
        simp [hy, dotProduct, Matrix.one_apply]
      have hc0 : 0 ≤ c := by
        have h1 := hMB (y 0) (hy_supp 0 (Nat.zero_le _))
        rw [hy0, mul_one] at h1
        have h2 : 0 ≤ (M ^ r₁ *ᵥ y 0) ⬝ᵥ (M ^ r₁ *ᵥ y 0) :=
          Finset.sum_nonneg fun i _ => mul_self_nonneg _
        linarith
      have hyb : ∀ k, k ≤ q → y k ⬝ᵥ y k ≤ c ^ k := by
        intro k
        induction k with
        | zero => intro _; rw [hy0, pow_zero]
        | succ k ih =>
          intro hk
          rw [hy_succ]
          calc (M ^ r₁ *ᵥ y k) ⬝ᵥ (M ^ r₁ *ᵥ y k) ≤ c * (y k ⬝ᵥ y k) := hMB _ (hy_supp k (by omega))
            _ ≤ c * c ^ k := mul_le_mul_of_nonneg_left (ih (by omega)) hc0
            _ = c ^ (k + 1) := by ring
      refine ⟨by linarith, ?_⟩
      have hAs : (H.adjMatrix ℝ ^ (q * r₁))ᵀ = H.adjMatrix ℝ ^ (q * r₁) := by
        rw [transpose_pow, SimpleGraph.transpose_adjMatrix]
      have hfin : (H.adjMatrix ℝ ^ (2 * (q * r₁))) v v = y q ⬝ᵥ y q := by
        rw [two_mul, pow_add, Matrix.mul_apply]
        simp only [dotProduct, hy]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hloc _ (by omega) w]
        congr 1
        rw [← hAs, transpose_apply, hAs]
      rw [hfin]
      exact hyb q le_rfl
  open Matrix in
  have L_mult_isolated : ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj] (v : V) (hv : ∀ w, ¬ H.Adj v w) (p : ℕ) (hp : 1 ≤ p), (H.adjMatrix ℝ ^ p) v v = 0 :=
    fun {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
        [DecidableRel H.Adj] (v : V) (hv : ∀ w, ¬ H.Adj v w) (p : ℕ) (hp : 1 ≤ p) => by
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_eq_zero (fun w _ => by simp [SimpleGraph.adjMatrix_apply, hv w])
  open Matrix in
  have L_mult : ∀ (lam : ℝ) (hlam : 0 < lam) (Δ : ℕ) (ε : ℝ) (hε : 0 < ε), ∃ C : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.Connected → (∀ v, (Finset.univ.filter (G.Adj v)).card ≤ Δ) →
        (∀ x y : V → ℝ, ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
          (a • x + b • y) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (a • x + b • y)) ≤
            lam * ((a • x + b • y) ⬝ᵥ (a • x + b • y))) →
        (Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix V V ℝ)))) : ℝ)
          ≤ ε * Fintype.card V + C :=
    fun (lam : ℝ) (hlam : 0 < lam) (Δ : ℕ) (ε : ℝ) (hε : 0 < ε) => by
      obtain ⟨r₀, hr₀⟩ := exists_nat_ge (2 / ε)
      obtain ⟨r₁, hr₁, hr₁ε⟩ : ∃ r₁ : ℕ, 1 ≤ r₁ ∧ 2 / ε ≤ (r₁ : ℝ) :=
        ⟨r₀ + 1, by omega, by push_cast; linarith⟩
      have hs : 0 < lam ^ (2 * r₁) := pow_pos hlam _
      obtain ⟨y, hy0, hy1, hyprop⟩ : ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧
          (1 ≤ lam ^ (2 * r₁) → lam ^ (2 * r₁) - 1 = lam ^ (2 * r₁) * y) := by
        refine ⟨max (1 - 1 / lam ^ (2 * r₁)) 0, le_max_right _ _,
          max_lt (by have : 0 < 1 / lam ^ (2 * r₁) := by positivity
                     linarith) one_pos, fun h => ?_⟩
        rw [max_eq_left (by rw [sub_nonneg, div_le_one hs]; exact h)]
        field_simp
      obtain ⟨q₀, hq₀⟩ := exists_pow_lt_of_lt_one (half_pos hε) hy1
      obtain ⟨q, hq1, hq⟩ : ∃ q : ℕ, 1 ≤ q ∧ y ^ q ≤ ε / 2 := by
        refine ⟨q₀ + 1, by omega, ?_⟩
        rw [pow_succ]
        have h1 : y ^ q₀ * y ≤ y ^ q₀ := mul_le_of_le_one_right (pow_nonneg hy0 _) hy1.le
        linarith
      refine ⟨1 + ((Δ : ℝ) + 1) ^ (2 * (r₁ + q * r₁) + 1), ?_⟩
      intro V _ _ G _ hconn hdeg hP2
      classical
      obtain ⟨N, hNcard, hN⟩ := L_mult_net G hconn r₁
      obtain ⟨U, hUdef⟩ : ∃ U : Finset V, ∀ u, u ∈ U ↔ ∃ x : V → ℝ,
          (∀ w, (¬ ∃ p : G.Walk u w, p.length ≤ r₁ + q * r₁) → x w = 0) ∧
            lam * (x ⬝ᵥ x) < x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) :=
        ⟨Finset.univ.filter (fun u => ∃ x : V → ℝ,
          (∀ w, (¬ ∃ p : G.Walk u w, p.length ≤ r₁ + q * r₁) → x w = 0) ∧
            lam * (x ⬝ᵥ x) < x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)),
          fun u => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))⟩
      obtain ⟨u₀, hu₀⟩ := L_mult_U G lam (r₁ + q * r₁) hconn hP2 U (fun u hu => (hUdef u).1 hu)
      have hUcard : (U.card : ℝ) ≤ ((Δ : ℝ) + 1) ^ (2 * (r₁ + q * r₁) + 1) :=
        L_mult_ball G Δ hdeg u₀ _ U hu₀
      obtain ⟨H, hH⟩ : ∃ H : SimpleGraph V, ∀ a b, H.Adj a b ↔ G.Adj a b ∧ a ∉ N ∪ U ∧ b ∉ N ∪ U :=
        ⟨{ Adj := fun a b => G.Adj a b ∧ a ∉ N ∪ U ∧ b ∉ N ∪ U
           symm := fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩
           loopless := fun a h => G.loopless a h.1 }, fun a b => Iff.rfl⟩
      have hdel := L_mult_delete G H lam (N ∪ U) hH
      have htr := L_mult_trace H lam (q * r₁)
      have hpow : lam ^ (2 * (q * r₁)) = (lam ^ (2 * r₁)) ^ q := by
        rw [← pow_mul]; ring_nf
      have hqr : 1 ≤ 2 * (q * r₁) :=
        le_trans (Nat.mul_pos hq1 hr₁) (Nat.le_mul_of_pos_left _ (by norm_num))
      have hUv : ∀ v, v ∉ U → ∀ x : V → ℝ,
          (∀ w, (¬ ∃ p : G.Walk v w, p.length ≤ r₁ + q * r₁) → x w = 0) →
            x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x) := by
        intro v hv x hx
        by_contra hcon
        exact hv ((hUdef v).2 ⟨x, hx, lt_of_not_ge hcon⟩)
      have hloc : ∀ v, (H.adjMatrix ℝ ^ (2 * (q * r₁))) v v ≤ (lam ^ (2 * r₁)) ^ q * y ^ q := by
        intro v
        by_cases hv : v ∈ N ∪ U
        · have hiso : ∀ w, ¬ H.Adj v w := fun w h => ((hH v w).1 h).2.1 hv
          rw [L_mult_isolated H v hiso (2 * (q * r₁)) hqr]
          positivity
        · obtain ⟨hs1, hb⟩ := L_mult_local G H lam hlam r₁ q hr₁ N U hN hUv hH v hv
          calc _ ≤ (lam ^ (2 * r₁) - 1) ^ q := hb
            _ = (lam ^ (2 * r₁)) ^ q * y ^ q := by rw [hyprop hs1, mul_pow]
      have hsum : ∑ v, (H.adjMatrix ℝ ^ (2 * (q * r₁))) v v ≤
          (Fintype.card V : ℝ) * ((lam ^ (2 * r₁)) ^ q * y ^ q) := by
        calc ∑ v, (H.adjMatrix ℝ ^ (2 * (q * r₁))) v v
            ≤ ∑ _v : V, (lam ^ (2 * r₁)) ^ q * y ^ q := Finset.sum_le_sum (fun v _ => hloc v)
          _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hsq : 0 < (lam ^ (2 * r₁)) ^ q := pow_pos hs q
      have hmH : (Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (H.adjMatrix ℝ - lam • (1 : Matrix V V ℝ)))) : ℝ) ≤
            (Fintype.card V : ℝ) * y ^ q := by
        rw [hpow] at htr
        have h2 : (Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' (H.adjMatrix ℝ - lam • (1 : Matrix V V ℝ)))) : ℝ) * (lam ^ (2 * r₁)) ^ q ≤
              ((Fintype.card V : ℝ) * y ^ q) * (lam ^ (2 * r₁)) ^ q := by
          have := le_trans htr hsum
          linarith
        exact le_of_mul_le_mul_right h2 hsq
      have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      have hNb : (Fintype.card V : ℝ) / ((r₁ : ℝ) + 1) ≤ ε / 2 * Fintype.card V := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : 2 / ε ≤ (r₁ : ℝ) + 1 := by linarith
        have h2 : 1 ≤ ε / 2 * ((r₁ : ℝ) + 1) := by
          rw [div_le_iff₀ hε] at h1
          linarith
        nlinarith
      have hS : ((N ∪ U).card : ℝ) ≤ N.card + U.card := by exact_mod_cast Finset.card_union_le N U
      have hyq : (Fintype.card V : ℝ) * y ^ q ≤ (Fintype.card V : ℝ) * (ε / 2) :=
        mul_le_mul_of_nonneg_left hq hn0
      linarith
  open Matrix in
  have L_case2_ker_le_codim : ∀ {n : ℕ} (K L : Submodule ℝ (Fin n → ℝ))
      (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ)
      (h : K ⊓ LinearMap.ker φ ≤ L), Module.finrank ℝ K ≤ 1 + Module.finrank ℝ L :=
    fun {n : ℕ} (K L : Submodule ℝ (Fin n → ℝ))
        (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ)
        (h : K ⊓ LinearMap.ker φ ≤ L) => by
      have h1 : Module.finrank ℝ ↥(K ⊓ LinearMap.ker φ) ≤ Module.finrank ℝ ↥L :=
        Submodule.finrank_mono h
      have h2 := Submodule.finrank_sup_add_finrank_inf_eq K (LinearMap.ker φ)
      have h3 : Module.finrank ℝ ↥(K ⊔ LinearMap.ker φ) ≤ n := by
        have := Submodule.finrank_le (K ⊔ LinearMap.ker φ)
        simpa using this
      have h4 : n ≤ Module.finrank ℝ ↥(LinearMap.ker φ) + 1 := by
        have h6 := LinearMap.finrank_range_add_finrank_ker φ
        have h5 : Module.finrank ℝ ↥(LinearMap.range φ) ≤ 1 := by
          have := Submodule.finrank_le (LinearMap.range φ)
          simpa using this
        simp only [Module.finrank_fin_fun] at h6
        omega
      omega
  open Matrix in
  have L_case2_ker_le_mem : ∀ {n : ℕ} (lam : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
      (hx : (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A
        + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x = 0)
      (hs : ∑ i, x i = 0), (A - lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x = 0 :=
    fun {n : ℕ} (lam : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
        (hx : (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - A
          + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x = 0)
        (hs : ∑ i, x i = 0) => by
      have hJ : (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x = 0 := by
        funext i
        simp [Matrix.mulVec, dotProduct, hs]
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, hJ, Matrix.one_mulVec, smul_zero, add_zero] at hx
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [sub_eq_zero] at hx ⊢
      exact hx.symm
  open Matrix in
  have L_case2_ker_le : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin n) (Fin n) ℝ)
            - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))))) ≤
        1 + Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)))) :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] => by
      let φ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun x => ∑ i, x i
          map_add' := fun x y => by simp [Finset.sum_add_distrib]
          map_smul' := fun c x => by simp [Finset.mul_sum] }
      apply L_case2_ker_le_codim _ _ φ
      intro x hx
      rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, Matrix.toLin'_apply] at hx
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      exact L_case2_ker_le_mem lam (G.adjMatrix ℝ) x hx.1 hx.2
  open Matrix in
  have L_case2_restrict : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (s : Set (Fin n)) [Fintype s] [DecidableRel (G.induce s).Adj]
      (hvan : ∀ y : Fin n → ℝ, (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y = 0 →
        ∀ i, i ∉ s → y i = 0), Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)))) ≤
        Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' ((G.induce s).adjMatrix ℝ - lam • (1 : Matrix s s ℝ)))) :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (s : Set (Fin n)) [Fintype s] [DecidableRel (G.induce s).Adj]
        (hvan : ∀ y : Fin n → ℝ, (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y = 0 →
          ∀ i, i ∉ s → y i = 0) => by
      let R : (Fin n → ℝ) →ₗ[ℝ] (s → ℝ) := LinearMap.funLeft ℝ ℝ Subtype.val
      have hR : ∀ y : Fin n → ℝ, ∀ j : s, R y j = y j.1 := fun y j => rfl
      have hmem : ∀ y ∈ LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ))),
          R y ∈ LinearMap.ker (Matrix.toLin' ((G.induce s).adjMatrix ℝ - lam • (1 : Matrix s s ℝ))) := by
        intro y hy
        rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy ⊢
        have hv := hvan y hy
        funext i
        have h1 := congrFun hy i.1
        have key : ((G.induce s).adjMatrix ℝ *ᵥ R y) i = (G.adjMatrix ℝ *ᵥ y) i.1 := by
          simp only [Matrix.mulVec, dotProduct]
          symm
          rw [← Finset.sum_subset (Finset.subset_univ s.toFinset)]
          · rw [Finset.sum_subtype s.toFinset (fun x => Set.mem_toFinset)]
            apply Finset.sum_congr rfl
            intro j _
            rw [hR]
            congr 1
            simp only [SimpleGraph.adjMatrix_apply]
            by_cases hij : G.Adj i.1 j.1
            · have hij' : (G.induce s).Adj i j := by simpa using hij
              rw [if_pos hij, if_pos hij']
            · have hij' : ¬ (G.induce s).Adj i j := by simpa using hij
              rw [if_neg hij, if_neg hij']
          · intro j _ hj
            rw [hv j (by simpa using hj), mul_zero]
        simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
          Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h1 ⊢
        rw [key, hR]
        exact h1
      let f := (R.comp (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)))).subtype).codRestrict
        (LinearMap.ker (Matrix.toLin' ((G.induce s).adjMatrix ℝ - lam • (1 : Matrix s s ℝ))))
        (fun y => hmem y.1 y.2)
      apply LinearMap.finrank_le_finrank_of_injective (f := f)
      intro y z hyz
      have hyz' : ∀ j : s, y.1 j.1 = z.1 j.1 := by
        intro j
        have h2 := congrFun (congrArg Subtype.val hyz) j
        simpa [f, hR] using h2
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ s
      · exact hyz' ⟨j, hj⟩
      · have hy := y.2
        have hz := z.2
        rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy hz
        rw [hvan _ hy j hj, hvan _ hz j hj]
  open Matrix in
  have L_case2_P2_sum_ext : ∀ {n : ℕ} (s : Set (Fin n)) [Fintype s] (f : Fin n → ℝ)
      (hf : ∀ i, i ∉ s → f i = 0), ∑ i : Fin n, f i = ∑ i : s, f i.1 :=
    fun {n : ℕ} (s : Set (Fin n)) [Fintype s] (f : Fin n → ℝ)
        (hf : ∀ i, i ∉ s → f i = 0) => by
      rw [← Finset.sum_subtype s.toFinset (fun x => Set.mem_toFinset) f]
      exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hf i (by simpa using hi))).symm
  open Matrix in
  have L_case2_P2 : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
            + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x))
      (s : Set (Fin n)) [Fintype s] [DecidableRel (G.induce s).Adj], ∀ x y : s → ℝ, ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
          (a • x + b • y) ⬝ᵥ ((G.induce s).adjMatrix ℝ *ᵥ (a • x + b • y)) ≤
            lam * ((a • x + b • y) ⬝ᵥ (a • x + b • y)) :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
              + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x))
        (s : Set (Fin n)) [Fintype s] [DecidableRel (G.induce s).Adj] => by
      intro x y
      classical
      obtain ⟨a, b, hab, hsum⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∑ j, (a • x + b • y) j = 0 := by
        by_cases h : ∑ j, y j = 0
        · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
          simp [h]
        · refine ⟨∑ j, y j, -∑ j, x j, Or.inl h, ?_⟩
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum]
          ring
      refine ⟨a, b, hab, ?_⟩
      generalize a • x + b • y = z at hsum ⊢
      obtain ⟨z', hz'1, hz'0⟩ : ∃ z' : Fin n → ℝ, (∀ i : s, z' i.1 = z i) ∧
          (∀ i, i ∉ s → z' i = 0) := by
        refine ⟨fun i => if h : i ∈ s then z ⟨i, h⟩ else 0, ?_, ?_⟩
        · intro i; simp [i.2]
        · intro i hi; simp [hi]
      have hsum' : ∑ i, z' i = 0 := by
        rw [L_case2_P2_sum_ext s z' hz'0]; simp only [hz'1]; exact hsum
      have hdot : z' ⬝ᵥ z' = z ⬝ᵥ z := by
        unfold dotProduct
        rw [L_case2_P2_sum_ext s _ (fun i hi => by simp [hz'0 i hi])]
        simp only [hz'1]
      have hA : z' ⬝ᵥ (G.adjMatrix ℝ *ᵥ z') = z ⬝ᵥ ((G.induce s).adjMatrix ℝ *ᵥ z) := by
        unfold dotProduct
        rw [L_case2_P2_sum_ext s _ (fun i hi => by simp [hz'0 i hi])]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hz'1 i]
        congr 1
        simp only [Matrix.mulVec, dotProduct]
        rw [L_case2_P2_sum_ext s _ (fun j hj => by simp [hz'0 j hj])]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hz'1 j]
        congr 1
        simp [SimpleGraph.adjMatrix_apply]
      have hJ : (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) *ᵥ z' = 0 := by
        funext i
        simp [Matrix.mulVec, dotProduct, hsum']
      have key : z' ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
              + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ z') =
            lam * (z' ⬝ᵥ z') - z' ⬝ᵥ (G.adjMatrix ℝ *ᵥ z') := by
        rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
          Matrix.smul_mulVec, hJ, Matrix.one_mulVec]
        simp [dotProduct_sub, dotProduct_smul]
      have h := hpsd z'
      rw [key, hdot, hA] at h
      linarith
  open Matrix in
  have L_case2_cross : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (u w : Fin n → ℝ)
      (hsep : ∀ i j, u i ≠ 0 → w j ≠ 0 → G.connectedComponentMk i ≠ G.connectedComponentMk j), u ⬝ᵥ (G.adjMatrix ℝ *ᵥ w) = 0 ∧ u ⬝ᵥ w = 0 :=
    fun (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (u w : Fin n → ℝ)
        (hsep : ∀ i j, u i ≠ 0 → w j ≠ 0 → G.connectedComponentMk i ≠ G.connectedComponentMk j) => by
      constructor
      · simp only [dotProduct, Matrix.mulVec]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        by_cases hu : u i = 0
        · simp [hu]
        by_cases hw : w j = 0
        · simp [hw]
        have hne := hsep i j hu hw
        have hadj : ¬ G.Adj i j := fun h =>
          hne (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h)
        simp [SimpleGraph.adjMatrix_apply, hadj]
      · simp only [dotProduct]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        by_cases hu : u i = 0
        · simp [hu]
        by_cases hw : w i = 0
        · simp [hw]
        exact absurd rfl (hsep i i hu hw)
  open Matrix in
  have L_case2_K : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
            + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x))
      (u w : Fin n → ℝ)
      (hsep : ∀ i j, u i ≠ 0 → w j ≠ 0 → G.connectedComponentMk i ≠ G.connectedComponentMk j)
      (hu : lam * (u ⬝ᵥ u) < u ⬝ᵥ (G.adjMatrix ℝ *ᵥ u))
      (hw : lam * (w ⬝ᵥ w) ≤ w ⬝ᵥ (G.adjMatrix ℝ *ᵥ w))
      (hsw : ∑ j, w j ≠ 0), False :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
              + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x))
        (u w : Fin n → ℝ)
        (hsep : ∀ i j, u i ≠ 0 → w j ≠ 0 → G.connectedComponentMk i ≠ G.connectedComponentMk j)
        (hu : lam * (u ⬝ᵥ u) < u ⬝ᵥ (G.adjMatrix ℝ *ᵥ u))
        (hw : lam * (w ⬝ᵥ w) ≤ w ⬝ᵥ (G.adjMatrix ℝ *ᵥ w))
        (hsw : ∑ j, w j ≠ 0) => by
      have hsep' : ∀ i j, w i ≠ 0 → u j ≠ 0 → G.connectedComponentMk i ≠ G.connectedComponentMk j :=
        fun i j h1 h2 => (hsep j i h2 h1).symm
      obtain ⟨h1, h2⟩ := L_case2_cross n G u w hsep
      obtain ⟨h3, h4⟩ := L_case2_cross n G w u hsep'
      set a := ∑ j, w j with ha
      set b := ∑ j, u j with hb
      have hJz : (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix (Fin n) (Fin n) ℝ) *ᵥ (a • u - b • w) = 0 := by
        ext i
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Pi.zero_apply]
        rw [← ha, ← hb]
        ring
      have hz := hpsd (a • u - b • w)
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, hJz, smul_zero, add_zero] at hz
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, h1, h2, h3, h4] at hz
      have ha2 : 0 < a * a := mul_self_pos.mpr hsw
      have e1 := mul_pos ha2 (sub_pos.mpr hu)
      have e2 := mul_nonneg (mul_self_nonneg b) (sub_nonneg.mpr hw)
      nlinarith [e1, e2]
  open Matrix in
  have L_case2_decomp : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (u v : Fin n → ℝ)
      (hsep : ∀ i j, u i ≠ 0 → v j ≠ 0 → G.connectedComponentMk i ≠ G.connectedComponentMk j)
      (h : lam * ((u + v) ⬝ᵥ (u + v)) < (u + v) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (u + v))), lam * (u ⬝ᵥ u) < u ⬝ᵥ (G.adjMatrix ℝ *ᵥ u) ∨
        lam * (v ⬝ᵥ v) < v ⬝ᵥ (G.adjMatrix ℝ *ᵥ v) :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (u v : Fin n → ℝ)
        (hsep : ∀ i j, u i ≠ 0 → v j ≠ 0 → G.connectedComponentMk i ≠ G.connectedComponentMk j)
        (h : lam * ((u + v) ⬝ᵥ (u + v)) < (u + v) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (u + v))) => by
      have hsep' : ∀ i j, v i ≠ 0 → u j ≠ 0 → G.connectedComponentMk i ≠ G.connectedComponentMk j :=
        fun i j h1 h2 => (hsep j i h2 h1).symm
      obtain ⟨h1, h2⟩ := L_case2_cross n G u v hsep
      obtain ⟨h3, h4⟩ := L_case2_cross n G v u hsep'
      simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, h1, h2, h3, h4] at h
      by_contra hc
      push_neg at hc
      linarith [hc.1, hc.2]
  open Matrix in
  have L_case2_eig : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      [DecidableEq G.ConnectedComponent] (y : Fin n → ℝ) (hy : (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y = 0)
      (c : G.ConnectedComponent), lam * ((fun i => if G.connectedComponentMk i = c then y i else 0) ⬝ᵥ
          (fun i => if G.connectedComponentMk i = c then y i else 0)) ≤
        (fun i => if G.connectedComponentMk i = c then y i else 0) ⬝ᵥ
          (G.adjMatrix ℝ *ᵥ (fun i => if G.connectedComponentMk i = c then y i else 0)) :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        [DecidableEq G.ConnectedComponent] (y : Fin n → ℝ) (hy : (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y = 0)
        (c : G.ConnectedComponent) => by
      set u : Fin n → ℝ := fun i => if G.connectedComponentMk i = c then y i else 0 with hu
      set v : Fin n → ℝ := fun i => if G.connectedComponentMk i = c then 0 else y i with hv
      have huv : y = u + v := by
        ext i
        simp only [hu, hv, Pi.add_apply]
        split_ifs <;> simp
      have hsep : ∀ i j, u i ≠ 0 → v j ≠ 0 →
          G.connectedComponentMk i ≠ G.connectedComponentMk j := by
        intro i j hi hj
        have h1 : G.connectedComponentMk i = c := by
          by_contra h
          exact hi (by simp [hu, h])
        have h2 : G.connectedComponentMk j ≠ c := by
          intro h
          exact hj (by simp [hv, h])
        rw [h1]
        exact fun h => h2 h.symm
      obtain ⟨h1, h2⟩ := L_case2_cross n G u v hsep
      have hAy : G.adjMatrix ℝ *ᵥ y = lam • y := by
        rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at hy
        exact hy
      have e1 : u ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) = u ⬝ᵥ (G.adjMatrix ℝ *ᵥ u) := by
        rw [huv, Matrix.mulVec_add, dotProduct_add, h1, add_zero]
      have e2 : u ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) = lam * (u ⬝ᵥ u) := by
        rw [hAy, dotProduct_smul, smul_eq_mul, huv, dotProduct_add, h2, add_zero]
      linarith
  open Matrix in
  have L_case2_abs : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (u : Fin n → ℝ) (h : lam * (u ⬝ᵥ u) ≤ u ⬝ᵥ (G.adjMatrix ℝ *ᵥ u)), lam * ((fun i => |u i|) ⬝ᵥ (fun i => |u i|)) ≤
        (fun i => |u i|) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (fun i => |u i|)) :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (u : Fin n → ℝ) (h : lam * (u ⬝ᵥ u) ≤ u ⬝ᵥ (G.adjMatrix ℝ *ᵥ u)) => by
      have e1 : (fun i => |u i|) ⬝ᵥ (fun i => |u i|) = u ⬝ᵥ u := by
        simp only [dotProduct, abs_mul_abs_self]
      have e2 : u ⬝ᵥ (G.adjMatrix ℝ *ᵥ u) ≤
          (fun i => |u i|) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (fun i => |u i|)) := by
        simp only [dotProduct, Matrix.mulVec]
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hA : 0 ≤ G.adjMatrix ℝ i j := by
          rw [SimpleGraph.adjMatrix_apply]
          split_ifs <;> norm_num
        calc u i * (G.adjMatrix ℝ i j * u j) ≤ |u i * (G.adjMatrix ℝ i j * u j)| := le_abs_self _
          _ = |u i| * (G.adjMatrix ℝ i j * |u j|) := by rw [abs_mul, abs_mul, abs_of_nonneg hA]
      rw [e1]
      linarith
  open Matrix in
  have L_case2_witness : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      [DecidableEq G.ConnectedComponent] (y : Fin n → ℝ) (hy : (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y = 0)
      (i : Fin n) (hi : y i ≠ 0), ∃ w : Fin n → ℝ, (∀ j, w j ≠ 0 → G.connectedComponentMk j = G.connectedComponentMk i) ∧
        lam * (w ⬝ᵥ w) ≤ w ⬝ᵥ (G.adjMatrix ℝ *ᵥ w) ∧ ∑ j, w j ≠ 0 :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        [DecidableEq G.ConnectedComponent] (y : Fin n → ℝ) (hy : (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y = 0)
        (i : Fin n) (hi : y i ≠ 0) => by
      have h := L_case2_abs lam n G _ (L_case2_eig lam n G y hy (G.connectedComponentMk i))
      refine ⟨fun j => |(fun i' => if G.connectedComponentMk i' = G.connectedComponentMk i
        then y i' else 0) j|, ?_, h, ?_⟩
      · intro j hj
        by_contra hne
        exact hj (by simp [hne])
      · have hwi : (fun j => |(fun i' => if G.connectedComponentMk i' = G.connectedComponentMk i
            then y i' else 0) j|) i = |y i| := by simp
        have hle := Finset.single_le_sum (f := fun j => |(fun i' => if G.connectedComponentMk i' =
            G.connectedComponentMk i then y i' else 0) j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)
        have hpos : 0 < |y i| := abs_pos.mpr hi
        exact (lt_of_lt_of_le (hwi ▸ hpos) hle).ne'
  open Matrix in
  have L_case2_top_component : ∀ (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
            + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x))
      (hx : ∃ x : Fin n → ℝ, lam * (x ⬝ᵥ x) < x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)), ∃ c : G.ConnectedComponent, ∀ y : Fin n → ℝ,
        (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y = 0 →
        ∀ i, i ∉ c.supp → y i = 0 :=
    fun (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
              + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x))
        (hx : ∃ x : Fin n → ℝ, lam * (x ⬝ᵥ x) < x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)) => by
      classical
      obtain ⟨x, hx⟩ := hx
      by_cases hex : ∃ y : Fin n → ℝ,
          (G.adjMatrix ℝ - lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ y = 0 ∧ ∃ i, y i ≠ 0
      · obtain ⟨y₀, hy₀, i₀, hi₀⟩ := hex
        refine ⟨G.connectedComponentMk i₀, ?_⟩
        intro y hy i hi
        by_contra hyi
        have hcc : G.connectedComponentMk i ≠ G.connectedComponentMk i₀ := fun h =>
          hi (by rw [SimpleGraph.ConnectedComponent.mem_supp_iff]; exact h)
        obtain ⟨w, hw1, hw2, hw3⟩ := L_case2_witness lam n G y hy i hyi
        obtain ⟨w₀, hw₀1, hw₀2, hw₀3⟩ := L_case2_witness lam n G y₀ hy₀ i₀ hi₀
        set c := G.connectedComponentMk i₀ with hc
        have hxs : x = (fun j => if G.connectedComponentMk j = c then x j else 0) +
            (fun j => if G.connectedComponentMk j = c then 0 else x j) := by
          ext j
          simp only [Pi.add_apply]
          split_ifs <;> simp
        rw [hxs] at hx
        have hsep0 : ∀ a b, (fun j => if G.connectedComponentMk j = c then x j else 0) a ≠ 0 →
            (fun j => if G.connectedComponentMk j = c then 0 else x j) b ≠ 0 →
            G.connectedComponentMk a ≠ G.connectedComponentMk b := by
          intro a b ha hb
          have h1 : G.connectedComponentMk a = c := by
            by_contra h
            exact ha (by simp [h])
          have h2 : G.connectedComponentMk b ≠ c := by
            intro h
            exact hb (by simp [h])
          rw [h1]
          exact fun h => h2 h.symm
        rcases L_case2_decomp lam n G _ _ hsep0 hx with h | h
        · refine L_case2_K lam n G hpsd _ w ?_ h hw2 hw3
          intro a b ha hb
          have h1 : G.connectedComponentMk a = c := by
            by_contra h
            exact ha (by simp [h])
          rw [h1, hw1 b hb]
          exact fun h => hcc h.symm
        · refine L_case2_K lam n G hpsd _ w₀ ?_ h hw₀2 hw₀3
          intro a b ha hb
          have h1 : G.connectedComponentMk a ≠ c := by
            intro h
            exact ha (by simp [h])
          rw [hw₀1 b hb]
          exact h1
      · push_neg at hex
        have hx0 : x ≠ 0 := by
          rintro rfl
          simp at hx
        obtain ⟨i, -⟩ := Function.ne_iff.mp hx0
        exact ⟨G.connectedComponentMk i, fun y hy j _ => hex y hy j⟩
  open Matrix in
  have L_case2_deg : ∀ (Δ n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hdeg : ∀ i, (Finset.univ.filter (G.Adj i)).card ≤ Δ)
      (s : Set (Fin n)) [Fintype s] [DecidableRel (G.induce s).Adj], ∀ v : s, (Finset.univ.filter ((G.induce s).Adj v)).card ≤ Δ :=
    fun (Δ n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (hdeg : ∀ i, (Finset.univ.filter (G.Adj i)).card ≤ Δ)
        (s : Set (Fin n)) [Fintype s] [DecidableRel (G.induce s).Adj] => by
      intro v
      refine le_trans ?_ (hdeg v.1)
      have : (Finset.univ.filter ((G.induce s).Adj v)).map (Function.Embedding.subtype _) ⊆
          Finset.univ.filter (G.Adj v.1) := by
        intro j hj
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coe_subtype] at hj ⊢
        obtain ⟨w, hw, rfl⟩ := hj
        simpa [SimpleGraph.comap_adj] using hw
      simpa using Finset.card_le_card this
  open Matrix in
  have L_case2 : ∀ (lam : ℝ) (hlam : 0 < lam) (Δ : ℕ) (ε : ℝ) (hε : 0 < ε), ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ i, (Finset.univ.filter (G.Adj i)).card ≤ Δ) →
        (∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((lam • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
            + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x)) →
        (∃ x : Fin n → ℝ, lam * (x ⬝ᵥ x) < x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)) →
        (Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin n) (Fin n) ℝ)
            - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))))) : ℝ) ≤ ε * n + C :=
    fun (lam : ℝ) (hlam : 0 < lam) (Δ : ℕ) (ε : ℝ) (hε : 0 < ε) => by
      obtain ⟨C, hC⟩ := L_mult lam hlam Δ ε hε
      refine ⟨1 + C, ?_⟩
      intro n G _ hdeg hpsd hx
      classical
      obtain ⟨c, hc⟩ := L_case2_top_component lam n G hpsd hx
      have h1 := L_case2_ker_le lam n G
      have h2 := L_case2_restrict lam n G c.supp hc
      have hconn : (G.induce c.supp).Connected := c.connected_toSimpleGraph
      have h3 := hC c.supp (G.induce c.supp) hconn (L_case2_deg Δ n G hdeg c.supp)
        (L_case2_P2 lam n G hpsd c.supp)
      have hcard : (Fintype.card c.supp : ℝ) ≤ n := by
        have := Fintype.card_subtype_le (fun i : Fin n => i ∈ c.supp)
        simp only [Fintype.card_fin] at this
        exact_mod_cast (le_of_eq_of_le (Fintype.card_congr (Equiv.refl _)) this)
      have h12 : (Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin n) (Fin n) ℝ)
              - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))))) : ℝ) ≤
          1 + (Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((G.induce c.supp).adjMatrix ℝ - lam • (1 : Matrix c.supp c.supp ℝ)))) : ℝ) := by
        exact_mod_cast h1.trans (Nat.add_le_add_left h2 1)
      have : ε * (Fintype.card c.supp : ℝ) ≤ ε * n := mul_le_mul_of_nonneg_left hcard hε.le
      linarith
  open Matrix in
  have L_construct : ∀ (lam : ℝ) (hlam : 0 < lam) (k₀ : ℕ) (H : SimpleGraph (Fin k₀))
      [DecidableRel H.Adj]
      (hH1 : ∀ x : Fin k₀ → ℝ, x ⬝ᵥ (H.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x))
      (hH2 : ∃ x : Fin k₀ → ℝ, x ≠ 0 ∧ H.adjMatrix ℝ *ᵥ x = lam • x) (m r : ℕ), ∃ (G : SimpleGraph (Fin (m * k₀ + r))) (_ : DecidableRel G.Adj),
        (∀ x : Fin (m * k₀ + r) → ℝ, 0 ≤ x ⬝ᵥ ((lam • (1 : Matrix (Fin (m * k₀ + r)) (Fin (m * k₀ + r)) ℝ)
            - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x)) ∧
        m * k₀ + r ≤ (m * (k₀ - 1) + r + 1) + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
            (lam • (1 : Matrix (Fin (m * k₀ + r)) (Fin (m * k₀ + r)) ℝ)
            - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))))) :=
    fun (lam : ℝ) (hlam : 0 < lam) (k₀ : ℕ) (H : SimpleGraph (Fin k₀))
        [DecidableRel H.Adj]
        (hH1 : ∀ x : Fin k₀ → ℝ, x ⬝ᵥ (H.adjMatrix ℝ *ᵥ x) ≤ lam * (x ⬝ᵥ x))
        (hH2 : ∃ x : Fin k₀ → ℝ, x ≠ 0 ∧ H.adjMatrix ℝ *ᵥ x = lam • x) (m r : ℕ) => by
      classical
      obtain ⟨u, hu0, hu⟩ := hH2
      have hk : 1 ≤ k₀ := by
        rcases Nat.eq_zero_or_pos k₀ with h | h
        · subst h; exact absurd (funext fun i => i.elim0) hu0
        · exact h
      have key : ∀ M K R F : ℕ, 1 ≤ K → M ≤ F + 1 → M * K + R ≤ M * (K - 1) + R + 1 + F := by
        intro M K R F hK hM
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
        rw [Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]; omega
      let e : (Fin m × Fin k₀ ⊕ Fin r) ≃ Fin (m * k₀ + r) :=
        (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv
      let G' : SimpleGraph (Fin m × Fin k₀ ⊕ Fin r) :=
        { Adj := fun p q => Sum.elim (fun ab => Sum.elim (fun cd => ab.1 = cd.1 ∧ H.Adj ab.2 cd.2)
              (fun _ => False) q) (fun _ => False) p
          symm := by
            intro p q h
            rcases p with ⟨a, b⟩ | s <;> rcases q with ⟨c, d⟩ | t <;> simp at h ⊢
            exact ⟨h.1.symm, h.2.symm⟩
          loopless := by
            intro p h
            rcases p with ⟨a, b⟩ | s <;> simp at h }
      let G : SimpleGraph (Fin (m * k₀ + r)) := G'.comap e.symm
      letI inst : DecidableRel G.Adj := Classical.decRel _
      have hAe : ∀ a b c d, G.adjMatrix ℝ (e (Sum.inl (a, b))) (e (Sum.inl (c, d)))
          = if a = c then H.adjMatrix ℝ b d else 0 := by
        intro a b c d
        rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
        by_cases h1 : a = c <;> by_cases h2 : H.Adj b d <;> simp [G, G', h1, h2]
      have hAe2 : ∀ p s, G.adjMatrix ℝ (e p) (e (Sum.inr s)) = 0 := by
        intro p s
        rw [SimpleGraph.adjMatrix_apply]
        rcases p with ⟨a, b⟩ | t <;> simp [G, G']
      have hAe3 : ∀ s q, G.adjMatrix ℝ (e (Sum.inr s)) (e q) = 0 := by
        intro s q
        rw [SimpleGraph.adjMatrix_apply]
        rcases q with ⟨a, b⟩ | t <;> simp [G, G']
      have hrow1 : ∀ (x : Fin (m * k₀ + r) → ℝ) a b, (G.adjMatrix ℝ *ᵥ x) (e (Sum.inl (a, b)))
          = ∑ d, H.adjMatrix ℝ b d * x (e (Sum.inl (a, d))) := by
        intro x a b
        simp only [mulVec, dotProduct]
        rw [← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
        simp only [hAe, hAe2, zero_mul, Finset.sum_const_zero, add_zero]
        rw [Finset.sum_eq_single a]
        · simp
        · intro c _ hc; simp [Ne.symm hc]
        · simp
      have hrow2 : ∀ (x : Fin (m * k₀ + r) → ℝ) s, (G.adjMatrix ℝ *ᵥ x) (e (Sum.inr s)) = 0 := by
        intro x s
        simp only [mulVec, dotProduct]
        rw [← e.sum_comp]
        simp only [hAe3, zero_mul, Finset.sum_const_zero]
      have hJ : ∀ x : Fin (m * k₀ + r) → ℝ, (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix (Fin (m * k₀ + r)) (Fin (m * k₀ + r)) ℝ) *ᵥ x = fun _ => ∑ j, x j := by
        intro x; ext i; simp [mulVec, dotProduct]
      have hquad : ∀ x : Fin (m * k₀ + r) → ℝ, x ⬝ᵥ ((lam • (1 : Matrix (Fin (m * k₀ + r)) (Fin (m * k₀ + r)) ℝ)
              - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x)
            = lam * (x ⬝ᵥ x) - x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) + (1 / 2) * (∑ i, x i) ^ 2 := by
        intro x
        simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_sub,
          dotProduct_smul, smul_eq_mul, hJ]
        congr 1
        simp only [dotProduct, ← Finset.sum_mul, sq]
      refine ⟨G, inst, ?_, ?_⟩
      · intro x
        rw [hquad]
        let y : Fin m → Fin k₀ → ℝ := fun a b => x (e (Sum.inl (a, b)))
        have hxx : x ⬝ᵥ x = ∑ a, (y a ⬝ᵥ y a) + ∑ s, x (e (Sum.inr s)) ^ 2 := by
          simp only [dotProduct]
          rw [← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
          simp [y, sq]
        have hxAx : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = ∑ a, (y a ⬝ᵥ (H.adjMatrix ℝ *ᵥ y a)) := by
          conv_lhs => simp only [dotProduct]
          rw [← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
          simp only [hrow1, hrow2, mul_zero, Finset.sum_const_zero, add_zero]
          simp [y, mulVec, dotProduct]
        have h2 : ∑ a, (y a ⬝ᵥ (H.adjMatrix ℝ *ᵥ y a)) ≤ ∑ a, lam * (y a ⬝ᵥ y a) :=
          Finset.sum_le_sum (fun a _ => hH1 (y a))
        rw [← Finset.mul_sum] at h2
        have h3 : 0 ≤ ∑ s, x (e (Sum.inr s)) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        rw [hxx, hxAx]
        nlinarith [sq_nonneg (∑ i, x i), mul_nonneg hlam.le h3]
      · rcases Nat.eq_zero_or_pos m with hm | hm
        · exact key m k₀ r _ hk (by omega)
        · obtain ⟨b0, hb0⟩ : ∃ b0, u b0 ≠ 0 := by
            by_contra hc; push_neg at hc; exact hu0 (funext hc)
          let U : Fin m → Fin (m * k₀ + r) → ℝ := fun c i =>
            Sum.elim (fun ab : Fin m × Fin k₀ => if ab.1 = c then u ab.2 else 0) (fun _ => 0) (e.symm i)
          have hU1 : ∀ c a b, U c (e (Sum.inl (a, b))) = if a = c then u b else 0 := by
            intro c a b; simp only [U, Equiv.symm_apply_apply, Sum.elim_inl]
          have hU2 : ∀ c s, U c (e (Sum.inr s)) = 0 := by
            intro c s; simp only [U, Equiv.symm_apply_apply, Sum.elim_inr]
          have hAU : ∀ c, G.adjMatrix ℝ *ᵥ U c = lam • U c := by
            intro c
            funext i
            obtain ⟨p, rfl⟩ := e.surjective i
            rcases p with ⟨a, b⟩ | s
            · rw [hrow1]
              simp only [hU1, Pi.smul_apply, smul_eq_mul]
              by_cases hac : a = c
              · simp only [hac, if_true]
                have := congrFun hu b
                simpa [mulVec, dotProduct] using this
              · simp [hac]
            · rw [hrow2]; simp [hU2]
          have hsumU : ∀ c, ∑ i, U c i = ∑ b, u b := by
            intro c
            rw [← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
            simp only [hU1, hU2, Finset.sum_const_zero, add_zero]
            rw [Finset.sum_eq_single c]
            · simp
            · intro a _ ha; simp [ha]
            · simp
          let c0 : Fin m := ⟨0, hm⟩
          let cs : Fin (m - 1) → Fin m := fun j => ⟨j.val + 1, by omega⟩
          have hcs : ∀ i j, cs j = cs i ↔ j = i := by
            intro i j; simp [cs, Fin.ext_iff]
          have hcs0 : ∀ j, cs j ≠ c0 := by
            intro j; simp [cs, c0, Fin.ext_iff]
          let w : Fin (m - 1) → Fin (m * k₀ + r) → ℝ := fun j => U (cs j) - U c0
          have hw : ∀ j, w j ∈ LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin (m * k₀ + r)) (Fin (m * k₀ + r)) ℝ)
              - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)))) := by
            intro j
            rw [LinearMap.mem_ker, Matrix.toLin'_apply]
            simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, hJ, w, mulVec_sub, hAU]
            funext i
            simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
              Finset.sum_sub_distrib, hsumU]
            ring
          let v : Fin (m - 1) → LinearMap.ker (Matrix.toLin' (lam • (1 : Matrix (Fin (m * k₀ + r)) (Fin (m * k₀ + r)) ℝ)
              - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)))) := fun j => ⟨w j, hw j⟩
          have hli : LinearIndependent ℝ v := by
            apply LinearIndependent.of_comp (LinearMap.ker _).subtype
            rw [Fintype.linearIndependent_iff]
            intro g hg j
            have := congrFun hg (e (Sum.inl (cs j, b0)))
            simp only [Function.comp_apply, Submodule.subtype_apply, v, w, Finset.sum_apply, Pi.smul_apply,
              Pi.sub_apply, hU1, hcs, if_neg (hcs0 j), sub_zero, smul_eq_mul, Pi.zero_apply, mul_ite, mul_zero,
              Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
            rcases mul_eq_zero.mp this with h | h
            · exact h
            · exact absurd h hb0
          have hcard := hli.fintype_card_le_finrank
          simp only [Fintype.card_fin] at hcard
          exact key m k₀ r _ hk (by omega)
  open Matrix in
  have L_gram_cons_inner : ∀ (m : ℕ) (a b : ℝ) (x y : EuclideanSpace ℝ (Fin m)), inner ℝ (WithLp.toLp 2 (Fin.cons a (WithLp.ofLp x) : Fin (m+1) → ℝ) : EuclideanSpace ℝ (Fin (m+1)))
        (WithLp.toLp 2 (Fin.cons b (WithLp.ofLp y) : Fin (m+1) → ℝ)) = a * b + inner ℝ x y :=
    fun (m : ℕ) (a b : ℝ) (x y : EuclideanSpace ℝ (Fin m)) => by
      rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
  open Matrix in
  have L_gram_quad_expand : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ), y ⬝ᵥ (M *ᵥ y) = ∑ i, ∑ j, y i * M i j * y j :=
    fun (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) => by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  open Matrix in
  have L_gram_symm : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.transpose = M) (i j : Fin n), M i j = M j i :=
    fun (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.transpose = M) (i j : Fin n) => by
      have := congrFun (congrFun hM i) j
      rw [Matrix.transpose_apply] at this
      exact this.symm
  open Matrix in
  have L_gram_quad_cons : ∀ (n : ℕ) (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hM : M.transpose = M)
      (t : ℝ) (y : Fin n → ℝ), (Fin.cons t y : Fin (n+1) → ℝ) ⬝ᵥ (M *ᵥ (Fin.cons t y : Fin (n+1) → ℝ)) =
        M 0 0 * t * t + 2 * t * (∑ j, M 0 j.succ * y j) + ∑ i, ∑ j, y i * M i.succ j.succ * y j :=
    fun (n : ℕ) (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hM : M.transpose = M)
        (t : ℝ) (y : Fin n → ℝ) => by
      have hs := L_gram_symm (n+1) M hM
      rw [L_gram_quad_expand]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have h1 : ∑ x : Fin n, y x * M x.succ 0 * t = t * ∑ j, M 0 j.succ * y j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hs j.succ 0]; ring
      have h2 : ∑ x : Fin n, t * M 0 x.succ * y x = t * ∑ j, M 0 j.succ * y j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [Finset.sum_add_distrib, h1, h2]
      ring
  open Matrix in
  have L_gram_schur_quad : ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (a : ℝ)
      (y : Fin n → ℝ), y ⬝ᵥ ((fun i j => P i j - b i * b j / a : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) =
        (∑ i, ∑ j, y i * P i j * y j) - (∑ j, b j * y j) ^ 2 / a :=
    fun (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (a : ℝ)
        (y : Fin n → ℝ) => by
      rw [L_gram_quad_expand, sq, Finset.sum_mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
  open Matrix in
  have L_gram_chol : ∀ (n : ℕ), ∀ (M : Matrix (Fin n) (Fin n) ℝ), M.transpose = M →
      (∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x)) →
      ∃ m, ∃ v : Fin n → EuclideanSpace ℝ (Fin m), ∀ i j, inner ℝ (v i) (v j) = M i j :=
    fun (n : ℕ) => by
      induction n with
      | zero => intro M _ _; exact ⟨0, fun i => i.elim0, fun i => i.elim0⟩
      | succ n ih =>
        intro M hM hpsd
        have hs := L_gram_symm (n+1) M hM
        have hQ := L_gram_quad_cons n M hM
        have ha : 0 ≤ M 0 0 := by
          have := hpsd (Fin.cons 1 0)
          rw [hQ] at this
          simpa using this
        have hb : M 0 0 = 0 → ∀ j : Fin n, M 0 j.succ = 0 := by
          intro h0 j
          have key : ∀ t : ℝ, 0 ≤ 2 * t * M 0 j.succ + M j.succ j.succ := by
            intro t
            have := hpsd (Fin.cons t (Pi.single j 1))
            rw [hQ, h0] at this
            simpa [Pi.single_apply] using this
          by_contra hne
          have := key (-(M j.succ j.succ + 1) / (2 * M 0 j.succ))
          have e : 2 * (-(M j.succ j.succ + 1) / (2 * M 0 j.succ)) * M 0 j.succ
              = -(M j.succ j.succ + 1) := by
            field_simp
          linarith
        have hCsym : Matrix.transpose (fun i j => M i.succ j.succ - M 0 i.succ * M 0 j.succ / M 0 0 :
            Matrix (Fin n) (Fin n) ℝ) =
            (fun i j => M i.succ j.succ - M 0 i.succ * M 0 j.succ / M 0 0 : Matrix (Fin n) (Fin n) ℝ) := by
          ext i j
          simp only [Matrix.transpose_apply]
          rw [hs j.succ i.succ]; ring
        have hCpsd : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ ((fun i j => M i.succ j.succ - M 0 i.succ * M 0 j.succ / M 0 0 :
            Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
          intro y
          have h1 := hpsd (Fin.cons (-(∑ j, M 0 j.succ * y j) / M 0 0) y)
          rw [hQ] at h1
          rw [L_gram_schur_quad n (fun i j => M i.succ j.succ) (fun j => M 0 j.succ) (M 0 0) y]
          rcases eq_or_lt_of_le ha with h0 | hpos
          · rw [← h0] at h1 ⊢
            simp only [div_zero, mul_zero, zero_mul, zero_add] at h1 ⊢
            linarith
          · have e : M 0 0 * (-(∑ j, M 0 j.succ * y j) / M 0 0) * (-(∑ j, M 0 j.succ * y j) / M 0 0) +
                2 * (-(∑ j, M 0 j.succ * y j) / M 0 0) * (∑ j, M 0 j.succ * y j) =
                -((∑ j, M 0 j.succ * y j) ^ 2 / M 0 0) := by
              field_simp
              ring
            linarith
        obtain ⟨m, w, hw⟩ := ih _ hCsym hCpsd
        refine ⟨m+1, Fin.cons (WithLp.toLp 2 (Fin.cons (Real.sqrt (M 0 0)) (WithLp.ofLp (0 : EuclideanSpace ℝ (Fin m)))))
          (fun i => WithLp.toLp 2 (Fin.cons (M 0 i.succ / Real.sqrt (M 0 0)) (WithLp.ofLp (w i)))), ?_⟩
        have hss : Real.sqrt (M 0 0) * Real.sqrt (M 0 0) = M 0 0 := Real.mul_self_sqrt ha
        have hcross : ∀ j : Fin n, Real.sqrt (M 0 0) * (M 0 j.succ / Real.sqrt (M 0 0)) = M 0 j.succ := by
          intro j
          rcases eq_or_lt_of_le ha with h0 | hpos
          · rw [hb h0.symm j]; simp
          · have : Real.sqrt (M 0 0) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
            field_simp
        intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · simp only [Fin.cons_zero]
          rw [L_gram_cons_inner, inner_zero_left, add_zero, hss]
        · simp only [Fin.cons_zero, Fin.cons_succ]
          rw [L_gram_cons_inner, inner_zero_left, add_zero, hcross]
        · simp only [Fin.cons_zero, Fin.cons_succ]
          rw [L_gram_cons_inner, inner_zero_right, add_zero, mul_comm, hcross, hs]
        · simp only [Fin.cons_succ]
          rw [L_gram_cons_inner, hw, div_mul_div_comm, hss]
          ring
  open Matrix in
  have L_gram_rank_key : ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)) (M : Matrix (Fin n) (Fin n) ℝ)
      (hv : ∀ i j, inner ℝ (v i) (v j) = M i j) (x : Fin n → ℝ), inner ℝ (∑ i, x i • v i) (∑ i, x i • v i) = x ⬝ᵥ (M *ᵥ x) :=
    fun (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)) (M : Matrix (Fin n) (Fin n) ℝ)
        (hv : ∀ i j, inner ℝ (v i) (v j) = M i j) (x : Fin n → ℝ) => by
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hv]
      simp only [dotProduct, mulVec]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
  open Matrix in
  have L_gram_rank : ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)) (M : Matrix (Fin n) (Fin n) ℝ)
      (hv : ∀ i j, inner ℝ (v i) (v j) = M i j), Module.finrank ℝ (Submodule.span ℝ (Set.range v)) + Module.finrank ℝ (LinearMap.ker (Matrix.toLin' M)) ≤ n :=
    fun (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)) (M : Matrix (Fin n) (Fin n) ℝ)
        (hv : ∀ i j, inner ℝ (v i) (v j) = M i j) => by
      let T : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := Fintype.linearCombination ℝ v
      have hT : ∀ x, T x = ∑ i, x i • v i := fun x => by
        simp only [T, Fintype.linearCombination_apply]
      have h1 : Submodule.span ℝ (Set.range v) ≤ LinearMap.range T := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine ⟨Pi.single i 1, ?_⟩
        rw [hT]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [hj]
        · intro h
          exact absurd (Finset.mem_univ i) h
      have h2 : LinearMap.ker (Matrix.toLin' M) ≤ LinearMap.ker T := by
        intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        rw [Matrix.toLin'_apply] at hx
        have key := L_gram_rank_key n m v M hv x
        rw [hx, dotProduct_zero, ← hT] at key
        exact inner_self_eq_zero.mp key
      have h3 := LinearMap.finrank_range_add_finrank_ker T
      rw [Module.finrank_fin_fun] at h3
      have h4 := Submodule.finrank_mono h1
      have h5 := Submodule.finrank_mono h2
      omega
  open Matrix in
  have L_gram_compress : ∀ (n m d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m))
      (h : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ d), ∃ u : Fin n → EuclideanSpace ℝ (Fin d), ∀ i j, inner ℝ (u i) (u j) = inner ℝ (v i) (v j) :=
    fun (n m d : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m))
        (h : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ d) => by
      have hv : ∀ i, v i ∈ Submodule.span ℝ (Set.range v) := fun i => Submodule.subset_span ⟨i, rfl⟩
      have he : Orthonormal ℝ (fun t : Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range v))) =>
          EuclideanSpace.single (Fin.castLE h t) (1:ℝ)) := by
        have := (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp _ (Fin.castLE_injective h)
        convert this using 1
        funext t
        simp
      refine ⟨fun i => ∑ t, ((stdOrthonormalBasis ℝ (Submodule.span ℝ (Set.range v))).repr
          ⟨v i, hv i⟩ t) • EuclideanSpace.single (Fin.castLE h t) (1:ℝ), fun i j => ?_⟩
      rw [he.inner_sum]
      have h1 : inner ℝ (v i) (v j) = inner ℝ ((⟨v i, hv i⟩ : Submodule.span ℝ (Set.range v)))
          (⟨v j, hv j⟩ : Submodule.span ℝ (Set.range v)) := by
        rw [Submodule.coe_inner]
      rw [h1, ← LinearIsometryEquiv.inner_map_map
        (stdOrthonormalBasis ℝ (Submodule.span ℝ (Set.range v))).repr, PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp [mul_comm]
  open Matrix in
  have L_gram : ∀ (n d : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.transpose = M)
      (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x))
      (hrank : n ≤ d + Module.finrank ℝ (LinearMap.ker (Matrix.toLin' M))), ∃ v : Fin n → EuclideanSpace ℝ (Fin d), ∀ i j, inner ℝ (v i) (v j) = M i j :=
    fun (n d : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.transpose = M)
        (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x))
        (hrank : n ≤ d + Module.finrank ℝ (LinearMap.ker (Matrix.toLin' M))) => by
      obtain ⟨m, w, hw⟩ := L_gram_chol n M hM hpsd
      have hr := L_gram_rank n m w M hw
      have hd : Module.finrank ℝ (Submodule.span ℝ (Set.range w)) ≤ d := by omega
      obtain ⟨u, hu⟩ := L_gram_compress n m d w hd
      exact ⟨u, fun i j => by rw [hu, hw]⟩
  open Matrix EquiangularLinesFixedAngle in
  have L_lower_fromGraph : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d n : ℕ) (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj]
      (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ)
            - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x))
      (hrank : n ≤ d + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
            (((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ)
            - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)))))), ∃ E : EquiangularLines α d, E.carrier.ncard = n :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d n : ℕ) (G : SimpleGraph (Fin n))
        [DecidableRel G.Adj]
        (hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ)
              - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x))
        (hrank : n ≤ d + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
              (((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ)
              - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)))))) => by
      obtain ⟨hα0, hα1⟩ := hα
      set ML : Matrix (Fin n) (Fin n) ℝ := ((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ)
              - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) with hML
      have h2α : (2 * α) ≠ 0 := by positivity
      have hT : ((2 * α) • ML).transpose = (2 * α) • ML := by
        rw [Matrix.transpose_smul]
        congr 1
        rw [hML, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
          Matrix.transpose_one, SimpleGraph.transpose_adjMatrix, Matrix.transpose_smul]
        congr 2
      have hpsd' : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (((2 * α) • ML) *ᵥ x) := by
        intro x
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact mul_nonneg (by positivity) (hpsd x)
      have hker : LinearMap.ker (Matrix.toLin' ((2 * α) • ML)) = LinearMap.ker (Matrix.toLin' ML) := by
        rw [map_smul]
        exact LinearMap.ker_smul _ _ h2α
      obtain ⟨v, hv⟩ := L_gram n d ((2 * α) • ML) hT hpsd' (by rw [hker]; exact hrank)
      have hentry : ∀ i j, ((2 * α) • ML) i j =
          if i = j then 1 else (if G.Adj i j then -α else α) := by
        intro i j
        simp only [hML, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
          SimpleGraph.adjMatrix_apply, Matrix.of_apply, smul_eq_mul]
        by_cases hij : i = j
        · subst hij
          simp only [if_true, SimpleGraph.irrefl, if_false]
          field_simp
          ring
        · simp only [hij, if_false]
          by_cases hadj : G.Adj i j
          · simp only [hadj, if_true]; ring
          · simp only [hadj, if_false]; ring
      have hdiag : ∀ i, inner ℝ (v i) (v i) = 1 := by
        intro i; rw [hv, hentry]; simp
      have hoff : ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α := by
        intro i j hij
        rw [hv, hentry]
        simp only [hij, if_false]
        split_ifs
        · rw [abs_neg, abs_of_pos hα0]
        · rw [abs_of_pos hα0]
      have hinj : Function.Injective v := by
        intro i j hij
        by_contra hne
        have h1 := hoff i j hne
        rw [← hij, hdiag] at h1
        rw [abs_one] at h1
        linarith
      refine ⟨⟨Set.range v, ?_, ?_⟩, ?_⟩
      · rintro x ⟨i, rfl⟩
        have h := hdiag i
        rw [real_inner_self_eq_norm_sq] at h
        have hn := norm_nonneg (v i)
        nlinarith
      · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hxy
        exact hoff i j (fun h => hxy (by rw [h]))
      · show (Set.range v).ncard = n
        rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  open Matrix EquiangularLinesFixedAngle in
  have L_lower_d : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d : ℕ), ∃ E : EquiangularLines α d, E.carrier.ncard = d :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d : ℕ) => by
      have hα' := hα
      obtain ⟨hα0, hα1⟩ := hα
      have hlam : 0 < (1 - α) / (2 * α) := div_pos (by linarith) (by linarith)
      have hA : (⊥ : SimpleGraph (Fin d)).adjMatrix ℝ = 0 := by
        ext i j; simp
      refine L_lower_fromGraph α hα' d d ⊥ ?_ (Nat.le_add_right _ _)
      intro x
      rw [hA, sub_zero, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul]
      have h1 : 0 ≤ x ⬝ᵥ x := by
        simp only [dotProduct]
        exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
      have h2 : x ⬝ᵥ (Matrix.of (fun _ _ => (1 : ℝ)) *ᵥ x) = (∑ i, x i) * (∑ i, x i) := by
        simp only [dotProduct, mulVec, Matrix.of_apply, one_mul]
        rw [Finset.sum_mul]
      rw [h2]
      have h3 := mul_self_nonneg (∑ i, x i)
      have h4 := mul_nonneg hlam.le h1
      nlinarith
  open Matrix EquiangularLinesFixedAngle in
  have L_lower_attained : ∀ (lam : ℝ) (k₀ : ℕ) (hk₀ : (k₀ : ℕ∞) = spectralRadiusOrder lam), ∃ (H : SimpleGraph (Fin k₀)) (_ : DecidableRel H.Adj),
        spectralRadius ℝ (H.adjMatrix ℝ) = .ofReal lam :=
    fun (lam : ℝ) (k₀ : ℕ) (hk₀ : (k₀ : ℕ∞) = spectralRadiusOrder lam) => by
      classical
      unfold spectralRadiusOrder at hk₀
      by_cases hne : Set.Nonempty {k : ℕ | ∃ G : SimpleGraph (Fin k),
          spectralRadius ℝ (G.adjMatrix ℝ) = .ofReal lam}
      · rw [← ENat.coe_sInf hne] at hk₀
        have := Nat.sInf_mem hne
        rw [← Nat.cast_inj.mp hk₀] at this
        obtain ⟨H, hH⟩ := this
        exact ⟨H, inferInstance, hH⟩
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne] at hk₀
        simp at hk₀
  open Matrix EquiangularLinesFixedAngle in
  have L_lower_floor : ∀ (k₀ d : ℕ) (hk2 : 2 ≤ k₀) (hd : 1 ≤ d), (d - 1) / (k₀ - 1) * (k₀ - 1) + (d - 1) % (k₀ - 1) + 1 = d ∧
      ⌊((k₀ : ℝ) * ((d : ℝ) - 1)) / ((k₀ : ℝ) - 1)⌋₊ =
        (d - 1) / (k₀ - 1) * k₀ + (d - 1) % (k₀ - 1) :=
    fun (k₀ d : ℕ) (hk2 : 2 ≤ k₀) (hd : 1 ≤ d) => by
      have hdm := Nat.div_add_mod (d - 1) (k₀ - 1)
      have hrlt : (d - 1) % (k₀ - 1) < k₀ - 1 := Nat.mod_lt _ (by omega)
      generalize (d - 1) / (k₀ - 1) = m at hdm ⊢
      generalize (d - 1) % (k₀ - 1) = r at hdm hrlt ⊢
      rw [Nat.mul_comm] at hdm
      have hd' : m * (k₀ - 1) + r + 1 = d := by omega
      refine ⟨hd', ?_⟩
      obtain ⟨K, rfl⟩ : ∃ K, k₀ = K + 1 := ⟨k₀ - 1, by omega⟩
      subst hd'
      simp only [Nat.add_sub_cancel] at hrlt ⊢
      have hK1 : 1 ≤ K := by omega
      have hK : (0:ℝ) < K := by exact_mod_cast hK1
      have hrR : (r:ℝ) < K := by exact_mod_cast hrlt
      have e1 : ((((K + 1 : ℕ) : ℝ)) * (((m * K + r + 1 : ℕ) : ℝ) - 1)) / (((K + 1 : ℕ) : ℝ) - 1)
          = ((m * (K + 1) + r : ℕ) : ℝ) + r / K := by
        have hK0 : (K:ℝ) ≠ 0 := hK.ne'
        push_cast
        rw [add_sub_cancel_right, add_sub_cancel_right]
        field_simp
        ring
      rw [e1, Nat.floor_eq_iff (by positivity)]
      have h0 : 0 ≤ (r:ℝ) / K := by positivity
      have h1 : (r:ℝ) / K < 1 := (div_lt_one hK).mpr hrR
      constructor
      · linarith
      · linarith
  open Matrix EquiangularLinesFixedAngle in
  have L_lower_k : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
      (hk : spectralRadiusOrder ((1 - α) / (2 * α)) < ⊤) (d : ℕ) (hd : 1 ≤ d), ∃ E : EquiangularLines α d, E.carrier.ncard =
        ⌊((spectralRadiusOrder ((1 - α) / (2 * α))).toNat * (d - 1) : ℝ) /
          ((spectralRadiusOrder ((1 - α) / (2 * α))).toNat - 1 : ℝ)⌋₊ :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
        (hk : spectralRadiusOrder ((1 - α) / (2 * α)) < ⊤) (d : ℕ) (hd : 1 ≤ d) => by
      have hα' := hα
      obtain ⟨hα0, hα1⟩ := hα
      have hlam : 0 < (1 - α) / (2 * α) := div_pos (by linarith) (by linarith)
      obtain ⟨k₀, hk₀⟩ := ENat.ne_top_iff_exists.mp hk.ne
      obtain ⟨H, instH, hH⟩ := L_lower_attained _ k₀ hk₀
      obtain ⟨hH1, hH2⟩ := (L_spec k₀ H _ hlam).mp hH
      have hk2 : 2 ≤ k₀ := by
        by_contra hlt
        push_neg at hlt
        obtain ⟨x, hx0, hx⟩ := hH2
        apply hx0
        have hA : H.adjMatrix ℝ = 0 := by
          ext i j
          have hi := i.isLt
          have hj := j.isLt
          have : i = j := Fin.ext (by omega)
          subst this
          simp
        rw [hA, Matrix.zero_mulVec] at hx
        exact (smul_eq_zero.mp hx.symm).resolve_left hlam.ne'
      rw [← hk₀, ENat.toNat_coe]
      obtain ⟨hd', hfloor⟩ := L_lower_floor k₀ d hk2 hd
      rw [hfloor]
      obtain ⟨G, inst, hpsd, hrank⟩ := L_construct _ hlam k₀ H hH1 hH2
        ((d - 1) / (k₀ - 1)) ((d - 1) % (k₀ - 1))
      rw [hd'] at hrank
      exact @L_lower_fromGraph α hα' d _ G inst hpsd hrank
  open Matrix in
  have L_switch_inner_smul : ∀ (d : ℕ) (a b : ℝ) (x y : EuclideanSpace ℝ (Fin d)), inner ℝ (a • x) (b • y) = a * b * inner ℝ x y :=
    fun (d : ℕ) (a b : ℝ) (x y : EuclideanSpace ℝ (Fin d)) => by
      rw [real_inner_smul_left, real_inner_smul_right]; ring
  open Matrix in
  have L_switch_ramsey : ∀ (n : ℕ) (r : Fin n → Fin n → Prop)
      (hr : ∀ i j, r i j → r j i), ∀ (N s t : ℕ), s + t = N → ∀ (V : Finset (Fin n)), 2 ^ (s + t) ≤ V.card →
        (∃ S ⊆ V, S.card = s ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r i j) ∨
        (∃ T ⊆ V, T.card = t ∧ ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ r i j) :=
    fun (n : ℕ) (r : Fin n → Fin n → Prop)
        (hr : ∀ i j, r i j → r j i) => by
      classical
      intro N
      induction N with
      | zero =>
        intro s t hst V _
        have hs : s = 0 := by omega
        left
        exact ⟨∅, Finset.empty_subset _, by simp [hs], by simp⟩
      | succ N ih =>
        intro s t hst V hV
        rcases Nat.eq_zero_or_pos s with hs | hs
        · left; exact ⟨∅, Finset.empty_subset _, by simp [hs], by simp⟩
        rcases Nat.eq_zero_or_pos t with ht | ht
        · right; exact ⟨∅, Finset.empty_subset _, by simp [ht], by simp⟩
        obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        have hVpos : 0 < V.card := lt_of_lt_of_le (pow_pos (by norm_num) _) hV
        obtain ⟨x, hx⟩ := Finset.card_pos.mp hVpos
        have hAB : ((V.erase x).filter (fun y => r x y)).card +
            ((V.erase x).filter (fun y => ¬ r x y)).card = V.card - 1 := by
          rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hx]
        have hpow : 2 ^ (s' + 1 + (t' + 1)) = 2 * 2 ^ (s' + t' + 1) := by ring
        have e1 : 2 ^ (s' + (t' + 1)) = 2 ^ (s' + t' + 1) := by ring_nf
        have e2 : 2 ^ (s' + 1 + t') = 2 ^ (s' + t' + 1) := by ring_nf
        rw [hpow] at hV
        by_cases hAc : 2 ^ (s' + t' + 1) ≤ ((V.erase x).filter (fun y => r x y)).card
        · rw [← e1] at hAc
          rcases ih s' (t' + 1) (by omega) _ hAc with ⟨S, hSA, hSc, hSr⟩ | ⟨T, hTA, hTc, hTr⟩
          · left
            have hxS : x ∉ S := fun h => by
              have := Finset.mem_filter.mp (hSA h)
              exact (Finset.ne_of_mem_erase this.1) rfl
            refine ⟨insert x S, ?_, ?_, ?_⟩
            · intro y hy
              rcases Finset.mem_insert.mp hy with rfl | hy
              · exact hx
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (hSA hy)).1
            · rw [Finset.card_insert_of_notMem hxS, hSc]
            · intro i hi j hj hij
              rw [Finset.mem_insert] at hi hj
              rcases hi with rfl | hi <;> rcases hj with rfl | hj
              · exact absurd rfl hij
              · exact (Finset.mem_filter.mp (hSA hj)).2
              · exact hr _ _ (Finset.mem_filter.mp (hSA hi)).2
              · exact hSr i hi j hj hij
          · right
            exact ⟨T, fun y hy => Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTA hy)).1, hTc, hTr⟩
        · have hBc : 2 ^ (s' + 1 + t') ≤ ((V.erase x).filter (fun y => ¬ r x y)).card := by
            rw [e2]
            generalize 2 ^ (s' + t' + 1) = P at *
            omega
          rcases ih (s' + 1) t' (by omega) _ hBc with ⟨S, hSA, hSc, hSr⟩ | ⟨T, hTA, hTc, hTr⟩
          · left
            exact ⟨S, fun y hy => Finset.mem_of_mem_erase (Finset.mem_filter.mp (hSA hy)).1, hSc, hSr⟩
          · right
            have hxT : x ∉ T := fun h => by
              have := Finset.mem_filter.mp (hTA h)
              exact (Finset.ne_of_mem_erase this.1) rfl
            refine ⟨insert x T, ?_, ?_, ?_⟩
            · intro y hy
              rcases Finset.mem_insert.mp hy with rfl | hy
              · exact hx
              · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTA hy)).1
            · rw [Finset.card_insert_of_notMem hxT, hTc]
            · intro i hi j hj hij
              rw [Finset.mem_insert] at hi hj
              rcases hi with rfl | hi <;> rcases hj with rfl | hj
              · exact absurd rfl hij
              · exact (Finset.mem_filter.mp (hTA hj)).2
              · exact fun h => (Finset.mem_filter.mp (hTA hi)).2 (hr _ _ h)
              · exact hTr i hi j hj hij
  open Matrix in
  have L_switch_clique : ∀ (d n : ℕ) (α : ℝ) (hα : 0 < α) (v : Fin n → EuclideanSpace ℝ (Fin d))
      (hv : ∀ i, ‖v i‖ = 1) (S : Finset (Fin n))
      (hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → inner ℝ (v i) (v j) = -α), (S.card : ℝ) ≤ 1 / α + 1 :=
    fun (d n : ℕ) (α : ℝ) (hα : 0 < α) (v : Fin n → EuclideanSpace ℝ (Fin d))
        (hv : ∀ i, ‖v i‖ = 1) (S : Finset (Fin n))
        (hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → inner ℝ (v i) (v j) = -α) => by
      have hrow : ∀ i ∈ S, ∑ j ∈ S, inner ℝ (v i) (v j) = 1 - ((S.card : ℝ) - 1) * α := by
        intro i hi
        rw [← Finset.add_sum_erase S _ hi]
        have h1 : inner ℝ (v i) (v i) = 1 := by
          rw [real_inner_self_eq_norm_sq, hv i]; norm_num
        have h2 : ∑ j ∈ S.erase i, inner ℝ (v i) (v j) = ∑ j ∈ S.erase i, (-α) := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          exact hS i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
        rw [h1, h2, Finset.sum_const, Finset.card_erase_of_mem hi, nsmul_eq_mul]
        have hc : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
        push_cast [Nat.cast_sub hc]
        ring
      have hsum : 0 ≤ ∑ i ∈ S, ∑ j ∈ S, inner ℝ (v i) (v j) := by
        have : ∑ i ∈ S, ∑ j ∈ S, inner ℝ (v i) (v j) = inner ℝ (∑ i ∈ S, v i) (∑ j ∈ S, v j) := by
          rw [sum_inner]; refine Finset.sum_congr rfl (fun i _ => ?_); rw [inner_sum]
        rw [this]; exact real_inner_self_nonneg
      rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul] at hsum
      rcases Nat.eq_zero_or_pos S.card with h0 | hpos
      · rw [h0]; simp only [Nat.cast_zero]; positivity
      · have hM : (0:ℝ) < S.card := by exact_mod_cast hpos
        have h3 : 0 ≤ 1 - ((S.card : ℝ) - 1) * α := by
          by_contra hneg; push_neg at hneg; nlinarith
        rw [div_add_one hα.ne', le_div_iff₀ hα]
        nlinarith
  open Matrix in
  have L_switch_cross : ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (S S' : Finset (Fin n))
      (γ : ℝ) (h : ∀ i ∈ S, ∀ j ∈ S', inner ℝ (v i) (v j) = γ), inner ℝ (∑ i ∈ S, v i) (∑ j ∈ S', v j) = S.card * S'.card * γ :=
    fun (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (S S' : Finset (Fin n))
        (γ : ℝ) (h : ∀ i ∈ S, ∀ j ∈ S', inner ℝ (v i) (v j) = γ) => by
      rw [sum_inner]
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [inner_sum, Finset.sum_congr rfl (fun j hj => h i hi j hj)])]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
  open Matrix in
  have L_switch_self_le : ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (hv : ∀ i, ‖v i‖ = 1)
      (S : Finset (Fin n)) (β : ℝ) (h : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → inner ℝ (v i) (v j) ≤ β), inner ℝ (∑ i ∈ S, v i) (∑ j ∈ S, v j) ≤ S.card + S.card * ((S.card : ℝ) - 1) * β :=
    fun (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (hv : ∀ i, ‖v i‖ = 1)
        (S : Finset (Fin n)) (β : ℝ) (h : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → inner ℝ (v i) (v j) ≤ β) => by
      rw [sum_inner]
      have hrow : ∀ i ∈ S, inner ℝ (v i) (∑ j ∈ S, v j) ≤ 1 + ((S.card : ℝ) - 1) * β := by
        intro i hi
        rw [inner_sum, ← Finset.add_sum_erase S _ hi]
        have h1 : inner ℝ (v i) (v i) = 1 := by rw [real_inner_self_eq_norm_sq, hv i]; norm_num
        rw [h1]
        have h2 : ∑ j ∈ S.erase i, inner ℝ (v i) (v j) ≤ ∑ j ∈ S.erase i, β :=
          Finset.sum_le_sum (fun j hj =>
            h i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm)
        rw [Finset.sum_const, Finset.card_erase_of_mem hi, nsmul_eq_mul] at h2
        have hc : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
        push_cast [Nat.cast_sub hc] at h2
        linarith
      calc ∑ i ∈ S, inner ℝ (v i) (∑ j ∈ S, v j) ≤ ∑ i ∈ S, (1 + ((S.card : ℝ) - 1) * β) :=
            Finset.sum_le_sum hrow
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  open Matrix in
  have L_switch_self_eq : ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (hv : ∀ i, ‖v i‖ = 1)
      (S : Finset (Fin n)) (β : ℝ) (h : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → inner ℝ (v i) (v j) = β), inner ℝ (∑ i ∈ S, v i) (∑ j ∈ S, v j) = S.card + S.card * ((S.card : ℝ) - 1) * β :=
    fun (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)) (hv : ∀ i, ‖v i‖ = 1)
        (S : Finset (Fin n)) (β : ℝ) (h : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → inner ℝ (v i) (v j) = β) => by
      rw [sum_inner]
      have hrow : ∀ i ∈ S, inner ℝ (v i) (∑ j ∈ S, v j) = 1 + ((S.card : ℝ) - 1) * β := by
        intro i hi
        rw [inner_sum, ← Finset.add_sum_erase S _ hi]
        have h1 : inner ℝ (v i) (v i) = 1 := by rw [real_inner_self_eq_norm_sq, hv i]; norm_num
        rw [h1, Finset.sum_congr rfl (fun j hj =>
          h i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm),
          Finset.sum_const, Finset.card_erase_of_mem hi, nsmul_eq_mul]
        have hc : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
        push_cast [Nat.cast_sub hc]
        ring
      rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]
      ring
  open Matrix in
  have L_switch_star_arith_core : ∀ (α lam D : ℝ) (hα0 : 0 < α) (hlam : 0 < lam)
      (h1 : 1 - α = 2 * α * lam) (hD : lam ^ 2 < D), ∃ M₁ : ℕ, ∀ m : ℕ, M₁ ≤ m →
        (1 - α) * ((D / lam) ^ 2 + D + (D / lam + D) ^ 2 / m) - 4 * α * D * (D / lam) < 0 :=
    fun (α lam D : ℝ) (hα0 : 0 < α) (hlam : 0 < lam)
        (h1 : 1 - α = 2 * α * lam) (hD : lam ^ 2 < D) => by
      have hDpos : 0 < D := lt_of_le_of_lt (sq_nonneg _) hD
      have hK : 0 < 2 * α * D * (D - lam ^ 2) / lam :=
        div_pos (mul_pos (mul_pos (mul_pos two_pos hα0) hDpos) (sub_pos.mpr hD)) hlam
      set K := 2 * α * D * (D - lam ^ 2) / lam with hKdef
      have hid : (1 - α) * ((D / lam) ^ 2 + D) - 4 * α * D * (D / lam) = -K := by
        rw [hKdef, h1]; field_simp; ring
      have hpos1 : 0 ≤ 1 - α := by
        have := mul_pos (mul_pos two_pos hα0) hlam
        linarith
      refine ⟨⌈(1 - α) * (D / lam + D) ^ 2 / K⌉₊ + 1, fun m hm => ?_⟩
      have hm' : (1 - α) * (D / lam + D) ^ 2 / K < m := by
        have h4 := Nat.le_ceil ((1 - α) * (D / lam + D) ^ 2 / K)
        have h5 : ((⌈(1 - α) * (D / lam + D) ^ 2 / K⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
        push_cast at h5
        linarith
      have hmpos : (0:ℝ) < m :=
        lt_of_le_of_lt (div_nonneg (mul_nonneg hpos1 (sq_nonneg _)) hK.le) hm'
      have h2 : (1 - α) * (D / lam + D) ^ 2 / m < K := by
        rw [div_lt_iff₀ hmpos]
        rw [div_lt_iff₀ hK] at hm'
        linarith [mul_comm (m:ℝ) K]
      have h3 : (1 - α) * ((D / lam) ^ 2 + D + (D / lam + D) ^ 2 / m) - 4 * α * D * (D / lam) =
          -K + (1 - α) * (D / lam + D) ^ 2 / m := by
        rw [← hid]; ring
      rw [h3]; linarith
  open Matrix in
  have L_switch_star : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1), ∃ M₁ D₀ : ℕ, ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)), (∀ i, ‖v i‖ = 1) →
        (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) →
        ∀ X : Finset (Fin n), M₁ ≤ X.card →
        (∀ i ∈ X, ∀ j ∈ X, i ≠ j → inner ℝ (v i) (v j) = α) →
        ∀ u, u ∉ X → (∀ x ∈ X, inner ℝ (v u) (v x) = α) →
          (Finset.univ.filter (fun w => w ∉ X ∧ w ≠ u ∧ (∀ x ∈ X, inner ℝ (v w) (v x) = α) ∧
              inner ℝ (v u) (v w) = -α)).card ≤ D₀ :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) => by
      classical
      have hlam0 : 0 < (1 - α) / (2 * α) := div_pos (by linarith [hα.2]) (by linarith [hα.1])
      have h10 : 1 - α = 2 * α * ((1 - α) / (2 * α)) := by field_simp [hα.1.ne']
      have hD0 : ((1 - α) / (2 * α)) ^ 2 < (((⌊((1 - α) / (2 * α)) ^ 2⌋₊ + 1 : ℕ)) : ℝ) := by
        push_cast; exact Nat.lt_floor_add_one _
      obtain ⟨M, hM⟩ := L_switch_star_arith_core α _ _ hα.1 hlam0 h10 hD0
      refine ⟨max M 1, ⌊((1 - α) / (2 * α)) ^ 2⌋₊, ?_⟩
      intro d n v hv hvv X hX hXi u huX hux
      by_contra hcon
      push_neg at hcon
      obtain ⟨L, hLsub, hLc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcon)
      have hXpos : (0:ℝ) < X.card := by
        have : 1 ≤ X.card := le_trans (le_max_right _ _) hX
        exact_mod_cast this
      have hm := hM X.card (le_trans (le_max_left _ _) hX)
      have hlampos : 0 < (1 - α) / (2 * α) := div_pos (by linarith [hα.2]) (by linarith [hα.1])
      have h1 : 1 - α = 2 * α * ((1 - α) / (2 * α)) := by field_simp [hα.1.ne']
      replace hLc : L.card = ⌊((1 - α) / (2 * α)) ^ 2⌋₊ + 1 := hLc
      generalize (1 - α) / (2 * α) = lam at hm hLc hlampos h1
      generalize ⌊lam ^ 2⌋₊ + 1 = Dn at hm hLc
      subst hLc
      have hL : ∀ w ∈ L, w ∉ X ∧ w ≠ u ∧ (∀ x ∈ X, inner ℝ (v w) (v x) = α) ∧
          inner ℝ (v u) (v w) = -α := fun w hw => (Finset.mem_filter.mp (hLsub hw)).2
      have hLL := L_switch_self_le d n v hv L α (fun i _ j _ hij => (le_abs_self _).trans (hvv i j hij).le)
      have hXX := L_switch_self_eq d n v hv X α hXi
      have huL : inner ℝ (v u) (∑ j ∈ L, v j) = L.card * (-α) := by
        rw [inner_sum, Finset.sum_congr rfl (fun j hj => (hL j hj).2.2.2), Finset.sum_const,
          nsmul_eq_mul]
      have huX' : inner ℝ (v u) (∑ j ∈ X, v j) = X.card * α := by
        rw [inner_sum, Finset.sum_congr rfl (fun j hj => hux j hj), Finset.sum_const, nsmul_eq_mul]
      have hLX : inner ℝ (∑ i ∈ L, v i) (∑ j ∈ X, v j) = L.card * X.card * α :=
        L_switch_cross d n v L X α (fun i hi j hj => (hL i hi).2.2.1 j hj)
      have huu : inner ℝ (v u) (v u) = 1 := by rw [real_inner_self_eq_norm_sq, hv u]; norm_num
      set c : ℝ := (L.card : ℝ) with hc
      set m : ℝ := (X.card : ℝ) with hmdef
      set SL := ∑ j ∈ L, v j with hSL
      set SX := ∑ j ∈ X, v j with hSX
      set a := c / lam with ha
      set b := a + c with hb
      have hz : 0 ≤ inner ℝ (a • v u + SL - (b / m) • SX) (a • v u + SL - (b / m) • SX) :=
        real_inner_self_nonneg
      have e1 : inner ℝ (a • v u + SL - (b / m) • SX) (a • v u + SL - (b / m) • SX) =
          a ^ 2 * inner ℝ (v u) (v u) + 2 * a * inner ℝ (v u) SL + inner ℝ SL SL
            - 2 * (b / m) * a * inner ℝ (v u) SX - 2 * (b / m) * inner ℝ SL SX
            + (b / m) ^ 2 * inner ℝ SX SX := by
        simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
          real_inner_smul_left, real_inner_smul_right, real_inner_comm (v u) SL,
          real_inner_comm (v u) SX, real_inner_comm SL SX]
        ring
      rw [e1, huu, huL, huX', hLX, hXX] at hz
      have key : a ^ 2 * 1 + 2 * a * (c * -α) + (c + c * (c - 1) * α) - 2 * (b / m) * a * (m * α)
          - 2 * (b / m) * (c * m * α) + (b / m) ^ 2 * (m + m * (m - 1) * α) =
          (1 - α) * (a ^ 2 + c + b ^ 2 / m) - 4 * α * c * a := by
        rw [hb]; field_simp [hXpos.ne']; ring
      linarith [hLL, key, hm, hz]
  open Matrix in
  have L_switch_tri : ∀ (d n : ℕ) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
      (v : Fin n → EuclideanSpace ℝ (Fin d)) (hv : ∀ i, ‖v i‖ = 1) (s : ℝ) (hs : s = 1 ∨ s = -1)
      (P Q R : Finset (Fin n))
      (hP : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → inner ℝ (v i) (v j) = α)
      (hQ : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → inner ℝ (v i) (v j) ≤ α)
      (hR : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → inner ℝ (v i) (v j) = α)
      (hPQ : ∀ i ∈ P, ∀ j ∈ Q, inner ℝ (v i) (v j) = -s * α)
      (hPR : ∀ i ∈ P, ∀ j ∈ R, inner ℝ (v i) (v j) = α)
      (hQR : ∀ i ∈ Q, ∀ j ∈ R, inner ℝ (v i) (v j) = s * α)
      (ha : 0 < P.card) (hc : 0 < Q.card) (hb : 0 < R.card), 4 * α ^ 2 ≤ (1 - α) * (1 / (P.card : ℝ) + 1 / (Q.card : ℝ)) :=
    fun (d n : ℕ) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
        (v : Fin n → EuclideanSpace ℝ (Fin d)) (hv : ∀ i, ‖v i‖ = 1) (s : ℝ) (hs : s = 1 ∨ s = -1)
        (P Q R : Finset (Fin n))
        (hP : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → inner ℝ (v i) (v j) = α)
        (hQ : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → inner ℝ (v i) (v j) ≤ α)
        (hR : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → inner ℝ (v i) (v j) = α)
        (hPQ : ∀ i ∈ P, ∀ j ∈ Q, inner ℝ (v i) (v j) = -s * α)
        (hPR : ∀ i ∈ P, ∀ j ∈ R, inner ℝ (v i) (v j) = α)
        (hQR : ∀ i ∈ Q, ∀ j ∈ R, inner ℝ (v i) (v j) = s * α)
        (ha : 0 < P.card) (hc : 0 < Q.card) (hb : 0 < R.card) => by
      have hxx := L_switch_self_le d n v hv P α (fun i hi j hj hij => (hP i hi j hj hij).le)
      have hyy := L_switch_self_le d n v hv Q α hQ
      have hzz := L_switch_self_le d n v hv R α (fun i hi j hj hij => (hR i hi j hj hij).le)
      have hxy := L_switch_cross d n v P Q _ hPQ
      have hxz := L_switch_cross d n v P R _ hPR
      have hyz := L_switch_cross d n v Q R _ hQR
      set x := ∑ i ∈ P, v i with hx
      set y := ∑ i ∈ Q, v i with hy
      set z := ∑ i ∈ R, v i with hz
      have ha' : (0:ℝ) < P.card := by exact_mod_cast ha
      have hb' : (0:ℝ) < R.card := by exact_mod_cast hb
      have hc' : (0:ℝ) < Q.card := by exact_mod_cast hc
      set a : ℝ := (P.card : ℝ) with hadef
      set b : ℝ := (R.card : ℝ) with hbdef
      set c : ℝ := (Q.card : ℝ) with hcdef
      have hT : 0 ≤ inner ℝ ((1 / a) • x + (s / c) • y - (2 * α / b) • z)
          ((1 / a) • x + (s / c) • y - (2 * α / b) • z) := real_inner_self_nonneg
      have e1 : inner ℝ ((1 / a) • x + (s / c) • y - (2 * α / b) • z)
          ((1 / a) • x + (s / c) • y - (2 * α / b) • z) =
          (1 / a) ^ 2 * inner ℝ x x + (s / c) ^ 2 * inner ℝ y y + (2 * α / b) ^ 2 * inner ℝ z z
          + 2 * (1 / a) * (s / c) * inner ℝ x y - 2 * (1 / a) * (2 * α / b) * inner ℝ x z
          - 2 * (s / c) * (2 * α / b) * inner ℝ y z := by
        simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
          real_inner_smul_left, real_inner_smul_right, real_inner_comm x y,
          real_inner_comm x z, real_inner_comm y z]
        ring
      rw [e1] at hT
      have hyy' : (s / c) ^ 2 * inner ℝ y y ≤ (s / c) ^ 2 * (c + c * (c - 1) * α) :=
        mul_le_mul_of_nonneg_left hyy (sq_nonneg _)
      have hzz' : (2 * α / b) ^ 2 * inner ℝ z z ≤ (2 * α / b) ^ 2 * (b + b * (b - 1) * α) :=
        mul_le_mul_of_nonneg_left hzz (sq_nonneg _)
      have hxx2 : (1 / a) ^ 2 * inner ℝ x x ≤ (1 / a) ^ 2 * (a + a * (a - 1) * α) :=
        mul_le_mul_of_nonneg_left hxx (sq_nonneg _)
      have hb1 : 1 ≤ b := by rw [hbdef]; exact_mod_cast hb
      have hzb : (2 * α / b) ^ 2 * (b + b * (b - 1) * α) ≤ 4 * α ^ 2 := by
        have : (2 * α / b) ^ 2 * (b + b * (b - 1) * α) = 4 * α ^ 2 * (α + (1 - α) / b) := by
          field_simp; ring
        rw [this]
        have h1 : (1 - α) / b ≤ 1 - α := div_le_self (by linarith [hα.2]) hb1
        calc 4 * α ^ 2 * (α + (1 - α) / b) ≤ 4 * α ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = 4 * α ^ 2 := mul_one _
      have key : (1 / a) ^ 2 * (a + a * (a - 1) * α) + (s / c) ^ 2 * (c + c * (c - 1) * α)
          + 2 * (1 / a) * (s / c) * (a * c * (-s * α)) - 2 * (1 / a) * (2 * α / b) * (a * b * α)
          - 2 * (s / c) * (2 * α / b) * (c * b * (s * α))
          = (1 - α) * (1 / a + 1 / c) - 8 * α ^ 2 := by
        rcases hs with rfl | rfl <;> field_simp <;> ring
      rw [hxy, hxz, hyz] at hT
      linarith
  open Matrix in
  have L_switch_class : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1), ∃ M₁ M₂ : ℕ, ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)), (∀ i, ‖v i‖ = 1) →
        (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) →
        ∀ X : Finset (Fin n), M₁ ≤ X.card →
        (∀ i ∈ X, ∀ j ∈ X, i ≠ j → inner ℝ (v i) (v j) = α) →
        ∀ Y ⊆ X, Y.Nonempty → Y ≠ X →
          (Finset.univ.filter (fun w => w ∉ X ∧ (∀ x ∈ Y, inner ℝ (v w) (v x) = -α) ∧
              (∀ x ∈ X \\ Y, inner ℝ (v w) (v x) = α))).card ≤ M₂ :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) => by
      classical
      obtain ⟨hα0, hα1⟩ := hα
      set N : ℕ := ⌊(1 - α) / α ^ 2⌋₊ + 1 with hN
      have hNlt : (1 - α) / α ^ 2 < (N : ℝ) := by rw [hN]; push_cast; exact Nat.lt_floor_add_one _
      have hNpos : (0:ℝ) < N := by rw [hN]; positivity
      -- `(1-α)/m < α²` once `N ≤ m`
      have hsmall : ∀ m : ℕ, N ≤ m → (1 - α) * (1 / (m : ℝ)) < α ^ 2 := by
        intro m hm
        have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
        have hmpos : (0:ℝ) < m := lt_of_lt_of_le hNpos hm'
        have h1 : (1 - α) / α ^ 2 < m := lt_of_lt_of_le hNlt hm'
        rw [div_lt_iff₀ (by positivity)] at h1
        rw [mul_one_div, div_lt_iff₀ hmpos]
        linarith
      refine ⟨2 * N, N, ?_⟩
      intro d n v hv hvv X hX hXi Y hYX hYne hYX'
      by_contra hcon
      push_neg at hcon
      obtain ⟨C, hCsub, hCc⟩ := Finset.exists_subset_card_eq hcon.le
      have hCm : ∀ w ∈ C, w ∉ X ∧ (∀ x ∈ Y, inner ℝ (v w) (v x) = -α) ∧
          (∀ x ∈ X \\ Y, inner ℝ (v w) (v x) = α) := fun w hw => (Finset.mem_filter.mp (hCsub hw)).2
      have hZne : (X \\ Y).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro h; exact hYX' (Finset.Subset.antisymm hYX h)
      have hcard : Y.card + (X \\ Y).card = X.card := by
        rw [Finset.card_sdiff_of_subset hYX]; have := Finset.card_le_card hYX; omega
      have hQ : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → inner ℝ (v i) (v j) ≤ α :=
        fun i _ j _ hij => (le_abs_self _).trans (hvv i j hij).le
      have hCpos : 0 < C.card := by rw [hCc]; omega
      have hsC : (1 - α) * (1 / (C.card : ℝ)) < α ^ 2 := hsmall _ hCc.ge
      rcases le_or_gt N Y.card with hA | hA
      · have h := L_switch_tri d n α ⟨hα0, hα1⟩ v hv 1 (Or.inl rfl) Y C (X \\ Y)
          (fun i hi j hj hij => hXi i (hYX hi) j (hYX hj) hij) hQ
          (fun i hi j hj hij => hXi i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1 hij)
          (fun i hi j hj => by rw [real_inner_comm, (hCm j hj).2.1 i hi]; ring)
          (fun i hi j hj => hXi i (hYX hi) j (Finset.mem_sdiff.mp hj).1
            (fun h => (Finset.mem_sdiff.mp hj).2 (h ▸ hi)))
          (fun i hi j hj => by rw [(hCm i hi).2.2 j hj]; ring)
          hYne.card_pos hCpos hZne.card_pos
        have hsA := hsmall _ hA
        nlinarith
      · have hB : N ≤ (X \\ Y).card := by omega
        have h := L_switch_tri d n α ⟨hα0, hα1⟩ v hv (-1) (Or.inr rfl) (X \\ Y) C Y
          (fun i hi j hj hij => hXi i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1 hij) hQ
          (fun i hi j hj hij => hXi i (hYX hi) j (hYX hj) hij)
          (fun i hi j hj => by rw [real_inner_comm, (hCm j hj).2.2 i hi]; ring)
          (fun i hi j hj => hXi i (Finset.mem_sdiff.mp hi).1 j (hYX hj)
            (fun h => (Finset.mem_sdiff.mp hi).2 (h ▸ hj)))
          (fun i hi j hj => by rw [(hCm i hi).2.1 j hj]; ring)
          hZne.card_pos hCpos hYne.card_pos
        have hsB := hsmall _ hB
        nlinarith
  open Matrix in
  have L_switch_star_class : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1), ∃ M₁ D₀ M₂ : ℕ, 1 ≤ M₁ ∧ ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)),
        (∀ i, ‖v i‖ = 1) → (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) →
        ∀ X : Finset (Fin n), M₁ ≤ X.card →
        (∀ i ∈ X, ∀ j ∈ X, i ≠ j → inner ℝ (v i) (v j) = α) →
        (∀ u, u ∉ X → (∀ x ∈ X, inner ℝ (v u) (v x) = α) →
          (Finset.univ.filter (fun w => w ∉ X ∧ w ≠ u ∧ (∀ x ∈ X, inner ℝ (v w) (v x) = α) ∧
              inner ℝ (v u) (v w) = -α)).card ≤ D₀) ∧
        (∀ Y ⊆ X, Y.Nonempty → Y ≠ X →
          (Finset.univ.filter (fun w => w ∉ X ∧ (∀ x ∈ Y, inner ℝ (v w) (v x) = -α) ∧
              (∀ x ∈ X \\ Y, inner ℝ (v w) (v x) = α))).card ≤ M₂) :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) => by
      obtain ⟨Ma, D₀, ha⟩ := L_switch_star α hα
      obtain ⟨Mb, M₂, hb⟩ := L_switch_class α hα
      refine ⟨max (max Ma Mb) 1, D₀, M₂, le_max_right _ _, ?_⟩
      intro d n v hv hvv X hX hXi
      have hXa : Ma ≤ X.card := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
      have hXb : Mb ≤ X.card := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
      exact ⟨ha d n v hv hvv X hXa hXi, hb d n v hv hvv X hXb hXi⟩
  open Matrix in
  have L_switch_abs_cases : ∀ (a α : ℝ) (h : |a| = α), a = α ∨ a = -α :=
    fun (a α : ℝ) (h : |a| = α) => by
      rcases abs_eq (show (0:ℝ) ≤ α from h ▸ abs_nonneg a) |>.mp h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
  open Matrix in
  have L_switch_flip : ∀ (d n : ℕ) (α : ℝ) (hα : 0 < α) (v : Fin n → EuclideanSpace ℝ (Fin d))
      (hvv : ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) (T : Finset (Fin n)), ∃ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧ (∀ i ∈ T, s i = 1) ∧
        ∀ i ∉ T, 2 * (T.filter (fun x => inner ℝ (s i • v i) (s x • v x) = -α)).card ≤ T.card :=
    fun (d n : ℕ) (α : ℝ) (hα : 0 < α) (v : Fin n → EuclideanSpace ℝ (Fin d))
        (hvv : ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) (T : Finset (Fin n)) => by
      classical
      let N : Fin n → ℕ := fun i => (T.filter (fun x => inner ℝ (v i) (v x) = -α)).card
      let s : Fin n → ℝ := fun i => if i ∉ T ∧ T.card < 2 * N i then -1 else 1
      have hsT : ∀ i ∈ T, s i = 1 := by
        intro i hi; simp only [s]; rw [if_neg]; exact fun h => h.1 hi
      refine ⟨s, ?_, hsT, ?_⟩
      · intro i; simp only [s]; split_ifs <;> simp
      · intro i hi
        have hsplit := Finset.card_filter_add_card_filter_not (s := T)
          (fun x => inner ℝ (v i) (v x) = -α)
        by_cases hc : T.card < 2 * N i
        · have hsi : s i = -1 := by simp only [s]; rw [if_pos ⟨hi, hc⟩]
          have hfe : T.filter (fun x => inner ℝ (s i • v i) (s x • v x) = -α) =
              T.filter (fun x => ¬ inner ℝ (v i) (v x) = -α) := by
            refine Finset.filter_congr (fun x hx => ?_)
            rw [L_switch_inner_smul, hsi, hsT x hx]
            have hix : i ≠ x := fun h => hi (h ▸ hx)
            rcases L_switch_abs_cases _ _ (hvv i x hix) with h | h <;> rw [h] <;> constructor <;>
              intro h' <;> first | linarith | (intro h''; linarith) | exact absurd rfl h'
          rw [hfe]
          simp only [N] at hc
          omega
        · have hsi : s i = 1 := by simp only [s]; rw [if_neg]; exact fun h => hc h.2
          have hfe : T.filter (fun x => inner ℝ (s i • v i) (s x • v x) = -α) =
              T.filter (fun x => inner ℝ (v i) (v x) = -α) := by
            refine Finset.filter_congr (fun x hx => ?_)
            rw [L_switch_inner_smul, hsi, hsT x hx]; simp
          rw [hfe]
          simp only [N] at hc
          omega
  open Matrix in
  have L_switch_outside : ∀ (d n : ℕ) (α : ℝ) (hα : 0 < α) (M₂ : ℕ)
      (w : Fin n → EuclideanSpace ℝ (Fin d))
      (hww : ∀ i j, i ≠ j → |inner ℝ (w i) (w j)| = α) (T : Finset (Fin n)) (hT : 1 ≤ T.card)
      (hhalf : ∀ i ∉ T, 2 * (T.filter (fun x => inner ℝ (w i) (w x) = -α)).card ≤ T.card)
      (hclass : ∀ Y ⊆ T, Y.Nonempty → Y ≠ T →
          (Finset.univ.filter (fun u => u ∉ T ∧ (∀ x ∈ Y, inner ℝ (w u) (w x) = -α) ∧
              (∀ x ∈ T \\ Y, inner ℝ (w u) (w x) = α))).card ≤ M₂), (Finset.univ.filter (fun u => u ∉ T ∧ ¬ (∀ x ∈ T, inner ℝ (w u) (w x) = α))).card
        ≤ 2 ^ T.card * M₂ :=
    fun (d n : ℕ) (α : ℝ) (hα : 0 < α) (M₂ : ℕ)
        (w : Fin n → EuclideanSpace ℝ (Fin d))
        (hww : ∀ i j, i ≠ j → |inner ℝ (w i) (w j)| = α) (T : Finset (Fin n)) (hT : 1 ≤ T.card)
        (hhalf : ∀ i ∉ T, 2 * (T.filter (fun x => inner ℝ (w i) (w x) = -α)).card ≤ T.card)
        (hclass : ∀ Y ⊆ T, Y.Nonempty → Y ≠ T →
            (Finset.univ.filter (fun u => u ∉ T ∧ (∀ x ∈ Y, inner ℝ (w u) (w x) = -α) ∧
                (∀ x ∈ T \\ Y, inner ℝ (w u) (w x) = α))).card ≤ M₂) => by
      classical
      set O := Finset.univ.filter (fun u => u ∉ T ∧ ¬ (∀ x ∈ T, inner ℝ (w u) (w x) = α)) with hO
      let f : Fin n → Finset (Fin n) := fun u => T.filter (fun x => inner ℝ (w u) (w x) = -α)
      have hmaps : Set.MapsTo f (O : Set (Fin n)) (T.powerset : Set (Finset (Fin n))) :=
        fun u _ => Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      calc ∑ Y ∈ T.powerset, (O.filter (fun u => f u = Y)).card ≤ ∑ Y ∈ T.powerset, M₂ := by
            refine Finset.sum_le_sum (fun Y hY => ?_)
            rw [Finset.mem_powerset] at hY
            by_cases hne : (O.filter (fun u => f u = Y)).Nonempty
            · obtain ⟨u0, hu0⟩ := hne
              rw [Finset.mem_filter] at hu0
              obtain ⟨hu0O, hfu0⟩ := hu0
              rw [hO, Finset.mem_filter] at hu0O
              have hYne : Y.Nonempty := by
                obtain ⟨_, hu0T, hnot⟩ := hu0O
                push_neg at hnot
                obtain ⟨x, hxT, hx⟩ := hnot
                refine ⟨x, ?_⟩
                rw [← hfu0]
                refine Finset.mem_filter.mpr ⟨hxT, ?_⟩
                have hux : u0 ≠ x := fun h => hu0T (h ▸ hxT)
                rcases L_switch_abs_cases _ _ (hww u0 x hux) with h | h
                · exact absurd h hx
                · exact h
              have hYT : Y ≠ T := by
                intro hYT
                have := hhalf u0 hu0O.2.1
                rw [show T.filter (fun x => inner ℝ (w u0) (w x) = -α) = Y from hfu0, hYT] at this
                omega
              refine le_trans (Finset.card_le_card ?_) (hclass Y hY hYne hYT)
              intro u hu
              rw [Finset.mem_filter] at hu
              obtain ⟨huO, hfu⟩ := hu
              rw [hO, Finset.mem_filter] at huO
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huO.2.1, ?_, ?_⟩
              · intro x hx
                rw [← hfu] at hx
                exact (Finset.mem_filter.mp hx).2
              · intro x hx
                rw [Finset.mem_sdiff] at hx
                have hux : u ≠ x := fun h => huO.2.1 (h ▸ hx.1)
                rcases L_switch_abs_cases _ _ (hww u x hux) with h | h
                · exact h
                · exfalso; apply hx.2; rw [← hfu]; exact Finset.mem_filter.mpr ⟨hx.1, h⟩
            · rw [Finset.not_nonempty_iff_eq_empty] at hne
              rw [hne]; simp
        _ = 2 ^ T.card * M₂ := by rw [Finset.sum_const, Finset.card_powerset, smul_eq_mul]
  open Matrix in
  have L_switch_degree : ∀ (d n : ℕ) (α : ℝ) (hα : 0 < α) (M₁ D₀ M₂ : ℕ) (hM₁ : 1 ≤ M₁)
      (w : Fin n → EuclideanSpace ℝ (Fin d))
      (hww : ∀ i j, i ≠ j → |inner ℝ (w i) (w j)| = α) (T : Finset (Fin n))
      (hTc : T.card = 2 * M₁)
      (hTi : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → inner ℝ (w i) (w j) = α)
      (hhalf : ∀ i ∉ T, 2 * (T.filter (fun x => inner ℝ (w i) (w x) = -α)).card ≤ T.card)
      (hstar : ∀ X ⊆ T, M₁ ≤ X.card → ∀ u, u ∉ X → (∀ x ∈ X, inner ℝ (w u) (w x) = α) →
          (Finset.univ.filter (fun j => j ∉ X ∧ j ≠ u ∧ (∀ x ∈ X, inner ℝ (w j) (w x) = α) ∧
              inner ℝ (w u) (w j) = -α)).card ≤ D₀)
      (hclass : ∀ Y ⊆ T, Y.Nonempty → Y ≠ T →
          (Finset.univ.filter (fun u => u ∉ T ∧ (∀ x ∈ Y, inner ℝ (w u) (w x) = -α) ∧
              (∀ x ∈ T \\ Y, inner ℝ (w u) (w x) = α))).card ≤ M₂), ∀ i, (Finset.univ.filter (fun j => j ≠ i ∧ inner ℝ (w i) (w j) = -α)).card
        ≤ D₀ + 2 * M₁ + 2 ^ (2 * M₁) * M₂ :=
    fun (d n : ℕ) (α : ℝ) (hα : 0 < α) (M₁ D₀ M₂ : ℕ) (hM₁ : 1 ≤ M₁)
        (w : Fin n → EuclideanSpace ℝ (Fin d))
        (hww : ∀ i j, i ≠ j → |inner ℝ (w i) (w j)| = α) (T : Finset (Fin n))
        (hTc : T.card = 2 * M₁)
        (hTi : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → inner ℝ (w i) (w j) = α)
        (hhalf : ∀ i ∉ T, 2 * (T.filter (fun x => inner ℝ (w i) (w x) = -α)).card ≤ T.card)
        (hstar : ∀ X ⊆ T, M₁ ≤ X.card → ∀ u, u ∉ X → (∀ x ∈ X, inner ℝ (w u) (w x) = α) →
            (Finset.univ.filter (fun j => j ∉ X ∧ j ≠ u ∧ (∀ x ∈ X, inner ℝ (w j) (w x) = α) ∧
                inner ℝ (w u) (w j) = -α)).card ≤ D₀)
        (hclass : ∀ Y ⊆ T, Y.Nonempty → Y ≠ T →
            (Finset.univ.filter (fun u => u ∉ T ∧ (∀ x ∈ Y, inner ℝ (w u) (w x) = -α) ∧
                (∀ x ∈ T \\ Y, inner ℝ (w u) (w x) = α))).card ≤ M₂) => by
      classical
      have hout := L_switch_outside d n α hα M₂ w hww T (by omega) hhalf hclass
      rw [hTc] at hout
      intro i
      set O := Finset.univ.filter (fun u => u ∉ T ∧ ¬ (∀ x ∈ T, inner ℝ (w u) (w x) = α)) with hO
      by_cases hiT : i ∈ T
      · calc _ ≤ O.card := by
              refine Finset.card_le_card (fun j hj => ?_)
              rw [Finset.mem_filter] at hj
              obtain ⟨-, hji, hj⟩ := hj
              have hjT : j ∉ T := fun hjT => by
                have := hTi i hiT j hjT (Ne.symm hji)
                rw [this] at hj; linarith
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjT, fun hall => ?_⟩
              have := hall i hiT
              rw [real_inner_comm] at this
              rw [this] at hj; linarith
          _ ≤ 2 ^ (2 * M₁) * M₂ := hout
          _ ≤ _ := Nat.le_add_left _ _
      · set Y := T.filter (fun x => inner ℝ (w i) (w x) = α) with hYdef
        have hYT : Y ⊆ T := Finset.filter_subset _ _
        have hYc : M₁ ≤ Y.card := by
          have h1 := hhalf i hiT
          have h2 := Finset.card_filter_add_card_filter_not (s := T)
            (fun x => inner ℝ (w i) (w x) = α)
          rw [← hYdef] at h2
          have h3 : (T.filter (fun x => ¬ inner ℝ (w i) (w x) = α)).card ≤
              (T.filter (fun x => inner ℝ (w i) (w x) = -α)).card := by
            refine Finset.card_le_card (fun x hx => ?_)
            rw [Finset.mem_filter] at hx ⊢
            refine ⟨hx.1, ?_⟩
            have hix : i ≠ x := fun h => hiT (h ▸ hx.1)
            rcases L_switch_abs_cases _ _ (hww i x hix) with h | h
            · exact absurd h hx.2
            · exact h
          omega
        have hA := hstar Y hYT hYc i (fun h => hiT (hYT h)) (fun x hx => (Finset.mem_filter.mp hx).2)
        calc _ ≤ ((Finset.univ.filter (fun j => j ∉ Y ∧ j ≠ i ∧ (∀ x ∈ Y, inner ℝ (w j) (w x) = α) ∧
                inner ℝ (w i) (w j) = -α)) ∪ T ∪ O).card := by
              refine Finset.card_le_card (fun j hj => ?_)
              rw [Finset.mem_filter] at hj
              obtain ⟨-, hji, hj⟩ := hj
              by_cases hjT : j ∈ T
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ hjT)
              · by_cases hall : ∀ x ∈ T, inner ℝ (w j) (w x) = α
                · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hjT (hYT h), hji,
                    fun x hx => hall x (hYT hx), hj⟩
                · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjT, hall⟩)
          _ ≤ _ := by
              refine le_trans (Finset.card_union_le _ _) ?_
              refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
              exact Nat.add_le_add (Nat.add_le_add hA hTc.le) hout
  open Matrix in
  have L_switch_indep : ∀ (d n : ℕ) (α : ℝ) (hα : 0 < α) (v : Fin n → EuclideanSpace ℝ (Fin d))
      (hv : ∀ i, ‖v i‖ = 1) (hvv : ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) (t : ℕ)
      (hn : 2 ^ ((⌊1 / α⌋₊ + 2) + t) ≤ n), ∃ T : Finset (Fin n), T.card = t ∧ ∀ i ∈ T, ∀ j ∈ T, i ≠ j → inner ℝ (v i) (v j) = α :=
    fun (d n : ℕ) (α : ℝ) (hα : 0 < α) (v : Fin n → EuclideanSpace ℝ (Fin d))
        (hv : ∀ i, ‖v i‖ = 1) (hvv : ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) (t : ℕ)
        (hn : 2 ^ ((⌊1 / α⌋₊ + 2) + t) ≤ n) => by
      classical
      have hr : ∀ i j : Fin n, inner ℝ (v i) (v j) = -α → inner ℝ (v j) (v i) = -α := by
        intro i j h; rw [real_inner_comm]; exact h
      have hcard : 2 ^ ((⌊1 / α⌋₊ + 2) + t) ≤ (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.card_univ, Fintype.card_fin]; exact hn
      rcases L_switch_ramsey n (fun i j => inner ℝ (v i) (v j) = -α) hr _ (⌊1 / α⌋₊ + 2) t rfl _
          hcard with ⟨S, -, hSc, hSr⟩ | ⟨T, -, hTc, hTr⟩
      · exfalso
        have h1 := L_switch_clique d n α hα v hv S hSr
        rw [hSc] at h1
        have h2 : 1 / α < (⌊1 / α⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        push_cast at h1
        linarith
      · refine ⟨T, hTc, fun i hi j hj hij => ?_⟩
        rcases L_switch_abs_cases _ _ (hvv i j hij) with h | h
        · exact h
        · exact absurd h (hTr i hi j hj hij)
  open Matrix in
  have L_switch : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1), ∃ Δ : ℕ, ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)), (∀ i, ‖v i‖ = 1) →
        (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) →
        ∃ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
          ∀ i, (Finset.univ.filter (fun j => j ≠ i ∧ inner ℝ (s i • v i) (s j • v j) = -α)).card ≤ Δ :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) => by
      obtain ⟨M₁, D₀, M₂, hM₁, hSC⟩ := L_switch_star_class α hα
      have hα0 : 0 < α := hα.1
      refine ⟨2 ^ ((⌊1 / α⌋₊ + 2) + 2 * M₁) + (D₀ + 2 * M₁ + 2 ^ (2 * M₁) * M₂), ?_⟩
      intro d n v hv hvv
      by_cases hn : 2 ^ ((⌊1 / α⌋₊ + 2) + 2 * M₁) ≤ n
      · obtain ⟨T, hTc, hTi⟩ := L_switch_indep d n α hα0 v hv hvv (2 * M₁) hn
        obtain ⟨s, hs, hsT, hhalf⟩ := L_switch_flip d n α hα0 v hvv T
        have hinner : ∀ i j, inner ℝ (s i • v i) (s j • v j) = s i * s j * inner ℝ (v i) (v j) :=
          fun i j => L_switch_inner_smul d _ _ _ _
        have hwn : ∀ i, ‖s i • v i‖ = 1 := by
          intro i; rw [norm_smul, hv i]; rcases hs i with h | h <;> simp [h]
        have hww : ∀ i j, i ≠ j → |inner ℝ (s i • v i) (s j • v j)| = α := by
          intro i j hij; rw [hinner, abs_mul, abs_mul, hvv i j hij]
          rcases hs i with h | h <;> rcases hs j with h' | h' <;> simp [h, h']
        have hTi' : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → inner ℝ (s i • v i) (s j • v j) = α := by
          intro i hi j hj hij; rw [hinner, hsT i hi, hsT j hj, hTi i hi j hj hij]; ring
        have hstar := fun (X : Finset (Fin n)) (hXT : X ⊆ T) (hX : M₁ ≤ X.card) =>
          (hSC d n (fun i => s i • v i) hwn hww X hX
            (fun i hi j hj hij => hTi' i (hXT hi) j (hXT hj) hij)).1
        have hclass := (hSC d n (fun i => s i • v i) hwn hww T (by omega) hTi').2
        have hdeg := L_switch_degree d n α hα0 M₁ D₀ M₂ hM₁ (fun i => s i • v i) hww T hTc hTi' hhalf
          hstar hclass
        exact ⟨s, hs, fun i => le_trans (hdeg i) (Nat.le_add_left _ _)⟩
      · refine ⟨fun _ => 1, fun _ => Or.inl rfl, fun i => ?_⟩
        calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = n := Finset.card_fin n
          _ ≤ 2 ^ ((⌊1 / α⌋₊ + 2) + 2 * M₁) := by omega
          _ ≤ _ := Nat.le_add_right _ _
  open Matrix in
  have L_toGraph : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d))
      (hv1 : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α)
      (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hG : ∀ i j, G.Adj i j ↔ (i ≠ j ∧ inner ℝ (v i) (v j) = -α)), (∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ)
          - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x)) ∧
      n ≤ d + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          (((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ)
          - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))))) :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d))
        (hv1 : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α)
        (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (hG : ∀ i j, G.Adj i j ↔ (i ≠ j ∧ inner ℝ (v i) (v j) = -α)) => by
      obtain ⟨hα0, hα1⟩ := hα
      set M : Matrix (Fin n) (Fin n) ℝ := ((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ)
            - G.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) with hM
      have hentry : ∀ i j, M i j = (1 / (2 * α)) * inner ℝ (v i) (v j) := by
        intro i j
        by_cases hij : i = j
        · subst hij
          have h1 : inner ℝ (v i) (v i) = 1 := by
            rw [real_inner_self_eq_norm_sq, hv1 i]; norm_num
          simp only [hM, h1, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
            Matrix.one_apply_eq, SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl, if_false,
            Matrix.of_apply, smul_eq_mul]
          field_simp
          ring
        · by_cases hadj : G.Adj i j
          · have h1 : inner ℝ (v i) (v j) = -α := ((hG i j).1 hadj).2
            simp [hM, Matrix.one_apply_ne hij, SimpleGraph.adjMatrix_apply, hadj, h1]
            field_simp
            ring
          · have h1 : inner ℝ (v i) (v j) = α := by
              have habs := hv2 i j hij
              have hne : inner ℝ (v i) (v j) ≠ -α := fun h => hadj ((hG i j).2 ⟨hij, h⟩)
              rcases (abs_eq (le_of_lt hα0)).1 habs with h | h
              · exact h
              · exact absurd h hne
            simp [hM, Matrix.one_apply_ne hij, SimpleGraph.adjMatrix_apply, hadj, h1]
            field_simp
      have hmul : ∀ x : Fin n → ℝ, ∀ j, (M *ᵥ x) j
          = (1 / (2 * α)) * inner ℝ (v j) (∑ i, x i • v i) := by
        intro x j
        rw [inner_sum, Finset.mul_sum]
        simp only [Matrix.mulVec, dotProduct, hentry, real_inner_smul_right]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      refine ⟨?_, ?_⟩
      · intro x
        have hq : x ⬝ᵥ (M *ᵥ x) = (1 / (2 * α)) * inner ℝ (∑ i, x i • v i) (∑ i, x i • v i) := by
          rw [sum_inner, Finset.mul_sum]
          simp only [dotProduct, hmul, real_inner_smul_left]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        rw [hq, real_inner_self_eq_norm_sq]
        have : 0 < 1 / (2 * α) := by positivity
        positivity
      · let T : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
          ∑ i, (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ).smulRight (v i)
        have hT : ∀ x, T x = ∑ i, x i • v i := by
          intro x
          simp [T, LinearMap.sum_apply, LinearMap.smulRight_apply]
        have hker : LinearMap.ker T ≤ LinearMap.ker (Matrix.toLin' M) := by
          intro x hx
          rw [LinearMap.mem_ker] at hx ⊢
          rw [hT] at hx
          rw [Matrix.toLin'_apply]
          funext j
          rw [hmul, hx]
          simp
        have h1 := Submodule.finrank_mono hker
        have h2 := LinearMap.finrank_range_add_finrank_ker T
        have h3 : Module.finrank ℝ (LinearMap.range T) ≤ d := by
          have := Submodule.finrank_le (LinearMap.range T)
          simpa [finrank_euclideanSpace] using this
        have h4 : Module.finrank ℝ (Fin n → ℝ) = n := by simp
        omega
  open Matrix EquiangularLinesFixedAngle in
  have L_upper_key1 : ∀ (a b c k : ℕ) (h1 : k * (b + 1) ≤ c) (h2 : c ≤ a + b), k * (c + 1 - a) ≤ c :=
    fun (a b c k : ℕ) (h1 : k * (b + 1) ≤ c) (h2 : c ≤ a + b) => le_trans (Nat.mul_le_mul_left k (by omega)) h1
  open Matrix EquiangularLinesFixedAngle in
  have L_upper_key2 : ∀ (ε C : ℝ) (a b c : ℕ) (h1 : c ≤ a + b) (h2 : (b : ℝ) ≤ ε * c + C), (c : ℝ) ≤ a + ε * c + max C 0 :=
    fun (ε C : ℝ) (a b c : ℕ) (h1 : c ≤ a + b) (h2 : (b : ℝ) ≤ ε * c + C) => by
      have h3 : (c : ℝ) ≤ a + b := by exact_mod_cast h1
      have h4 := le_max_left C 0
      linarith
  open Matrix EquiangularLinesFixedAngle in
  have L_upper : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (ε : ℝ) (hε : 0 < ε), ∃ C : ℝ, ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)), (∀ i, ‖v i‖ = 1) →
        (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) →
        ((n : ℝ) ≤ d + ε * n + C ∨
          (spectralRadiusOrder ((1 - α) / (2 * α)) < ⊤ ∧
            (spectralRadiusOrder ((1 - α) / (2 * α))).toNat * (n + 1 - d) ≤ n)) :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (ε : ℝ) (hε : 0 < ε) => by
      classical
      obtain ⟨Δ, hΔ⟩ := L_switch α hα
      have hlam : 0 < (1 - α) / (2 * α) := by
        obtain ⟨h0, h1⟩ := hα
        apply div_pos <;> linarith
      obtain ⟨C, hC⟩ := L_case2 ((1 - α) / (2 * α)) hlam Δ ε hε
      refine ⟨max C 0, ?_⟩
      intro d n v hv1 hv2
      obtain ⟨s, hs, hsΔ⟩ := hΔ d n v hv1 hv2
      have habs : ∀ i, |s i| = 1 := by
        intro i; rcases hs i with h | h <;> rw [h] <;> norm_num
      set w : Fin n → EuclideanSpace ℝ (Fin d) := fun i => s i • v i with hw
      have hw1 : ∀ i, ‖w i‖ = 1 := by
        intro i; simp only [hw, norm_smul, Real.norm_eq_abs, habs, hv1, one_mul]
      have hw2 : ∀ i j, i ≠ j → |inner ℝ (w i) (w j)| = α := by
        intro i j hij
        simp only [hw, real_inner_smul_left, real_inner_smul_right, abs_mul, habs, hv2 i j hij,
          one_mul]
      let G : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun i j => inner ℝ (w i) (w j) = -α)
      have hG : ∀ i j, G.Adj i j ↔ (i ≠ j ∧ inner ℝ (w i) (w j) = -α) := by
        intro i j
        simp only [G, SimpleGraph.fromRel_adj]
        constructor
        · rintro ⟨hne, h | h⟩
          · exact ⟨hne, h⟩
          · exact ⟨hne, by rw [real_inner_comm]; exact h⟩
        · rintro ⟨hne, h⟩
          exact ⟨hne, Or.inl h⟩
      have hdeg : ∀ i, (Finset.univ.filter (G.Adj i)).card ≤ Δ := by
        intro i
        refine le_trans (Finset.card_le_card ?_) (hsΔ i)
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        obtain ⟨hne, h⟩ := (hG i j).1 hj
        exact ⟨fun h' => hne h'.symm, h⟩
      obtain ⟨hPSD, hdim⟩ := L_toGraph α hα d n w hw1 hw2 G hG
      by_cases hcase : ∀ x : Fin n → ℝ, x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ (1 - α) / (2 * α) * (x ⬝ᵥ x)
      · rcases L_case1 ((1 - α) / (2 * α)) hlam n G hcase with h0 | ⟨hlt, hk⟩
        · left
          have hnd : n ≤ d := by omega
          have hnd' : (n : ℝ) ≤ d := by exact_mod_cast hnd
          have hεn : 0 ≤ ε * n := by positivity
          have hC0 : 0 ≤ max C 0 := le_max_right _ _
          linarith
        · right
          exact ⟨hlt, L_upper_key1 _ _ _ _ hk hdim⟩
      · push_neg at hcase
        left
        exact L_upper_key2 ε C _ _ _ hdim (hC n G hdeg hPSD hcase)
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_enum : ∀ (α : ℝ) (d : ℕ) (E : EquiangularLines α d) (hfin : E.carrier.Finite), ∃ v : Fin E.carrier.ncard → EuclideanSpace ℝ (Fin d), (∀ i, ‖v i‖ = 1) ∧
        (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) :=
    fun (α : ℝ) (d : ℕ) (E : EquiangularLines α d) (hfin : E.carrier.Finite) => by
      haveI := hfin.to_subtype
      have h : Nat.card E.carrier = E.carrier.ncard := Nat.card_coe_set_eq _
      let e : E.carrier ≃ Fin E.carrier.ncard := (Finite.equivFin E.carrier).trans (finCongr h)
      refine ⟨fun i => (e.symm i).1, fun i => E.norm _ (e.symm i).2, fun i j hij => ?_⟩
      apply E.angle (e.symm i).2 (e.symm j).2
      intro heq
      apply hij
      have : e.symm i = e.symm j := Subtype.ext heq
      exact e.symm.injective this
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_k2 : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
      (hk : spectralRadiusOrder ((1 - α) / (2 * α)) < ⊤), 2 ≤ (spectralRadiusOrder ((1 - α) / (2 * α))).toNat :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
        (hk : spectralRadiusOrder ((1 - α) / (2 * α)) < ⊤) => by
      have hlam : 0 < (1 - α) / (2 * α) := by
        obtain ⟨h0, h1⟩ := hα
        apply div_pos <;> linarith
      have h2 : (2 : ℕ∞) ≤ spectralRadiusOrder ((1 - α) / (2 * α)) := by
        unfold spectralRadiusOrder
        refine le_iInf₂ fun k hk' => ?_
        obtain ⟨G, hG⟩ := hk'
        by_contra hlt
        push_neg at hlt
        have hk1 : k < 2 := by exact_mod_cast hlt
        have hz : ∀ (inst : DecidableRel G.Adj), G.adjMatrix ℝ = 0 := by
          intro inst
          refine Matrix.ext fun i j => ?_
          have hij : i = j := by
            apply Fin.ext
            have := i.isLt
            have := j.isLt
            omega
          subst hij
          simp
        rw [hz _, spectrum.spectralRadius_zero] at hG
        exact (ENNReal.ofReal_pos.mpr hlam).ne hG
      have hne : spectralRadiusOrder ((1 - α) / (2 * α)) ≠ ⊤ := hk.ne
      rw [← ENat.coe_toNat hne] at h2
      exact_mod_cast h2
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_upE : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (ε : ℝ) (hε : 0 < ε), ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (E : EquiangularLines α d),
        ((E.carrier.ncard : ℝ) ≤ d + ε * E.carrier.ncard + C ∨
          (spectralRadiusOrder ((1 - α) / (2 * α)) < ⊤ ∧
            (spectralRadiusOrder ((1 - α) / (2 * α))).toNat * (E.carrier.ncard + 1 - d) ≤
              E.carrier.ncard)) :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (ε : ℝ) (hε : 0 < ε) => by
      obtain ⟨C, hC⟩ := L_upper α hα ε hε
      refine ⟨max C 0, le_max_right _ _, fun d E => ?_⟩
      by_cases hfin : E.carrier.Finite
      · obtain ⟨v, hv1, hv2⟩ := L_final_enum α d E hfin
        rcases hC d _ v hv1 hv2 with h | h
        · left; linarith [le_max_left C 0]
        · right; exact h
      · left
        rw [Set.Infinite.ncard hfin]
        simp only [Nat.cast_zero, mul_zero, add_zero]
        linarith [le_max_right C 0, (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_bdd : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d : ℕ), BddAbove (Set.range fun E : EquiangularLines α d => E.carrier.ncard) :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d : ℕ) => by
      obtain ⟨C, hC0, hC⟩ := L_final_upE α hα (1/2) (by norm_num)
      refine ⟨2 * d + ⌈2 * C⌉₊, ?_⟩
      rintro _ ⟨E, rfl⟩
      show E.carrier.ncard ≤ 2 * d + ⌈2 * C⌉₊
      rcases hC d E with h | ⟨hk, h⟩
      · have h2 := Nat.le_ceil (2 * C)
        have : (E.carrier.ncard : ℝ) ≤ 2 * d + ⌈2 * C⌉₊ := by linarith
        exact_mod_cast this
      · have hk2 := L_final_k2 α hα hk
        have : 2 * (E.carrier.ncard + 1 - d) ≤ E.carrier.ncard :=
          le_trans (Nat.mul_le_mul_right _ hk2) h
        omega
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_attained : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d : ℕ), ∃ E : EquiangularLines α d, E.carrier.ncard = N α d :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d : ℕ) => by
      haveI : Nonempty (EquiangularLines α d) := ⟨⟨∅, by simp, by simp⟩⟩
      obtain ⟨E, hE⟩ := Nat.sSup_mem (Set.range_nonempty _) (L_final_bdd α hα d)
      exact ⟨E, hE⟩
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_le : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d : ℕ) (E : EquiangularLines α d), E.carrier.ncard ≤ N α d :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d : ℕ) (E : EquiangularLines α d) => le_ciSup (L_final_bdd α hα d) E
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_ar1 : ∀ (K n d C : ℝ) (hK : 2 ≤ K) (_hn : 0 ≤ n)
      (h : n ≤ d + 1 / (2 * K) * n + C) (hdR : 2 * C * (K - 1) + 2 * K ≤ d), n * (K - 1) ≤ K * (d - 1) :=
    fun (K n d C : ℝ) (hK : 2 ≤ K) (_hn : 0 ≤ n)
        (h : n ≤ d + 1 / (2 * K) * n + C) (hdR : 2 * C * (K - 1) + 2 * K ≤ d) => by
      have hm := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 2 * K)
      have e : 2 * K * (1 / (2 * K) * n) = n := by field_simp
      have h1 : (2 * K - 1) * n ≤ 2 * K * (d + C) := by nlinarith [hm, e]
      have P1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ K - 1)
      have P2 := mul_le_mul_of_nonneg_left hdR (by linarith : (0:ℝ) ≤ K)
      have e1 : (2 * K - 1) * (n * (K - 1)) ≤ (2 * K - 1) * (K * (d - 1)) := by nlinarith [P1, P2]
      exact le_of_mul_le_mul_left e1 (by linarith)
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_ar2 : ∀ (K0 n d : ℕ) (hK : 2 ≤ K0) (h : K0 * (n + 1 - d) ≤ n), (n : ℝ) * ((K0 : ℝ) - 1) ≤ (K0 : ℝ) * ((d : ℝ) - 1) :=
    fun (K0 n d : ℕ) (hK : 2 ≤ K0) (h : K0 * (n + 1 - d) ≤ n) => by
      have hKR : (2 : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast hK
      rcases le_or_gt (n + 1) d with hnd | hnd
      · have h' : (n : ℝ) ≤ d - 1 := by
          have : ((n + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hnd
          push_cast at this
          linarith
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [mul_nonneg (sub_nonneg.mpr h') (by linarith : (0:ℝ) ≤ (K0 : ℝ) - 1)]
      · have hsub : ((n + 1 - d : ℕ) : ℝ) = n + 1 - d := by
          rw [Nat.cast_sub hnd.le, Nat.cast_add_one]
        have hR : (K0 : ℝ) * ((n + 1 - d : ℕ) : ℝ) ≤ n := by exact_mod_cast h
        rw [hsub] at hR
        nlinarith [hR]
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_ar3 : ∀ (c ε C N d : ℝ) (hc : 0 < c) (hε1 : ε ≤ 1 / 2) (hε2 : ε ≤ c / 4)
      (_hC0 : 0 ≤ C) (hN0 : 0 ≤ N) (h : N ≤ d + ε * N + C) (hB : 2 * (c / 2 * C + C) ≤ d * c), N - d ≤ c * d :=
    fun (c ε C N d : ℝ) (hc : 0 < c) (hε1 : ε ≤ 1 / 2) (hε2 : ε ≤ c / 4)
        (_hC0 : 0 ≤ C) (hN0 : 0 ≤ N) (h : N ≤ d + ε * N + C) (hB : 2 * (c / 2 * C + C) ≤ d * c) => by
      have q1 := mul_le_mul_of_nonneg_right hε1 hN0
      have q2 := mul_le_mul_of_nonneg_right hε2 hN0
      have hN2 : N ≤ 2 * (d + C) := by linarith
      have q3 := mul_le_mul_of_nonneg_left hN2 (by positivity : (0:ℝ) ≤ c / 4)
      nlinarith [q1, q2, q3, hB]
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_fin : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1), spectralRadiusOrder ((1 - α) / (2 * α)) < ⊤ → ∀ᶠ d in atTop, N α d =
        ⌊((spectralRadiusOrder ((1 - α) / (2 * α))).toNat * (d - 1) : ℝ) /
          ((spectralRadiusOrder ((1 - α) / (2 * α))).toNat - 1 : ℝ)⌋₊ :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) => by
      intro hk
      have hk2 := L_final_k2 α hα hk
      have hKR : (2 : ℝ) ≤ ((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ) := by
        exact_mod_cast hk2
      obtain ⟨C, hC0, hC⟩ := L_final_upE α hα
        (1 / (2 * ((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ))) (by positivity)
      rw [Filter.eventually_atTop]
      refine ⟨⌈2 * C * (((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ) - 1) +
        2 * ((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ)⌉₊ + 1, fun d hd => ?_⟩
      have hd1 : 1 ≤ d := by omega
      obtain ⟨E0, hE0⟩ := L_lower_k α hα hk d hd1
      obtain ⟨E, hE⟩ := L_final_attained α hα d
      have hlow := L_final_le α hα d E0
      have hCE := hC d E
      have hceil := Nat.le_ceil (2 * C * (((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ) - 1) +
        2 * ((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ))
      have hdc : ((⌈2 * C * (((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ) - 1) +
        2 * ((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ)⌉₊ : ℕ) : ℝ) ≤ d := by
        exact_mod_cast (by omega : ⌈2 * C * (((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ) - 1) +
          2 * ((spectralRadiusOrder ((1 - α) / (2 * α))).toNat : ℝ)⌉₊ ≤ d)
      rw [← hE] at hlow ⊢
      rw [hE0] at hlow
      clear hC
      generalize (spectralRadiusOrder ((1 - α) / (2 * α))).toNat = K0 at hk2 hKR hCE hceil hdc hlow ⊢
      generalize E.carrier.ncard = n at hCE hlow ⊢
      apply le_antisymm _ hlow
      have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      have hdR : 2 * C * ((K0 : ℝ) - 1) + 2 * (K0 : ℝ) ≤ d := le_trans hceil hdc
      apply Nat.le_floor
      rw [le_div_iff₀ (by linarith : (0:ℝ) < (K0 : ℝ) - 1)]
      rcases hCE with h | ⟨_, h⟩
      · exact L_final_ar1 _ _ _ _ hKR (Nat.cast_nonneg n) h hdR
      · exact L_final_ar2 K0 n d hk2 h
  open Matrix EquiangularLinesFixedAngle Filter in
  have L_final_inf : ∀ (α : ℝ) (hα : α ∈ Set.Ioo 0 1), spectralRadiusOrder ((1 - α) / (2 * α)) = ⊤ →
        ∃ e : ℕ → ℝ, e =o[atTop] (Nat.cast : ℕ → ℝ) ∧ ∀ d, N α d = d + e d :=
    fun (α : ℝ) (hα : α ∈ Set.Ioo 0 1) => by
      intro hk
      refine ⟨fun d => (N α d : ℝ) - d, ?_, fun d => by ring⟩
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      have hε0 : 0 < min (c / 4) (1 / 2) := lt_min (by positivity) (by norm_num)
      obtain ⟨C, hC0, hC⟩ := L_final_upE α hα (min (c / 4) (1 / 2)) hε0
      have hε1 : min (c / 4) (1 / 2) ≤ 1 / 2 := min_le_right _ _
      have hε2 : min (c / 4) (1 / 2) ≤ c / 4 := min_le_left _ _
      rw [Filter.eventually_atTop]
      refine ⟨⌈2 * (c / 2 * C + C) / c⌉₊, fun d hd => ?_⟩
      have hceil := Nat.le_ceil (2 * (c / 2 * C + C) / c)
      have hdc : ((⌈2 * (c / 2 * C + C) / c⌉₊ : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
      have hB : 2 * (c / 2 * C + C) ≤ d * c := (div_le_iff₀ hc).mp (le_trans hceil hdc)
      obtain ⟨E0, hE0⟩ := L_lower_d α hα d
      have hlow := L_final_le α hα d E0
      rw [hE0] at hlow
      obtain ⟨E, hE⟩ := L_final_attained α hα d
      have hCE := hC d E
      rw [hE] at hCE
      have h : (N α d : ℝ) ≤ d + min (c / 4) (1 / 2) * (N α d : ℝ) + C := by
        rcases hCE with h | ⟨hlt, _⟩
        · exact h
        · exact absurd hk hlt.ne
      have hlowR : (d : ℝ) ≤ N α d := by exact_mod_cast hlow
      show ‖(N α d : ℝ) - d‖ ≤ c * ‖(d : ℝ)‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), Nat.abs_cast]
      exact L_final_ar3 c _ C _ d hc hε1 hε2 hC0 (Nat.cast_nonneg _) h hB
  intro k
  exact ⟨L_final_fin α hα, L_final_inf α hα⟩)")
    let act : Lean.Elab.Tactic.TacticM Unit :=
      withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 })
        (do Lean.Elab.Tactic.evalTactic stx; Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing)
    controlAt (EIO Lean.Exception) fun runInBase => do
      let t ← EIO.asTask (runInBase act) Task.Priority.dedicated
      match ← IO.wait t with
      | .ok a => pure a
      | .error e => throw e

end Submission
