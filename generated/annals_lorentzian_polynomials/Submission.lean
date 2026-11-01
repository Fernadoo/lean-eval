import ChallengeDeps
import Submission.Helpers
import Lean

open LorentzianPolynomials
open Finsupp Matrix MvPolynomial UpperHalfPlane

set_option autoImplicit false

namespace Submission

theorem theorem_2_25 (n d : ℕ) (hn : 0 < n) : closure (Ŀ n d) = L n d := by
  run_tac do
    let stx ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "(
  open Matrix in
  have LZeig_quad : ∀ (a b : ℝ) (h : ∀ t : ℝ, a * t + b * t ^ 2 ≤ 0), a = 0 :=
    fun (a b : ℝ) (h : ∀ t : ℝ, a * t + b * t ^ 2 ≤ 0) => by
      have hb : 0 < |b| + 1 := by positivity
      set ε : ℝ := 1 / (|b| + 1) with hε
      have hε0 : 0 < ε := by positivity
      have hbe : 0 < 1 + b * ε := by
        have h1 : |b| * ε < 1 := by
          rw [hε, mul_one_div, div_lt_one hb]; linarith
        have h2 : -(|b| * ε) ≤ b * ε := by
          have := neg_abs_le b
          nlinarith
        linarith
      have := h (ε * a)
      have h3 : a ^ 2 * (ε * (1 + b * ε)) ≤ 0 := by nlinarith
      have h4 : 0 < ε * (1 + b * ε) := mul_pos hε0 hbe
      have h5 : a ^ 2 ≤ 0 := by
        by_contra hc
        push_neg at hc
        have := mul_pos hc h4
        linarith
      nlinarith [sq_nonneg a]
  open Matrix in
  have LZeig_symm : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose = Q)
      (x y : Fin n → ℝ), x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose = Q)
        (x y : Fin n → ℝ) => by
      rw [dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]
  open Matrix in
  have LZeig_self_eq_zero : ∀ (n : ℕ) (x : Fin n → ℝ) (h : x ⬝ᵥ x = 0), x = 0 :=
    fun (n : ℕ) (x : Fin n → ℝ) (h : x ⬝ᵥ x = 0) => by
      have h' : ∀ j ∈ Finset.univ, x j * x j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).1 h
      funext j
      have := h' j (Finset.mem_univ j)
      simpa using this
  open Matrix in
  have LZeig_perp : ∀ (n k : ℕ) (hk : k < n) (v : Fin n → Fin n → ℝ)
      (hv : ∀ i j : Fin n, i.val < k → j.val < k → v i ⬝ᵥ v j = if i = j then 1 else 0), ∃ x : Fin n → ℝ, x ≠ 0 ∧ ∀ i : Fin n, i.val < k → v i ⬝ᵥ x = 0 :=
    fun (n k : ℕ) (hk : k < n) (v : Fin n → Fin n → ℝ)
        (hv : ∀ i j : Fin n, i.val < k → j.val < k → v i ⬝ᵥ v j = if i = j then 1 else 0) => by
      by_contra hcon
      push_neg at hcon
      set S := Finset.univ.filter (fun i : Fin n => i.val < k) with hS
      have hw : ∀ j : Fin n, Pi.single j 1 = ∑ i ∈ S, v i j • v i := by
        intro j
        by_contra hne
        have hne' : Pi.single j 1 - ∑ i ∈ S, v i j • v i ≠ 0 := sub_ne_zero.2 hne
        obtain ⟨i, hi, hdot⟩ := hcon _ hne'
        apply hdot
        rw [dotProduct_sub, dotProduct_sum]
        have : ∑ l ∈ S, v i ⬝ᵥ (v l j • v l) = v i j := by
          rw [Finset.sum_eq_single i]
          · rw [dotProduct_smul, hv i i hi hi]; simp
          · intro l hl hli
            have hl' : l.val < k := (Finset.mem_filter.1 hl).2
            rw [dotProduct_smul, hv i l hi hl', if_neg (Ne.symm hli)]; simp
          · intro h; exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩) h
        rw [this]
        simp [dotProduct, Pi.single_apply]
      have h1 : ∀ j : Fin n, (1 : ℝ) = ∑ i ∈ S, v i j * v i j := by
        intro j
        have := congrFun (hw j) j
        simpa [Finset.sum_apply] using this
      have h2 : (n : ℝ) = (S.card : ℝ) := by
        calc (n : ℝ) = ∑ j : Fin n, (1 : ℝ) := by simp
          _ = ∑ j : Fin n, ∑ i ∈ S, v i j * v i j := Finset.sum_congr rfl (fun j _ => h1 j)
          _ = ∑ i ∈ S, v i ⬝ᵥ v i := by rw [Finset.sum_comm]; rfl
          _ = ∑ i ∈ S, (1 : ℝ) := Finset.sum_congr rfl (fun i hi => by
                have hi' := (Finset.mem_filter.1 hi).2
                rw [hv i i hi' hi']; simp)
          _ = (S.card : ℝ) := by simp
      have h3 : S.card < n := by
        have : S ⊂ Finset.univ := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.subset_univ _, fun h => ?_⟩
          have : (⟨k, hk⟩ : Fin n) ∈ S := by rw [h]; exact Finset.mem_univ _
          simp [hS] at this
        have := Finset.card_lt_card this
        simpa using this
      have : (S.card : ℝ) < n := by exact_mod_cast h3
      linarith
  open Matrix in
  have LZeig_step : ∀ (n k : ℕ) (hk : k < n) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose = Q)
      (v : Fin n → Fin n → ℝ) (μ : Fin n → ℝ)
      (hv : ∀ i j : Fin n, i.val < k → j.val < k → v i ⬝ᵥ v j = if i = j then 1 else 0)
      (heig : ∀ i : Fin n, i.val < k → Q *ᵥ v i = μ i • v i), ∃ (x : Fin n → ℝ) (lam : ℝ), x ⬝ᵥ x = 1 ∧ (∀ i : Fin n, i.val < k → v i ⬝ᵥ x = 0) ∧
        Q *ᵥ x = lam • x :=
    fun (n k : ℕ) (hk : k < n) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose = Q)
        (v : Fin n → Fin n → ℝ) (μ : Fin n → ℝ)
        (hv : ∀ i j : Fin n, i.val < k → j.val < k → v i ⬝ᵥ v j = if i = j then 1 else 0)
        (heig : ∀ i : Fin n, i.val < k → Q *ᵥ v i = μ i • v i) => by
      set P : Set (Fin n → ℝ) := {x | x ⬝ᵥ x = 1 ∧ ∀ i : Fin n, i.val < k → v i ⬝ᵥ x = 0} with hP
      have hcd : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ x) := by
        simp only [dotProduct]; fun_prop
      have hcv : ∀ i : Fin n, Continuous (fun x : Fin n → ℝ => v i ⬝ᵥ x) := by
        intro i; simp only [dotProduct]; fun_prop
      have hcf : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ (Q *ᵥ x)) := by
        simp only [dotProduct, mulVec]; fun_prop
      have hclosed : IsClosed P := by
        have : P = {x | x ⬝ᵥ x = 1} ∩ ⋂ (i : Fin n), ⋂ (_ : i.val < k), {x | v i ⬝ᵥ x = 0} := by
          ext x; simp [hP]
        rw [this]
        exact (isClosed_eq hcd continuous_const).inter
          (isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (hcv i) continuous_const)
      have hsub : P ⊆ Metric.closedBall 0 1 := by
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
        intro j
        have h1 : x j * x j ≤ x ⬝ᵥ x :=
          Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
            (Finset.mem_univ j)
        rw [hx.1] at h1
        rw [Real.norm_eq_abs]
        nlinarith [abs_nonneg (x j), sq_abs (x j)]
      have hcomp : IsCompact P := (isCompact_closedBall 0 1).of_isClosed_subset hclosed hsub
      -- normalization
      have hnorm : ∀ z : Fin n → ℝ, z ≠ 0 → (∀ i : Fin n, i.val < k → v i ⬝ᵥ z = 0) →
          (1 / Real.sqrt (z ⬝ᵥ z)) • z ∈ P ∧ (1 / Real.sqrt (z ⬝ᵥ z)) ^ 2 = 1 / (z ⬝ᵥ z) ∧
          0 < z ⬝ᵥ z := by
        intro z hz hzv
        have hpos : 0 < z ⬝ᵥ z := by
          rcases lt_or_eq_of_le (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
            mul_self_nonneg (z j))) with h | h
          · exact h
          · exact absurd (LZeig_self_eq_zero n z h.symm) hz
        have hsq : (1 / Real.sqrt (z ⬝ᵥ z)) ^ 2 = 1 / (z ⬝ᵥ z) := by
          rw [div_pow, Real.sq_sqrt hpos.le, one_pow]
        refine ⟨⟨?_, ?_⟩, hsq, hpos⟩
        · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, hsq]
          field_simp
        · intro i hi; rw [dotProduct_smul, hzv i hi, smul_zero]
      obtain ⟨z0, hz0, hz0v⟩ := LZeig_perp n k hk v hv
      have hne : P.Nonempty := ⟨_, (hnorm z0 hz0 hz0v).1⟩
      obtain ⟨x, hxP, hmax⟩ := hcomp.exists_isMaxOn hne hcf.continuousOn
      set lam := x ⬝ᵥ (Q *ᵥ x) with hlam
      have key : ∀ z : Fin n → ℝ, (∀ i : Fin n, i.val < k → v i ⬝ᵥ z = 0) →
          z ⬝ᵥ (Q *ᵥ z) ≤ lam * (z ⬝ᵥ z) := by
        intro z hzv
        by_cases hz : z = 0
        · subst hz; simp
        obtain ⟨hmem, hsq, hpos⟩ := hnorm z hz hzv
        have := hmax hmem
        simp only [Set.mem_setOf_eq] at this
        rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc,
          ← sq, hsq, ← hlam] at this
        rw [one_div, inv_mul_eq_div, div_le_iff₀ hpos] at this
        linarith
      set r := Q *ᵥ x - lam • x with hr
      have hrv : ∀ i : Fin n, i.val < k → v i ⬝ᵥ r = 0 := by
        intro i hi
        rw [hr, dotProduct_sub, dotProduct_smul, hxP.2 i hi, LZeig_symm n Q hQ, heig i hi,
          dotProduct_smul, dotProduct_comm, hxP.2 i hi]
        simp
      have hQx : Q *ᵥ x = r + lam • x := by rw [hr, sub_add_cancel]
      have hquad : ∀ t : ℝ, (2 * (r ⬝ᵥ r)) * t + (r ⬝ᵥ (Q *ᵥ r) - lam * (r ⬝ᵥ r)) * t ^ 2 ≤ 0 := by
        intro t
        have hzv : ∀ i : Fin n, i.val < k → v i ⬝ᵥ (x + t • r) = 0 := by
          intro i hi; rw [dotProduct_add, dotProduct_smul, hxP.2 i hi, hrv i hi]; simp
        have h := key _ hzv
        simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
          smul_dotProduct, smul_eq_mul] at h
        have e1 : x ⬝ᵥ (Q *ᵥ r) = r ⬝ᵥ (Q *ᵥ x) := LZeig_symm n Q hQ x r
        have e2 : r ⬝ᵥ (Q *ᵥ x) = r ⬝ᵥ r + lam * (r ⬝ᵥ x) := by
          rw [hQx, dotProduct_add, dotProduct_smul, smul_eq_mul]
        have e3 : x ⬝ᵥ r = r ⬝ᵥ x := dotProduct_comm _ _
        rw [e1, e2, e3, ← hlam, hxP.1] at h
        nlinarith [h]
      have h0 := LZeig_quad _ _ hquad
      have hrr : r ⬝ᵥ r = 0 := by linarith
      have hr0 := LZeig_self_eq_zero n r hrr
      refine ⟨x, lam, hxP.1, hxP.2, ?_⟩
      rw [hQx, hr0, zero_add]
  open Matrix in
  have LZeig_ind : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose = Q) (k : ℕ)
      (hk : k ≤ n), ∃ (v : Fin n → Fin n → ℝ) (μ : Fin n → ℝ),
        (∀ i j : Fin n, i.val < k → j.val < k → v i ⬝ᵥ v j = if i = j then 1 else 0) ∧
        (∀ i : Fin n, i.val < k → Q *ᵥ v i = μ i • v i) :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose = Q) (k : ℕ)
        (hk : k ≤ n) => by
      induction k with
      | zero => exact ⟨0, 0, fun i _ hi => absurd hi (Nat.not_lt_zero _),
          fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      | succ k ih =>
        have hk' : k < n := by omega
        obtain ⟨v, μ, hv, heig⟩ := ih hk'.le
        obtain ⟨x, lam, hxx, hxv, hQx⟩ := LZeig_step n k hk' Q hQ v μ hv heig
        set K : Fin n := ⟨k, hk'⟩ with hK
        have hcase : ∀ i : Fin n, i.val < k + 1 → i = K ∨ (i.val < k ∧ i ≠ K) := by
          intro i hi
          by_cases h : i.val = k
          · left; exact Fin.ext h
          · right; refine ⟨by omega, fun h' => h (by rw [h'])⟩
        refine ⟨Function.update v K x, Function.update μ K lam, ?_, ?_⟩
        · intro i j hi hj
          rcases hcase i hi with rfl | ⟨hi', hiK⟩ <;> rcases hcase j hj with rfl | ⟨hj', hjK⟩
          · simp [hxx]
          · rw [Function.update_self, Function.update_of_ne hjK, dotProduct_comm, hxv j hj',
              if_neg (Ne.symm hjK)]
          · rw [Function.update_self, Function.update_of_ne hiK, hxv i hi', if_neg hiK]
          · rw [Function.update_of_ne hiK, Function.update_of_ne hjK, hv i j hi' hj']
        · intro i hi
          rcases hcase i hi with rfl | ⟨hi', hiK⟩
          · simp [hQx]
          · rw [Function.update_of_ne hiK, Function.update_of_ne hiK, heig i hi']
  open Matrix in
  have LZeig : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose = Q), ∃ (O : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ),
        O.transpose * O = 1 ∧ Q = O * Matrix.diagonal D * O.transpose :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose = Q) => by
      obtain ⟨v, μ, hv, heig⟩ := LZeig_ind n Q hQ n le_rfl
      set O : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a i => v i a with hO
      have h1 : O.transpose * O = 1 := by
        ext i j
        have := hv i j i.isLt j.isLt
        simp only [Matrix.mul_apply, Matrix.transpose_apply, hO, Matrix.of_apply, Matrix.one_apply]
        rw [← this]; rfl
      have h2 : O * O.transpose = 1 := mul_eq_one_comm.1 h1
      have h3 : Q * O = O * Matrix.diagonal μ := by
        ext a i
        have := congrFun (heig i i.isLt) a
        rw [Matrix.mul_diagonal]
        simp only [Matrix.mul_apply, hO, Matrix.of_apply]
        simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
        rw [this, mul_comm]
      refine ⟨O, μ, h1, ?_⟩
      calc Q = Q * (O * O.transpose) := by rw [h2, Matrix.mul_one]
        _ = (Q * O) * O.transpose := by rw [Matrix.mul_assoc]
        _ = O * Matrix.diagonal μ * O.transpose := by rw [h3]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZspec_aux_form : ∀ (n : ℕ) (Q O : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ)
      (hQ : Q = O * Matrix.diagonal D * O.transpose) (u v : Fin n → ℝ), u ⬝ᵥ (Q *ᵥ v) = ∑ i, D i * (O.transpose *ᵥ u) i * (O.transpose *ᵥ v) i :=
    fun (n : ℕ) (Q O : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ)
        (hQ : Q = O * Matrix.diagonal D * O.transpose) (u v : Fin n → ℝ) => by
      rw [hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose]
      simp only [dotProduct, Matrix.mulVec_diagonal]
      apply Finset.sum_congr rfl; intro i _; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZspec_aux_A : ∀ (n : ℕ) (D : Fin n → ℝ) (h1 : (Finset.univ.filter (fun i => 0 < D i)).card = 1)
      (y z : Fin n → ℝ) (hy : 0 < ∑ i, D i * y i * y i), (∑ i, D i * y i * y i) * (∑ i, D i * z i * z i) ≤ (∑ i, D i * y i * z i) ^ 2 :=
    fun (n : ℕ) (D : Fin n → ℝ) (h1 : (Finset.univ.filter (fun i => 0 < D i)).card = 1)
        (y z : Fin n → ℝ) (hy : 0 < ∑ i, D i * y i * y i) => by
      obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp h1
      have hneg : ∀ i, i ≠ i0 → D i ≤ 0 := by
        intro i hi; by_contra hc; push_neg at hc
        have : i ∈ Finset.univ.filter (fun i => 0 < D i) := by simp [hc]
        rw [hi0, Finset.mem_singleton] at this; exact hi this
      have hnp : ∀ w : Fin n → ℝ, w i0 = 0 → ∑ i, D i * w i * w i ≤ 0 := by
        intro w hw
        apply Finset.sum_nonpos; intro i _
        by_cases h : i = i0
        · rw [h, hw]; simp
        · nlinarith [hneg i h, mul_self_nonneg (w i)]
      have hy0 : y i0 ≠ 0 := by
        intro h; have := hnp y h; linarith
      have hw := hnp (fun i => z i - (z i0 / y i0) * y i) (by simp only; field_simp; ring)
      have hexp : ∑ i, D i * (z i - (z i0 / y i0) * y i) * (z i - (z i0 / y i0) * y i)
          = ∑ i, D i * z i * z i - 2 * (z i0 / y i0) * ∑ i, D i * y i * z i
            + (z i0 / y i0) ^ 2 * ∑ i, D i * y i * y i := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      simp only at hw
      rw [hexp] at hw
      have hm := mul_le_mul_of_nonneg_left hw hy.le
      nlinarith [sq_nonneg (∑ i, D i * y i * z i - (z i0 / y i0) * ∑ i, D i * y i * y i)]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZspec_aux_B : ∀ (n : ℕ) (D : Fin n → ℝ)
      (hN : ∀ y z : Fin n → ℝ, 0 < ∑ i, D i * y i * y i →
        (∑ i, D i * y i * y i) * (∑ i, D i * z i * z i) ≤ (∑ i, D i * y i * z i) ^ 2)
      (hpos : ∃ y : Fin n → ℝ, 0 < ∑ i, D i * y i * y i), (Finset.univ.filter (fun i => 0 < D i)).card = 1 :=
    fun (n : ℕ) (D : Fin n → ℝ)
        (hN : ∀ y z : Fin n → ℝ, 0 < ∑ i, D i * y i * y i →
          (∑ i, D i * y i * y i) * (∑ i, D i * z i * z i) ≤ (∑ i, D i * y i * z i) ^ 2)
        (hpos : ∃ y : Fin n → ℝ, 0 < ∑ i, D i * y i * y i) => by
      obtain ⟨y, hy⟩ := hpos
      have hne : ∃ i, 0 < D i := by
        by_contra hc; push_neg at hc
        have : ∑ i, D i * y i * y i ≤ 0 :=
          Finset.sum_nonpos (fun i _ => by nlinarith [hc i, mul_self_nonneg (y i)])
        linarith
      obtain ⟨i0, hi0⟩ := hne
      have e1 : ∀ a : Fin n, ∑ i, D i * (Pi.single a (1:ℝ) : Fin n → ℝ) i *
          (Pi.single a (1:ℝ) : Fin n → ℝ) i = D a := by
        intro a
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [Pi.single_apply, hb]
        · intro h; exact absurd (Finset.mem_univ a) h
      have e2 : ∀ a b : Fin n, a ≠ b → ∑ i, D i * (Pi.single a (1:ℝ) : Fin n → ℝ) i *
          (Pi.single b (1:ℝ) : Fin n → ℝ) i = 0 := by
        intro a b hab
        apply Finset.sum_eq_zero; intro i _
        by_cases h : i = a
        · subst h; simp [Pi.single_apply, hab]
        · simp [Pi.single_apply, h]
      have h1 : 1 ≤ (Finset.univ.filter (fun i => 0 < D i)).card :=
        Finset.card_pos.mpr ⟨i0, by simp [hi0]⟩
      have h2 : (Finset.univ.filter (fun i => 0 < D i)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        by_contra hab
        have := hN (Pi.single a 1) (Pi.single b 1) (by rw [e1]; exact ha)
        rw [e1, e1, e2 a b hab] at this
        nlinarith [mul_pos ha hb]
      omega
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZspec_aux_charpoly : ∀ (n : ℕ) (Q O : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ)
      (hO : O.transpose * O = 1) (hQ : Q = O * Matrix.diagonal D * O.transpose), Q.charpoly = (Matrix.diagonal D).charpoly :=
    fun (n : ℕ) (Q O : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ)
        (hO : O.transpose * O = 1) (hQ : Q = O * Matrix.diagonal D * O.transpose) => by
      rw [hQ, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hO, Matrix.one_mul]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZspec_aux_roots : ∀ (n : ℕ) (D : Fin n → ℝ), ((Matrix.diagonal D).charpoly.roots.filter (0 < ·)).card =
        (Finset.univ.filter (fun i => 0 < D i)).card :=
    fun (n : ℕ) (D : Fin n → ℝ) => by
      rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod]
      have : Multiset.map (fun i => Polynomial.X - Polynomial.C (D i)) (Finset.univ : Finset (Fin n)).val
          = Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map D Finset.univ.val) := by
        rw [Multiset.map_map]; rfl
      rw [this, Polynomial.roots_multiset_prod_X_sub_C, Multiset.filter_map, Multiset.card_map]
      rfl
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZspec : ∀ (n : ℕ) (hn : 0 < n) (g : H n 2), g ∈ Ŀ n 2 ↔ (g ∈ P n 2 ∧ IsUnit (H.hessian g) ∧
        ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (H.hessian g *ᵥ u) →
          (u ⬝ᵥ (H.hessian g *ᵥ u)) * (v ⬝ᵥ (H.hessian g *ᵥ v)) ≤
            (u ⬝ᵥ (H.hessian g *ᵥ v)) ^ 2) :=
    fun (n : ℕ) (hn : 0 < n) (g : H n 2) => by
      have hsym : (H.hessian g).transpose = H.hessian g := by
        ext i j
        simp only [Matrix.transpose_apply, H.hessian]
        by_cases h : i = j
        · subst h; simp
        · rw [if_neg (Ne.symm h), if_neg h, add_comm]
      obtain ⟨O, D, hO, hQ⟩ := LZeig n (H.hessian g) hsym
      have hcard : ((H.hessian g).charpoly.roots.filter (0 < ·)).card =
          (Finset.univ.filter (fun i => 0 < D i)).card := by
        rw [LZspec_aux_charpoly n _ O D hO hQ, LZspec_aux_roots]
      have hform := LZspec_aux_form n _ O D hQ
      show (g ∈ P n 2 ∧ IsUnit (H.hessian g) ∧
          ((H.hessian g).charpoly.roots.filter (0 < ·)).card = 1) ↔ _
      rw [hcard]
      constructor
      · rintro ⟨hP, hU, h1⟩
        refine ⟨hP, hU, ?_⟩
        intro u v hu
        rw [hform] at hu
        rw [hform, hform, hform]
        exact LZspec_aux_A n D h1 _ _ hu
      · rintro ⟨hP, hU, hN⟩
        refine ⟨hP, hU, ?_⟩
        apply LZspec_aux_B n D
        · intro y z hy
          have := hN (O *ᵥ y) (O *ᵥ z)
          rw [hform, hform, hform] at this
          have ey : O.transpose *ᵥ (O *ᵥ y) = y := by
            rw [Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
          have ez : O.transpose *ᵥ (O *ᵥ z) = z := by
            rw [Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
          rw [ey, ez] at this
          exact this hy
        · refine ⟨O.transpose *ᵥ Pi.single ⟨0, hn⟩ 1, ?_⟩
          rw [← hform]
          have e : (Pi.single (⟨0, hn⟩ : Fin n) 1 : Fin n → ℝ) ⬝ᵥ
              (H.hessian g *ᵥ Pi.single ⟨0, hn⟩ 1) = H.hessian g ⟨0, hn⟩ ⟨0, hn⟩ := by
            simp [Matrix.mulVec, dotProduct, Pi.single_apply]
          rw [e]
          simp only [H.hessian, if_true]
          have hw : weight 1 (Finsupp.single (⟨0, hn⟩ : Fin n) 2) = 2 := by
            simp [Finsupp.weight_apply, Finsupp.sum_single_index]
          have := hP _ hw
          linarith
  open Matrix in
  have LZpf_aux_form : ∀ (n : ℕ) (Q O : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ)
      (hQ : Q = O * Matrix.diagonal D * O.transpose) (u v : Fin n → ℝ), u ⬝ᵥ (Q *ᵥ v) = ∑ i, D i * (O.transpose *ᵥ u) i * (O.transpose *ᵥ v) i :=
    fun (n : ℕ) (Q O : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ)
        (hQ : Q = O * Matrix.diagonal D * O.transpose) (u v : Fin n → ℝ) => by
      rw [hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose]
      simp only [dotProduct, Matrix.mulVec_diagonal]
      apply Finset.sum_congr rfl; intro i _; ring
  open Matrix in
  have LZpf_aux_diag : ∀ (n : ℕ) (D : Fin n → ℝ) (h1 : ∀ i i', 0 < D i → 0 < D i' → i = i')
      (y z : Fin n → ℝ) (hy : 0 < ∑ i, D i * y i * y i), (∑ i, D i * y i * y i) * (∑ i, D i * z i * z i) ≤ (∑ i, D i * y i * z i) ^ 2 :=
    fun (n : ℕ) (D : Fin n → ℝ) (h1 : ∀ i i', 0 < D i → 0 < D i' → i = i')
        (y z : Fin n → ℝ) (hy : 0 < ∑ i, D i * y i * y i) => by
      have hne : ∃ i, 0 < D i := by
        by_contra hc; push_neg at hc
        have : ∑ i, D i * y i * y i ≤ 0 :=
          Finset.sum_nonpos (fun i _ => by nlinarith [hc i, mul_self_nonneg (y i)])
        linarith
      obtain ⟨i0, hi0⟩ := hne
      have hneg : ∀ i, i ≠ i0 → D i ≤ 0 := by
        intro i hi; by_contra hc; push_neg at hc
        exact hi (h1 i i0 hc hi0)
      have hnp : ∀ w : Fin n → ℝ, w i0 = 0 → ∑ i, D i * w i * w i ≤ 0 := by
        intro w hw
        apply Finset.sum_nonpos; intro i _
        by_cases h : i = i0
        · rw [h, hw]; simp
        · nlinarith [hneg i h, mul_self_nonneg (w i)]
      have hy0 : y i0 ≠ 0 := by
        intro h; have := hnp y h; linarith
      have hw := hnp (fun i => z i - (z i0 / y i0) * y i) (by simp only; field_simp; ring)
      have hexp : ∑ i, D i * (z i - (z i0 / y i0) * y i) * (z i - (z i0 / y i0) * y i)
          = ∑ i, D i * z i * z i - 2 * (z i0 / y i0) * ∑ i, D i * y i * z i
            + (z i0 / y i0) ^ 2 * ∑ i, D i * y i * y i := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      simp only at hw
      rw [hexp] at hw
      have hm := mul_le_mul_of_nonneg_left hw hy.le
      nlinarith [sq_nonneg (∑ i, D i * y i * z i - (z i0 / y i0) * ∑ i, D i * y i * y i)]
  open Matrix in
  have LZpf_aux_PF : ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (R : Finset (Fin n))
      (hBs : ∀ j k, B j k = B k j) (hBn : ∀ j k, 0 ≤ B j k) (hu : ∀ j, 0 < u j)
      (hBu : ∀ j ∈ R, (B *ᵥ u) j = u j) (hR : ∀ j ∉ R, ∀ k, B j k = 0)
      (hirr : ∀ S : Finset (Fin n), (∃ j ∈ S, j ∈ R) → (∃ j ∉ S, j ∈ R) →
        ∃ j ∈ S, ∃ k ∉ S, 0 < B j k)
      (v : Fin n → ℝ) (lam : ℝ) (hv : B *ᵥ v = lam • v) (hlam : 1 ≤ lam) (hv0 : v ≠ 0), lam = 1 ∧ ∃ c : ℝ, ∀ j, v j = c * (if j ∈ R then u j else 0) :=
    fun (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (R : Finset (Fin n))
        (hBs : ∀ j k, B j k = B k j) (hBn : ∀ j k, 0 ≤ B j k) (hu : ∀ j, 0 < u j)
        (hBu : ∀ j ∈ R, (B *ᵥ u) j = u j) (hR : ∀ j ∉ R, ∀ k, B j k = 0)
        (hirr : ∀ S : Finset (Fin n), (∃ j ∈ S, j ∈ R) → (∃ j ∉ S, j ∈ R) →
          ∃ j ∈ S, ∃ k ∉ S, 0 < B j k)
        (v : Fin n → ℝ) (lam : ℝ) (hv : B *ᵥ v = lam • v) (hlam : 1 ≤ lam) (hv0 : v ≠ 0) => by
      have hvj : ∀ j, ∑ k, B j k * v k = lam * v j := by
        intro j; have := congrFun hv j; simpa [mulVec, dotProduct] using this
      have huj : ∀ j, (B *ᵥ u) j = ∑ k, B j k * u k := fun j => rfl
      have hoff : ∀ j ∉ R, v j = 0 := by
        intro j hj
        have h := hvj j
        simp only [hR j hj, zero_mul, Finset.sum_const_zero] at h
        have : lam ≠ 0 := by linarith
        exact (mul_eq_zero.mp h.symm).resolve_left this
      obtain ⟨k0, hk0⟩ : ∃ k, v k ≠ 0 := by
        by_contra hc; push_neg at hc; exact hv0 (funext hc)
      have hBu_le : ∀ j, ∑ k, B j k * u k ≤ u j := by
        intro j
        by_cases hj : j ∈ R
        · rw [← huj]; exact (hBu j hj).le
        · simp [hR j hj, (hu j).le]
      -- λ ≤ 1
      have hlam1 : lam ≤ 1 := by
        obtain ⟨js, -, hjs⟩ := Finset.exists_max_image Finset.univ (fun j => |v j| / u j)
          ⟨k0, Finset.mem_univ _⟩
        set M := |v js| / u js with hM
        have hle : ∀ k, |v k| ≤ M * u k := by
          intro k
          have := hjs k (Finset.mem_univ _)
          rw [div_le_iff₀ (hu k)] at this; exact this
        have hMpos : 0 < M := by
          have h1 : 0 < |v k0| / u k0 := div_pos (abs_pos.mpr hk0) (hu k0)
          exact lt_of_lt_of_le h1 (hjs k0 (Finset.mem_univ _))
        have hvjs : |v js| = M * u js := by
          rw [hM]; field_simp [(hu js).ne']
        have h1 : lam * |v js| ≤ |v js| := by
          calc lam * |v js| = |∑ k, B js k * v k| := by
                  rw [hvj js, abs_mul, abs_of_pos (by linarith : (0:ℝ) < lam)]
            _ ≤ ∑ k, |B js k * v k| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k, B js k * (M * u k) := by
                  apply Finset.sum_le_sum; intro k _
                  rw [abs_mul, abs_of_nonneg (hBn js k)]
                  exact mul_le_mul_of_nonneg_left (hle k) (hBn js k)
            _ = M * ∑ k, B js k * u k := by
                  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
            _ ≤ M * u js := mul_le_mul_of_nonneg_left (hBu_le js) hMpos.le
            _ = |v js| := hvjs.symm
        have hpos : 0 < |v js| := by rw [hvjs]; exact mul_pos hMpos (hu js)
        nlinarith
      have hl : lam = 1 := le_antisymm hlam1 hlam
      refine ⟨hl, ?_⟩
      subst hl
      have hk0R : k0 ∈ R := by
        by_contra h; exact hk0 (hoff k0 h)
      obtain ⟨j0, hj0R, hj0⟩ := Finset.exists_max_image R (fun j => v j / u j) ⟨k0, hk0R⟩
      set M := v j0 / u j0 with hM
      have hle : ∀ k ∈ R, v k ≤ M * u k := by
        intro k hk
        have := hj0 k hk
        rw [div_le_iff₀ (hu k)] at this; exact this
      have hall : ∀ j ∈ R, v j / u j = M := by
        by_contra hc
        push_neg at hc
        obtain ⟨j1, hj1R, hj1⟩ := hc
        obtain ⟨j, hjS, k, hkS, hjk⟩ := hirr (R.filter (fun j => v j / u j = M))
          ⟨j0, by simp [hj0R, hM], hj0R⟩ ⟨j1, by simp [hj1], hj1R⟩
        simp only [Finset.mem_filter, not_and] at hjS hkS
        have hkR : k ∈ R := by
          by_contra h
          have := hR k h j
          rw [hBs j k, this] at hjk; exact lt_irrefl _ hjk
        have hk_lt : v k < M * u k := by
          have h1 := hle k hkR
          have h2 : v k ≠ M * u k := by
            intro h; apply hkS hkR; rw [h]; field_simp [(hu k).ne']
          exact lt_of_le_of_ne h1 h2
        have hvj0 : v j = M * u j := by
          rw [← hjS.2]; field_simp [(hu j).ne']
        have hsum : ∑ l, B j l * (M * u l - v l) = 0 := by
          have e1 : ∑ l, B j l * (M * u l - v l) = M * ∑ l, B j l * u l - ∑ l, B j l * v l := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro l _; ring
          rw [e1, hvj j, ← huj, hBu j hjS.1, hvj0]; ring
        have hnn : ∀ l ∈ Finset.univ, 0 ≤ B j l * (M * u l - v l) := by
          intro l _
          by_cases hl : l ∈ R
          · exact mul_nonneg (hBn j l) (by linarith [hle l hl])
          · rw [hBs j l, hR l hl j]; simp
        have hpos : 0 < B j k * (M * u k - v k) := mul_pos hjk (by linarith)
        have := Finset.single_le_sum hnn (Finset.mem_univ k)
        linarith
      refine ⟨M, fun j => ?_⟩
      by_cases hj : j ∈ R
      · rw [if_pos hj, ← hall j hj]; field_simp [(hu j).ne']
      · rw [if_neg hj, hoff j hj]; ring
  open Matrix in
  have LZpf : ∀ (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
      (hsym1 : ∀ i j k, Q i j k = Q j i k) (hsym2 : ∀ i j k, Q i j k = Q i k j)
      (hnn : ∀ i j k, 0 ≤ Q i j k) (ha : ∀ i, 0 < a i)
      (hQ : ∀ i (u v : Fin n → ℝ), 0 < u ⬝ᵥ (Q i *ᵥ u) →
        (u ⬝ᵥ (Q i *ᵥ u)) * (v ⬝ᵥ (Q i *ᵥ v)) ≤ (u ⬝ᵥ (Q i *ᵥ v)) ^ 2)
      (hirr : ∀ S : Finset (Fin n), (∃ j ∈ S, ∃ k k', 0 < Q j k k') →
        (∃ j ∉ S, ∃ k k', 0 < Q j k k') → ∃ j ∈ S, ∃ k ∉ S, ∃ i, 0 < Q i j k), ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ ((∑ i, a i • Q i) *ᵥ u) →
        (u ⬝ᵥ ((∑ i, a i • Q i) *ᵥ u)) * (v ⬝ᵥ ((∑ i, a i • Q i) *ᵥ v)) ≤
          (u ⬝ᵥ ((∑ i, a i • Q i) *ᵥ v)) ^ 2 :=
    fun (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
        (hsym1 : ∀ i j k, Q i j k = Q j i k) (hsym2 : ∀ i j k, Q i j k = Q i k j)
        (hnn : ∀ i j k, 0 ≤ Q i j k) (ha : ∀ i, 0 < a i)
        (hQ : ∀ i (u v : Fin n → ℝ), 0 < u ⬝ᵥ (Q i *ᵥ u) →
          (u ⬝ᵥ (Q i *ᵥ u)) * (v ⬝ᵥ (Q i *ᵥ v)) ≤ (u ⬝ᵥ (Q i *ᵥ v)) ^ 2)
        (hirr : ∀ S : Finset (Fin n), (∃ j ∈ S, ∃ k k', 0 < Q j k k') →
          (∃ j ∉ S, ∃ k k', 0 < Q j k k') → ∃ j ∈ S, ∃ k ∉ S, ∃ i, 0 < Q i j k) => by
      set A := ∑ i, a i • Q i with hAdef
      have hA : ∀ j k, A j k = ∑ i, a i * Q i j k := by
        intro j k; simp [hAdef, Matrix.sum_apply]
      have hAs : ∀ j k, A j k = A k j := by
        intro j k; rw [hA, hA]; apply Finset.sum_congr rfl; intro i _; rw [hsym2]
      have hAn : ∀ j k, 0 ≤ A j k := by
        intro j k; rw [hA]; exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i).le (hnn i j k))
      have F1 : ∀ (z : Fin n → ℝ) j, (A *ᵥ z) j = a ⬝ᵥ (Q j *ᵥ z) := by
        intro z j
        simp only [mulVec, dotProduct, hA, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _
        rw [hsym1]; ring
      have F2 : ∀ z : Fin n → ℝ, z ⬝ᵥ (A *ᵥ z) = ∑ j, a j * (z ⬝ᵥ (Q j *ᵥ z)) := by
        intro z
        simp only [mulVec, dotProduct, hA, Finset.sum_mul, Finset.mul_sum]
        have : ∀ j : Fin n, ∑ k, ∑ i, z j * (a i * Q i j k * z k) = ∑ i, ∑ k, z j * (a i * Q i j k * z k) :=
          fun j => Finset.sum_comm
        rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _; ring
      set r : Fin n → ℝ := fun j => (A *ᵥ a) j with hrdef
      have hr : ∀ j, r j = ∑ k, A j k * a k := fun j => rfl
      have hr_nn : ∀ j, 0 ≤ r j := fun j => by
        rw [hr]; exact Finset.sum_nonneg (fun k _ => mul_nonneg (hAn j k) (ha k).le)
      have hrQ : ∀ j, r j = a ⬝ᵥ (Q j *ᵥ a) := fun j => F1 a j
      have hQ0 : ∀ j, r j = 0 → ∀ k l, Q j k l = 0 := by
        intro j hj k l
        rw [hrQ] at hj
        simp only [dotProduct, mulVec] at hj
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (ha k).le
          (Finset.sum_nonneg (fun l _ => mul_nonneg (hnn j k l) (ha l).le)))).mp hj k
          (Finset.mem_univ _)
        have h2 : ∑ l, Q j k l * a l = 0 := (mul_eq_zero.mp h1).resolve_left (ha k).ne'
        have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_nonneg (hnn j k l)
          (ha l).le)).mp h2 l (Finset.mem_univ _)
        exact (mul_eq_zero.mp h3).resolve_right (ha l).ne'
      have hA0 : ∀ j, r j = 0 → ∀ k, A j k = 0 := by
        intro j hj k
        rw [hr] at hj
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hAn j k)
          (ha k).le)).mp hj k (Finset.mem_univ _)
        exact (mul_eq_zero.mp h1).resolve_right (ha k).ne'
      set e : Fin n → ℝ := fun j => if 0 < r j then r j / a j else 1 with hedef
      have he : ∀ j, 0 < e j := by
        intro j; simp only [hedef]; split_ifs with h
        · exact div_pos h (ha j)
        · norm_num
      set s : Fin n → ℝ := fun j => Real.sqrt (e j) with hsdef
      have hs : ∀ j, 0 < s j := fun j => Real.sqrt_pos.mpr (he j)
      have hs2 : ∀ j, s j * s j = e j := fun j => Real.mul_self_sqrt (he j).le
      set B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun j k => A j k / (s j * s k)) with hBdef
      have hB : ∀ j k, B j k = A j k / (s j * s k) := fun j k => rfl
      have hBs : ∀ j k, B j k = B k j := by intro j k; rw [hB, hB, hAs, mul_comm (s j)]
      have hBn : ∀ j k, 0 ≤ B j k := fun j k =>
        div_nonneg (hAn j k) (mul_pos (hs j) (hs k)).le
      -- B 满足 yᵀBy ≤ |By|²
      have hBkey : ∀ y : Fin n → ℝ, y ⬝ᵥ (B *ᵥ y) ≤ (B *ᵥ y) ⬝ᵥ (B *ᵥ y) := by
        intro y
        set z : Fin n → ℝ := fun j => y j / s j with hzdef
        have hAz : ∀ j, (A *ᵥ z) j = s j * (B *ᵥ y) j := by
          intro j
          simp only [mulVec, dotProduct, hB, hzdef, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _
          field_simp [(hs j).ne', (hs k).ne']
        have hyz : y ⬝ᵥ (B *ᵥ y) = z ⬝ᵥ (A *ᵥ z) := by
          simp only [dotProduct, hAz]
          simp only [mulVec, dotProduct, hB, hzdef, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _
          field_simp [(hs j).ne', (hs k).ne']
        rw [hyz, F2]
        show ∑ j, a j * (z ⬝ᵥ (Q j *ᵥ z)) ≤ ∑ j, (B *ᵥ y) j * (B *ᵥ y) j
        apply Finset.sum_le_sum; intro j _
        by_cases hrj : 0 < r j
        · have h1 := hQ j a z (by rw [← hrQ]; exact hrj)
          rw [← hrQ, ← F1, hAz] at h1
          have hej : e j = r j / a j := by simp [hedef, hrj]
          have h2 : r j * (z ⬝ᵥ (Q j *ᵥ z)) ≤ r j / a j * ((B *ᵥ y) j * (B *ᵥ y) j) := by
            rw [← hej, ← hs2]; nlinarith
          rw [div_mul_eq_mul_div, le_div_iff₀ (ha j)] at h2
          have h3 : r j * (a j * (z ⬝ᵥ (Q j *ᵥ z))) ≤ r j * ((B *ᵥ y) j * (B *ᵥ y) j) := by
            nlinarith
          exact le_of_mul_le_mul_left h3 hrj
        · have hr0 : r j = 0 := le_antisymm (not_lt.mp hrj) (hr_nn j)
          have : z ⬝ᵥ (Q j *ᵥ z) = 0 := by
            simp [dotProduct, mulVec, hQ0 j hr0]
          rw [this, mul_zero]; exact mul_self_nonneg _
      -- Perron–Frobenius 数据
      set R : Finset (Fin n) := Finset.univ.filter (fun j => 0 < r j) with hRdef
      set u0 : Fin n → ℝ := fun j => s j * a j with hu0def
      have hu0 : ∀ j, 0 < u0 j := fun j => mul_pos (hs j) (ha j)
      have hBu : ∀ j ∈ R, (B *ᵥ u0) j = u0 j := by
        intro j hj
        simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hej : s j * s j = r j / a j := by rw [hs2]; simp [hedef, hj]
        have e1 : (B *ᵥ u0) j = r j / s j := by
          rw [hr, div_eq_mul_inv, Finset.sum_mul]
          simp only [mulVec, dotProduct, hB, hu0def]
          apply Finset.sum_congr rfl; intro k _
          field_simp [(hs j).ne', (hs k).ne']
        rw [e1, hu0def]
        rw [eq_div_iff (ha j).ne'] at hej
        field_simp [(hs j).ne']
        linear_combination -hej
      have hRB : ∀ j ∉ R, ∀ k, B j k = 0 := by
        intro j hj k
        simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hr0 : r j = 0 := le_antisymm (not_lt.mp hj) (hr_nn j)
        rw [hB, hA0 j hr0 k, zero_div]
      have hirrB : ∀ S : Finset (Fin n), (∃ j ∈ S, j ∈ R) → (∃ j ∉ S, j ∈ R) →
          ∃ j ∈ S, ∃ k ∉ S, 0 < B j k := by
        intro S ⟨j, hjS, hjR⟩ ⟨j', hj'S, hj'R⟩
        have hex : ∀ j ∈ R, ∃ k k', 0 < Q j k k' := by
          intro j hj
          by_contra hc; push_neg at hc
          simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have : r j = 0 := by
            rw [hrQ]; simp [dotProduct, mulVec, fun k l => le_antisymm (hc k l) (hnn j k l)]
          linarith
        obtain ⟨j1, hj1, k1, hk1, i1, hi1⟩ := hirr S ⟨j, hjS, hex j hjR⟩ ⟨j', hj'S, hex j' hj'R⟩
        refine ⟨j1, hj1, k1, hk1, ?_⟩
        rw [hB]
        apply div_pos _ (mul_pos (hs j1) (hs k1))
        rw [hA]
        exact lt_of_lt_of_le (mul_pos (ha i1) hi1)
          (Finset.single_le_sum (f := fun i => a i * Q i j1 k1)
            (fun i _ => mul_nonneg (ha i).le (hnn i j1 k1)) (Finset.mem_univ i1))
      -- 谱分解
      have hBt : B.transpose = B := by
        ext j k; rw [Matrix.transpose_apply, hBs]
      obtain ⟨O, D, hO, hBO⟩ := LZeig n B hBt
      set o : Fin n → Fin n → ℝ := fun i => O *ᵥ Pi.single i 1 with hodef
      have hOt : ∀ i, O.transpose *ᵥ o i = Pi.single i 1 := by
        intro i; rw [hodef]; simp only; rw [Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
      have hBo : ∀ i, B *ᵥ o i = D i • o i := by
        intro i
        rw [hBO, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hOt, Matrix.mulVec_single]
        rw [hodef]; simp only
        rw [← Matrix.mulVec_smul]; congr 1
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [Pi.single_apply, h]
      have hoo : ∀ i i', o i ⬝ᵥ o i' = if i = i' then 1 else 0 := by
        intro i i'
        have : o i ⬝ᵥ o i' = (O.transpose *ᵥ o i) ⬝ᵥ Pi.single i' 1 := by
          conv_lhs => rw [show o i' = O *ᵥ Pi.single i' 1 from rfl]
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
        rw [this, hOt]
        by_cases h : i = i' <;> simp [h, Pi.single_apply]
      have hDsq : ∀ i, D i ≤ D i * D i := by
        intro i
        have h := hBkey (o i)
        rw [hBo, dotProduct_smul, smul_dotProduct, dotProduct_smul, hoo] at h
        simpa using h
      have hdot : ∀ (x y w : Fin n → ℝ) (c c' : ℝ), (∀ j, x j = c * w j) → (∀ j, y j = c' * w j) →
          x ⬝ᵥ y = c * c' * (w ⬝ᵥ w) := by
        intro x y w c c' hx hy
        simp only [dotProduct, hx, hy, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
      have h1 : ∀ i i', 0 < D i → 0 < D i' → i = i' := by
        intro i i' hi hi'
        by_contra hne
        have hne0 : ∀ i, o i ≠ 0 := by
          intro i h; have := hoo i i; rw [h] at this; simp at this
        have hge : ∀ i, 0 < D i → 1 ≤ D i := by
          intro i hi; have := hDsq i; nlinarith
        obtain ⟨-, c, hc⟩ := LZpf_aux_PF n B u0 R hBs hBn hu0 hBu hRB hirrB (o i) (D i) (hBo i)
          (hge i hi) (hne0 i)
        obtain ⟨-, c', hc'⟩ := LZpf_aux_PF n B u0 R hBs hBn hu0 hBu hRB hirrB (o i') (D i') (hBo i')
          (hge i' hi') (hne0 i')
        set w : Fin n → ℝ := fun j => if j ∈ R then u0 j else 0
        have e1 := hdot _ _ w c c hc hc
        have e2 := hdot _ _ w c' c' hc' hc'
        have e3 := hdot _ _ w c c' hc hc'
        rw [hoo, if_pos rfl] at e1 e2
        rw [hoo, if_neg hne] at e3
        have : (c * c' * (w ⬝ᵥ w)) * (c * c' * (w ⬝ᵥ w)) = (c * c * (w ⬝ᵥ w)) * (c' * c' * (w ⬝ᵥ w)) := by
          ring
        rw [← e1, ← e2, ← e3] at this; norm_num at this
      have hNB : ∀ y z : Fin n → ℝ, 0 < y ⬝ᵥ (B *ᵥ y) →
          (y ⬝ᵥ (B *ᵥ y)) * (z ⬝ᵥ (B *ᵥ z)) ≤ (y ⬝ᵥ (B *ᵥ z)) ^ 2 := by
        intro y z hy
        rw [LZpf_aux_form n B O D hBO] at hy ⊢
        rw [LZpf_aux_form n B O D hBO, LZpf_aux_form n B O D hBO]
        exact LZpf_aux_diag n D h1 _ _ hy
      have hcong : ∀ x y : Fin n → ℝ, x ⬝ᵥ (A *ᵥ y) =
          (fun j => s j * x j) ⬝ᵥ (B *ᵥ (fun j => s j * y j)) := by
        intro x y
        simp only [dotProduct, mulVec, hB, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _
        field_simp [(hs j).ne', (hs k).ne']
      intro u v hu
      rw [hcong u u] at hu
      rw [hcong u u, hcong v v, hcong u v]
      exact hNB _ _ hu
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZtop_lin : ∀ (n d : ℕ) (φ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ), Continuous (fun f : H n d => φ f.1) :=
    fun (n d : ℕ) (φ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) => by
      letI : TopologicalSpace (homogeneousSubmodule (Fin n) ℝ d) := moduleTopology ℝ _
      haveI : IsModuleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d) := ⟨rfl⟩
      exact IsModuleTopology.continuous_of_linearMap
        (φ.comp (homogeneousSubmodule (Fin n) ℝ d).subtype)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZtop_pderiv : ∀ (n d : ℕ) (i : Fin n), @Continuous (H n (d + 3)) (H n (d + 2)) _ _ (fun f => ⟨f.1.pderiv i, f.2.pderiv⟩) :=
    fun (n d : ℕ) (i : Fin n) => by
      letI : TopologicalSpace (homogeneousSubmodule (Fin n) ℝ (d + 3)) := moduleTopology ℝ _
      haveI : IsModuleTopology ℝ (homogeneousSubmodule (Fin n) ℝ (d + 3)) := ⟨rfl⟩
      letI : TopologicalSpace (homogeneousSubmodule (Fin n) ℝ (d + 2)) := moduleTopology ℝ _
      haveI : IsModuleTopology ℝ (homogeneousSubmodule (Fin n) ℝ (d + 2)) := ⟨rfl⟩
      let ψ : homogeneousSubmodule (Fin n) ℝ (d + 3) →ₗ[ℝ] homogeneousSubmodule (Fin n) ℝ (d + 2) :=
        LinearMap.codRestrict _
          ((pderiv i).toLinearMap.comp (homogeneousSubmodule (Fin n) ℝ (d + 3)).subtype)
          (fun f => f.2.pderiv)
      haveI : ContinuousAdd (homogeneousSubmodule (Fin n) ℝ (d + 2)) := ModuleTopology.continuousAdd ℝ _
      haveI : ContinuousSMul ℝ (homogeneousSubmodule (Fin n) ℝ (d + 2)) :=
        ModuleTopology.continuousSMul ℝ _
      exact IsModuleTopology.continuous_of_linearMap ψ
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZtop_aux_fin : ∀ (n d : ℕ), ∃ D : Finset (Fin n →₀ ℕ), ∀ m, m ∈ D ↔ weight 1 m = d :=
    fun (n d : ℕ) => by
      classical
      refine ⟨(Finset.univ.image (fun g : Fin n → Fin (d+1) =>
        Finsupp.equivFunOnFinite.symm (fun i => (g i : ℕ)))).filter (fun m => weight 1 m = d), ?_⟩
      intro m
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨⟨fun i => ⟨m i, ?_⟩, ?_⟩, h⟩
        · have : m i ≤ weight 1 m := by
            rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
            simpa using Finset.single_le_sum (f := fun j => m j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
          omega
        · ext i; simp
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZtop_aux_main : ∀ (n d : ℕ), ∃ (D : Finset (Fin n →₀ ℕ)) (g : (D → ℝ) → H n d),
        Continuous g ∧ ∀ p : H n d, g (fun m => p.1.coeff m.1) = p :=
    fun (n d : ℕ) => by
      letI : TopologicalSpace (homogeneousSubmodule (Fin n) ℝ d) := moduleTopology ℝ _
      haveI : IsModuleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d) := ⟨rfl⟩
      haveI : ContinuousAdd (homogeneousSubmodule (Fin n) ℝ d) := ModuleTopology.continuousAdd ℝ _
      haveI : ContinuousSMul ℝ (homogeneousSubmodule (Fin n) ℝ d) :=
        ModuleTopology.continuousSMul ℝ _
      obtain ⟨D, hD⟩ := LZtop_aux_fin n d
      let e : D → homogeneousSubmodule (Fin n) ℝ d := fun m => ⟨monomial m.1 1, by
        rw [mem_homogeneousSubmodule]
        intro m' h
        rw [coeff_monomial] at h
        split_ifs at h with hm
        · rw [← hm]; exact (hD _).1 m.2
        · exact absurd rfl h⟩
      let gl : (D → ℝ) →ₗ[ℝ] homogeneousSubmodule (Fin n) ℝ d :=
        ∑ m : D, (LinearMap.proj m : (D → ℝ) →ₗ[ℝ] ℝ).smulRight (e m)
      refine ⟨D, gl, IsModuleTopology.continuous_of_linearMap gl, ?_⟩
      intro p
      apply Subtype.ext
      simp only [gl, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
        LinearMap.proj_apply, Submodule.coe_sum, Submodule.coe_smul, e]
      ext m
      rw [coeff_sum]
      simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_coe_sort D (fun x => if x = m then p.1.coeff x else 0)]
      rw [Finset.sum_ite_eq']
      split_ifs with hm
      · rfl
      · by_contra hne
        exact hm ((hD m).2 (((mem_homogeneousSubmodule _ _).1 p.2) (Ne.symm hne)))
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZtop : ∀ (n d : ℕ) (ι : Type) (l : Filter ι) (F : ι → H n d) (f : H n d)
      (hc : ∀ m, Filter.Tendsto (fun t => (F t).1.coeff m) l (nhds (f.1.coeff m))), Filter.Tendsto F l (nhds f) :=
    fun (n d : ℕ) (ι : Type) (l : Filter ι) (F : ι → H n d) (f : H n d)
        (hc : ∀ m, Filter.Tendsto (fun t => (F t).1.coeff m) l (nhds (f.1.coeff m))) => by
      obtain ⟨D, g, hg, hgc⟩ := LZtop_aux_main n d
      have h1 : Filter.Tendsto (fun t => (fun m : D => (F t).1.coeff m.1)) l
          (nhds (fun m : D => f.1.coeff m.1)) :=
        tendsto_pi_nhds.2 (fun m => hc m.1)
      have h2 := (hg.tendsto _).comp h1
      have e1 : (g ∘ fun t => (fun m : D => (F t).1.coeff m.1)) = F := funext fun t => hgc (F t)
      rw [e1] at h2
      have e2 : g (fun m : D => f.1.coeff m.1) = f := hgc f
      rw [e2] at h2
      exact h2
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_coeff_pderiv : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (m : Fin n →₀ ℕ), (pderiv i p).coeff m = p.coeff (m + Finsupp.single i 1) * ((m i : ℝ) + 1) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (m : Fin n →₀ ℕ) => by
      induction p using MvPolynomial.induction_on' with
      | monomial s c =>
        rw [pderiv_monomial, coeff_monomial, coeff_monomial]
        by_cases h : s = m + Finsupp.single i 1
        · subst h
          rw [if_pos (add_tsub_cancel_right _ _), if_pos rfl]
          simp
        · rw [if_neg h, zero_mul]
          by_cases h2 : s - Finsupp.single i 1 = m
          · rw [if_pos h2]
            have : s i = 0 := by
              by_contra h3
              apply h
              rw [← h2]
              ext k
              simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
              by_cases hk : k = i
              · subst hk; simp; omega
              · simp [Ne.symm hk]
            simp [this]
          · rw [if_neg h2]
      | add p q hp hq =>
        rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_hess : ∀ (n : ℕ) (h : H n 2) (j k : Fin n), H.hessian h j k = (pderiv j (pderiv k h.1)).coeff 0 :=
    fun (n : ℕ) (h : H n 2) (j k : Fin n) => by
      rw [LZdir_aux_coeff_pderiv, LZdir_aux_coeff_pderiv, zero_add]
      simp only [H.hessian, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add, mul_one]
      by_cases hjk : j = k
      · subst hjk
        rw [if_pos rfl, ← Finsupp.single_add]
        simp; ring
      · rw [if_neg hjk]
        simp [hjk]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_comm2 : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (i l : Fin n), pderiv i (pderiv l P) = pderiv l (pderiv i P) :=
    fun (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (i l : Fin n) => by
      conv_lhs => rw [P.as_sum]
      conv_rhs => rw [P.as_sum]
      simp only [map_sum, pderiv_monomial]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [tsub_right_comm]
      congr 1
      by_cases h : i = l
      · subst h; ring
      · simp [Finsupp.tsub_apply, h, Ne.symm h]; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_comm : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) (i : Fin n), pderiv i (∑ l, w l • pderiv l P) = ∑ l, w l • pderiv l (pderiv i P) :=
    fun (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) (i : Fin n) => by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Derivation.map_smul, LZdir_aux_comm2]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_P : ∀ (n d : ℕ) (f : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i) (ha' : ∃ i, 0 < a i)
      (h : ∀ i (m : Fin n →₀ ℕ), weight 1 m = d → 0 < (pderiv i f).coeff m), ∀ m : Fin n →₀ ℕ, weight 1 m = d → 0 < (∑ i, a i • pderiv i f).coeff m :=
    fun (n d : ℕ) (f : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ)
        (ha : ∀ i, 0 ≤ a i) (ha' : ∃ i, 0 < a i)
        (h : ∀ i (m : Fin n →₀ ℕ), weight 1 m = d → 0 < (pderiv i f).coeff m) => by
      intro m hm
      rw [coeff_sum]
      obtain ⟨p, hp⟩ := ha'
      apply Finset.sum_pos'
      · intro i _
        rw [coeff_smul, smul_eq_mul]
        exact mul_nonneg (ha i) (h i m hm).le
      · exact ⟨p, Finset.mem_univ _, by rw [coeff_smul, smul_eq_mul]; exact mul_pos hp (h p m hm)⟩
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_hpos : ∀ (n : ℕ) (h : H n 2) (hP : h ∈ P n 2) (j k : Fin n), 0 < H.hessian h j k :=
    fun (n : ℕ) (h : H n 2) (hP : h ∈ P n 2) (j k : Fin n) => by
      simp only [H.hessian]
      split_ifs with hjk
      · subst hjk
        have := hP (Finsupp.single j 2) (by simp [weight_apply])
        linarith
      · exact hP _ (by simp [weight_apply, Finsupp.sum_add_index])
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_lin : ∀ (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a v u : Fin n → ℝ), v ⬝ᵥ ((∑ i, a i • Q i) *ᵥ u) = ∑ i, a i * (v ⬝ᵥ (Q i *ᵥ u)) :=
    fun (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a v u : Fin n → ℝ) => by
      simp only [dotProduct, mulVec, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_mul, Finset.mul_sum]
      conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_row : ∀ (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a z : Fin n → ℝ)
      (hsym1 : ∀ i j k, Q i j k = Q j i k) (i : Fin n), ((∑ k, a k • Q k) *ᵥ z) i = a ⬝ᵥ (Q i *ᵥ z) :=
    fun (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a z : Fin n → ℝ)
        (hsym1 : ∀ i j k, Q i j k = Q j i k) (i : Fin n) => by
      simp only [dotProduct, mulVec, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsym1]; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_lim : ∀ (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i)
      (hb : ∀ b : Fin n → ℝ, (∀ i, 0 < b i) → ∀ u v : Fin n → ℝ,
        0 < u ⬝ᵥ ((∑ i, b i • Q i) *ᵥ u) →
        (u ⬝ᵥ ((∑ i, b i • Q i) *ᵥ u)) * (v ⬝ᵥ ((∑ i, b i • Q i) *ᵥ v)) ≤
          (u ⬝ᵥ ((∑ i, b i • Q i) *ᵥ v)) ^ 2), ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ ((∑ i, a i • Q i) *ᵥ u) →
        (u ⬝ᵥ ((∑ i, a i • Q i) *ᵥ u)) * (v ⬝ᵥ ((∑ i, a i • Q i) *ᵥ v)) ≤
          (u ⬝ᵥ ((∑ i, a i • Q i) *ᵥ v)) ^ 2 :=
    fun (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
        (ha : ∀ i, 0 ≤ a i)
        (hb : ∀ b : Fin n → ℝ, (∀ i, 0 < b i) → ∀ u v : Fin n → ℝ,
          0 < u ⬝ᵥ ((∑ i, b i • Q i) *ᵥ u) →
          (u ⬝ᵥ ((∑ i, b i • Q i) *ᵥ u)) * (v ⬝ᵥ ((∑ i, b i • Q i) *ᵥ v)) ≤
            (u ⬝ᵥ ((∑ i, b i • Q i) *ᵥ v)) ^ 2) => by
      intro u v hu
      have key : ∀ x y : Fin n → ℝ, Filter.Tendsto
          (fun ε : ℝ => x ⬝ᵥ ((∑ i, (a i + ε) • Q i) *ᵥ y)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (x ⬝ᵥ ((∑ i, a i • Q i) *ᵥ y))) := by
        intro x y
        have hc : Continuous (fun ε : ℝ => x ⬝ᵥ ((∑ i, (a i + ε) • Q i) *ᵥ y)) := by
          simp_rw [LZdir_aux_lin]
          fun_prop
        have := hc.tendsto 0
        simp only [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have hev1 := (key u u).eventually_const_lt hu
      have hev2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε := self_mem_nhdsWithin
      have hT := (((key u v).pow 2).sub ((key u u).mul (key v v)))
      have : (0:ℝ) ≤ _ := ge_of_tendsto hT (by
        filter_upwards [hev1, hev2] with ε h1 h2
        have := hb (fun i => a i + ε) (fun i => add_pos_of_nonneg_of_pos (ha i) h2) u v h1
        simp only at this
        linarith)
      linarith
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_null : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (a z : Fin n → ℝ)
      (hsym : ∀ j k, Q j k = Q k j)
      (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (Q *ᵥ u) →
        (u ⬝ᵥ (Q *ᵥ u)) * (v ⬝ᵥ (Q *ᵥ v)) ≤ (u ⬝ᵥ (Q *ᵥ v)) ^ 2)
      (haa : 0 < a ⬝ᵥ (Q *ᵥ a)) (haz : a ⬝ᵥ (Q *ᵥ z) = 0) (hzz : z ⬝ᵥ (Q *ᵥ z) = 0), Q *ᵥ z = 0 :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (a z : Fin n → ℝ)
        (hsym : ∀ j k, Q j k = Q k j)
        (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (Q *ᵥ u) →
          (u ⬝ᵥ (Q *ᵥ u)) * (v ⬝ᵥ (Q *ᵥ v)) ≤ (u ⬝ᵥ (Q *ᵥ v)) ^ 2)
        (haa : 0 < a ⬝ᵥ (Q *ᵥ a)) (haz : a ⬝ᵥ (Q *ᵥ z) = 0) (hzz : z ⬝ᵥ (Q *ᵥ z) = 0) => by
      have hT : Q.transpose = Q := by ext j k; exact hsym k j
      have hswap : ∀ x y : Fin n → ℝ, x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
        intro x y
        rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
      have hzv : ∀ v : Fin n → ℝ, z ⬝ᵥ (Q *ᵥ v) = 0 := by
        intro v
        set w : Fin n → ℝ := (a ⬝ᵥ (Q *ᵥ a)) • v - (a ⬝ᵥ (Q *ᵥ v)) • a with hw
        have haw : a ⬝ᵥ (Q *ᵥ w) = 0 := by
          rw [hw, mulVec_sub, mulVec_smul, mulVec_smul, dotProduct_sub, dotProduct_smul,
            dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
        have hquad : ∀ t : ℝ, 2 * t * (z ⬝ᵥ (Q *ᵥ w)) + t ^ 2 * (w ⬝ᵥ (Q *ᵥ w)) ≤ 0 := by
          intro t
          have h := hN a (z + t • w) haa
          have e1 : a ⬝ᵥ (Q *ᵥ (z + t • w)) = 0 := by
            rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, haz, haw]; simp
          have e2 : (z + t • w) ⬝ᵥ (Q *ᵥ (z + t • w)) =
              2 * t * (z ⬝ᵥ (Q *ᵥ w)) + t ^ 2 * (w ⬝ᵥ (Q *ᵥ w)) := by
            rw [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
              dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul, hzz,
              hswap w z]
            simp only [smul_eq_mul]; ring
          rw [e1, e2] at h
          nlinarith
        set b := z ⬝ᵥ (Q *ᵥ w)
        set c := w ⬝ᵥ (Q *ᵥ w)
        have h1 := hquad 1
        have h2 := hquad (-1)
        have hc : c ≤ 0 := by nlinarith
        have h3 := hquad (b / (1 - c))
        have hb : b = 0 := by
          have hpos : 0 < 1 - c := by linarith
          have ht : b / (1 - c) * (1 - c) = b := div_mul_cancel₀ _ hpos.ne'
          set t := b / (1 - c)
          have h4 : t ^ 2 * (2 - c) ≤ 0 := by rw [← ht] at h3; nlinarith
          have h5 : t = 0 := by nlinarith
          rw [← ht, h5, zero_mul]
        have hzw : z ⬝ᵥ (Q *ᵥ w) =
            (a ⬝ᵥ (Q *ᵥ a)) * (z ⬝ᵥ (Q *ᵥ v)) - (a ⬝ᵥ (Q *ᵥ v)) * (z ⬝ᵥ (Q *ᵥ a)) := by
          rw [hw, mulVec_sub, mulVec_smul, mulVec_smul, dotProduct_sub, dotProduct_smul,
            dotProduct_smul, smul_eq_mul, smul_eq_mul]
        rw [hswap z a, haz, mul_zero, sub_zero] at hzw
        have : (a ⬝ᵥ (Q *ᵥ a)) * (z ⬝ᵥ (Q *ᵥ v)) = 0 := by rw [← hzw]; exact hb
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact h
      have h0 := hzv (Q *ᵥ z)
      rw [hswap] at h0
      have hsq : ∀ j, (Q *ᵥ z) j * (Q *ᵥ z) j = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (f := fun j => (Q *ᵥ z) j * (Q *ᵥ z) j) (fun j _ => mul_self_nonneg _)).1 h0
        exact fun j => this j (Finset.mem_univ _)
      funext j
      exact mul_self_eq_zero.1 (hsq j)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_quadpos : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i) (p : Fin n) (hp : 0 < a p) (hpos : ∀ j k, 0 < Q j k), 0 < a ⬝ᵥ (Q *ᵥ a) :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
        (ha : ∀ i, 0 ≤ a i) (p : Fin n) (hp : 0 < a p) (hpos : ∀ j k, 0 < Q j k) => by
      have hQa : ∀ j, 0 < (Q *ᵥ a) j := by
        intro j
        simp only [mulVec, dotProduct]
        exact Finset.sum_pos' (fun k _ => mul_nonneg (hpos j k).le (ha k))
          ⟨p, Finset.mem_univ _, mul_pos (hpos j p) hp⟩
      simp only [dotProduct]
      exact Finset.sum_pos' (fun j _ => mul_nonneg (ha j) (hQa j).le)
        ⟨p, Finset.mem_univ _, mul_pos hp (hQa p)⟩
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_unit : ∀ (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i) (p : Fin n) (hp : 0 < a p)
      (hsym1 : ∀ i j k, Q i j k = Q j i k) (hsym2 : ∀ i j k, Q i j k = Q i k j)
      (hpos : ∀ i j k, 0 < Q i j k) (hU : ∀ i, IsUnit (Q i))
      (hN : ∀ i (u v : Fin n → ℝ), 0 < u ⬝ᵥ (Q i *ᵥ u) →
        (u ⬝ᵥ (Q i *ᵥ u)) * (v ⬝ᵥ (Q i *ᵥ v)) ≤ (u ⬝ᵥ (Q i *ᵥ v)) ^ 2), IsUnit (∑ i, a i • Q i) :=
    fun (n : ℕ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
        (ha : ∀ i, 0 ≤ a i) (p : Fin n) (hp : 0 < a p)
        (hsym1 : ∀ i j k, Q i j k = Q j i k) (hsym2 : ∀ i j k, Q i j k = Q i k j)
        (hpos : ∀ i j k, 0 < Q i j k) (hU : ∀ i, IsUnit (Q i))
        (hN : ∀ i (u v : Fin n → ℝ), 0 < u ⬝ᵥ (Q i *ᵥ u) →
          (u ⬝ᵥ (Q i *ᵥ u)) * (v ⬝ᵥ (Q i *ᵥ v)) ≤ (u ⬝ᵥ (Q i *ᵥ v)) ^ 2) => by
      have hker : ∀ z : Fin n → ℝ, (∑ i, a i • Q i) *ᵥ z = 0 → z = 0 := by
        intro z hz
        have haz : ∀ i, a ⬝ᵥ (Q i *ᵥ z) = 0 := by
          intro i
          rw [← LZdir_aux_row n Q a z hsym1 i, hz]; rfl
        have haa : ∀ i, 0 < a ⬝ᵥ (Q i *ᵥ a) := fun i =>
          LZdir_aux_quadpos n (Q i) a ha p hp (hpos i)
        have hzz : ∀ i, z ⬝ᵥ (Q i *ᵥ z) ≤ 0 := by
          intro i
          have := hN i a z (haa i)
          rw [haz i] at this
          nlinarith [haa i]
        have hsum : ∑ i, a i * (z ⬝ᵥ (Q i *ᵥ z)) = 0 := by
          rw [← LZdir_aux_lin, hz, dotProduct_zero]
        have hall := (Finset.sum_eq_zero_iff_of_nonpos (s := Finset.univ)
          (fun i _ => mul_nonpos_of_nonneg_of_nonpos (ha i) (hzz i))).1 hsum p (Finset.mem_univ _)
        have hzp : z ⬝ᵥ (Q p *ᵥ z) = 0 := by
          rcases mul_eq_zero.1 hall with h | h
          · linarith
          · exact h
        have hQz := LZdir_aux_null n (Q p) a z (hsym2 p) (hN p) (haa p) (haz p) hzp
        obtain ⟨U, hU'⟩ := hU p
        have hinv : ((U⁻¹).val * U.val) = 1 := U.inv_mul
        calc z = ((U⁻¹).val * U.val) *ᵥ z := by rw [hinv, one_mulVec]
          _ = (U⁻¹).val *ᵥ (Q p *ᵥ z) := by rw [← mulVec_mulVec, hU']
          _ = 0 := by rw [hQz, mulVec_zero]
      rw [← Matrix.mulVec_injective_iff_isUnit]
      intro x y hxy
      have := hker (x - y) (by rw [mulVec_sub, hxy, sub_self])
      exact sub_eq_zero.1 this
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_base : ∀ (n : ℕ) (f : H n 3) (hf : f ∈ Ŀ n 3) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i) (ha' : ∃ i, 0 < a i), ∃ g : H n 2, g.1 = ∑ i, a i • pderiv i f.1 ∧ g ∈ Ŀ n 2 :=
    fun (n : ℕ) (f : H n 3) (hf : f ∈ Ŀ n 3) (a : Fin n → ℝ)
        (ha : ∀ i, 0 ≤ a i) (ha' : ∃ i, 0 < a i) => by
      obtain ⟨p, hp⟩ := ha'
      have hn : 0 < n := Fin.pos p
      have hf' : f ∈ P n 3 ∧ ∀ i, (⟨pderiv i f.1, f.2.pderiv⟩ : H n 2) ∈ Ŀ n 2 := hf
      have spec := fun i => (LZspec n hn _).1 (hf'.2 i)
      have hmem : (∑ i, a i • pderiv i f.1) ∈ homogeneousSubmodule (Fin n) ℝ 2 :=
        Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (f.2.pderiv))
      refine ⟨⟨_, hmem⟩, rfl, ?_⟩
      set g : H n 2 := ⟨_, hmem⟩ with hgdef
      let Q : Fin n → Matrix (Fin n) (Fin n) ℝ := fun i =>
        H.hessian (⟨pderiv i f.1, f.2.pderiv⟩ : H n 2)
      have hQ : ∀ i j k, Q i j k = (pderiv j (pderiv k (pderiv i f.1))).coeff 0 :=
        fun i j k => LZdir_aux_hess n _ j k
      have hg : H.hessian g = ∑ i, a i • Q i := by
        ext j k
        rw [LZdir_aux_hess, Matrix.sum_apply]
        simp only [Matrix.smul_apply, hQ, smul_eq_mul]
        show (pderiv j (pderiv k (∑ i, a i • pderiv i f.1))).coeff 0 = _
        simp only [map_sum, Derivation.map_smul, coeff_sum, coeff_smul, smul_eq_mul]
      have hsym1 : ∀ i j k, Q i j k = Q j i k := by
        intro i j k
        rw [hQ, hQ, LZdir_aux_comm2 n f.1 k i, LZdir_aux_comm2 n (pderiv k f.1) j i,
          LZdir_aux_comm2 n f.1 k j]
      have hsym2 : ∀ i j k, Q i j k = Q i k j := by
        intro i j k
        rw [hQ, hQ, LZdir_aux_comm2 n (pderiv i f.1) j k]
      have hpos : ∀ i j k, 0 < Q i j k := fun i j k => LZdir_aux_hpos n _ (spec i).1 j k
      have hN := fun i => (spec i).2.2
      apply (LZspec n hn g).2
      refine ⟨?_, ?_, ?_⟩
      · exact LZdir_aux_P n 2 f.1 a ha ⟨p, hp⟩ (fun i m hm => (spec i).1 m hm)
      · rw [hg]
        exact LZdir_aux_unit n Q a ha p hp hsym1 hsym2 hpos (fun i => (spec i).2.1) hN
      · rw [hg]
        exact LZdir_aux_lim n Q a ha (fun b hb => LZpf n Q b hsym1 hsym2
          (fun i j k => (hpos i j k).le) hb hN
          (fun S ⟨j, hj, _⟩ ⟨k, hk, _⟩ => ⟨j, hj, k, hk, j, hpos j j k⟩))
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir : ∀ (n e : ℕ) (f : H n (e + 3)) (hf : f ∈ Ŀ n (e + 3)) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i) (ha' : ∃ i, 0 < a i), ∃ g : H n (e + 2), g.1 = ∑ i, a i • pderiv i f.1 ∧ g ∈ Ŀ n (e + 2) :=
    fun (n e : ℕ) (f : H n (e + 3)) (hf : f ∈ Ŀ n (e + 3)) (a : Fin n → ℝ)
        (ha : ∀ i, 0 ≤ a i) (ha' : ∃ i, 0 < a i) => by
      induction e with
      | zero => exact LZdir_aux_base n f hf a ha ha'
      | succ e ih =>
        have hf' : f ∈ P n (e + 1 + 3) ∧
            ∀ i, (⟨pderiv i f.1, f.2.pderiv⟩ : H n (e + 3)) ∈ Ŀ n (e + 3) := hf
        have hmem : (∑ i, a i • pderiv i f.1) ∈ homogeneousSubmodule (Fin n) ℝ (e + 3) :=
          Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (f.2.pderiv))
        refine ⟨⟨_, hmem⟩, rfl, ?_⟩
        show (⟨_, hmem⟩ : H n (e + 3)) ∈ P n (e + 3) ∧ ∀ k,
          (⟨pderiv k (∑ i, a i • pderiv i f.1), _⟩ : H n (e + 2)) ∈ Ŀ n (e + 2)
        refine ⟨?_, fun k => ?_⟩
        · exact LZdir_aux_P n (e + 3) f.1 a ha ha' (fun i m hm => (hf'.2 i).1 m hm)
        · obtain ⟨g', hg'1, hg'2⟩ := ih (⟨pderiv k f.1, f.2.pderiv⟩ : H n (e + 3)) (hf'.2 k)
          have : (⟨pderiv k (∑ i, a i • pderiv i f.1), (hmem : _).pderiv⟩ : H n (e + 2)) = g' := by
            apply Subtype.ext
            rw [hg'1]
            exact LZdir_aux_comm n f.1 a k
          rw [this]
          exact hg'2
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_coeff_pderiv : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (m : Fin n →₀ ℕ), (pderiv i p).coeff m = p.coeff (m + Finsupp.single i 1) * ((m i : ℝ) + 1) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (m : Fin n →₀ ℕ) => by
      induction p using MvPolynomial.induction_on' with
      | monomial s c =>
        rw [pderiv_monomial, coeff_monomial, coeff_monomial]
        by_cases h : s = m + Finsupp.single i 1
        · subst h
          rw [if_pos (add_tsub_cancel_right _ _), if_pos rfl]
          simp
        · rw [if_neg h, zero_mul]
          by_cases h2 : s - Finsupp.single i 1 = m
          · rw [if_pos h2]
            have : s i = 0 := by
              by_contra h3
              apply h
              rw [← h2]
              ext k
              simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
              by_cases hk : k = i
              · subst hk; simp; omega
              · simp [Ne.symm hk]
            simp [this]
          · rw [if_neg h2]
      | add p q hp hq =>
        rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_hess : ∀ (n : ℕ) (h : H n 2) (j k : Fin n), H.hessian h j k = (pderiv j (pderiv k h.1)).coeff 0 :=
    fun (n : ℕ) (h : H n 2) (j k : Fin n) => by
      rw [LZdir_aux_coeff_pderiv, LZdir_aux_coeff_pderiv, zero_add]
      simp only [H.hessian, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add, mul_one]
      by_cases hjk : j = k
      · subst hjk
        rw [if_pos rfl, ← Finsupp.single_add]
        simp; ring
      · rw [if_neg hjk]
        simp [hjk]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_comm2 : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (i l : Fin n), pderiv i (pderiv l P) = pderiv l (pderiv i P) :=
    fun (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (i l : Fin n) => by
      conv_lhs => rw [P.as_sum]
      conv_rhs => rw [P.as_sum]
      simp only [map_sum, pderiv_monomial]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [tsub_right_comm]
      congr 1
      by_cases h : i = l
      · subst h; ring
      · simp [Finsupp.tsub_apply, h, Ne.symm h]; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_comm : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) (i : Fin n), pderiv i (∑ l, w l • pderiv l P) = ∑ l, w l • pderiv l (pderiv i P) :=
    fun (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) (i : Fin n) => by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Derivation.map_smul, LZdir_aux_comm2]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_P : ∀ (n d : ℕ) (f : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i) (ha' : ∃ i, 0 < a i)
      (h : ∀ i (m : Fin n →₀ ℕ), weight 1 m = d → 0 < (pderiv i f).coeff m), ∀ m : Fin n →₀ ℕ, weight 1 m = d → 0 < (∑ i, a i • pderiv i f).coeff m :=
    fun (n d : ℕ) (f : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ)
        (ha : ∀ i, 0 ≤ a i) (ha' : ∃ i, 0 < a i)
        (h : ∀ i (m : Fin n →₀ ℕ), weight 1 m = d → 0 < (pderiv i f).coeff m) => by
      intro m hm
      rw [coeff_sum]
      obtain ⟨p, hp⟩ := ha'
      apply Finset.sum_pos'
      · intro i _
        rw [coeff_smul, smul_eq_mul]
        exact mul_nonneg (ha i) (h i m hm).le
      · exact ⟨p, Finset.mem_univ _, by rw [coeff_smul, smul_eq_mul]; exact mul_pos hp (h p m hm)⟩
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdir_aux_hpos : ∀ (n : ℕ) (h : H n 2) (hP : h ∈ P n 2) (j k : Fin n), 0 < H.hessian h j k :=
    fun (n : ℕ) (h : H n 2) (hP : h ∈ P n 2) (j k : Fin n) => by
      simp only [H.hessian]
      split_ifs with hjk
      · subst hjk
        have := hP (Finsupp.single j 2) (by simp [weight_apply])
        linarith
      · exact hP _ (by simp [weight_apply, Finsupp.sum_add_index])
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZshadow_aux_core : ∀ (n : ℕ) (J : Set (Fin n →₀ ℕ)) (hJ : IsMConvex J) (T : Set (Fin n))
      (g d : Fin n →₀ ℕ) (a b k : Fin n) (_ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b)
      (hk : g k > d k) (hβ : d + Finsupp.single b 1 ∈ J)
      (hρ : g - Finsupp.single k 1 + Finsupp.single a 1 + Finsupp.single b 1 ∈ J), ∃ l, g l < d l ∧ ∃ c ∈ T, g - Finsupp.single k 1 + Finsupp.single l 1 + Finsupp.single c 1 ∈ J :=
    fun (n : ℕ) (J : Set (Fin n →₀ ℕ)) (hJ : IsMConvex J) (T : Set (Fin n))
        (g d : Fin n →₀ ℕ) (a b k : Fin n) (_ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b)
        (hk : g k > d k) (hβ : d + Finsupp.single b 1 ∈ J)
        (hρ : g - Finsupp.single k 1 + Finsupp.single a 1 + Finsupp.single b 1 ∈ J) => by
      by_cases hga : g a < d a
      · exact ⟨a, hga, b, hb, hρ⟩
      · push_neg at hga
        have hgt : (g - Finsupp.single k 1 + Finsupp.single a 1 + Finsupp.single b 1 : Fin n →₀ ℕ) a > (d + Finsupp.single b 1 : Fin n →₀ ℕ) a := by
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
        obtain ⟨j, hj1, hj2⟩ := hJ _ hρ _ hβ a hgt
        have hj : g j < d j := by
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply] at hj1 hgt
          split_ifs at hj1 hgt <;> subst_vars <;> omega
        refine ⟨j, hj, b, hb, ?_⟩
        have e : g - Finsupp.single k 1 + Finsupp.single j 1 + Finsupp.single b 1
            = g - Finsupp.single k 1 + Finsupp.single a 1 + Finsupp.single b 1 - Finsupp.single a 1 + Finsupp.single j 1 := by
          ext t
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
        rw [e]; exact hj2
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZshadow : ∀ (n : ℕ) (J : Set (Fin n →₀ ℕ)) (hJ : IsMConvex J) (T : Set (Fin n)), IsMConvex {γ : Fin n →₀ ℕ | ∃ i ∈ T, γ + Finsupp.single i 1 ∈ J} :=
    fun (n : ℕ) (J : Set (Fin n →₀ ℕ)) (hJ : IsMConvex J) (T : Set (Fin n)) => by
      rintro g ⟨a, ha, hα⟩ d ⟨b, hb, hβ⟩ k hk
      simp only [Set.mem_setOf_eq]
      by_cases hB : k = b ∧ a ≠ b ∧ g k = d k + 1
      · obtain ⟨rfl, hab, hgk⟩ := hB
        apply LZshadow_aux_core n J hJ T g d a k k ha hb hab hk hβ
        have e : g - Finsupp.single k 1 + Finsupp.single a 1 + Finsupp.single k 1 = g + Finsupp.single a 1 := by
          ext t
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
        rw [e]; exact hα
      · have hB' : k = b → a ≠ b → g k ≠ d k + 1 := fun h1 h2 h3 => hB ⟨h1, h2, h3⟩
        have hgt : (g + Finsupp.single a 1 : Fin n →₀ ℕ) k > (d + Finsupp.single b 1 : Fin n →₀ ℕ) k := by
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
          by_cases h2 : b = k
          · subst h2
            by_cases h1 : a = b
            · subst h1; simp; omega
            · have := hB' rfl h1
              simp [h1]; omega
          · by_cases h1 : a = k <;> simp [h1, h2] <;> omega
        obtain ⟨j, hj1, hj2⟩ := hJ _ hα _ hβ k hgt
        by_cases hgj : g j < d j
        · refine ⟨j, hgj, a, ha, ?_⟩
          have e : g - Finsupp.single k 1 + Finsupp.single j 1 + Finsupp.single a 1 = g + Finsupp.single a 1 - Finsupp.single k 1 + Finsupp.single j 1 := by
            ext t
            simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_apply]
            split_ifs <;> subst_vars <;> omega
          rw [e]; exact hj2
        · have hjb : j = b := by
            by_contra hne
            have h0 : (if b = j then 1 else 0) = 0 := if_neg (fun h => hne h.symm)
            simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, h0] at hj1
            split_ifs at hj1 <;> omega
          subst hjb
          have hab : a ≠ j := by
            rintro rfl
            simp at hj1
            omega
          apply LZshadow_aux_core n J hJ T g d a j k ha hb hab hk hβ
          have e : g - Finsupp.single k 1 + Finsupp.single a 1 + Finsupp.single j 1 = g + Finsupp.single a 1 - Finsupp.single k 1 + Finsupp.single j 1 := by
            ext t
            simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_apply]
            split_ifs <;> subst_vars <;> omega
          rw [e]; exact hj2
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_split : ∀ (n : ℕ) (m : Fin n →₀ ℕ) (k : ℕ) (h : m.degree = k + 1), ∃ a : Fin n, ∃ m' : Fin n →₀ ℕ, m = m' + Finsupp.single a 1 ∧ m'.degree = k :=
    fun (n : ℕ) (m : Fin n →₀ ℕ) (k : ℕ) (h : m.degree = k + 1) => by
      have h0 : m ≠ 0 := by rintro rfl; simp at h
      obtain ⟨a, ha⟩ : ∃ a, m a ≠ 0 := by
        by_contra hc; push_neg at hc; exact h0 (Finsupp.ext hc)
      have h1 : Finsupp.single a 1 ≤ m := by
        intro x; rw [Finsupp.single_apply]; split_ifs with hx
        · subst hx; omega
        · exact Nat.zero_le _
      refine ⟨a, m - Finsupp.single a 1, (tsub_add_cancel_of_le h1).symm, ?_⟩
      have := congrArg Finsupp.degree (tsub_add_cancel_of_le h1)
      rw [map_add, Finsupp.degree_single] at this
      omega
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_cls : ∀ (n : ℕ) (m : Fin n →₀ ℕ) (h : m.degree = 2), ∃ a b : Fin n, m = Finsupp.single a 1 + Finsupp.single b 1 :=
    fun (n : ℕ) (m : Fin n →₀ ℕ) (h : m.degree = 2) => by
      obtain ⟨a, m', hm, hd⟩ := LZstab_aux_split n m 1 h
      obtain ⟨b, m'', hm', hd'⟩ := LZstab_aux_split n m' 0 hd
      have : m'' = 0 := (Finsupp.degree_eq_zero_iff m'').1 hd'
      subst this
      exact ⟨b, a, by rw [hm, hm', zero_add]⟩
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_XX : ∀ (n : ℕ) (i j : Fin n), (X i * X j : MvPolynomial (Fin n) ℝ) = monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 :=
    fun (n : ℕ) (i j : Fin n) => by
      rw [X, X, monomial_mul, one_mul]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_poly : ∀ (n : ℕ) (g : H n 2), g.1 = ∑ i : Fin n, ∑ j : Fin n, C (H.hessian g i j / 2) * (X i * X j) :=
    fun (n : ℕ) (g : H n 2) => by
      have hg : g.1.IsHomogeneous 2 := (mem_homogeneousSubmodule 2 g.1).1 g.2
      ext m
      simp only [coeff_sum, coeff_C_mul, LZstab_aux_XX, coeff_monomial]
      by_cases hm : m.degree = 2
      · obtain ⟨a, b, rfl⟩ := LZstab_aux_cls n m hm
        have key : ∀ i j : Fin n, (Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single a 1 + Finsupp.single b 1) ↔
            ((i = a ∧ j = b) ∨ (i = b ∧ j = a)) := by
          intro i j
          rw [Finsupp.single_add_single_eq_single_add_single one_ne_zero one_ne_zero]
          simp
        simp only [key]
        by_cases hab : a = b
        · subst hab
          rw [Fintype.sum_eq_single a, Fintype.sum_eq_single a]
          · simp [H.hessian, ← Finsupp.single_add]
          all_goals (intro x hx; simp [hx])
        · rw [Fintype.sum_eq_add a b hab, Fintype.sum_eq_single b, Fintype.sum_eq_single a]
          · simp [H.hessian, hab, Ne.symm hab, add_comm (Finsupp.single b 1)]
          all_goals first
            | (intro x ⟨hxa, hxb⟩; simp [hxa, hxb])
            | (intro x hx; simp [hx, hab, Ne.symm hab])
      · rw [hg.coeff_eq_zero hm]
        symm
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg, mul_zero]
        intro h
        apply hm
        rw [← h, map_add, Finsupp.degree_single, Finsupp.degree_single]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_eval : ∀ (n : ℕ) (g : H n 2) (z : Fin n → ℂ), aeval z g.1 = ∑ i : Fin n, ∑ j : Fin n, ((H.hessian g i j / 2 : ℝ) : ℂ) * (z i * z j) :=
    fun (n : ℕ) (g : H n 2) (z : Fin n → ℂ) => by
      rw [LZstab_aux_poly n g]
      simp [map_sum, map_mul, aeval_X, aeval_C]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_dot : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ), x ⬝ᵥ (Q *ᵥ y) = ∑ i : Fin n, ∑ j : Fin n, Q i j * (x i * y j) :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) => by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_symm : ∀ (n : ℕ) (g : H n 2) (i j : Fin n), H.hessian g i j = H.hessian g j i :=
    fun (n : ℕ) (g : H n 2) (i j : Fin n) => by
      by_cases h : i = j
      · subst h; rfl
      · simp [H.hessian, h, Ne.symm h, add_comm]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_dotsymm : ∀ (n : ℕ) (g : H n 2) (x y : Fin n → ℝ), x ⬝ᵥ (H.hessian g *ᵥ y) = y ⬝ᵥ (H.hessian g *ᵥ x) :=
    fun (n : ℕ) (g : H n 2) (x y : Fin n → ℝ) => by
      rw [LZstab_aux_dot, LZstab_aux_dot, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
      rw [LZstab_aux_symm n g j i]; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_re : ∀ (n : ℕ) (g : H n 2) (x y : Fin n → ℝ), (aeval (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) g.1).re =
        (x ⬝ᵥ (H.hessian g *ᵥ x) - y ⬝ᵥ (H.hessian g *ᵥ y)) / 2 :=
    fun (n : ℕ) (g : H n 2) (x y : Fin n → ℝ) => by
      rw [LZstab_aux_eval, LZstab_aux_dot, LZstab_aux_dot, ← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul,
        Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Complex.re_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      simp [Complex.mul_re, Complex.mul_im]
      ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_im : ∀ (n : ℕ) (g : H n 2) (x y : Fin n → ℝ), (aeval (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) g.1).im =
        (x ⬝ᵥ (H.hessian g *ᵥ y) + y ⬝ᵥ (H.hessian g *ᵥ x)) / 2 :=
    fun (n : ℕ) (g : H n 2) (x y : Fin n → ℝ) => by
      rw [LZstab_aux_eval, LZstab_aux_dot, LZstab_aux_dot, ← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul,
        Complex.im_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Complex.im_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      simp [Complex.mul_re, Complex.mul_im]
      ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_nn : ∀ (n : ℕ) (g : H n 2) (hg : ∀ m, 0 ≤ g.1.coeff m) (i j : Fin n), 0 ≤ H.hessian g i j :=
    fun (n : ℕ) (g : H n 2) (hg : ∀ m, 0 ≤ g.1.coeff m) (i j : Fin n) => by
      unfold H.hessian; split_ifs
      · have := hg (Finsupp.single i 2); linarith
      · exact hg _
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_lin : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) (u v y : Fin n → ℝ), (a • u - b • v) ⬝ᵥ (Q *ᵥ y) = a * (u ⬝ᵥ (Q *ᵥ y)) - b * (v ⬝ᵥ (Q *ᵥ y)) :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) (u v y : Fin n → ℝ) => by
      rw [LZstab_aux_dot, LZstab_aux_dot, LZstab_aux_dot, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      simp; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_quad : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) (u v : Fin n → ℝ), (a • u - b • v) ⬝ᵥ (Q *ᵥ (a • u - b • v)) = a * a * (u ⬝ᵥ (Q *ᵥ u))
        - a * b * (u ⬝ᵥ (Q *ᵥ v)) - a * b * (v ⬝ᵥ (Q *ᵥ u)) + b * b * (v ⬝ᵥ (Q *ᵥ v)) :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) (u v : Fin n → ℝ) => by
      rw [LZstab_aux_dot, LZstab_aux_dot, LZstab_aux_dot, LZstab_aux_dot, LZstab_aux_dot,
        Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      simp; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_smul : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ), (c • x) ⬝ᵥ (Q *ᵥ y) = c * (x ⬝ᵥ (Q *ᵥ y)) ∧
      (c • x) ⬝ᵥ (Q *ᵥ (c • x)) = c * c * (x ⬝ᵥ (Q *ᵥ x)) :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ) => by
      constructor
      · rw [LZstab_aux_dot, LZstab_aux_dot, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        simp; ring
      · rw [LZstab_aux_dot, LZstab_aux_dot, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        simp; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab_aux_ypos : ∀ (n : ℕ) (g : H n 2) (hg : ∀ m, 0 ≤ g.1.coeff m) (i0 j0 : Fin n)
      (hpos : 0 < H.hessian g i0 j0) (y : Fin n → ℝ) (hy : ∀ k, 0 < y k), 0 < y ⬝ᵥ (H.hessian g *ᵥ y) :=
    fun (n : ℕ) (g : H n 2) (hg : ∀ m, 0 ≤ g.1.coeff m) (i0 j0 : Fin n)
        (hpos : 0 < H.hessian g i0 j0) (y : Fin n → ℝ) (hy : ∀ k, 0 < y k) => by
      rw [LZstab_aux_dot]
      have hnn : ∀ i j, 0 ≤ H.hessian g i j * (y i * y j) := fun i j =>
        mul_nonneg (LZstab_aux_nn n g hg i j) (mul_nonneg (hy i).le (hy j).le)
      have h1 : H.hessian g i0 j0 * (y i0 * y j0) ≤ ∑ j, H.hessian g i0 j * (y i0 * y j) :=
        Finset.single_le_sum (f := fun j => H.hessian g i0 j * (y i0 * y j))
          (fun j _ => hnn i0 j) (Finset.mem_univ j0)
      have h2 : ∑ j, H.hessian g i0 j * (y i0 * y j) ≤
          ∑ i, ∑ j, H.hessian g i j * (y i * y j) :=
        Finset.single_le_sum (f := fun i => ∑ j, H.hessian g i j * (y i * y j))
          (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j)) (Finset.mem_univ i0)
      have h3 : 0 < H.hessian g i0 j0 * (y i0 * y j0) := mul_pos hpos (mul_pos (hy i0) (hy j0))
      linarith
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstab : ∀ (n : ℕ) (g : H n 2) (hg : ∀ m, 0 ≤ g.1.coeff m), IsStable g.1 ↔ ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (H.hessian g *ᵥ u) →
          (u ⬝ᵥ (H.hessian g *ᵥ u)) * (v ⬝ᵥ (H.hessian g *ᵥ v)) ≤
            (u ⬝ᵥ (H.hessian g *ᵥ v)) ^ 2 :=
    fun (n : ℕ) (g : H n 2) (hg : ∀ m, 0 ≤ g.1.coeff m) => by
      constructor
      · intro hst u v hu
        by_contra hlt
        push_neg at hlt
        have hex : ∃ i0 j0, 0 < H.hessian g i0 j0 := by
          by_contra hne
          push_neg at hne
          have hz : ∀ i j, H.hessian g i j = 0 := fun i j =>
            le_antisymm (hne i j) (LZstab_aux_nn n g hg i j)
          have : u ⬝ᵥ (H.hessian g *ᵥ u) = 0 := by rw [LZstab_aux_dot]; simp [hz]
          linarith
        obtain ⟨i0, j0, hpos⟩ := hex
        have hg0 : g.1 ≠ 0 := by
          intro h0
          have : H.hessian g i0 j0 = 0 := by
            unfold H.hessian; split_ifs <;> simp [h0]
          linarith
        rcases hst with h | hst
        · exact hg0 h
        obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun _ => 1 := ⟨_, rfl⟩
        have hyp : ∀ k, 0 < y k := fun k => by simp [hy]
        have hyQy : 0 < y ⬝ᵥ (H.hessian g *ᵥ y) := LZstab_aux_ypos n g hg i0 j0 hpos y hyp
        have hx0 : ∃ x : Fin n → ℝ, x ⬝ᵥ (H.hessian g *ᵥ y) = 0 ∧ 0 < x ⬝ᵥ (H.hessian g *ᵥ x) := by
          by_cases hab : v ⬝ᵥ (H.hessian g *ᵥ y) = 0 ∧ u ⬝ᵥ (H.hessian g *ᵥ y) = 0
          · exact ⟨u, hab.2, hu⟩
          · refine ⟨(v ⬝ᵥ (H.hessian g *ᵥ y)) • u - (u ⬝ᵥ (H.hessian g *ᵥ y)) • v, ?_, ?_⟩
            · rw [LZstab_aux_lin]; ring
            · rw [LZstab_aux_quad, LZstab_aux_dotsymm n g v u]
              set a := v ⬝ᵥ (H.hessian g *ᵥ y)
              set b := u ⬝ᵥ (H.hessian g *ᵥ y)
              set A := u ⬝ᵥ (H.hessian g *ᵥ u)
              set B := u ⬝ᵥ (H.hessian g *ᵥ v)
              set Cc := v ⬝ᵥ (H.hessian g *ᵥ v)
              have hkey : A * (a * a * A - a * b * B - a * b * B + b * b * Cc) =
                  (a * A - b * B) ^ 2 + b ^ 2 * (A * Cc - B ^ 2) := by ring
              have hpos2 : 0 < A * (a * a * A - a * b * B - a * b * B + b * b * Cc) := by
                rw [hkey]
                by_cases hb : b = 0
                · have ha : a ≠ 0 := fun ha => hab ⟨ha, hb⟩
                  rw [hb]
                  have : 0 < (a * A - 0 * B) ^ 2 := by
                    have : a * A - 0 * B ≠ 0 := by
                      simp; exact ⟨ha, ne_of_gt hu⟩
                    positivity
                  nlinarith
                · have : 0 < b ^ 2 := by positivity
                  nlinarith [sq_nonneg (a * A - b * B)]
              exact pos_of_mul_pos_right hpos2 hu.le
        obtain ⟨x0, hx0y, hx0x⟩ := hx0
        obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt (y ⬝ᵥ (H.hessian g *ᵥ y) / x0 ⬝ᵥ (H.hessian g *ᵥ x0)) :=
          ⟨_, rfl⟩
        have hcc : c * c = y ⬝ᵥ (H.hessian g *ᵥ y) / x0 ⬝ᵥ (H.hessian g *ᵥ x0) := by
          rw [hc]; exact Real.mul_self_sqrt (div_nonneg hyQy.le hx0x.le)
        obtain ⟨h1, h2⟩ := LZstab_aux_smul n (H.hessian g) c x0 y
        obtain ⟨_, h3⟩ := LZstab_aux_smul n (H.hessian g) c x0 x0
        set x := c • x0 with hxdef
        have hxy : x ⬝ᵥ (H.hessian g *ᵥ y) = 0 := by rw [h1, hx0y]; ring
        have hyx : y ⬝ᵥ (H.hessian g *ᵥ x) = 0 := by rw [LZstab_aux_dotsymm]; exact hxy
        have hxx : x ⬝ᵥ (H.hessian g *ᵥ x) = y ⬝ᵥ (H.hessian g *ᵥ y) := by
          rw [h3, hcc]; field_simp
        let z : Fin n → ℍ := fun k => UpperHalfPlane.mk ((x k : ℂ) + (y k : ℂ) * Complex.I)
          (by simp [hy])
        apply hst z
        have hfun : (((↑) : ℍ → ℂ) ∘ z) = fun k => (x k : ℂ) + (y k : ℂ) * Complex.I := by
          funext k; simp [z]
        rw [hfun]
        apply Complex.ext
        · rw [LZstab_aux_re, hxx]; simp
        · rw [LZstab_aux_im, hxy, hyx]; simp
      · intro hnpd
        by_cases hall : ∀ i j, H.hessian g i j = 0
        · left; rw [LZstab_aux_poly n g]; simp [hall]
        · right
          intro z hz
          push_neg at hall
          obtain ⟨i0, j0, hij⟩ := hall
          have hpos : 0 < H.hessian g i0 j0 := lt_of_le_of_ne (LZstab_aux_nn n g hg i0 j0) (Ne.symm hij)
          obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, x = fun k => ((z k : ℂ)).re := ⟨_, rfl⟩
          obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun k => ((z k : ℂ)).im := ⟨_, rfl⟩
          have hyp : ∀ k, 0 < y k := fun k => by rw [hy]; exact (z k).im_pos
          have hfun : (((↑) : ℍ → ℂ) ∘ z) = fun k => (x k : ℂ) + (y k : ℂ) * Complex.I := by
            funext k; rw [hx, hy]; exact (Complex.re_add_im ((z k : ℂ))).symm
          rw [hfun] at hz
          have hre := LZstab_aux_re n g x y
          have him := LZstab_aux_im n g x y
          rw [hz] at hre him
          simp at hre him
          have hyQy : 0 < y ⬝ᵥ (H.hessian g *ᵥ y) := LZstab_aux_ypos n g hg i0 j0 hpos y hyp
          have hsym := LZstab_aux_dotsymm n g x y
          have := hnpd y x hyQy
          nlinarith
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_coeff : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (m : Fin n →₀ ℕ), (pderiv i p).coeff m = ((m i : ℝ) + 1) * p.coeff (m + Finsupp.single i 1) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (m : Fin n →₀ ℕ) => by
      conv_lhs => rw [p.as_sum]
      conv_rhs => rw [p.as_sum]
      rw [map_sum, coeff_sum, coeff_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [pderiv_monomial, coeff_monomial, coeff_monomial]
      by_cases h1 : s = m + Finsupp.single i 1
      · subst h1
        simp only [add_tsub_cancel_right, if_true, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
        push_cast; ring
      · rw [if_neg h1]
        split_ifs with h2
        · have : s i = 0 := by
            by_contra h3
            apply h1; subst h2; ext t
            simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
            split_ifs <;> subst_vars <;> omega
          simp [this]
        · ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_comm2 : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (i l : Fin n), pderiv i (pderiv l P) = pderiv l (pderiv i P) :=
    fun (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (i l : Fin n) => by
      conv_lhs => rw [P.as_sum]
      conv_rhs => rw [P.as_sum]
      simp only [map_sum, pderiv_monomial]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [tsub_right_comm]
      congr 1
      by_cases h : i = l
      · subst h; ring
      · simp [Finsupp.tsub_apply, h, Ne.symm h]; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_comm : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) (i : Fin n), pderiv i (∑ l, w l • pderiv l P) = ∑ l, w l • pderiv l (pderiv i P) :=
    fun (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) (i : Fin n) => by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Derivation.map_smul, LZdl_aux_comm2]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_hom : ∀ (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
      (hp : p ∈ homogeneousSubmodule (Fin n) ℝ (d + 1)) (a : Fin n → ℝ), (∑ i, a i • pderiv i p) ∈ homogeneousSubmodule (Fin n) ℝ d :=
    fun (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
        (hp : p ∈ homogeneousSubmodule (Fin n) ℝ (d + 1)) (a : Fin n → ℝ) => by
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      have := ((mem_homogeneousSubmodule _ _).1 hp).pderiv (i := i)
      simpa using this
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_nn : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
      (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (m : Fin n →₀ ℕ), 0 ≤ (∑ i, a i • pderiv i p).coeff m :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
        (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (m : Fin n →₀ ℕ) => by
      rw [coeff_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [coeff_smul, LZdl_aux_coeff, smul_eq_mul]
      exact mul_nonneg (ha i) (mul_nonneg (by positivity) (hp _))
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_hess : ∀ (n : ℕ) (g : H n 2) (j k : Fin n), H.hessian g j k = (pderiv j (pderiv k g.1)).coeff 0 :=
    fun (n : ℕ) (g : H n 2) (j k : Fin n) => by
      rw [LZdl_aux_coeff, LZdl_aux_coeff]
      unfold H.hessian
      split_ifs with h
      · subst h
        rw [zero_add, ← Finsupp.single_add]
        simp; norm_num
      · simp [h]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_triple : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i j k : Fin n), ∃ c : ℝ, 0 < c ∧ (pderiv j (pderiv k (pderiv i p))).coeff 0 =
        c * p.coeff (Finsupp.single j 1 + Finsupp.single k 1 + Finsupp.single i 1) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i j k : Fin n) => by
      rw [LZdl_aux_coeff, LZdl_aux_coeff, LZdl_aux_coeff]
      refine ⟨(((0 : Fin n →₀ ℕ) j : ℝ) + 1) * (((Finsupp.single j 1 : Fin n →₀ ℕ) k : ℝ) + 1) *
        (((Finsupp.single j 1 + Finsupp.single k 1 : Fin n →₀ ℕ) i : ℝ) + 1), by positivity, ?_⟩
      rw [zero_add]; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_lim : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
      (h : ∀ ε : ℝ, 0 < ε → ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ ((A + ε • B) *ᵥ u) →
        (u ⬝ᵥ ((A + ε • B) *ᵥ u)) * (v ⬝ᵥ ((A + ε • B) *ᵥ v)) ≤ (u ⬝ᵥ ((A + ε • B) *ᵥ v)) ^ 2), ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (A *ᵥ u) →
        (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) ≤ (u ⬝ᵥ (A *ᵥ v)) ^ 2 :=
    fun (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
        (h : ∀ ε : ℝ, 0 < ε → ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ ((A + ε • B) *ᵥ u) →
          (u ⬝ᵥ ((A + ε • B) *ᵥ u)) * (v ⬝ᵥ ((A + ε • B) *ᵥ v)) ≤ (u ⬝ᵥ ((A + ε • B) *ᵥ v)) ^ 2) => by
      intro u v hu
      have e : ∀ (x y : Fin n → ℝ) (ε : ℝ),
          x ⬝ᵥ ((A + ε • B) *ᵥ y) = x ⬝ᵥ (A *ᵥ y) + ε * (x ⬝ᵥ (B *ᵥ y)) := by
        intro x y ε; simp [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul]
      simp only [e] at h
      have hc : ∀ p q : ℝ, Filter.Tendsto (fun ε : ℝ => p + ε * q) (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
        intro p q
        have hcont : Continuous (fun ε : ℝ => p + ε * q) := by fun_prop
        have := hcont.tendsto 0
        simp only [zero_mul, add_zero] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
          0 < ε ∧ 0 < u ⬝ᵥ (A *ᵥ u) + ε * (u ⬝ᵥ (B *ᵥ u)) := by
        refine Filter.Eventually.and self_mem_nhdsWithin ?_
        exact (hc _ _).eventually (lt_mem_nhds hu)
      apply le_of_tendsto_of_tendsto ((hc _ _).mul (hc _ _)) ((hc _ _).pow 2)
      filter_upwards [hev] with ε hε
      exact h ε hε.1 u v hε.2
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_split : ∀ (n : ℕ) (m : Fin n →₀ ℕ) (k : ℕ) (h : m.degree = k + 1), ∃ a : Fin n, ∃ m' : Fin n →₀ ℕ, m = m' + Finsupp.single a 1 ∧ m'.degree = k :=
    fun (n : ℕ) (m : Fin n →₀ ℕ) (k : ℕ) (h : m.degree = k + 1) => by
      have h0 : m ≠ 0 := by rintro rfl; simp at h
      obtain ⟨a, ha⟩ : ∃ a, m a ≠ 0 := by
        by_contra hc; push_neg at hc; exact h0 (Finsupp.ext hc)
      have h1 : Finsupp.single a 1 ≤ m := by
        intro x; rw [Finsupp.single_apply]; split_ifs with hx
        · subst hx; omega
        · exact Nat.zero_le _
      refine ⟨a, m - Finsupp.single a 1, (tsub_add_cancel_of_le h1).symm, ?_⟩
      have := congrArg Finsupp.degree (tsub_add_cancel_of_le h1)
      rw [map_add, Finsupp.degree_single] at this
      omega
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_three : ∀ (n : ℕ) (γ : Fin n →₀ ℕ) (hγ : γ.degree = 3) (p q : Fin n) (hpq : p ≠ q)
      (hp : 0 < γ p) (hq : 0 < γ q), ∃ r, γ = Finsupp.single p 1 + Finsupp.single q 1 + Finsupp.single r 1 :=
    fun (n : ℕ) (γ : Fin n →₀ ℕ) (hγ : γ.degree = 3) (p q : Fin n) (hpq : p ≠ q)
        (hp : 0 < γ p) (hq : 0 < γ q) => by
      have hle : Finsupp.single p 1 + Finsupp.single q 1 ≤ γ := by
        intro x
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
        split_ifs <;> subst_vars <;> omega
      have hdeg := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single] at hdeg
      obtain ⟨r, m', hm, hd⟩ := LZdl_aux_split n (γ - (Finsupp.single p 1 + Finsupp.single q 1)) 0
        (by omega)
      have : m' = 0 := (Finsupp.degree_eq_zero_iff m').1 hd
      subst this
      refine ⟨r, ?_⟩
      rw [zero_add] at hm
      rw [← tsub_add_cancel_of_le hle, hm]
      abel
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_mixed : ∀ (n : ℕ) (J : Set (Fin n →₀ ℕ)) (hJ : IsMConvex J)
      (hdeg : ∀ α ∈ J, α.degree = 3) (S : Finset (Fin n))
      (α : Fin n →₀ ℕ) (hα : α ∈ J) (j : Fin n) (hj : j ∈ S) (hαj : 0 < α j)
      (β : Fin n →₀ ℕ) (hβ : β ∈ J) (j' : Fin n) (hj' : j' ∉ S) (hβj : 0 < β j'), ∃ γ ∈ J, ∃ p ∈ S, ∃ q ∉ S, 0 < γ p ∧ 0 < γ q :=
    fun (n : ℕ) (J : Set (Fin n →₀ ℕ)) (hJ : IsMConvex J)
        (hdeg : ∀ α ∈ J, α.degree = 3) (S : Finset (Fin n))
        (α : Fin n →₀ ℕ) (hα : α ∈ J) (j : Fin n) (hj : j ∈ S) (hαj : 0 < α j)
        (β : Fin n →₀ ℕ) (hβ : β ∈ J) (j' : Fin n) (hj' : j' ∉ S) (hβj : 0 < β j') => by
      by_cases h1 : ∃ q ∉ S, 0 < α q
      · obtain ⟨q, hq, hq'⟩ := h1; exact ⟨α, hα, j, hj, q, hq, hαj, hq'⟩
      push_neg at h1
      by_cases h2 : ∃ p ∈ S, 0 < β p
      · obtain ⟨p, hp, hp'⟩ := h2; exact ⟨β, hβ, p, hp, j', hj', hp', hβj⟩
      push_neg at h2
      have hβj0 : β j = 0 := by have := h2 j hj; omega
      obtain ⟨q, hq1, hq2⟩ := hJ α hα β hβ j (by omega)
      have hqS : q ∉ S := by intro hq; have := h2 q hq; omega
      have hjq : j ≠ q := by rintro rfl; exact hqS hj
      have hev : ∀ t, (α - Finsupp.single j 1 + Finsupp.single q 1 : Fin n →₀ ℕ) t =
          α t - (if j = t then 1 else 0) + (if q = t then 1 else 0) := by
        intro t
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      obtain ⟨p, hpS, hp⟩ : ∃ p ∈ S, 0 < (α - Finsupp.single j 1 + Finsupp.single q 1 : Fin n →₀ ℕ) p := by
        by_cases h3 : 2 ≤ α j
        · refine ⟨j, hj, ?_⟩
          rw [hev]; simp; omega
        · obtain ⟨p, hpj, hp⟩ : ∃ p, p ≠ j ∧ 0 < α p := by
            by_contra hc
            push_neg at hc
            have : α = Finsupp.single j 1 := by
              ext t
              rw [Finsupp.single_apply]
              split_ifs with ht
              · subst ht; omega
              · have := hc t (Ne.symm ht); omega
            have hd := hdeg α hα
            rw [this, Finsupp.degree_single] at hd
            omega
          have hpS : p ∈ S := by
            by_contra hpS; have := h1 p hpS; omega
          have hpq : p ≠ q := by rintro rfl; exact hqS hpS
          refine ⟨p, hpS, ?_⟩
          rw [hev]; simp [Ne.symm hpj, Ne.symm hpq]; omega
      refine ⟨_, hq2, p, hpS, q, hqS, hp, ?_⟩
      rw [hev]; simp
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_base : ∀ (n : ℕ) (f : H n 3) (hf : f ∈ L n 3) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i), ∃ g : H n 2, g.1 = ∑ i, a i • pderiv i f.1 ∧ g ∈ L n 2 :=
    fun (n : ℕ) (f : H n 3) (hf : f ∈ L n 3) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) => by
      have hM : f ∈ M n 3 := hf.1
      have hD : ∀ i, (⟨f.1.pderiv i, f.2.pderiv⟩ : H n 2) ∈ L n 2 := hf.2
      have hfnn : ∀ m, 0 ≤ f.1.coeff m := hM.2
      let g : H n 2 := ⟨∑ i, a i • pderiv i f.1, LZdl_aux_hom n 2 f.1 f.2 a⟩
      refine ⟨g, rfl, ?_⟩
      have hgnn : ∀ m, 0 ≤ g.1.coeff m := LZdl_aux_nn n f.1 hfnn a ha
      refine ⟨(LZstab n g hgnn).2 ?_, hgnn⟩
      let Q : Fin n → Matrix (Fin n) (Fin n) ℝ :=
        fun i => H.hessian (⟨f.1.pderiv i, f.2.pderiv⟩ : H n 2)
      have hH : H.hessian g = ∑ i, a i • Q i := by
        ext j k
        rw [LZdl_aux_hess, Matrix.sum_apply]
        simp only [Q, Matrix.smul_apply, LZdl_aux_hess, g]
        simp [map_sum, coeff_sum]
      rw [hH]
      have hQc : ∀ i j k, Q i j k = (pderiv j (pderiv k (pderiv i f.1))).coeff 0 :=
        fun i j k => LZdl_aux_hess n _ j k
      have hsym1 : ∀ i j k, Q i j k = Q j i k := by
        intro i j k
        rw [hQc, hQc, LZdl_aux_comm2 n _ k i, LZdl_aux_comm2 n _ j i, LZdl_aux_comm2 n _ k j]
      have hsym2 : ∀ i j k, Q i j k = Q i k j := by
        intro i j k
        rw [hQc, hQc, LZdl_aux_comm2 n _ j k]
      have hnn : ∀ i j k, 0 ≤ Q i j k := by
        intro i j k
        obtain ⟨c, hc, hc'⟩ := LZdl_aux_triple n f.1 i j k
        rw [hQc, hc']
        exact mul_nonneg hc.le (hfnn _)
      have hpos : ∀ i j k, 0 < Q i j k ↔
          Finsupp.single j 1 + Finsupp.single k 1 + Finsupp.single i 1 ∈ f.1.support := by
        intro i j k
        obtain ⟨c, hc, hc'⟩ := LZdl_aux_triple n f.1 i j k
        rw [hQc, hc', MvPolynomial.mem_support_iff]
        constructor
        · intro h h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
        · intro h; exact mul_pos hc (lt_of_le_of_ne (hfnn _) (Ne.symm h))
      have hQ : ∀ i (u v : Fin n → ℝ), 0 < u ⬝ᵥ (Q i *ᵥ u) →
          (u ⬝ᵥ (Q i *ᵥ u)) * (v ⬝ᵥ (Q i *ᵥ v)) ≤ (u ⬝ᵥ (Q i *ᵥ v)) ^ 2 := by
        intro i
        exact (LZstab n _ (hD i).2).1 (hD i).1
      have hdeg : ∀ α ∈ (f.1.support : Set (Fin n →₀ ℕ)), α.degree = 3 := by
        intro α hα
        have := f.2 (Finsupp.mem_support_iff.1 hα)
        rw [Finsupp.degree_eq_weight_one]; exact this
      have hirr : ∀ S : Finset (Fin n), (∃ j ∈ S, ∃ k k', 0 < Q j k k') →
          (∃ j ∉ S, ∃ k k', 0 < Q j k k') → ∃ j ∈ S, ∃ k ∉ S, ∃ i, 0 < Q i j k := by
        rintro S ⟨j, hj, k, k', h1⟩ ⟨j', hj', l, l', h2⟩
        rw [hpos] at h1 h2
        obtain ⟨γ, hγ, p, hp, q, hq, hγp, hγq⟩ := LZdl_aux_mixed n _ hM.1 hdeg S _ h1 j hj
          (by simp) _ h2 j' hj' (by simp)
        have hpq : p ≠ q := by rintro rfl; exact hq hp
        obtain ⟨r, rfl⟩ := LZdl_aux_three n γ (hdeg γ hγ) p q hpq hγp hγq
        exact ⟨p, hp, q, hq, r, (hpos r p q).2 hγ⟩
      apply LZdl_aux_lim n _ (∑ i, Q i)
      intro ε hε
      have e : ∑ i, a i • Q i + ε • ∑ i, Q i = ∑ i, (a i + ε) • Q i := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        simp [add_smul]
      rw [e]
      exact LZpf n Q (fun i => a i + ε) hsym1 hsym2 hnn (fun i => by linarith [ha i]) hQ hirr
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl_aux_supp : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
      (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i), (((∑ i, a i • pderiv i p).support : Finset (Fin n →₀ ℕ)) : Set (Fin n →₀ ℕ)) =
        {γ | ∃ i ∈ {i | 0 < a i}, γ + Finsupp.single i 1 ∈ (p.support : Set (Fin n →₀ ℕ))} :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
        (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) => by
      ext γ
      simp only [Finset.mem_coe, MvPolynomial.mem_support_iff, Set.mem_setOf_eq, coeff_sum, coeff_smul,
        LZdl_aux_coeff, smul_eq_mul]
      have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          0 ≤ a i * (((γ i : ℝ) + 1) * p.coeff (γ + Finsupp.single i 1)) :=
        fun i _ => mul_nonneg (ha i) (mul_nonneg (by positivity) (hp _))
      rw [Ne, Finset.sum_eq_zero_iff_of_nonneg hnn]
      push_neg
      constructor
      · rintro ⟨i, _, hi⟩
        refine ⟨i, ?_, ?_⟩
        · rcases (ha i).lt_or_eq with h | h
          · exact h
          · rw [← h, zero_mul] at hi; exact absurd rfl hi
        · intro h0; rw [h0, mul_zero, mul_zero] at hi; exact hi rfl
      · rintro ⟨i, hi, h0⟩
        exact ⟨i, Finset.mem_univ _, mul_ne_zero hi.ne' (mul_ne_zero (by positivity) h0)⟩
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZdl : ∀ (n e : ℕ) (f : H n (e + 3)) (hf : f ∈ L n (e + 3)) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i), ∃ g : H n (e + 2), g.1 = ∑ i, a i • pderiv i f.1 ∧ g ∈ L n (e + 2) :=
    fun (n e : ℕ) (f : H n (e + 3)) (hf : f ∈ L n (e + 3)) (a : Fin n → ℝ)
        (ha : ∀ i, 0 ≤ a i) => by
      induction e with
      | zero => exact LZdl_aux_base n f hf a ha
      | succ e ih =>
        have hM : f ∈ M n (e + 4) := hf.1
        have hD : ∀ i, (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (e + 3)) ∈ L n (e + 3) := hf.2
        have hfnn : ∀ m, 0 ≤ f.1.coeff m := hM.2
        let g : H n (e + 3) := ⟨∑ i, a i • pderiv i f.1, LZdl_aux_hom n (e + 3) f.1 f.2 a⟩
        refine ⟨g, rfl, ?_⟩
        have hgnn : ∀ m, 0 ≤ g.1.coeff m := LZdl_aux_nn n f.1 hfnn a ha
        refine ⟨⟨?_, hgnn⟩, ?_⟩
        · show IsMConvex (((∑ i, a i • pderiv i f.1).support : Finset (Fin n →₀ ℕ)) : Set (Fin n →₀ ℕ))
          rw [LZdl_aux_supp n f.1 hfnn a ha]
          exact LZshadow n _ hM.1 _
        · intro k
          obtain ⟨g', hg'1, hg'2⟩ := ih _ (hD k)
          have : (⟨g.1.pderiv k, g.2.pderiv⟩ : H n (e + 2)) = g' := by
            apply Subtype.ext
            show pderiv k (∑ i, a i • pderiv i f.1) = g'.1
            rw [hg'1, LZdl_aux_comm]
          rw [this]; exact hg'2
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_P : ∀ (n d : ℕ) (f : H n d) (hf : f ∈ Ŀ n d), f ∈ P n d :=
    fun (n d : ℕ) (f : H n d) (hf : f ∈ Ŀ n d) => by
      rcases d with _ | _ | _ | d
      · exact hf
      · exact hf
      · exact hf.1
      · exact hf.1
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_nonneg : ∀ (n d : ℕ) (f : H n d) (hf : f ∈ P n d) (m : Fin n →₀ ℕ), 0 ≤ f.1.coeff m :=
    fun (n d : ℕ) (f : H n d) (hf : f ∈ P n d) (m : Fin n →₀ ℕ) => by
      by_cases h : f.1.coeff m = 0
      · rw [h]
      · have hw := f.2 h
        exact (hf m (by simpa [Finsupp.degree, Finsupp.weight] using hw)).le
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_eval_nonneg : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
      (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k), 0 ≤ eval w p :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
        (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) => by
      rw [MvPolynomial.eval_eq]
      exact Finset.sum_nonneg fun m _ => mul_nonneg (hp m)
        (Finset.prod_nonneg fun k _ => pow_nonneg (hw k) _)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_pderiv_nonneg : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
      (k : Fin n), ∀ m, 0 ≤ (pderiv k p).coeff m :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
        (k : Fin n) => by
      intro m
      conv_rhs => rw [p.as_sum]
      rw [map_sum, coeff_sum]
      refine Finset.sum_nonneg fun s _ => ?_
      rw [pderiv_monomial, coeff_monomial]
      split_ifs
      · exact mul_nonneg (hp s) (Nat.cast_nonneg _)
      · exact le_rfl
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_low : ∀ (n e : ℕ) (g : H n e) (he : e ≤ 1) (hg : ∀ m, 0 ≤ g.1.coeff m)
      (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k), eval w g.1 * eval w (pderiv i (pderiv j g.1)) ≤
        2 * (eval w (pderiv i g.1) * eval w (pderiv j g.1)) :=
    fun (n e : ℕ) (g : H n e) (he : e ≤ 1) (hg : ∀ m, 0 ≤ g.1.coeff m)
        (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) => by
      have h1 : (pderiv j g.1).IsHomogeneous (e - 1) := g.2.pderiv
      have h2 : (pderiv j g.1).totalDegree = 0 := by
        have := h1.totalDegree_le; omega
      rw [totalDegree_eq_zero_iff_eq_C] at h2
      rw [h2, pderiv_C, map_zero, mul_zero]
      have hi := LZhr_aux_eval_nonneg n _ (LZhr_aux_pderiv_nonneg n g.1 hg i) w hw
      have hj := LZhr_aux_eval_nonneg n _ (LZhr_aux_pderiv_nonneg n g.1 hg j) w hw
      rw [← h2]
      positivity
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_euler : ∀ (n k : ℕ) (P : MvPolynomial (Fin n) ℝ) (hP : P.IsHomogeneous k)
      (w : Fin n → ℝ), eval w (∑ l, w l • pderiv l P) = (k : ℝ) * eval w P :=
    fun (n k : ℕ) (P : MvPolynomial (Fin n) ℝ) (hP : P.IsHomogeneous k)
        (w : Fin n → ℝ) => by
      have h := congrArg (eval w) hP.sum_X_mul_pderiv
      simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at h
      simp only [map_sum, smul_eval]
      exact h
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_coeff_pderiv : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n)
      (m : Fin n →₀ ℕ), (pderiv i p).coeff m = p.coeff (m + Finsupp.single i 1) * ((m i : ℝ) + 1) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n)
        (m : Fin n →₀ ℕ) => by
      induction p using MvPolynomial.induction_on' with
      | monomial s a =>
        rw [pderiv_monomial, coeff_monomial, coeff_monomial]
        by_cases h : s = m + Finsupp.single i 1
        · subst h; simp
        · rw [if_neg h, zero_mul]
          split_ifs with h2
          · have hs : s i = 0 := by
              by_contra hs
              apply h
              ext k
              have := congrArg (· k) h2
              by_cases hk : k = i
              · subst hk; simp at this ⊢; omega
              · simp [Finsupp.single_apply, Ne.symm hk] at this ⊢; omega
            simp [hs]
          · rfl
      | add p q hp hq => simp [hp, hq, add_mul]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_hess : ∀ (n : ℕ) (g : H n 2) (k l : Fin n), pderiv k (pderiv l g.1) = C (H.hessian g k l) :=
    fun (n : ℕ) (g : H n 2) (k l : Fin n) => by
      have h1 : (pderiv k (pderiv l g.1)).IsHomogeneous 0 := g.2.pderiv.pderiv
      have h2 : (pderiv k (pderiv l g.1)).totalDegree = 0 := by
        have := h1.totalDegree_le; omega
      rw [totalDegree_eq_zero_iff_eq_C] at h2
      rw [h2]
      congr 1
      rw [LZhr_aux_coeff_pderiv, LZhr_aux_coeff_pderiv]
      simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, H.hessian]
      by_cases hkl : k = l
      · subst hkl; simp [← Finsupp.single_add]; ring
      · simp [hkl, Finsupp.single_apply, Ne.symm hkl]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_col : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (i : Fin n), u ⬝ᵥ (Q *ᵥ (Pi.single i 1 : Fin n → ℝ)) = ∑ k, u k * Q k i :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (i : Fin n) => by
      simp [mulVec, dotProduct, Pi.single_apply]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_bil : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (i j : Fin n)
      (x y : ℝ), u ⬝ᵥ (Q *ᵥ (x • (Pi.single i 1 : Fin n → ℝ) + y • (Pi.single j 1 : Fin n → ℝ))) =
        x * ∑ k, u k * Q k i + y * ∑ k, u k * Q k j :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (i j : Fin n)
        (x y : ℝ) => by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add,
        dotProduct_smul, dotProduct_smul, LZhr_aux_col, LZhr_aux_col, smul_eq_mul, smul_eq_mul]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_bil2 : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x y : ℝ), (x • (Pi.single i 1 : Fin n → ℝ) + y • (Pi.single j 1 : Fin n → ℝ)) ⬝ᵥ
        (Q *ᵥ (x • (Pi.single i 1 : Fin n → ℝ) + y • (Pi.single j 1 : Fin n → ℝ))) =
        x * x * Q i i + x * y * Q i j + y * x * Q j i + y * y * Q j j :=
    fun (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x y : ℝ) => by
      rw [LZhr_aux_bil]
      have e : ∀ l : Fin n, ∑ k, (x • (Pi.single i 1 : Fin n → ℝ) + y • (Pi.single j 1 : Fin n → ℝ)) k
          * Q k l = x * Q i l + y * Q j l := by
        intro l
        simp [add_mul, Finset.sum_add_distrib, Pi.single_apply]
      rw [e, e]
      ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_lim : ∀ (c K : ℝ) (hK : 0 ≤ K) (h : ∀ t : ℝ, 0 < t → 4 * t * c ≤ t ^ 2 * K), c ≤ 0 :=
    fun (c K : ℝ) (hK : 0 ≤ K) (h : ∀ t : ℝ, 0 < t → 4 * t * c ≤ t ^ 2 * K) => by
      by_contra hc
      push_neg at hc
      have ht : 0 < c / (K + 1) := by positivity
      have h1 := h _ ht
      have h2 : 4 * c ≤ c / (K + 1) * K := by
        have : c / (K + 1) * (4 * c) ≤ c / (K + 1) * (c / (K + 1) * K) := by nlinarith
        exact le_of_mul_le_mul_left this ht
      have h3 : c / (K + 1) * K ≤ c := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_quad : ∀ (n : ℕ) (g : H n 2) (hg : g ∈ Ŀ n 2)
      (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) (hw0 : w ≠ 0), eval w g.1 * eval w (pderiv i (pderiv j g.1)) ≤
        eval w (pderiv i g.1) * eval w (pderiv j g.1) :=
    fun (n : ℕ) (g : H n 2) (hg : g ∈ Ŀ n 2)
        (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) (hw0 : w ≠ 0) => by
      have hn : 0 < n := by
        by_contra h
        apply hw0
        funext k
        exact absurd k.2 (by omega)
      obtain ⟨hP, -, hN⟩ := (LZspec n hn g).mp hg
      have hc := fun m => (show 0 ≤ g.1.coeff m by
        by_cases h : g.1.coeff m = 0
        · rw [h]
        · have hw := g.2 h
          exact (hP m (by simpa [Finsupp.degree, Finsupp.weight] using hw)).le)
      have hsym : ∀ k l, H.hessian g k l = H.hessian g l k := by
        intro k l
        simp only [H.hessian]
        by_cases h : k = l
        · subst h; simp
        · rw [if_neg (Ne.symm h), if_neg h, add_comm]
      have hQnn : ∀ k l, 0 ≤ H.hessian g k l := by
        intro k l
        simp only [H.hessian]
        split_ifs
        · linarith [hc (Finsupp.single k 2)]
        · exact hc _
      have hQkk : ∀ k, 0 < H.hessian g k k := by
        intro k
        simp only [H.hessian, if_true]
        have := hP (Finsupp.single k 2) (by simp [Finsupp.weight_apply, Finsupp.sum_single_index])
        linarith
      have hhom : g.1.IsHomogeneous 2 := g.2
      have hA : ∀ k, eval w (pderiv k g.1) = ∑ l, w l * H.hessian g l k := by
        intro k
        have := LZhr_aux_euler n 1 (pderiv k g.1) hhom.pderiv w
        simp only [LZhr_aux_hess, map_sum, smul_eval, eval_C] at this
        rw [this]; simp
      have hG : 2 * eval w g.1 = ∑ l, w l * eval w (pderiv l g.1) := by
        have := LZhr_aux_euler n 2 g.1 hhom w
        simp only [map_sum, smul_eval] at this
        rw [this]; norm_num
      have hAnn : ∀ k, 0 ≤ eval w (pderiv k g.1) := by
        intro k
        rw [hA]
        exact Finset.sum_nonneg fun l _ => mul_nonneg (hw l) (hQnn l k)
      have hpos : ∃ k, 0 < w k := by
        by_contra hcon
        push_neg at hcon
        exact hw0 (funext fun k => le_antisymm (hcon k) (hw k))
      obtain ⟨k0, hk0⟩ := hpos
      have hAk : w k0 * H.hessian g k0 k0 ≤ eval w (pderiv k0 g.1) := by
        rw [hA]
        exact Finset.single_le_sum (f := fun l => w l * H.hessian g l k0)
          (fun l _ => mul_nonneg (hw l) (hQnn l k0)) (Finset.mem_univ k0)
      have hGk : w k0 * eval w (pderiv k0 g.1) ≤ 2 * eval w g.1 := by
        rw [hG]
        exact Finset.single_le_sum (f := fun l => w l * eval w (pderiv l g.1))
          (fun l _ => mul_nonneg (hw l) (hAnn l)) (Finset.mem_univ k0)
      have hGpos : 0 < eval w g.1 := by
        have := mul_pos hk0 (hQkk k0)
        have : 0 < eval w (pderiv k0 g.1) := by linarith
        have := mul_pos hk0 this
        linarith
      have hww : w ⬝ᵥ (H.hessian g *ᵥ w) = 2 * eval w g.1 := by
        rw [hG]
        simp only [dotProduct, mulVec]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hA k]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hsym]; ring
      have key : ∀ x y : ℝ, 2 * eval w g.1 * (x * x * H.hessian g i i + x * y * H.hessian g i j +
          y * x * H.hessian g j i + y * y * H.hessian g j j) ≤
          (x * eval w (pderiv i g.1) + y * eval w (pderiv j g.1)) ^ 2 := by
        intro x y
        have := hN w (x • (Pi.single i 1 : Fin n → ℝ) + y • (Pi.single j 1 : Fin n → ℝ))
          (by rw [hww]; linarith)
        rw [hww, LZhr_aux_bil2, LZhr_aux_bil] at this
        simpa only [hA] using this
      rw [LZhr_aux_hess, eval_C]
      rw [hsym j i] at key
      have hii := hQnn i i
      have hjj := hQnn j j
      set G := eval w g.1
      set a := eval w (pderiv i g.1)
      set b := eval w (pderiv j g.1)
      set q := H.hessian g i j
      have ha := hAnn i
      have hb := hAnn j
      rcases ha.lt_or_eq with ha' | ha'
      · rcases hb.lt_or_eq with hb' | hb'
        · have h := key b a
          have hab : 0 < 4 * (a * b) := by positivity
          have : 4 * (a * b) * (G * q) ≤ 4 * (a * b) * (a * b) := by
            nlinarith [mul_nonneg hGpos.le hii, mul_nonneg hGpos.le hjj, sq_nonneg a, sq_nonneg b,
              mul_nonneg (mul_nonneg hGpos.le hii) (sq_nonneg b),
              mul_nonneg (mul_nonneg hGpos.le hjj) (sq_nonneg a)]
          exact le_of_mul_le_mul_left this hab
        · have hb0 : b = 0 := hb'.symm
          rw [hb0, mul_zero]
          apply LZhr_aux_lim (G * q) (a ^ 2) (sq_nonneg a)
          intro t ht
          have h := key t 1
          rw [hb0] at h
          nlinarith [mul_nonneg hGpos.le hii, mul_nonneg hGpos.le hjj,
            mul_nonneg (mul_nonneg hGpos.le hii) (sq_nonneg t)]
      · have ha0 : a = 0 := ha'.symm
        rw [ha0, zero_mul]
        apply LZhr_aux_lim (G * q) (b ^ 2) (sq_nonneg b)
        intro t ht
        have h := key 1 t
        rw [ha0] at h
        nlinarith [mul_nonneg hGpos.le hii, mul_nonneg hGpos.le hjj,
          mul_nonneg (mul_nonneg hGpos.le hjj) (sq_nonneg t)]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_comm2 : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (i l : Fin n), pderiv i (pderiv l P) = pderiv l (pderiv i P) :=
    fun (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (i l : Fin n) => by
      conv_lhs => rw [P.as_sum]
      conv_rhs => rw [P.as_sum]
      simp only [map_sum, pderiv_monomial]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [tsub_right_comm]
      congr 1
      by_cases h : i = l
      · subst h; ring
      · simp [Finsupp.tsub_apply, h, Ne.symm h]; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_comm : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) (i : Fin n), pderiv i (∑ l, w l • pderiv l P) = ∑ l, w l • pderiv l (pderiv i P) :=
    fun (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) (i : Fin n) => by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Derivation.map_smul, LZhr_aux_comm2]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_iter : ∀ (n m : ℕ) (g : H n (m + 2)) (hg : g ∈ Ŀ n (m + 2))
      (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) (hw0 : w ≠ 0), ((m : ℝ) + 2) * (eval w g.1 * eval w (pderiv i (pderiv j g.1))) ≤
        2 * ((m : ℝ) + 1) * (eval w (pderiv i g.1) * eval w (pderiv j g.1)) :=
    fun (n m : ℕ) (g : H n (m + 2)) (hg : g ∈ Ŀ n (m + 2))
        (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) (hw0 : w ≠ 0) => by
      induction m with
      | zero =>
        have := LZhr_aux_quad n g hg i j w hw hw0
        push_cast
        linarith
      | succ m ih =>
        have hpos : ∃ k, 0 < w k := by
          by_contra hc
          push_neg at hc
          exact hw0 (funext fun k => le_antisymm (hc k) (hw k))
        obtain ⟨F, hF, hFL⟩ := LZdir n m g hg w hw hpos
        have h := ih F hFL
        have hh : g.1.IsHomogeneous (m + 3) := (mem_homogeneousSubmodule _ _).mp g.2
        have hhi : (pderiv i g.1).IsHomogeneous (m + 2) := hh.pderiv
        have hhj : (pderiv j g.1).IsHomogeneous (m + 2) := hh.pderiv
        have hhij : (pderiv i (pderiv j g.1)).IsHomogeneous (m + 1) := hhj.pderiv
        have e0 : eval w F.1 = ((m : ℝ) + 3) * eval w g.1 := by
          rw [hF, LZhr_aux_euler n (m + 3) _ hh w]; push_cast; ring
        have e1 : eval w (pderiv i F.1) = ((m : ℝ) + 2) * eval w (pderiv i g.1) := by
          rw [hF, LZhr_aux_comm, LZhr_aux_euler n (m + 2) _ hhi w]; push_cast; ring
        have e2 : eval w (pderiv j F.1) = ((m : ℝ) + 2) * eval w (pderiv j g.1) := by
          rw [hF, LZhr_aux_comm, LZhr_aux_euler n (m + 2) _ hhj w]; push_cast; ring
        have e3 : eval w (pderiv i (pderiv j F.1)) =
            ((m : ℝ) + 1) * eval w (pderiv i (pderiv j g.1)) := by
          rw [hF, LZhr_aux_comm, LZhr_aux_comm, LZhr_aux_euler n (m + 1) _ hhij w]; push_cast; ring
        rw [e0, e1, e2, e3] at h
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        push_cast
        have key : ((m : ℝ) + 1) * ((m : ℝ) + 2) *
            (((m : ℝ) + 3) * (eval w g.1 * eval w (pderiv i (pderiv j g.1)))) ≤
            ((m : ℝ) + 1) * ((m : ℝ) + 2) *
            (2 * ((m : ℝ) + 2) * (eval w (pderiv i g.1) * eval w (pderiv j g.1))) := by
          nlinarith
        have hpos' : (0 : ℝ) < ((m : ℝ) + 1) * ((m : ℝ) + 2) := by positivity
        have := le_of_mul_le_mul_left key hpos'
        linarith
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_core_pos : ∀ (n e : ℕ) (g : H n e) (he : 2 ≤ e) (hg : g ∈ Ŀ n e)
      (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) (hw0 : w ≠ 0), eval w g.1 * eval w (pderiv i (pderiv j g.1)) ≤
        2 * (eval w (pderiv i g.1) * eval w (pderiv j g.1)) :=
    fun (n e : ℕ) (g : H n e) (he : 2 ≤ e) (hg : g ∈ Ŀ n e)
        (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) (hw0 : w ≠ 0) => by
      obtain ⟨m, rfl⟩ : ∃ m, e = m + 2 := ⟨e - 2, by omega⟩
      have h := LZhr_aux_iter n m g hg i j w hw hw0
      have hc := LZhr_aux_nonneg n _ g (LZhr_aux_P n _ g hg)
      have hi := LZhr_aux_eval_nonneg n _ (LZhr_aux_pderiv_nonneg n g.1 hc i) w hw
      have hj := LZhr_aux_eval_nonneg n _ (LZhr_aux_pderiv_nonneg n g.1 hc j) w hw
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hp : 0 ≤ eval w (pderiv i g.1) * eval w (pderiv j g.1) := mul_nonneg hi hj
      by_contra hcon
      push_neg at hcon
      nlinarith
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_core : ∀ (n e : ℕ) (g : H n e) (he : 2 ≤ e) (hg : g ∈ Ŀ n e)
      (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k), eval w g.1 * eval w (pderiv i (pderiv j g.1)) ≤
        2 * (eval w (pderiv i g.1) * eval w (pderiv j g.1)) :=
    fun (n e : ℕ) (g : H n e) (he : 2 ≤ e) (hg : g ∈ Ŀ n e)
        (i j : Fin n) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) => by
      by_cases hw0 : w = 0
      · have hh : g.1.IsHomogeneous e := (mem_homogeneousSubmodule _ _).mp g.2
        have h0 : eval w g.1 = 0 := by
          subst hw0
          rw [eval_zero, constantCoeff_eq]
          exact hh.coeff_eq_zero (by rw [map_zero]; omega)
        have hc := LZhr_aux_nonneg n e g (LZhr_aux_P n e g hg)
        have hi := LZhr_aux_eval_nonneg n _ (LZhr_aux_pderiv_nonneg n g.1 hc i) w hw
        have hj := LZhr_aux_eval_nonneg n _ (LZhr_aux_pderiv_nonneg n g.1 hc j) w hw
        rw [h0, zero_mul]
        positivity
      · exact LZhr_aux_core_pos n e g he hg i j w hw hw0
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr_aux_struct : ∀ (n d : ℕ) (f : H n d) (hf : f ∈ Ŀ n d) (l : List (Fin n)), ∃ e, ∃ g : H n e, g.1 = List.foldr (fun k q => pderiv k q) f.1 l ∧
        ((2 ≤ e ∧ g ∈ Ŀ n e) ∨ (e ≤ 1 ∧ ∀ m, 0 ≤ g.1.coeff m)) :=
    fun (n d : ℕ) (f : H n d) (hf : f ∈ Ŀ n d) (l : List (Fin n)) => by
      induction l with
      | nil =>
        refine ⟨d, f, rfl, ?_⟩
        by_cases hd : 2 ≤ d
        · exact Or.inl ⟨hd, hf⟩
        · exact Or.inr ⟨by omega, LZhr_aux_nonneg n d f (LZhr_aux_P n d f hf)⟩
      | cons k l ih =>
        obtain ⟨e, g, hgD, h⟩ := ih
        simp only [List.foldr_cons]
        rcases h with ⟨he, hg⟩ | ⟨he, hg⟩
        · rcases e with _ | _ | _ | e
          · omega
          · omega
          · refine ⟨1, ⟨pderiv k g.1, g.2.pderiv⟩, congrArg (pderiv k) hgD, Or.inr ⟨le_rfl, ?_⟩⟩
            exact LZhr_aux_pderiv_nonneg n g.1 (LZhr_aux_nonneg n 2 g (LZhr_aux_P n 2 g hg)) k
          · exact ⟨e + 2, ⟨pderiv k g.1, g.2.pderiv⟩, congrArg (pderiv k) hgD, Or.inl ⟨by omega, hg.2 k⟩⟩
        · exact ⟨e - 1, ⟨pderiv k g.1, g.2.pderiv⟩, congrArg (pderiv k) hgD,
            Or.inr ⟨by omega, LZhr_aux_pderiv_nonneg n g.1 hg k⟩⟩
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZhr : ∀ (n d : ℕ) (f : H n d) (hf : f ∈ Ŀ n d), ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ), (∀ k, 0 ≤ w k) →
        eval w (List.foldr (fun k q => pderiv k q) f.1 l) *
            eval w (pderiv i (pderiv j (List.foldr (fun k q => pderiv k q) f.1 l))) ≤
          2 * (eval w (pderiv i (List.foldr (fun k q => pderiv k q) f.1 l)) *
            eval w (pderiv j (List.foldr (fun k q => pderiv k q) f.1 l))) :=
    fun (n d : ℕ) (f : H n d) (hf : f ∈ Ŀ n d) => by
      intro l i j w hw
      obtain ⟨e, g, hgD, h⟩ := LZhr_aux_struct n d f hf l
      rw [← hgD]
      rcases h with ⟨he, hg⟩ | ⟨he, hg⟩
      · exact LZhr_aux_core n e g he hg i j w hw
      · exact LZhr_aux_low n e g he hg i j w hw
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZlow : ∀ (n d : ℕ) (hn : 0 < n) (hd : d ≤ 2), closure (Ŀ n d) = L n d :=
    fun (n d : ℕ) (hn : 0 < n) (hd : d ≤ 2) => by
      have LZlow_aux_ccoeff (n d : ℕ) (m : Fin n →₀ ℕ) : Continuous (fun f : H n d => f.1.coeff m) := by
        exact LZtop_lin n d (MvPolynomial.lcoeff ℝ m)

      have LZlow_aux_tend (n d : ℕ) (g h1 h2 : H n d) :
          @Filter.Tendsto ℝ (H n d) (fun ε : ℝ => (⟨g.1 + ε • h1.1 + (ε ^ 2) • h2.1,
            add_mem (add_mem g.2 (Submodule.smul_mem _ ε h1.2)) (Submodule.smul_mem _ _ h2.2)⟩ : H n d))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds g) := by
        apply LZtop
        intro m
        simp only [coeff_add, coeff_smul, smul_eq_mul]
        have hc : Continuous (fun ε : ℝ => g.1.coeff m + ε * h1.1.coeff m + ε ^ 2 * h2.1.coeff m) := by
          fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
        simpa using this

      have LZlow_aux_hess (n : ℕ) (g h1 h2 p : H n 2) (ε : ℝ)
          (hp : p.1 = g.1 + ε • h1.1 + (ε ^ 2) • h2.1) :
          H.hessian p = H.hessian g + ε • H.hessian h1 + (ε ^ 2) • H.hessian h2 := by
        ext i j
        simp only [H.hessian, hp, coeff_add, coeff_smul, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]
        split_ifs <;> ring

      have LZlow_aux_deg (n : ℕ) (m : Fin n →₀ ℕ) : weight 1 m = m.degree := by
        rw [Finsupp.degree_eq_weight_one]; rfl

      have LZlow_aux_P_nonneg (n d : ℕ) (f : H n d) (hf : f ∈ P n d) : ∀ m, 0 ≤ f.1.coeff m := by
        intro m
        have hg : f.1.IsHomogeneous d := (mem_homogeneousSubmodule d f.1).1 f.2
        by_cases hm : m.degree = d
        · exact (hf m (by rw [LZlow_aux_deg]; exact hm)).le
        · rw [hg.coeff_eq_zero hm]

      have LZlow_aux_mk (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = M j i) :
          ∃ p : H n 2, H.hessian p = M := by
        have hmem : (∑ i : Fin n, ∑ j : Fin n, C (M i j / 2) * (X i * X j) : MvPolynomial (Fin n) ℝ)
            ∈ homogeneousSubmodule (Fin n) ℝ 2 := by
          apply Submodule.sum_mem; intro i _
          apply Submodule.sum_mem; intro j _
          rw [mem_homogeneousSubmodule]
          have := (isHomogeneous_C (Fin n) (M i j / 2)).mul ((isHomogeneous_X ℝ i).mul (isHomogeneous_X ℝ j))
          simpa using this
        refine ⟨⟨_, hmem⟩, ?_⟩
        ext a b
        simp only [H.hessian, coeff_sum, coeff_C_mul, LZstab_aux_XX, coeff_monomial]
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl]
          have key : ∀ i j : Fin n, (Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single a 2) ↔
              (i = a ∧ j = a) := by
            intro i j
            rw [show (2:ℕ) = 1 + 1 from rfl, Finsupp.single_add,
              Finsupp.single_add_single_eq_single_add_single one_ne_zero one_ne_zero]
            constructor
            · intro h; clear * - h; aesop
            · intro h; clear * - h; aesop
          simp only [key]
          rw [Fintype.sum_eq_single a, Fintype.sum_eq_single a]
          · simp; ring
          all_goals (intro x hx; simp [hx])
        · rw [if_neg hab]
          have key : ∀ i j : Fin n, (Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single a 1 + Finsupp.single b 1) ↔
              ((i = a ∧ j = b) ∨ (i = b ∧ j = a)) := by
            intro i j
            rw [Finsupp.single_add_single_eq_single_add_single one_ne_zero one_ne_zero]
            simp
          simp only [key]
          rw [Fintype.sum_eq_add a b hab, Fintype.sum_eq_single b, Fintype.sum_eq_single a]
          · simp [hab, Ne.symm hab, hM b a]
          all_goals first
            | (intro x ⟨hxa, hxb⟩; simp [hxa, hxb])
            | (intro x hx; simp [hx, hab, Ne.symm hab])

      have LZlow_aux_sub (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
          (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (Q *ᵥ u) →
            (u ⬝ᵥ (Q *ᵥ u)) * (v ⬝ᵥ (Q *ᵥ v)) ≤ (u ⬝ᵥ (Q *ᵥ v)) ^ 2) :
          ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ ((Q - δ • 1) *ᵥ u) →
            (u ⬝ᵥ ((Q - δ • 1) *ᵥ u)) * (v ⬝ᵥ ((Q - δ • 1) *ᵥ v)) ≤
              (u ⬝ᵥ ((Q - δ • 1) *ᵥ v)) ^ 2 := by
        have e : ∀ x y : Fin n → ℝ, x ⬝ᵥ ((Q - δ • 1) *ᵥ y) = x ⬝ᵥ (Q *ᵥ y) - δ * (x ⬝ᵥ y) := by
          intro x y
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
            dotProduct_smul, smul_eq_mul]
        intro u v hu
        rw [e] at hu
        rw [e, e, e]
        have hU : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
        have ha : 0 < u ⬝ᵥ (Q *ᵥ u) := by nlinarith
        have h1 := hN u v ha
        set a := u ⬝ᵥ (Q *ᵥ u)
        set b := u ⬝ᵥ (Q *ᵥ v)
        set c := v ⬝ᵥ (Q *ᵥ v)
        set s := b / a with hs
        have hsa : s * a = b := by rw [hs]; field_simp
        have hw : 0 ≤ (v - s • u) ⬝ᵥ (v - s • u) :=
          Finset.sum_nonneg (fun i _ => mul_self_nonneg ((v - s • u) i))
        have hw' : (v - s • u) ⬝ᵥ (v - s • u) = v ⬝ᵥ v - 2 * s * (u ⬝ᵥ v) + s ^ 2 * (u ⬝ᵥ u) := by
          simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
            dotProduct_comm v u]
          ring
        rw [hw'] at hw
        have hq : c - 2 * s * b + s ^ 2 * a ≤ 0 := by
          have : a * (c - 2 * s * b + s ^ 2 * a) = a * c - b ^ 2 := by
            rw [← hsa]; ring
          nlinarith
        set U := u ⬝ᵥ u
        set W := u ⬝ᵥ v
        set V := v ⬝ᵥ v
        have hq2 : (c - δ * V) - 2 * s * (b - δ * W) + s ^ 2 * (a - δ * U) ≤ 0 := by nlinarith
        have key : (a - δ * U) * ((c - δ * V) - 2 * s * (b - δ * W) + s ^ 2 * (a - δ * U)) =
            (a - δ * U) * (c - δ * V) - (b - δ * W) ^ 2 + (s * (a - δ * U) - (b - δ * W)) ^ 2 := by ring
        have := mul_nonpos_of_nonneg_of_nonpos hu.le hq2
        nlinarith [sq_nonneg (s * (a - δ * U) - (b - δ * W))]

      have LZlow_aux_cong (n : ℕ) (Q A : Matrix (Fin n) (Fin n) ℝ)
          (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (Q *ᵥ u) →
            (u ⬝ᵥ (Q *ᵥ u)) * (v ⬝ᵥ (Q *ᵥ v)) ≤ (u ⬝ᵥ (Q *ᵥ v)) ^ 2) :
          ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ ((A.transpose * Q * A) *ᵥ u) →
            (u ⬝ᵥ ((A.transpose * Q * A) *ᵥ u)) * (v ⬝ᵥ ((A.transpose * Q * A) *ᵥ v)) ≤
              (u ⬝ᵥ ((A.transpose * Q * A) *ᵥ v)) ^ 2 := by
        have e : ∀ x y : Fin n → ℝ, x ⬝ᵥ ((A.transpose * Q * A) *ᵥ y) = (A *ᵥ x) ⬝ᵥ (Q *ᵥ (A *ᵥ y)) := by
          intro x y
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
            Matrix.vecMul_transpose]
        intro u v hu
        rw [e] at hu
        rw [e, e, e]
        exact hN _ _ hu

      have LZlow_aux_inv (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.transpose = Q) (δ : ℝ)
          (hδ : 0 < δ)
          (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (Q *ᵥ u) →
            (u ⬝ᵥ (Q *ᵥ u)) * (v ⬝ᵥ (Q *ᵥ v)) ≤ (u ⬝ᵥ (Q *ᵥ v)) ^ 2)
          (h1 : 0 < (fun _ => (1:ℝ)) ⬝ᵥ ((Q - δ • 1) *ᵥ (fun _ => (1:ℝ)))) :
          IsUnit (Q - δ • 1) := by
        rw [← Matrix.mulVec_injective_iff_isUnit]
        intro x y hxy
        have hz : (Q - δ • 1) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
        by_contra hne
        have hz0 : x - y ≠ 0 := sub_ne_zero.mpr hne
        set z := x - y
        have hQz : Q *ᵥ z = δ • z := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
          exact hz
        have hzz : 0 < z ⬝ᵥ z := by
          rcases (Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i)) : 0 ≤ z ⬝ᵥ z).lt_or_eq with h | h
          · exact h
          · exact absurd (LZeig_self_eq_zero n z h.symm) hz0
        set one : Fin n → ℝ := fun _ => 1 with hone
        have hqz : z ⬝ᵥ (Q *ᵥ z) = δ * (z ⬝ᵥ z) := by rw [hQz, dotProduct_smul, smul_eq_mul]
        have hb : z ⬝ᵥ (Q *ᵥ one) = δ * (one ⬝ᵥ z) := by
          rw [LZeig_symm n Q hQ, hQz, dotProduct_smul, smul_eq_mul]
        have hq1 : one ⬝ᵥ (Q *ᵥ one) = one ⬝ᵥ ((Q - δ • 1) *ᵥ one) + δ * (n : ℝ) := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
            dotProduct_smul, smul_eq_mul]
          simp [one, dotProduct]
        have hcs : (one ⬝ᵥ z) ^ 2 ≤ (n : ℝ) * (z ⬝ᵥ z) := by
          have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ one z
          simpa [one, dotProduct, pow_two] using this
        have := hN z one (by rw [hqz]; positivity)
        rw [hqz, hb, hq1] at this
        set q := one ⬝ᵥ ((Q - δ • 1) *ᵥ one)
        have h3 := mul_le_mul_of_nonneg_left hcs (sq_nonneg δ)
        have h2 : δ * (z ⬝ᵥ z) * q ≤ 0 := by nlinarith
        have : 0 < δ * (z ⬝ᵥ z) * q := by positivity
        linarith

      have LZlow_aux_key (n : ℕ) (hn : 0 < n) (p : H n 2) (Q : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
          (hδ : 0 < δ)
          (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (Q *ᵥ u) →
            (u ⬝ᵥ (Q *ᵥ u)) * (v ⬝ᵥ (Q *ᵥ v)) ≤ (u ⬝ᵥ (Q *ᵥ v)) ^ 2)
          (hp : H.hessian p = Q - δ • 1) (hpos : ∀ i j, 0 < H.hessian p i j) : p ∈ Ŀ n 2 := by
        rw [LZspec n hn]
        have hQe : Q = H.hessian p + δ • 1 := by rw [hp]; abel
        have hQ : Q.transpose = Q := by
          ext i j
          rw [hQe]
          simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, LZstab_aux_symm n p j i,
            Matrix.one_apply, eq_comm]
        haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        refine ⟨?_, ?_, ?_⟩
        · intro m hm
          rw [LZlow_aux_deg] at hm
          obtain ⟨a, b, rfl⟩ := LZstab_aux_cls n m hm
          by_cases hab : a = b
          · subst hab
            have := hpos a a
            simp only [H.hessian, if_true] at this
            rw [← Finsupp.single_add]
            linarith
          · have := hpos a b
            simp only [H.hessian, if_neg hab] at this
            exact this
        · rw [hp]
          apply LZlow_aux_inv n Q hQ δ hδ hN
          rw [← hp, LZstab_aux_dot]
          exact Finset.sum_pos (fun i _ => Finset.sum_pos (fun j _ => by simpa using hpos i j)
            Finset.univ_nonempty) Finset.univ_nonempty
        · rw [hp]
          exact LZlow_aux_sub n Q δ hδ.le hN

      have LZlow_aux_approx2 (n : ℕ) (hn : 0 < n) (g : H n 2) (hg : ∀ m, 0 ≤ g.1.coeff m)
          (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (H.hessian g *ᵥ u) →
            (u ⬝ᵥ (H.hessian g *ᵥ u)) * (v ⬝ᵥ (H.hessian g *ᵥ v)) ≤ (u ⬝ᵥ (H.hessian g *ᵥ v)) ^ 2) :
          g ∈ closure (Ŀ n 2) := by
        have hQnn : ∀ i j, 0 ≤ H.hessian g i j := LZstab_aux_nn n g hg
        have hQs : ∀ i j, H.hessian g i j = H.hessian g j i := LZstab_aux_symm n g
        set Q := H.hessian g with hQdef
        set J : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun _ _ => 1 with hJ
        have hJt : J.transpose = J := by ext i j; simp [J]
        by_cases h0 : ∀ i j, Q i j = 0
        · have hQ0 : Q = 0 := by ext i j; exact h0 i j
          obtain ⟨p1, hp1⟩ := LZlow_aux_mk n ((2:ℝ) • J - 1) (by
            intro i j; simp [J, Matrix.one_apply, eq_comm])
          obtain ⟨p2, hp2⟩ := LZlow_aux_mk n 0 (by simp)
          apply mem_closure_of_tendsto (LZlow_aux_tend n 2 g p1 p2)
          filter_upwards [self_mem_nhdsWithin] with ε hε
          have hε' : (0:ℝ) < ε := hε
          have hH := LZlow_aux_hess n g p1 p2 (⟨g.1 + ε • p1.1 + (ε ^ 2) • p2.1,
            add_mem (add_mem g.2 (Submodule.smul_mem _ ε p1.2)) (Submodule.smul_mem _ _ p2.2)⟩ : H n 2)
            ε rfl
          rw [hp1, hp2, ← hQdef, hQ0] at hH
          apply LZlow_aux_key n hn _ ((2 * ε) • J) ε hε'
          · intro u v hu
            have e : ∀ x y : Fin n → ℝ, x ⬝ᵥ (((2 * ε) • J) *ᵥ y) =
                2 * ε * ((∑ i, x i) * (∑ j, y j)) := by
              intro x y
              have hJy : ((2 * ε) • J) *ᵥ y = fun _ => 2 * ε * ∑ j, y j := by
                ext i; simp [J, Matrix.mulVec, dotProduct, Finset.mul_sum]
              rw [hJy]; simp only [dotProduct]; rw [← Finset.sum_mul]; ring
            rw [e, e, e]
            apply le_of_eq; ring
          · rw [hH]; ext i j; simp [J, Matrix.one_apply]; split_ifs <;> ring
          · intro i j
            rw [hH]; simp [J, Matrix.one_apply]; split_ifs <;> linarith
        · have hS : 0 < ∑ k, ∑ l, Q k l := by
            push_neg at h0
            obtain ⟨i0, j0, hij⟩ := h0
            have hp : 0 < Q i0 j0 := lt_of_le_of_ne (hQnn i0 j0) (Ne.symm hij)
            have h1 : Q i0 j0 ≤ ∑ l, Q i0 l :=
              Finset.single_le_sum (f := fun l => Q i0 l) (fun l _ => hQnn i0 l) (Finset.mem_univ j0)
            have h2 : ∑ l, Q i0 l ≤ ∑ k, ∑ l, Q k l :=
              Finset.single_le_sum (f := fun k => ∑ l, Q k l)
                (fun k _ => Finset.sum_nonneg (fun l _ => hQnn k l)) (Finset.mem_univ i0)
            linarith
          set S := ∑ k, ∑ l, Q k l with hSdef
          have eJQ : ∀ i j, (J * Q) i j = ∑ k, Q k j := by intro i j; simp [J, Matrix.mul_apply]
          have eQJ : ∀ i j, (Q * J) i j = ∑ k, Q i k := by intro i j; simp [J, Matrix.mul_apply]
          have eJQJ : ∀ i j, (J * Q * J) i j = S := by
            intro i j; simp only [Matrix.mul_apply, eJQ]; simp [J, hSdef]; rw [Finset.sum_comm]
          obtain ⟨p1, hp1⟩ := LZlow_aux_mk n (J * Q + Q * J) (by
            intro i j
            simp only [Matrix.add_apply, eJQ, eQJ]
            rw [add_comm]; congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> exact hQs _ _)
          obtain ⟨p2, hp2⟩ := LZlow_aux_mk n (J * Q * J - (S / 2) • 1) (by
            intro i j
            simp [eJQJ, Matrix.one_apply, eq_comm])
          apply mem_closure_of_tendsto (LZlow_aux_tend n 2 g p1 p2)
          filter_upwards [self_mem_nhdsWithin] with ε hε
          have hε' : (0:ℝ) < ε := hε
          have hH := LZlow_aux_hess n g p1 p2 (⟨g.1 + ε • p1.1 + (ε ^ 2) • p2.1,
            add_mem (add_mem g.2 (Submodule.smul_mem _ ε p1.2)) (Submodule.smul_mem _ _ p2.2)⟩ : H n 2)
            ε rfl
          rw [hp1, hp2, ← hQdef] at hH
          apply LZlow_aux_key n hn _ ((1 + ε • J).transpose * Q * (1 + ε • J)) (ε ^ 2 * S / 2)
            (by positivity)
          · exact LZlow_aux_cong n Q _ hN
          · rw [hH]
            simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hJt,
              Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
              Matrix.mul_smul, smul_smul, Matrix.mul_assoc, smul_sub, smul_add]
            module
          · intro i j
            rw [hH]
            simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, eJQ, eQJ, eJQJ, smul_eq_mul]
            have a1 : 0 ≤ ∑ k, Q k j := Finset.sum_nonneg (fun k _ => hQnn k j)
            have a2 : 0 ≤ ∑ k, Q i k := Finset.sum_nonneg (fun k _ => hQnn i k)
            have a3 : (1 : Matrix (Fin n) (Fin n) ℝ) i j ≤ 1 := by
              rw [Matrix.one_apply]; split_ifs <;> norm_num
            have a4 := hQnn i j
            have : 0 < ε ^ 2 * (S - S / 2 * (1 : Matrix (Fin n) (Fin n) ℝ) i j) := by
              apply mul_pos (by positivity); nlinarith
            nlinarith [mul_nonneg hε'.le (add_nonneg a1 a2)]

      have LZlow_aux_clnn (n d : ℕ) (s : Set (H n d)) (hs : ∀ f ∈ s, ∀ m, 0 ≤ f.1.coeff m)
          (g : H n d) (hg : g ∈ closure s) : ∀ m, 0 ≤ g.1.coeff m := by
        intro m
        have := closure_minimal (s := s) (t := {f : H n d | 0 ≤ f.1.coeff m})
          (fun f hf => hs f hf m) (isClosed_le continuous_const (LZlow_aux_ccoeff n d m)) hg
        exact this

      have LZlow_aux_chess (n : ℕ) (u v : Fin n → ℝ) :
          Continuous (fun f : H n 2 => u ⬝ᵥ (H.hessian f *ᵥ v)) := by
        have hent : ∀ i j : Fin n, Continuous (fun f : H n 2 => H.hessian f i j) := by
          intro i j
          by_cases h : i = j
          · subst h
            simp only [H.hessian, if_true]
            exact continuous_const.mul (LZlow_aux_ccoeff n 2 _)
          · simp only [H.hessian, if_neg h]
            exact LZlow_aux_ccoeff n 2 _
        have e : (fun f : H n 2 => u ⬝ᵥ (H.hessian f *ᵥ v)) =
            fun f => ∑ i : Fin n, ∑ j : Fin n, H.hessian f i j * (u i * v j) := by
          funext f; exact LZstab_aux_dot n _ u v
        rw [e]
        exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
          (fun j _ => (hent i j).mul continuous_const))

      have LZlow_aux_cl2 (n : ℕ) (hn : 0 < n) (g : H n 2) (hg : g ∈ closure (Ŀ n 2)) :
          (∀ m, 0 ≤ g.1.coeff m) ∧ ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (H.hessian g *ᵥ u) →
            (u ⬝ᵥ (H.hessian g *ᵥ u)) * (v ⬝ᵥ (H.hessian g *ᵥ v)) ≤ (u ⬝ᵥ (H.hessian g *ᵥ v)) ^ 2 := by
        refine ⟨LZlow_aux_clnn n 2 _ (fun f hf => LZlow_aux_P_nonneg n 2 f ((LZspec n hn f).1 hf).1) g hg, ?_⟩
        intro u v hu
        have := closure_minimal (s := Ŀ n 2)
          (t := {f : H n 2 | u ⬝ᵥ (H.hessian f *ᵥ u) ≤ 0} ∪
            {f : H n 2 | (u ⬝ᵥ (H.hessian f *ᵥ u)) * (v ⬝ᵥ (H.hessian f *ᵥ v)) ≤
              (u ⬝ᵥ (H.hessian f *ᵥ v)) ^ 2})
          (by
            intro f hf
            obtain ⟨_, _, hN⟩ := (LZspec n hn f).1 hf
            by_cases hq : u ⬝ᵥ (H.hessian f *ᵥ u) ≤ 0
            · exact Or.inl hq
            · exact Or.inr (hN u v (lt_of_not_ge hq)))
          ((isClosed_le (LZlow_aux_chess n u u) continuous_const).union
            (isClosed_le ((LZlow_aux_chess n u u).mul (LZlow_aux_chess n v v))
              ((LZlow_aux_chess n u v).pow 2))) hg
        rcases this with h | h
        · exact absurd h (not_le.mpr hu)
        · exact h

      have LZlow_aux_rep0 (n : ℕ) (f : H n 0) : f.1 = C (f.1.coeff 0) := by
        have hg : f.1.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 f.1).1 f.2
        ext m
        rw [coeff_C]
        split_ifs with h
        · subst h; rfl
        · exact hg.coeff_eq_zero (fun hd => h ((Finsupp.degree_eq_zero_iff m).1 hd).symm)

      have LZlow_aux_rep1 (n : ℕ) (f : H n 1) :
          f.1 = ∑ i : Fin n, C (f.1.coeff (Finsupp.single i 1)) * X i := by
        have hg : f.1.IsHomogeneous 1 := (mem_homogeneousSubmodule 1 f.1).1 f.2
        ext m
        simp only [coeff_sum, coeff_C_mul, coeff_X']
        by_cases hm : m.degree = 1
        · obtain ⟨a, m', rfl, hd⟩ := LZstab_aux_split n m 0 hm
          have : m' = 0 := (Finsupp.degree_eq_zero_iff m').1 hd
          subst this
          rw [zero_add, Fintype.sum_eq_single a]
          · simp
          · intro i hi; simp [Finsupp.single_left_inj one_ne_zero, hi]
        · rw [hg.coeff_eq_zero hm]
          symm
          apply Finset.sum_eq_zero
          intro i _
          rw [if_neg, mul_zero]
          intro h; apply hm; rw [← h, Finsupp.degree_single]

      have LZlow_aux_stab0 (n : ℕ) (f : H n 0) : IsStable f.1 := by
        by_cases hc : f.1.coeff 0 = 0
        · left; rw [LZlow_aux_rep0 n f, hc, C_0]
        · right; intro z
          rw [LZlow_aux_rep0 n f, aeval_C]
          simpa using hc

      have LZlow_aux_stab1 (n : ℕ) (f : H n 1) (hf : ∀ m, 0 ≤ f.1.coeff m) : IsStable f.1 := by
        by_cases hall : ∀ i : Fin n, f.1.coeff (Finsupp.single i 1) = 0
        · left; rw [LZlow_aux_rep1 n f]; simp [hall]
        · right
          push_neg at hall
          obtain ⟨i0, hi0⟩ := hall
          intro z hz
          rw [LZlow_aux_rep1 n f] at hz
          simp only [map_sum, map_mul, aeval_X, aeval_C] at hz
          have him := congrArg Complex.im hz
          rw [Complex.im_sum] at him
          simp only [Function.comp_apply, Complex.zero_im] at him
          have : 0 < ∑ i : Fin n, ((algebraMap ℝ ℂ) (f.1.coeff (Finsupp.single i 1)) * ((z i : ℂ))).im := by
            apply Finset.sum_pos'
            · intro i _
              simp only [Complex.coe_algebraMap, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
              exact mul_nonneg (hf _) (z i).im_pos.le
            · refine ⟨i0, Finset.mem_univ _, ?_⟩
              simp only [Complex.coe_algebraMap, Complex.im_ofReal_mul]
              exact mul_pos (lt_of_le_of_ne (hf _) (Ne.symm hi0)) (z i0).im_pos
          linarith

      have LZlow_aux_approx0 (n : ℕ) (g : H n 0) (hg : ∀ m, 0 ≤ g.1.coeff m) :
          g ∈ closure (Ŀ n 0) := by
        have h1 : (1 : MvPolynomial (Fin n) ℝ) ∈ homogeneousSubmodule (Fin n) ℝ 0 := by
          rw [mem_homogeneousSubmodule]; exact isHomogeneous_one (Fin n) ℝ
        apply mem_closure_of_tendsto (LZlow_aux_tend n 0 g ⟨1, h1⟩ ⟨0, Submodule.zero_mem _⟩)
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : (0:ℝ) < ε := hε
        show _ ∈ P n 0
        intro m hm
        rw [LZlow_aux_deg] at hm
        have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
        subst hm0
        simp only [coeff_add, coeff_smul, smul_eq_mul, coeff_zero, coeff_one, if_true, mul_zero, add_zero,
          mul_one]
        linarith [hg 0]

      have LZlow_aux_approx1 (n : ℕ) (g : H n 1) (hg : ∀ m, 0 ≤ g.1.coeff m) :
          g ∈ closure (Ŀ n 1) := by
        have h1 : (∑ i : Fin n, X i : MvPolynomial (Fin n) ℝ) ∈ homogeneousSubmodule (Fin n) ℝ 1 := by
          apply Submodule.sum_mem; intro i _
          rw [mem_homogeneousSubmodule]; exact isHomogeneous_X ℝ i
        apply mem_closure_of_tendsto (LZlow_aux_tend n 1 g ⟨_, h1⟩ ⟨0, Submodule.zero_mem _⟩)
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : (0:ℝ) < ε := hε
        show _ ∈ P n 1
        intro m hm
        rw [LZlow_aux_deg] at hm
        obtain ⟨a, m', rfl, hd⟩ := LZstab_aux_split n m 0 hm
        have : m' = 0 := (Finsupp.degree_eq_zero_iff m').1 hd
        subst this
        have hc : (∑ i : Fin n, X i : MvPolynomial (Fin n) ℝ).coeff (0 + Finsupp.single a 1) = 1 := by
          rw [zero_add, coeff_sum, Fintype.sum_eq_single a]
          · simp
          · intro i hi; simp [coeff_X', Finsupp.single_left_inj one_ne_zero, hi]
        simp only [coeff_add, coeff_smul, smul_eq_mul, coeff_zero, mul_zero, add_zero]
        rw [hc]
        linarith [hg (0 + Finsupp.single a 1)]
      match d, hd with
      | 0, _ =>
        apply Set.Subset.antisymm
        · intro g hg
          have hnn := LZlow_aux_clnn n 0 (Ŀ n 0) (fun f hf => LZlow_aux_P_nonneg n 0 f hf) g hg
          show g ∈ S n 0
          exact ⟨LZlow_aux_stab0 n g, hnn⟩
        · intro g hg
          have hg' : g ∈ S n 0 := hg
          exact LZlow_aux_approx0 n g hg'.2
      | 1, _ =>
        apply Set.Subset.antisymm
        · intro g hg
          have hnn := LZlow_aux_clnn n 1 (Ŀ n 1) (fun f hf => LZlow_aux_P_nonneg n 1 f hf) g hg
          show g ∈ S n 1
          exact ⟨LZlow_aux_stab1 n g hnn, hnn⟩
        · intro g hg
          have hg' : g ∈ S n 1 := hg
          exact LZlow_aux_approx1 n g hg'.2
      | 2, _ =>
        apply Set.Subset.antisymm
        · intro g hg
          obtain ⟨hnn, hN⟩ := LZlow_aux_cl2 n hn g hg
          show g ∈ S n 2
          exact ⟨(LZstab n g hnn).2 hN, hnn⟩
        · intro g hg
          have hg' : g ∈ S n 2 := hg
          exact LZlow_aux_approx2 n hn g hg'.2 ((LZstab n g hg'.2).1 hg'.1)
      | k + 3, h => exact absurd h (by omega)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_coeff_pderiv : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (m : Fin n →₀ ℕ), (pderiv j p).coeff m = ((m j : ℝ) + 1) * p.coeff (m + Finsupp.single j 1) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (m : Fin n →₀ ℕ) => by
      induction p using MvPolynomial.induction_on' with
      | monomial s a =>
        rw [pderiv_monomial, coeff_monomial, coeff_monomial]
        by_cases hs : s j = 0
        · have h1 : s - Finsupp.single j 1 = s := by
            ext t; simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
            split_ifs <;> subst_vars <;> omega
          have h2 : s ≠ m + Finsupp.single j 1 := by
            intro h; have := congrArg (fun f => f j) h; simp at this; omega
          rw [h1, if_neg h2, hs]; simp
        · have hiff : s - Finsupp.single j 1 = m ↔ s = m + Finsupp.single j 1 := by
            constructor
            · rintro rfl; ext t; simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, Finsupp.single_apply]
              split_ifs <;> subst_vars <;> omega
            · rintro rfl; ext t; simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, Finsupp.single_apply]
              split_ifs <;> subst_vars <;> omega
          by_cases h : s = m + Finsupp.single j 1
          · rw [if_pos (hiff.2 h), if_pos h]; subst h; simp; ring
          · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]; simp
      | add p q hp hq => simp only [map_add, coeff_add, hp, hq]; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_nn_pderiv : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
      (hp : ∀ m, 0 ≤ p.coeff m), ∀ m, 0 ≤ (pderiv j p).coeff m :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
        (hp : ∀ m, 0 ≤ p.coeff m) => by
      intro m; rw [LZray_coeff_pderiv]; exact mul_nonneg (by positivity) (hp _)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_mem_supp_pderiv : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (m : Fin n →₀ ℕ), m ∈ (pderiv j p).support ↔ m + Finsupp.single j 1 ∈ p.support :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (j : Fin n) (m : Fin n →₀ ℕ) => by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, LZray_coeff_pderiv]
      have : ((m j : ℝ) + 1) ≠ 0 := by positivity
      constructor
      · intro h h'; exact h (by rw [h', mul_zero])
      · intro h h'; exact h ((mul_eq_zero.1 h').resolve_left this)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_eval_nonneg : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
      (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k), 0 ≤ eval w p :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
        (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) => by
      rw [eval_eq']
      exact Finset.sum_nonneg fun d _ => mul_nonneg (hp d) (Finset.prod_nonneg fun t _ => pow_nonneg (hw t) _)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_eval_pos : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
      (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) (m : Fin n →₀ ℕ) (hm : m ∈ p.support)
      (hmw : ∀ k, w k = 0 → m k = 0), 0 < eval w p :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
        (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k) (m : Fin n →₀ ℕ) (hm : m ∈ p.support)
        (hmw : ∀ k, w k = 0 → m k = 0) => by
      rw [eval_eq']
      have hpos : 0 < p.coeff m * ∏ t, w t ^ m t := by
        apply mul_pos (lt_of_le_of_ne (hp m) (Ne.symm (MvPolynomial.mem_support_iff.1 hm)))
        apply Finset.prod_pos; intro t _
        by_cases h : w t = 0
        · rw [hmw t h, pow_zero]; norm_num
        · exact pow_pos (lt_of_le_of_ne (hw t) (Ne.symm h)) _
      exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun d => p.coeff d * ∏ t, w t ^ d t)
        (fun d _ => mul_nonneg (hp d) (Finset.prod_nonneg fun t _ => pow_nonneg (hw t) _)) hm)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_eval_zero : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ)
      (h : ∀ m ∈ p.support, ∃ k, w k = 0 ∧ m k ≠ 0), eval w p = 0 :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ)
        (h : ∀ m ∈ p.support, ∃ k, w k = 0 ∧ m k ≠ 0) => by
      rw [eval_eq']
      apply Finset.sum_eq_zero; intro d hd
      obtain ⟨k, hk, hdk⟩ := h d hd
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; exact zero_pow hdk), mul_zero]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_T_pderiv : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) (j : Fin n) (hj : u j = 0)
      (δ : Fin n →₀ ℕ), (∃ m ∈ (pderiv j p).support, ∀ t, u t = 0 → m t = δ t) ↔
        (∃ m ∈ p.support, ∀ t, u t = 0 → m t = (δ + Finsupp.single j 1 : Fin n →₀ ℕ) t) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) (j : Fin n) (hj : u j = 0)
        (δ : Fin n →₀ ℕ) => by
      constructor
      · rintro ⟨m, hm, hmt⟩
        refine ⟨m + Finsupp.single j 1, (LZray_mem_supp_pderiv n p j m).1 hm, fun t ht => ?_⟩
        simp only [Finsupp.coe_add, Pi.add_apply, hmt t ht]
      · rintro ⟨m, hm, hmt⟩
        have hmj : m j = δ j + 1 := by
          have := hmt j hj; simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
          exact this
        have he : m - Finsupp.single j 1 + Finsupp.single j 1 = m := by
          ext t; simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
        refine ⟨m - Finsupp.single j 1, (LZray_mem_supp_pderiv n p j _).2 (by rw [he]; exact hm),
          fun t ht => ?_⟩
        have := hmt t ht
        simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, Finsupp.single_apply] at this ⊢
        split_ifs at this ⊢ <;> omega
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_ray_pderiv : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
      (hR : ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ), (∀ k, 0 ≤ w k) →
        eval w (List.foldr (fun k q => pderiv k q) p l) *
            eval w (pderiv i (pderiv j (List.foldr (fun k q => pderiv k q) p l))) ≤
          2 * (eval w (pderiv i (List.foldr (fun k q => pderiv k q) p l)) *
            eval w (pderiv j (List.foldr (fun k q => pderiv k q) p l)))), ∀ (l : List (Fin n)) (i k : Fin n) (w : Fin n → ℝ), (∀ k, 0 ≤ w k) →
        eval w (List.foldr (fun k q => pderiv k q) (pderiv j p) l) *
            eval w (pderiv i (pderiv k (List.foldr (fun k q => pderiv k q) (pderiv j p) l))) ≤
          2 * (eval w (pderiv i (List.foldr (fun k q => pderiv k q) (pderiv j p) l)) *
            eval w (pderiv k (List.foldr (fun k q => pderiv k q) (pderiv j p) l))) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
        (hR : ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ), (∀ k, 0 ≤ w k) →
          eval w (List.foldr (fun k q => pderiv k q) p l) *
              eval w (pderiv i (pderiv j (List.foldr (fun k q => pderiv k q) p l))) ≤
            2 * (eval w (pderiv i (List.foldr (fun k q => pderiv k q) p l)) *
              eval w (pderiv j (List.foldr (fun k q => pderiv k q) p l)))) => by
      intro l i k w hw
      have := hR (l ++ [j]) i k w hw
      simpa [List.foldr_append] using this
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_scale : ∀ (n : ℕ) (u : Fin n → ℝ) (S : Finset (Fin n)) (ε : ℝ) (d : Fin n →₀ ℕ), ∏ t, (if t ∈ S then ε else u t) ^ d t =
        ε ^ (∑ t ∈ S, d t) * ∏ t, (if t ∈ S then (1:ℝ) else u t) ^ d t :=
    fun (n : ℕ) (u : Fin n → ℝ) (S : Finset (Fin n)) (ε : ℝ) (d : Fin n →₀ ℕ) => by
      have h1 : ∀ t, (if t ∈ S then ε else u t) ^ d t =
          (if t ∈ S then ε ^ d t else 1) * (if t ∈ S then (1:ℝ) else u t) ^ d t := by
        intro t; split_ifs <;> simp
      rw [Finset.prod_congr rfl (fun t _ => h1 t), Finset.prod_mul_distrib, Finset.prod_ite_mem,
        Finset.univ_inter, Finset.prod_pow_eq_pow_sum]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_prod_pos : ∀ (n : ℕ) (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (S : Finset (Fin n))
      (d : Fin n →₀ ℕ) (h : ∀ t, u t = 0 → t ∉ S → d t = 0), 0 < ∏ t, (if t ∈ S then (1:ℝ) else u t) ^ d t :=
    fun (n : ℕ) (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (S : Finset (Fin n))
        (d : Fin n →₀ ℕ) (h : ∀ t, u t = 0 → t ∉ S → d t = 0) => by
      apply Finset.prod_pos; intro t _
      by_cases htS : t ∈ S
      · simp [htS]
      · by_cases hut : u t = 0
        · simp [htS, h t hut htS]
        · rw [if_neg htS]; exact pow_pos (lt_of_le_of_ne (hu t) (Ne.symm hut)) _
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_upper : ∀ (n : ℕ) (q : MvPolynomial (Fin n) ℝ) (hq : ∀ m, 0 ≤ q.coeff m)
      (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (S : Finset (Fin n)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
      (M : ℕ) (hM : ∀ d ∈ q.support, (∀ t, u t = 0 → t ∉ S → d t = 0) → M ≤ ∑ t ∈ S, d t), eval (fun t => if t ∈ S then ε else u t) q ≤
        ε ^ M * eval (fun t => if t ∈ S then (1:ℝ) else u t) q :=
    fun (n : ℕ) (q : MvPolynomial (Fin n) ℝ) (hq : ∀ m, 0 ≤ q.coeff m)
        (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (S : Finset (Fin n)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
        (M : ℕ) (hM : ∀ d ∈ q.support, (∀ t, u t = 0 → t ∉ S → d t = 0) → M ≤ ∑ t ∈ S, d t) => by
      rw [eval_eq', eval_eq', Finset.mul_sum]
      apply Finset.sum_le_sum; intro d hd
      rw [LZray_scale]
      have hP : 0 ≤ ∏ t, (if t ∈ S then (1:ℝ) else u t) ^ d t := by
        apply Finset.prod_nonneg; intro t _; split_ifs
        · simp
        · exact pow_nonneg (hu t) _
      by_cases h : ∀ t, u t = 0 → t ∉ S → d t = 0
      · have he := pow_le_pow_of_le_one hε0 hε1 (hM d hd h)
        have := mul_le_mul_of_nonneg_right he (mul_nonneg (hq d) hP)
        calc q.coeff d * (ε ^ (∑ t ∈ S, d t) * ∏ t, (if t ∈ S then (1:ℝ) else u t) ^ d t)
            = ε ^ (∑ t ∈ S, d t) * (q.coeff d * ∏ t, (if t ∈ S then (1:ℝ) else u t) ^ d t) := by ring
          _ ≤ _ := this
      · push_neg at h
        obtain ⟨t, ht, htS, hdt⟩ := h
        have h0 : ∏ t, (if t ∈ S then (1:ℝ) else u t) ^ d t = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ t) (by simp [htS, ht, zero_pow hdt])
        rw [h0]; simp
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_lower : ∀ (n : ℕ) (q : MvPolynomial (Fin n) ℝ) (hq : ∀ m, 0 ≤ q.coeff m)
      (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (S : Finset (Fin n)) (ε : ℝ) (hε0 : 0 ≤ ε)
      (d : Fin n →₀ ℕ) (hd : d ∈ q.support), ε ^ (∑ t ∈ S, d t) * (q.coeff d * ∏ t, (if t ∈ S then (1:ℝ) else u t) ^ d t) ≤
        eval (fun t => if t ∈ S then ε else u t) q :=
    fun (n : ℕ) (q : MvPolynomial (Fin n) ℝ) (hq : ∀ m, 0 ≤ q.coeff m)
        (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (S : Finset (Fin n)) (ε : ℝ) (hε0 : 0 ≤ ε)
        (d : Fin n →₀ ℕ) (hd : d ∈ q.support) => by
      rw [eval_eq']
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun d => q.coeff d * ∏ t, (if t ∈ S then ε else u t) ^ d t)
        (fun d _ => mul_nonneg (hq d) (Finset.prod_nonneg fun t _ => by
          split_ifs
          · exact pow_nonneg hε0 _
          · exact pow_nonneg (hu t) _)) hd)
      beta_reduce; rw [LZray_scale n u S ε d]; ring
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_asym : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
      (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (S : Finset (Fin n)) (hS : ∀ k ∈ S, u k = 0)
      (N : ℕ) (hN : 2 ≤ N) (k l : Fin n) (hk : k ∈ S) (hl : l ∈ S)
      (h0 : ∃ m ∈ p.support, ∀ t, u t = 0 → m t = 0)
      (hβ : ∃ m ∈ p.support, (∀ t, u t = 0 → t ∉ S → m t = 0) ∧ ∑ t ∈ S, m t = N ∧
        1 ≤ m k ∧ 1 ≤ m l ∧ (k = l → 2 ≤ m k))
      (hgap : ∀ m ∈ p.support, (∀ t, u t = 0 → t ∉ S → m t = 0) →
        ∑ t ∈ S, m t = 0 ∨ N ≤ ∑ t ∈ S, m t), ∃ w : Fin n → ℝ, (∀ t, 0 ≤ w t) ∧
        2 * (eval w (pderiv k p) * eval w (pderiv l p)) < eval w p * eval w (pderiv k (pderiv l p)) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m, 0 ≤ p.coeff m)
        (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (S : Finset (Fin n)) (hS : ∀ k ∈ S, u k = 0)
        (N : ℕ) (hN : 2 ≤ N) (k l : Fin n) (hk : k ∈ S) (hl : l ∈ S)
        (h0 : ∃ m ∈ p.support, ∀ t, u t = 0 → m t = 0)
        (hβ : ∃ m ∈ p.support, (∀ t, u t = 0 → t ∉ S → m t = 0) ∧ ∑ t ∈ S, m t = N ∧
          1 ≤ m k ∧ 1 ≤ m l ∧ (k = l → 2 ≤ m k))
        (hgap : ∀ m ∈ p.support, (∀ t, u t = 0 → t ∉ S → m t = 0) →
          ∑ t ∈ S, m t = 0 ∨ N ≤ ∑ t ∈ S, m t) => by
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
      -- notation
      set w₁ : Fin n → ℝ := fun t => if t ∈ S then (1:ℝ) else u t with hw₁
      -- (1) constant a
      obtain ⟨m0, hm0, hm0u⟩ := h0
      have hm0c : ∀ t, u t = 0 → t ∉ S → m0 t = 0 := fun t ht _ => hm0u t ht
      have hm0S : ∑ t ∈ S, m0 t = 0 := Finset.sum_eq_zero fun t ht => hm0u t (hS t ht)
      set a := p.coeff m0 * ∏ t, (if t ∈ S then (1:ℝ) else u t) ^ m0 t with ha
      have ha0 : 0 < a := mul_pos (lt_of_le_of_ne (hp m0) (Ne.symm (MvPolynomial.mem_support_iff.1 hm0)))
        (LZray_prod_pos n u hu S m0 hm0c)
      -- (2) constant b
      obtain ⟨m, hm, hmc, hmS, hmk, hml, hkl⟩ := hβ
      set m' : Fin n →₀ ℕ := m - Finsupp.single k 1 - Finsupp.single l 1 with hm'
      have hm'eq : m' + Finsupp.single k 1 + Finsupp.single l 1 = m := by
        by_cases hkl' : k = l
        · subst hkl'
          have := hkl rfl
          ext t; simp only [hm', Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
            Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
        · ext t; simp only [hm', Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
            Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
      have hm'supp : m' ∈ (pderiv k (pderiv l p)).support := by
        rw [LZray_mem_supp_pderiv, LZray_mem_supp_pderiv, hm'eq]; exact hm
      have hm'le : ∀ t, m' t ≤ m t := by
        intro t; rw [← hm'eq]; simp only [Finsupp.coe_add, Pi.add_apply]; omega
      have hm'c : ∀ t, u t = 0 → t ∉ S → m' t = 0 := fun t ht htS => by
        have := hm'le t; have := hmc t ht htS; omega
      have hm'S : ∑ t ∈ S, m' t = M := by
        have := congrArg (fun f : Fin n →₀ ℕ => ∑ t ∈ S, f t) hm'eq
        simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
          Finset.sum_ite_eq, hk, hl, if_true] at this
        omega
      have hq : ∀ m, 0 ≤ (pderiv k (pderiv l p)).coeff m :=
        LZray_nn_pderiv n _ k (LZray_nn_pderiv n p l hp)
      set b := (pderiv k (pderiv l p)).coeff m' * ∏ t, (if t ∈ S then (1:ℝ) else u t) ^ m' t with hb
      have hb0 : 0 < b := mul_pos (lt_of_le_of_ne (hq m') (Ne.symm (MvPolynomial.mem_support_iff.1 hm'supp)))
        (LZray_prod_pos n u hu S m' hm'c)
      -- (3) constants C, C'
      have hw₁nn : ∀ t, 0 ≤ w₁ t := fun t => by
        simp only [hw₁]; split_ifs
        · norm_num
        · exact hu t
      set C := eval w₁ (pderiv k p) with hC
      set C' := eval w₁ (pderiv l p) with hC'
      have hC0 : 0 ≤ C := LZray_eval_nonneg n _ (LZray_nn_pderiv n p k hp) w₁ hw₁nn
      have hC'0 : 0 ≤ C' := LZray_eval_nonneg n _ (LZray_nn_pderiv n p l hp) w₁ hw₁nn
      have hgapj : ∀ j ∈ S, ∀ d ∈ (pderiv j p).support, (∀ t, u t = 0 → t ∉ S → d t = 0) →
          M + 1 ≤ ∑ t ∈ S, d t := by
        intro j hj d hd hdc
        have h1 := (LZray_mem_supp_pderiv n p j d).1 hd
        have h2 : ∀ t, u t = 0 → t ∉ S → (d + Finsupp.single j 1 : Fin n →₀ ℕ) t = 0 := by
          intro t ht htS
          have htj : t ≠ j := fun h => htS (h ▸ hj)
          simp [hdc t ht htS, Ne.symm htj]
        have h3 : ∑ t ∈ S, (d + Finsupp.single j 1 : Fin n →₀ ℕ) t = ∑ t ∈ S, d t + 1 := by
          simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
            Finset.sum_ite_eq, hj, if_true]
        have := hgap _ h1 h2
        rw [h3] at this; omega
      -- (4) choose ε
      set D := a * b + 2 * C * C' + 1 with hD
      have hD0 : 0 < D := by positivity
      set ε := a * b / D with hε
      have hε0 : 0 < ε := div_pos (mul_pos ha0 hb0) hD0
      have hε1 : ε ≤ 1 := (div_le_one hD0).2 (by nlinarith [mul_nonneg hC0 hC'0])
      have hεD : ε * D = a * b := div_mul_cancel₀ _ (ne_of_gt hD0)
      have hkey : 2 * C * C' * ε < a * b := by nlinarith [mul_nonneg hC0 hC'0, mul_pos ha0 hb0]
      have hwnn : ∀ t, 0 ≤ (fun t => if t ∈ S then ε else u t) t := fun t => by
        show 0 ≤ if t ∈ S then ε else u t
        split_ifs
        · exact hε0.le
        · exact hu t
      refine ⟨fun t => if t ∈ S then ε else u t, hwnn, ?_⟩
      have hE1 := LZray_upper n (pderiv k p) (LZray_nn_pderiv n p k hp) u hu S ε hε0.le hε1 (M + 1)
        (hgapj k hk)
      have hE2 := LZray_upper n (pderiv l p) (LZray_nn_pderiv n p l hp) u hu S ε hε0.le hε1 (M + 1)
        (hgapj l hl)
      have hE1n := LZray_eval_nonneg n _ (LZray_nn_pderiv n p k hp) _ hwnn
      have hE2n := LZray_eval_nonneg n _ (LZray_nn_pderiv n p l hp) _ hwnn
      have hP := LZray_lower n p hp u hu S ε hε0.le m0 hm0
      rw [hm0S, pow_zero, one_mul] at hP
      have hQ := LZray_lower n _ hq u hu S ε hε0.le m' hm'supp
      rw [hm'S] at hQ
      have hεM : 0 < ε ^ M := pow_pos hε0 M
      have hεM2 : ε ^ (M + 2) ≤ ε := pow_le_of_le_one hε0.le hε1 (by omega)
      calc 2 * (eval (fun t => if t ∈ S then ε else u t) (pderiv k p) *
            eval (fun t => if t ∈ S then ε else u t) (pderiv l p))
          ≤ 2 * ((ε ^ (M + 1) * C) * (ε ^ (M + 1) * C')) := by
            have := mul_le_mul hE1 hE2 hE2n (by positivity)
            linarith
        _ = ε ^ M * (2 * C * C' * ε ^ (M + 2)) := by ring
        _ ≤ ε ^ M * (2 * C * C' * ε) := by
            apply mul_le_mul_of_nonneg_left _ hεM.le
            exact mul_le_mul_of_nonneg_left hεM2 (by positivity)
        _ < ε ^ M * (a * b) := mul_lt_mul_of_pos_left hkey hεM
        _ = a * (ε ^ M * b) := by ring
        _ ≤ _ := mul_le_mul hP hQ (by positivity) (LZray_eval_nonneg n p hp _ hwnn)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_sum_sub_single : ∀ (n : ℕ) (β : Fin n →₀ ℕ) (j : Fin n) (hj : β j ≠ 0), ∑ t, (β - Finsupp.single j 1 : Fin n →₀ ℕ) t + 1 = ∑ t, β t :=
    fun (n : ℕ) (β : Fin n →₀ ℕ) (j : Fin n) (hj : β j ≠ 0) => by
      have e : ∀ t, β t = (β - Finsupp.single j 1 : Fin n →₀ ℕ) t + (if t = j then 1 else 0) := by
        intro t; simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
        split_ifs <;> subst_vars <;> omega
      rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_add_distrib]
      simp
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_int : ∀ (n : ℕ) (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (N : ℕ), ∀ (p : MvPolynomial (Fin n) ℝ), (∀ m, 0 ≤ p.coeff m) →
      (∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ), (∀ k, 0 ≤ w k) →
        eval w (List.foldr (fun k q => pderiv k q) p l) *
            eval w (pderiv i (pderiv j (List.foldr (fun k q => pderiv k q) p l))) ≤
          2 * (eval w (pderiv i (List.foldr (fun k q => pderiv k q) p l)) *
            eval w (pderiv j (List.foldr (fun k q => pderiv k q) p l)))) →
      (∃ m ∈ p.support, ∀ t, u t = 0 → m t = 0) →
      ∀ β : Fin n →₀ ℕ, (∀ t, u t ≠ 0 → β t = 0) → ∑ t, β t = N →
      (∃ m ∈ p.support, ∀ t, u t = 0 → m t = β t) →
      ∀ γ : Fin n →₀ ℕ, γ ≤ β → ∃ m ∈ p.support, ∀ t, u t = 0 → m t = γ t :=
    fun (n : ℕ) (u : Fin n → ℝ) (hu : ∀ k, 0 ≤ u k) (N : ℕ) => by
      induction N using Nat.strong_induction_on with
      | _ N IH =>
      intro p hp hR h0 β hβA hβN hβ γ hγβ
      by_contra hγ
      -- 步骤 a：存在 i ∈ supp γ 使 e_i 不可达
      have stepa : ∃ i, γ i ≠ 0 ∧ ¬ ∃ m ∈ p.support, ∀ t, u t = 0 →
          m t = (Finsupp.single i 1 : Fin n →₀ ℕ) t := by
        by_contra hcon
        push_neg at hcon
        have hγ0 : γ ≠ 0 := by rintro rfl; exact hγ (by simpa using h0)
        obtain ⟨j, hj⟩ : ∃ j, γ j ≠ 0 := by
          by_contra h; push_neg at h; exact hγ0 (Finsupp.ext h)
        have hβj : β j ≠ 0 := by have := hγβ j; omega
        have huj : u j = 0 := by by_contra h; exact hβj (hβA j h)
        have hT0' : ∃ m ∈ (pderiv j p).support, ∀ t, u t = 0 → m t = 0 := by
          have := (LZray_T_pderiv n p u j huj 0).2 (by simpa using hcon j hj)
          simpa using this
        have hTβ' : ∃ m ∈ (pderiv j p).support, ∀ t, u t = 0 →
            m t = (β - Finsupp.single j 1 : Fin n →₀ ℕ) t := by
          rw [LZray_T_pderiv n p u j huj]
          have e : β - Finsupp.single j 1 + Finsupp.single j 1 = β := by
            ext t; simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
              Finsupp.single_apply]
            split_ifs <;> subst_vars <;> omega
          rw [e]; exact hβ
        have hN' := LZray_sum_sub_single n β j hβj
        have key := IH (N - 1) (by omega) (pderiv j p) (LZray_nn_pderiv n p j hp)
          (LZray_ray_pderiv n p j hR) hT0' (β - Finsupp.single j 1)
          (fun t ht => by
            simp only [Finsupp.coe_tsub, Pi.sub_apply, hβA t ht, Nat.zero_sub])
          (by omega) hTβ' (γ - Finsupp.single j 1)
          (fun t => by
            have := hγβ t
            simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega)
        rw [LZray_T_pderiv n p u j huj] at key
        have e : γ - Finsupp.single j 1 + Finsupp.single j 1 = γ := by
          ext t; simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
            Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
        rw [e] at key; exact hγ key
      obtain ⟨i, hγi, hTi⟩ := stepa
      have hβi : β i ≠ 0 := by have := hγβ i; omega
      have hui : u i = 0 := by by_contra h; exact hβi (hβA i h)
      have hpos0 : 0 < eval u p := by
        obtain ⟨m, hm, hmt⟩ := h0
        exact LZray_eval_pos n p hp u hu m hm hmt
      have hevi : eval u (pderiv i p) = 0 := by
        apply LZray_eval_zero
        intro m hm
        by_contra h; push_neg at h
        refine hTi ⟨m + Finsupp.single i 1, (LZray_mem_supp_pderiv n p i m).1 hm, fun t ht => ?_⟩
        simp [h t ht]
      -- 步骤 b：β 支撑上的 e_j 都不可达
      have stepb : ∀ j, β j ≠ 0 → ¬ ∃ m ∈ p.support, ∀ t, u t = 0 →
          m t = (Finsupp.single j 1 : Fin n →₀ ℕ) t := by
        intro j hβj hTj
        by_cases hji : j = i
        · subst hji; exact hTi hTj
        have huj : u j = 0 := by by_contra h; exact hβj (hβA j h)
        have hT0' : ∃ m ∈ (pderiv j p).support, ∀ t, u t = 0 → m t = 0 := by
          have := (LZray_T_pderiv n p u j huj 0).2 (by simpa using hTj)
          simpa using this
        have hTβ' : ∃ m ∈ (pderiv j p).support, ∀ t, u t = 0 →
            m t = (β - Finsupp.single j 1 : Fin n →₀ ℕ) t := by
          rw [LZray_T_pderiv n p u j huj]
          have e : β - Finsupp.single j 1 + Finsupp.single j 1 = β := by
            ext t; simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
              Finsupp.single_apply]
            split_ifs <;> subst_vars <;> omega
          rw [e]; exact hβ
        have hN' := LZray_sum_sub_single n β j hβj
        have key := IH (N - 1) (by omega) (pderiv j p) (LZray_nn_pderiv n p j hp)
          (LZray_ray_pderiv n p j hR) hT0' (β - Finsupp.single j 1)
          (fun t ht => by
            simp only [Finsupp.coe_tsub, Pi.sub_apply, hβA t ht, Nat.zero_sub])
          (by omega) hTβ' (Finsupp.single i 1)
          (fun t => by
            simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
            split_ifs <;> subst_vars <;> omega)
        have hT2 : ∃ m ∈ (pderiv i (pderiv j p)).support, ∀ t, u t = 0 → m t = 0 := by
          have := (LZray_T_pderiv n (pderiv j p) u i hui 0).2 (by simpa using key)
          simpa using this
        obtain ⟨m2, hm2, hm2t⟩ := hT2
        have hpos2 : 0 < eval u (pderiv i (pderiv j p)) :=
          LZray_eval_pos n _ (LZray_nn_pderiv n _ i (LZray_nn_pderiv n p j hp)) u hu m2 hm2 hm2t
        have hRu := hR [] i j u hu
        simp only [List.foldr_nil, hevi, zero_mul, mul_zero] at hRu
        have := mul_pos hpos0 hpos2
        linarith
      -- 步骤 c：β 支撑内的非零可达点次数 ≥ N
      have stepc : ∀ δ : Fin n →₀ ℕ, (∀ t, δ t ≠ 0 → β t ≠ 0) →
          (∃ m ∈ p.support, ∀ t, u t = 0 → m t = δ t) → δ = 0 ∨ N ≤ ∑ t, δ t := by
        intro δ hδ hTδ
        by_contra h; push_neg at h
        obtain ⟨hδ0, hlt⟩ := h
        obtain ⟨j, hj⟩ : ∃ j, δ j ≠ 0 := by
          by_contra h; push_neg at h; exact hδ0 (Finsupp.ext h)
        have key := IH (∑ t, δ t) hlt p hp hR h0 δ
          (fun t ht => by by_contra h'; exact hδ t h' (hβA t ht)) rfl hTδ (Finsupp.single j 1)
          (fun t => by
            simp only [Finsupp.single_apply]
            split_ifs <;> subst_vars <;> omega)
        exact stepb j (hδ j hj) key
      -- 步骤 d：渐近矛盾
      obtain ⟨l, hβl, hli⟩ : ∃ l, β l ≠ 0 ∧ (i = l → 2 ≤ β i) := by
        by_cases h2 : 2 ≤ β i
        · exact ⟨i, hβi, fun _ => h2⟩
        by_contra hcon; push_neg at hcon
        have hβe : β = Finsupp.single i 1 := by
          ext t
          simp only [Finsupp.single_apply]
          split_ifs with h
          · subst h; omega
          · by_contra h'
            have := hcon t h'
            exact h (this.1.symm ▸ rfl)
        exact hTi (hβe ▸ hβ)
      have hN2 : 2 ≤ N := by
        rw [← hβN]
        by_cases hil : i = l
        · have := hli hil
          have : β i ≤ ∑ t, β t := Finset.single_le_sum (fun t _ => Nat.zero_le _) (Finset.mem_univ i)
          omega
        · have : ∑ t ∈ {i, l}, β t ≤ ∑ t, β t :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          rw [Finset.sum_pair hil] at this
          omega
      obtain ⟨mβ, hmβ, hmβt⟩ := hβ
      let S : Finset (Fin n) := Finset.univ.filter (fun t => β t ≠ 0)
      have hS : ∀ t ∈ S, u t = 0 := by
        intro t ht
        have : β t ≠ 0 := (Finset.mem_filter.1 ht).2
        by_contra h; exact this (hβA t h)
      have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hβi⟩
      have hlS : l ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hβl⟩
      have hsumS : ∀ m : Fin n →₀ ℕ, (∀ t, u t = 0 → t ∉ S → m t = 0) →
          ∑ t ∈ S, m t = ∑ t, (fun t => if u t = 0 then m t else 0) t := by
        intro m hm
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        · apply Finset.sum_congr rfl
          intro t ht; simp [hS t ht]
        · intro t _ htS
          by_cases h : u t = 0
          · simp [h, hm t h htS]
          · simp [h]
      obtain ⟨w, hw, hlt⟩ := LZray_asym n p hp u hu S hS N hN2 i l hiS hlS h0
        ⟨mβ, hmβ, ⟨fun t ht htS => by
            rw [hmβt t ht]
            by_contra h; exact htS (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩),
          by
            rw [Finset.sum_congr rfl (fun t ht => hmβt t (hS t ht))]
            rw [← hβN]
            exact Finset.sum_filter_ne_zero _,
          by rw [hmβt i hui]; omega,
          by rw [hmβt l (hS l hlS)]; omega,
          fun h => by rw [hmβt i hui]; exact hli h⟩⟩
        (fun m hm hmS => by
          let δ : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun t => if u t = 0 then m t else 0)
          have hδ : ∀ t, δ t = if u t = 0 then m t else 0 := fun t => rfl
          have hc := stepc δ
            (fun t ht => by
              rw [hδ] at ht
              split_ifs at ht with h
              · by_contra h'
                exact ht (hmS t h (fun htS => (Finset.mem_filter.1 htS).2 h'))
              · exact absurd rfl ht)
            ⟨m, hm, fun t ht => by rw [hδ, if_pos ht]⟩
          rw [hsumS m hmS]
          rcases hc with hc | hc
          · left
            apply Finset.sum_eq_zero
            intro t _
            have := congrArg (fun f => f t) hc
            simp only [hδ, Finsupp.coe_zero, Pi.zero_apply] at this
            exact this
          · right
            simpa [hδ] using hc)
      have hRw := hR [] i l w hw
      simp only [List.foldr_nil] at hRw
      linarith
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray_deg : ∀ (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d)
      (m : Fin n →₀ ℕ) (hm : m ∈ p.support), ∑ t, m t = d :=
    fun (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d)
        (m : Fin n →₀ ℕ) (hm : m ∈ p.support) => by
      have := hp (MvPolynomial.mem_support_iff.1 hm)
      rw [← this]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZray : ∀ (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d)
      (hnn : ∀ m, 0 ≤ p.coeff m)
      (hR : ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ), (∀ k, 0 ≤ w k) →
        eval w (List.foldr (fun k q => pderiv k q) p l) *
            eval w (pderiv i (pderiv j (List.foldr (fun k q => pderiv k q) p l))) ≤
          2 * (eval w (pderiv i (List.foldr (fun k q => pderiv k q) p l)) *
            eval w (pderiv j (List.foldr (fun k q => pderiv k q) p l)))), IsMConvex (p.support : Set (Fin n →₀ ℕ)) :=
    fun (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d)
        (hnn : ∀ m, 0 ≤ p.coeff m)
        (hR : ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ), (∀ k, 0 ≤ w k) →
          eval w (List.foldr (fun k q => pderiv k q) p l) *
              eval w (pderiv i (pderiv j (List.foldr (fun k q => pderiv k q) p l))) ≤
            2 * (eval w (pderiv i (List.foldr (fun k q => pderiv k q) p l)) *
              eval w (pderiv j (List.foldr (fun k q => pderiv k q) p l)))) => by
      induction d using Nat.strong_induction_on generalizing p with
      | _ d IH =>
      intro α hα β hβ i hi
      rw [Finset.mem_coe] at hα hβ
      by_cases hcom : ∃ k, α k ≠ 0 ∧ β k ≠ 0
      · -- 公共变量：沿 ∂_k 收缩
        obtain ⟨k, hαk, hβk⟩ := hcom
        have hd : 1 ≤ d := by
          have h1 := LZray_deg n d p hp α hα
          have h2 : α k ≤ ∑ t, α t := Finset.single_le_sum (fun t _ => Nat.zero_le _) (Finset.mem_univ k)
          rw [h1] at h2
          omega
        have IHk := IH (d - 1) (by omega) (pderiv k p) hp.pderiv (LZray_nn_pderiv n p k hnn)
          (LZray_ray_pderiv n p k hR)
        have eα : α - Finsupp.single k 1 + Finsupp.single k 1 = α := by
          ext t; simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
            Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
        have eβ : β - Finsupp.single k 1 + Finsupp.single k 1 = β := by
          ext t; simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
            Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
        have hα' : α - Finsupp.single k 1 ∈ ((pderiv k p).support : Set (Fin n →₀ ℕ)) := by
          rw [Finset.mem_coe, LZray_mem_supp_pderiv, eα]; exact hα
        have hβ' : β - Finsupp.single k 1 ∈ ((pderiv k p).support : Set (Fin n →₀ ℕ)) := by
          rw [Finset.mem_coe, LZray_mem_supp_pderiv, eβ]; exact hβ
        have hi' : (α - Finsupp.single k 1 : Fin n →₀ ℕ) i > (β - Finsupp.single k 1 : Fin n →₀ ℕ) i := by
          simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
          split_ifs <;> subst_vars <;> omega
        obtain ⟨j, hj1, hj2⟩ := IHk _ hα' _ hβ' i hi'
        refine ⟨j, ?_, ?_⟩
        · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply] at hj1
          split_ifs at hj1 <;> subst_vars <;> omega
        · rw [Finset.mem_coe, LZray_mem_supp_pderiv] at hj2
          have e : α - Finsupp.single k 1 - Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1
              = α - Finsupp.single i 1 + Finsupp.single j 1 := by
            ext t; simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
              Finsupp.single_apply]
            split_ifs <;> subst_vars <;> omega
          rw [Finset.mem_coe, ← e]; exact hj2
      · -- 支撑不交：冻结 β 的变量为 1，用区间凸性
        push_neg at hcom
        let u : Fin n → ℝ := fun t => if β t ≠ 0 then 1 else 0
        have hu : ∀ k, 0 ≤ u k := fun k => by simp only [u]; split_ifs <;> norm_num
        have hu0 : ∀ t, u t = 0 ↔ β t = 0 := fun t => by
          simp only [u]; split_ifs with h
          · simp [h]
          · push_neg at h; simp [h]
        have hβi : β i = 0 := by
          by_contra h; exact h (hcom i (by omega))
        obtain ⟨m, hm, hmt⟩ := LZray_int n u hu (∑ t, α t) p hnn hR
          ⟨β, hβ, fun t ht => (hu0 t).1 ht⟩ α
          (fun t ht => by
            by_contra h; exact ht ((hu0 t).2 (hcom t h)))
          rfl ⟨α, hα, fun t _ => rfl⟩ (α - Finsupp.single i 1)
          (fun t => by simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega)
        have hmt' : ∀ t, β t = 0 → m t = (α - Finsupp.single i 1 : Fin n →₀ ℕ) t :=
          fun t ht => hmt t ((hu0 t).2 ht)
        let F : Finset (Fin n) := Finset.univ.filter (fun t => β t ≠ 0)
        have hsplit : ∀ t, m t = (α - Finsupp.single i 1 : Fin n →₀ ℕ) t +
            (if β t ≠ 0 then m t else 0) := by
          intro t
          by_cases h : β t = 0
          · rw [hmt' t h]; simp [h]
          · have hαt : α t = 0 := by by_contra h'; exact h (hcom t h')
            have hti : t ≠ i := by rintro rfl; exact h hβi
            simp [h, hαt, Finsupp.single_apply, Ne.symm hti]
        have hsumF : ∑ t ∈ F, m t = 1 := by
          have h1 := LZray_deg n d p hp m hm
          have h2 := LZray_deg n d p hp α hα
          have h3 := LZray_sum_sub_single n α i (by omega)
          rw [Finset.sum_congr rfl (fun t _ => hsplit t), Finset.sum_add_distrib,
            ← Finset.sum_filter] at h1
          show ∑ t ∈ Finset.univ.filter (fun t => β t ≠ 0), m t = 1
          omega
        obtain ⟨j, hjF, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsumF]; norm_num :
          ∑ t ∈ F, m t ≠ 0)
        have hβj : β j ≠ 0 := (Finset.mem_filter.1 hjF).2
        have hother : ∀ t ∈ F, t ≠ j → m t = 0 := by
          intro t ht htj
          have : ∑ x ∈ {t, j}, m x ≤ ∑ x ∈ F, m x :=
            Finset.sum_le_sum_of_subset (by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption)
          rw [Finset.sum_pair htj] at this
          omega
        have hmj : m j = 1 := by
          have : m j ≤ ∑ x ∈ F, m x := Finset.single_le_sum (fun t _ => Nat.zero_le _) hjF
          omega
        refine ⟨j, ?_, ?_⟩
        · have : α j = 0 := by by_contra h'; exact hβj (hcom j h')
          omega
        · have e : m = α - Finsupp.single i 1 + Finsupp.single j 1 := by
            ext t
            by_cases h : β t = 0
            · have htj : t ≠ j := by rintro rfl; exact hβj h
              rw [hmt' t h]; simp [Finsupp.single_apply, Ne.symm htj]
            · have hαt : α t = 0 := by by_contra h'; exact h (hcom t h')
              have hti : t ≠ i := by rintro rfl; exact h hβi
              have htF : t ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
              by_cases htj : t = j
              · subst htj; simp [hαt, hmj]
              · rw [hother t htF htj]; simp [hαt, Finsupp.single_apply, Ne.symm hti, Ne.symm htj]
          rw [Finset.mem_coe, ← e]; exact hm
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZmconv_aux_P : ∀ (n d : ℕ) (g : H n d) (hg : g ∈ Ŀ n d), g ∈ P n d :=
    fun (n d : ℕ) (g : H n d) (hg : g ∈ Ŀ n d) => by
      rcases d with _ | _ | _ | d
      · exact hg
      · exact hg
      · exact hg.1
      · exact hg.1
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZmconv_aux_nn : ∀ (n d : ℕ) (g : H n d) (hg : g ∈ Ŀ n d) (m : Fin n →₀ ℕ), 0 ≤ g.1.coeff m :=
    fun (n d : ℕ) (g : H n d) (hg : g ∈ Ŀ n d) (m : Fin n →₀ ℕ) => by
      have hP := LZmconv_aux_P n d g hg
      by_cases h : weight 1 m = d
      · exact (hP m h).le
      · have hh := (mem_homogeneousSubmodule _ _).mp g.2
        by_contra hne
        exact h (hh (by intro h0; apply hne; rw [h0]))
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZmconv_aux_lin : ∀ (n : ℕ) (l : List (Fin n)), ∃ φ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ,
        ∀ p, φ p = List.foldr (fun k q => pderiv k q) p l :=
    fun (n : ℕ) (l : List (Fin n)) => by
      induction l with
      | nil => exact ⟨LinearMap.id, fun p => rfl⟩
      | cons a l ih =>
        obtain ⟨φ, hφ⟩ := ih
        exact ⟨(pderiv a).toLinearMap ∘ₗ φ, fun p => by rw [List.foldr_cons, ← hφ]; rfl⟩
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZmconv_aux_cont : ∀ (n d : ℕ) (l : List (Fin n))
      (ψ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ), Continuous (fun g : H n d => eval w (ψ (List.foldr (fun k q => pderiv k q) g.1 l))) :=
    fun (n d : ℕ) (l : List (Fin n))
        (ψ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) => by
      obtain ⟨φ, hφ⟩ := LZmconv_aux_lin n l
      have h1 := LZtop_lin n d ((aeval w).toLinearMap ∘ₗ ψ ∘ₗ φ)
      have h2 : ∀ g : H n d, eval w (ψ (List.foldr (fun k q => pderiv k q) g.1 l)) =
          ((aeval w).toLinearMap ∘ₗ ψ ∘ₗ φ) g.1 := fun g => by
        simp only [LinearMap.comp_apply, hφ]
        rfl
      rw [show (fun g : H n d => eval w (ψ (List.foldr (fun k q => pderiv k q) g.1 l))) =
          fun g => ((aeval w).toLinearMap ∘ₗ ψ ∘ₗ φ) g.1 from funext h2]
      exact h1
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZmconv : ∀ (n d : ℕ) (f : H n d) (hf : f ∈ closure (Ŀ n d)), IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) :=
    fun (n d : ℕ) (f : H n d) (hf : f ∈ closure (Ŀ n d)) => by
      apply LZray n d f.1 ((mem_homogeneousSubmodule _ _).mp f.2)
      · intro m
        have hcl : IsClosed {g : H n d | 0 ≤ g.1.coeff m} :=
          isClosed_le continuous_const (LZtop_lin n d (MvPolynomial.lcoeff ℝ m))
        exact closure_minimal (fun g hg => LZmconv_aux_nn n d g hg m) hcl hf
      · intro l i j w hw
        have hcl : IsClosed {g : H n d | eval w (List.foldr (fun k q => pderiv k q) g.1 l) *
              eval w (pderiv i (pderiv j (List.foldr (fun k q => pderiv k q) g.1 l))) ≤
            2 * (eval w (pderiv i (List.foldr (fun k q => pderiv k q) g.1 l)) *
              eval w (pderiv j (List.foldr (fun k q => pderiv k q) g.1 l)))} :=
          isClosed_le ((LZmconv_aux_cont n d l LinearMap.id w).mul
              (LZmconv_aux_cont n d l ((pderiv i).toLinearMap ∘ₗ (pderiv j).toLinearMap) w))
            (continuous_const.mul ((LZmconv_aux_cont n d l (pderiv i).toLinearMap w).mul
              (LZmconv_aux_cont n d l (pderiv j).toLinearMap w)))
        exact closure_minimal (fun g hg => LZhr n d g hg l i j w hw) hcl hf
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZsubst : ∀ (n d : ℕ) (f : H n d) (hf : f ∈ L n d) (A : Matrix (Fin n) (Fin n) ℝ)
      (hA : ∀ i j, 0 < A i j), ∃ g : H n d, g.1 = aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) f.1 ∧
        g ∈ L n d :=
    fun (n d : ℕ) (f : H n d) (hf : f ∈ L n d) (A : Matrix (Fin n) (Fin n) ℝ)
        (hA : ∀ i j, 0 < A i j) => by
      have LZsubst_aux_mul : ∀ (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (i : Fin n) (q : MvPolynomial (Fin n) ℝ) (hq0 : ∀ m, 0 ≤ q.coeff m) (hq : ∀ m : Fin n →₀ ℕ, weight 1 m = k → 0 < q.coeff m), (∀ m, 0 ≤ ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) * q).coeff m) ∧ (∀ m : Fin n →₀ ℕ, weight 1 m = k + 1 → 0 < ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) * q).coeff m) := by
        intro n k A hA i q hq0 hq
        have e : ∀ m, ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) * q).coeff m =
            ∑ j, A i j * (if j ∈ m.support then q.coeff (m - Finsupp.single j 1) else 0) := by
          intro m
          simp only [Finset.sum_mul, coeff_sum, smul_mul_assoc, coeff_smul, coeff_X_mul', smul_eq_mul]
        refine ⟨fun m => ?_, fun m hm => ?_⟩
        · rw [e]
          apply Finset.sum_nonneg
          intro j _
          apply mul_nonneg (hA i j).le
          split_ifs
          · exact hq0 _
          · exact le_rfl
        · rw [e]
          have hm0 : m ≠ 0 := by
            rintro rfl; simp at hm
          obtain ⟨j, hj⟩ : ∃ j, j ∈ m.support := by
            by_contra h
            push_neg at h
            exact hm0 (Finsupp.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
          apply Finset.sum_pos'
          · intro j _
            apply mul_nonneg (hA i j).le
            split_ifs
            · exact hq0 _
            · exact le_rfl
          · refine ⟨j, Finset.mem_univ _, ?_⟩
            rw [if_pos hj]
            apply mul_pos (hA i j)
            apply hq
            have hle : Finsupp.single j 1 ≤ m := by
              intro x
              rw [Finsupp.single_apply]
              split_ifs with h
              · subst h; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)
              · exact Nat.zero_le _
            have := congrArg (weight (1 : Fin n → ℕ)) (tsub_add_cancel_of_le hle)
            rw [map_add, hm] at this
            have hs : weight (1 : Fin n → ℕ) (Finsupp.single j 1) = 1 := by
              rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]; simp
            rw [hs] at this
            omega
      have LZsubst_aux_powmul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (i : Fin n) (b : ℕ), ∀ (k : ℕ) (q : MvPolynomial (Fin n) ℝ), (∀ m, 0 ≤ q.coeff m) → (∀ m : Fin n →₀ ℕ, weight 1 m = k → 0 < q.coeff m) → (∀ m, 0 ≤ ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) ^ b * q).coeff m) ∧ (∀ m : Fin n →₀ ℕ, weight 1 m = b + k → 0 < ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) ^ b * q).coeff m) := by
        intro n A hA i b
        induction b with
        | zero => intro k q h0 h; simpa using ⟨h0, h⟩
        | succ b ih =>
          intro k q h0 h
          obtain ⟨h1, h2⟩ := ih k q h0 h
          have := LZsubst_aux_mul n (b + k) A hA i _ h1 h2
          rw [pow_succ', mul_assoc]
          refine ⟨this.1, fun m hm => this.2 m (by rw [hm]; ring)⟩
      have LZsubst_aux_prod : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (α : Fin n →₀ ℕ), (∀ m, 0 ≤ (α.prod (fun i k => (∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) ^ k)).coeff m) ∧ (∀ m : Fin n →₀ ℕ, weight (1 : Fin n → ℕ) m = weight (1 : Fin n → ℕ) α → 0 < (α.prod (fun i k => (∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) ^ k)).coeff m) := by
        intro n A hA α
        induction α using Finsupp.induction with
        | zero =>
          simp only [Finsupp.prod_zero_index, map_zero]
          refine ⟨fun m => ?_, fun m hm => ?_⟩
          · rw [coeff_one]; split_ifs <;> norm_num
          · have : m = 0 := by
              rw [← Finsupp.degree_eq_zero_iff, Finsupp.degree_eq_weight_one]
              exact hm
            subst this; simp
        | single_add a b f ha hb ih =>
          rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
            Finsupp.prod_single_index (by simp)]
          have := LZsubst_aux_powmul n A hA a b _ _ ih.1 ih.2
          refine ⟨this.1, fun m hm => this.2 m ?_⟩
          rw [hm, map_add]
          congr 1
          rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]; simp
      have LZsubst_aux_pos : ∀ (n d : ℕ) (f : H n d) (hf0 : f.1 ≠ 0) (hfn : ∀ m, 0 ≤ f.1.coeff m) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (m : Fin n →₀ ℕ) (hm : weight 1 m = d), 0 < (aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) f.1).coeff m := by
        intro n d f hf0 hfn A hA m hm
        have hhom : f.1.IsHomogeneous d := f.2
        conv => rhs; rw [f.1.as_sum]
        simp only [map_sum, aeval_monomial, coeff_sum, algebraMap_eq, coeff_C_mul]
        obtain ⟨α, hα⟩ := Finsupp.support_nonempty_iff.2 hf0
        apply Finset.sum_pos'
        · intro β _
          exact mul_nonneg (hfn β) ((LZsubst_aux_prod n A hA β).1 m)
        · refine ⟨α, hα, mul_pos ?_ ((LZsubst_aux_prod n A hA α).2 m ?_)⟩
          · exact lt_of_le_of_ne (hfn α) (Ne.symm (Finsupp.mem_support_iff.1 hα))
          · rw [hm, hhom (Finsupp.mem_support_iff.1 hα)]
      have LZsubst_aux_nn : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (p : MvPolynomial (Fin n) ℝ) (hfn : ∀ m, 0 ≤ p.coeff m) (m : Fin n →₀ ℕ), 0 ≤ (aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) p).coeff m := by
        intro n A hA p hfn m
        conv => rhs; rw [p.as_sum]
        simp only [map_sum, aeval_monomial, coeff_sum, algebraMap_eq, coeff_C_mul]
        exact Finset.sum_nonneg fun β _ => mul_nonneg (hfn β) ((LZsubst_aux_prod n A hA β).1 m)
      have LZsubst_aux_homog : ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ) (hp : p ∈ homogeneousSubmodule (Fin n) ℝ d), aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) p ∈ homogeneousSubmodule (Fin n) ℝ d := by
        intro n d A p hp
        rw [mem_homogeneousSubmodule] at hp ⊢
        have := hp.aeval (n := 1) (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) (fun i => by
          apply IsHomogeneous.sum; intro j _
          rw [smul_eq_C_mul]
          simpa using (isHomogeneous_C (Fin n) (A i j)).mul (isHomogeneous_X ℝ j))
        simpa using this
      have LZsubst_aux_chain : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (p : MvPolynomial (Fin n) ℝ), pderiv k (aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) p) = aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) (∑ i, A i k • pderiv i p) := by
        intro n A k p
        have hl : ∀ i, pderiv k (∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) = C (A i k) := by
          intro i
          simp [map_sum, pderiv_X, Pi.single_apply, smul_eq_C_mul]
        induction p using MvPolynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
        | mul_X p i hp =>
          rw [map_mul, aeval_X, Derivation.leibniz, hl, hp]
          simp only [Derivation.leibniz, pderiv_X, smul_add, Finset.sum_add_distrib, map_add, map_sum,
            map_smul, smul_eq_mul, map_mul, aeval_X, Pi.single_apply]
          congr 1
          · simp only [apply_ite, map_one, map_zero, mul_one, mul_zero, smul_zero,
              Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_eq_C_mul]
            ring
          · rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => mul_smul_comm _ _ _
      have LZsubst_aux_stab : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (p : MvPolynomial (Fin n) ℝ) (hp : IsStable p), IsStable (aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) p) := by
        intro n A hA p hp
        rcases hp with h | h
        · left; simp [h]
        · right; intro z
          have hw : ∀ i, 0 < (∑ j, (A i j : ℂ) * ((z j : ℍ) : ℂ)).im := by
            intro i
            rw [Complex.im_sum]
            apply Finset.sum_pos _ ⟨i, Finset.mem_univ _⟩
            intro j _
            simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
            exact mul_pos (hA i j) (z j).im_pos
          let w : Fin n → ℍ := fun i => ⟨∑ j, (A i j : ℂ) * ((z j : ℍ) : ℂ), hw i⟩
          have key := congrArg (fun φ => φ p)
            (comp_aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ))
              (aeval (R := ℝ) (((↑) : ℍ → ℂ) ∘ z)))
          simp only [AlgHom.comp_apply] at key
          rw [key]
          convert h w using 2
          congr 1
          funext i
          simp [w, map_sum, aeval_X, Complex.real_smul]
      have LZsubst_aux_wsingle : ∀ (n : ℕ) (j : Fin n), weight (1 : Fin n → ℕ) (Finsupp.single j 1) = 1 := by
        intro n j
        rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]; simp
      have LZsubst_aux_mconv : ∀ (n d : ℕ) (q : MvPolynomial (Fin n) ℝ) (hq : q.IsHomogeneous d) (hpos : ∀ m : Fin n →₀ ℕ, weight 1 m = d → 0 < q.coeff m), IsMConvex (q.support : Set (Fin n →₀ ℕ)) := by
        intro n d q hq hpos α hα β hβ i hi
        have hαd : weight 1 α = d := hq (Finsupp.mem_support_iff.1 hα)
        have hβd : weight 1 β = d := hq (Finsupp.mem_support_iff.1 hβ)
        obtain ⟨j, hj⟩ : ∃ j, α j < β j := by
          by_contra hc
          push_neg at hc
          have hle : β ≤ α := fun x => hc x
          have e := congrArg (weight (1 : Fin n → ℕ)) (tsub_add_cancel_of_le hle)
          rw [map_add, hαd, hβd] at e
          have h0 : weight (1 : Fin n → ℕ) (α - β) = 0 := by omega
          have h1 : α - β = 0 := by
            rw [← Finsupp.degree_eq_zero_iff, Finsupp.degree_eq_weight_one]; exact h0
          have := congrArg (fun m => m i) h1
          simp only [Finsupp.tsub_apply, Finsupp.coe_zero, Pi.zero_apply] at this
          omega
        refine ⟨j, hj, ?_⟩
        have hle : Finsupp.single i 1 ≤ α := by
          intro x
          rw [Finsupp.single_apply]
          split_ifs with h
          · subst h; omega
          · exact Nat.zero_le _
        have e := congrArg (weight (1 : Fin n → ℕ)) (tsub_add_cancel_of_le hle)
        rw [map_add, hαd, LZsubst_aux_wsingle] at e
        rw [Finset.mem_coe, MvPolynomial.mem_support_iff]
        apply ne_of_gt
        apply hpos
        rw [map_add, LZsubst_aux_wsingle]
        omega
      have LZsubst_aux_S : ∀ (n d : ℕ) (f : H n d) (hf : f ∈ S n d) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j), ∃ g : H n d, g.1 = aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) f.1 ∧ g ∈ S n d := by
        intro n d f hf A hA
        exact ⟨⟨_, LZsubst_aux_homog n d A f.1 f.2⟩, rfl, LZsubst_aux_stab n A hA f.1 hf.1,
          LZsubst_aux_nn n A hA f.1 hf.2⟩
      have LZsubst_aux_ind : ∀ (n e : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j), ∀ f : H n (e + 3), f ∈ L n (e + 3) → ∃ g : H n (e + 3), g.1 = aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) f.1 ∧ g ∈ L n (e + 3) := by
        intro n e A hA
        induction e with
        | zero =>
          intro f hf
          have hM : f ∈ M n 3 := hf.1
          let g : H n 3 := ⟨_, LZsubst_aux_homog n 3 A f.1 f.2⟩
          refine ⟨g, rfl, ⟨⟨?_, LZsubst_aux_nn n A hA f.1 hM.2⟩, fun k => ?_⟩⟩
          · by_cases hf0 : f.1 = 0
            · show IsMConvex ((aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) f.1).support :
                Set (Fin n →₀ ℕ))
              rw [hf0, map_zero, MvPolynomial.support_zero]
              intro α hα; simp at hα
            · exact LZsubst_aux_mconv n 3 g.1 g.2
                (fun m hm => LZsubst_aux_pos n 3 f hf0 hM.2 A hA m hm)
          · obtain ⟨h, hh1, hh2⟩ := LZdl n 0 f hf (fun i => A i k) (fun i => (hA i k).le)
            obtain ⟨h', hh'1, hh'2⟩ := LZsubst_aux_S n 2 h hh2 A hA
            have : (⟨g.1.pderiv k, g.2.pderiv⟩ : H n 2) = h' := by
              apply Subtype.ext
              show pderiv k (aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) f.1) = h'.1
              rw [hh'1, hh1, LZsubst_aux_chain]
            rw [this]; exact hh'2
        | succ e ih =>
          intro f hf
          have hM : f ∈ M n (e + 4) := hf.1
          let g : H n (e + 4) := ⟨_, LZsubst_aux_homog n (e + 4) A f.1 f.2⟩
          refine ⟨g, rfl, ⟨⟨?_, LZsubst_aux_nn n A hA f.1 hM.2⟩, fun k => ?_⟩⟩
          · by_cases hf0 : f.1 = 0
            · show IsMConvex ((aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) f.1).support :
                Set (Fin n →₀ ℕ))
              rw [hf0, map_zero, MvPolynomial.support_zero]
              intro α hα; simp at hα
            · exact LZsubst_aux_mconv n (e + 4) g.1 g.2
                (fun m hm => LZsubst_aux_pos n (e + 4) f hf0 hM.2 A hA m hm)
          · obtain ⟨h, hh1, hh2⟩ := LZdl n (e + 1) f hf (fun i => A i k) (fun i => (hA i k).le)
            obtain ⟨h', hh'1, hh'2⟩ := ih h hh2
            have : (⟨g.1.pderiv k, g.2.pderiv⟩ : H n (e + 3)) = h' := by
              apply Subtype.ext
              show pderiv k (aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) f.1) = h'.1
              rw [hh'1, hh1, LZsubst_aux_chain]
            rw [this]; exact hh'2
      match d, f, hf with
      | 0, f, hf => exact LZsubst_aux_S n 0 f hf A hA
      | 1, f, hf => exact LZsubst_aux_S n 1 f hf A hA
      | 2, f, hf => exact LZsubst_aux_S n 2 f hf A hA
      | e + 3, f, hf => exact LZsubst_aux_ind n e A hA f hf
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos_aux_mul : ∀ (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
      (i : Fin n) (q : MvPolynomial (Fin n) ℝ) (hq0 : ∀ m, 0 ≤ q.coeff m)
      (hq : ∀ m : Fin n →₀ ℕ, weight 1 m = k → 0 < q.coeff m), (∀ m, 0 ≤ ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) * q).coeff m) ∧
      (∀ m : Fin n →₀ ℕ, weight 1 m = k + 1 →
        0 < ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) * q).coeff m) :=
    fun (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
        (i : Fin n) (q : MvPolynomial (Fin n) ℝ) (hq0 : ∀ m, 0 ≤ q.coeff m)
        (hq : ∀ m : Fin n →₀ ℕ, weight 1 m = k → 0 < q.coeff m) => by
      have e : ∀ m, ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) * q).coeff m =
          ∑ j, A i j * (if j ∈ m.support then q.coeff (m - Finsupp.single j 1) else 0) := by
        intro m
        simp only [Finset.sum_mul, coeff_sum, smul_mul_assoc, coeff_smul, coeff_X_mul', smul_eq_mul]
      refine ⟨fun m => ?_, fun m hm => ?_⟩
      · rw [e]
        apply Finset.sum_nonneg
        intro j _
        apply mul_nonneg (hA i j).le
        split_ifs
        · exact hq0 _
        · exact le_rfl
      · rw [e]
        have hm0 : m ≠ 0 := by
          rintro rfl; simp at hm
        obtain ⟨j, hj⟩ : ∃ j, j ∈ m.support := by
          by_contra h
          push_neg at h
          exact hm0 (Finsupp.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
        apply Finset.sum_pos'
        · intro j _
          apply mul_nonneg (hA i j).le
          split_ifs
          · exact hq0 _
          · exact le_rfl
        · refine ⟨j, Finset.mem_univ _, ?_⟩
          rw [if_pos hj]
          apply mul_pos (hA i j)
          apply hq
          have hle : Finsupp.single j 1 ≤ m := by
            intro x
            rw [Finsupp.single_apply]
            split_ifs with h
            · subst h; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)
            · exact Nat.zero_le _
          have := congrArg (weight (1 : Fin n → ℕ)) (tsub_add_cancel_of_le hle)
          rw [map_add, hm] at this
          have hs : weight (1 : Fin n → ℕ) (Finsupp.single j 1) = 1 := by
            rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]; simp
          rw [hs] at this
          omega
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos_aux_powmul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
      (i : Fin n) (b : ℕ), ∀ (k : ℕ) (q : MvPolynomial (Fin n) ℝ), (∀ m, 0 ≤ q.coeff m) →
      (∀ m : Fin n →₀ ℕ, weight 1 m = k → 0 < q.coeff m) →
      (∀ m, 0 ≤ ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) ^ b * q).coeff m) ∧
      (∀ m : Fin n →₀ ℕ, weight 1 m = b + k →
        0 < ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) ^ b * q).coeff m) :=
    fun (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
        (i : Fin n) (b : ℕ) => by
      induction b with
      | zero => intro k q h0 h; simpa using ⟨h0, h⟩
      | succ b ih =>
        intro k q h0 h
        obtain ⟨h1, h2⟩ := ih k q h0 h
        have := LZpos_aux_mul n (b + k) A hA i _ h1 h2
        rw [pow_succ', mul_assoc]
        refine ⟨this.1, fun m hm => this.2 m (by rw [hm]; ring)⟩
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos_aux_prod : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
      (α : Fin n →₀ ℕ), (∀ m, 0 ≤ (α.prod (fun i k => (∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) ^ k)).coeff m) ∧
      (∀ m : Fin n →₀ ℕ, weight (1 : Fin n → ℕ) m = weight (1 : Fin n → ℕ) α →
        0 < (α.prod (fun i k => (∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) ^ k)).coeff m) :=
    fun (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
        (α : Fin n →₀ ℕ) => by
      induction α using Finsupp.induction with
      | zero =>
        simp only [Finsupp.prod_zero_index, map_zero]
        refine ⟨fun m => ?_, fun m hm => ?_⟩
        · rw [coeff_one]; split_ifs <;> norm_num
        · have : m = 0 := by
            rw [← Finsupp.degree_eq_zero_iff, Finsupp.degree_eq_weight_one]
            exact hm
          subst this; simp
      | single_add a b f ha hb ih =>
        rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
          Finsupp.prod_single_index (by simp)]
        have := LZpos_aux_powmul n A hA a b _ _ ih.1 ih.2
        refine ⟨this.1, fun m hm => this.2 m ?_⟩
        rw [hm, map_add]
        congr 1
        rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]; simp
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos_aux_pos : ∀ (n d : ℕ) (f : H n d) (hf0 : f.1 ≠ 0) (hfn : ∀ m, 0 ≤ f.1.coeff m)
      (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (m : Fin n →₀ ℕ) (hm : weight 1 m = d), 0 < (aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) f.1).coeff m :=
    fun (n d : ℕ) (f : H n d) (hf0 : f.1 ≠ 0) (hfn : ∀ m, 0 ≤ f.1.coeff m)
        (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (m : Fin n →₀ ℕ) (hm : weight 1 m = d) => by
      have hhom : f.1.IsHomogeneous d := f.2
      conv => rhs; rw [f.1.as_sum]
      simp only [map_sum, aeval_monomial, coeff_sum, algebraMap_eq, coeff_C_mul]
      obtain ⟨α, hα⟩ := Finsupp.support_nonempty_iff.2 hf0
      apply Finset.sum_pos'
      · intro β _
        exact mul_nonneg (hfn β) ((LZpos_aux_prod n A hA β).1 m)
      · refine ⟨α, hα, mul_pos ?_ ((LZpos_aux_prod n A hA α).2 m ?_)⟩
        · exact lt_of_le_of_ne (hfn α) (Ne.symm (Finsupp.mem_support_iff.1 hα))
        · rw [hm, hhom (Finsupp.mem_support_iff.1 hα)]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos_aux_cont : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ), Filter.Tendsto (fun θ : ℝ => (aeval (fun i => ∑ j, ((if i = j then 1 - θ else 0) + θ) •
        (X j : MvPolynomial (Fin n) ℝ)) p).coeff m) (nhds 0) (nhds (p.coeff m)) :=
    fun (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) => by
      have h0 : (fun i => ∑ j, ((if i = j then 1 - (0:ℝ) else 0) + 0) •
          (X j : MvPolynomial (Fin n) ℝ)) = X := by
        funext i; simp
      suffices H : ∀ m, Filter.Tendsto (fun θ : ℝ => (aeval (fun i => ∑ j,
          ((if i = j then 1 - θ else 0) + θ) • (X j : MvPolynomial (Fin n) ℝ)) p).coeff m) (nhds 0)
          (nhds ((aeval (fun i => ∑ j, ((if i = j then 1 - (0:ℝ) else 0) + 0) •
            (X j : MvPolynomial (Fin n) ℝ)) p).coeff m)) by
        have := H m
        rwa [h0, aeval_X_left_apply] at this
      induction p using MvPolynomial.induction_on with
      | C a => intro m; simp only [aeval_C]; exact tendsto_const_nhds
      | add p q hp hq => intro m; simp only [map_add, coeff_add]; exact (hp m).add (hq m)
      | mul_X p i hp =>
        intro m
        simp only [map_mul, aeval_X, Finset.mul_sum, mul_smul_comm, coeff_sum, coeff_smul,
          coeff_mul_X', smul_eq_mul]
        apply tendsto_finset_sum
        intro j _
        apply Filter.Tendsto.mul
        · have hc : Continuous (fun θ : ℝ => (if i = j then 1 - θ else 0) + θ) := by
            split_ifs <;> fun_prop
          exact hc.tendsto 0
        · split_ifs
          · exact hp _
          · exact tendsto_const_nhds
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos_aux_powS : ∀ (n k : ℕ) (i0 : Fin n) (c : ℝ) (hc : 0 ≤ c) (g : H n k)
      (hg : g.1 = c • X i0 ^ k), g ∈ S n k :=
    fun (n k : ℕ) (i0 : Fin n) (c : ℝ) (hc : 0 ≤ c) (g : H n k)
        (hg : g.1 = c • X i0 ^ k) => by
      refine ⟨?_, fun m => ?_⟩
      · rcases hc.eq_or_lt with h | h
        · left; rw [hg, ← h, zero_smul]
        · right
          intro z
          rw [hg]
          simp only [map_smul, map_pow, aeval_X, Function.comp_apply]
          have hz : ((z i0 : ℍ) : ℂ) ≠ 0 := (z i0).ne_zero
          exact smul_ne_zero h.ne' (pow_ne_zero _ hz)
      · rw [hg, coeff_smul, coeff_X_pow, smul_eq_mul]
        split_ifs <;> simp [hc]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos_aux_pow : ∀ (n : ℕ) (i0 : Fin n), ∀ (k : ℕ) (c : ℝ), 0 ≤ c → ∀ g : H n k,
      g.1 = c • X i0 ^ k → g ∈ L n k :=
    fun (n : ℕ) (i0 : Fin n) => by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro c hc g hg
        rcases k with _ | _ | _ | k
        · exact LZpos_aux_powS n 0 i0 c hc g hg
        · exact LZpos_aux_powS n 1 i0 c hc g hg
        · exact LZpos_aux_powS n 2 i0 c hc g hg
        refine ⟨⟨?_, fun m => ?_⟩, fun j => ?_⟩
        · intro α hα β hβ i hi
          exfalso
          have hsub : ∀ γ ∈ (g.1.support : Set (Fin n →₀ ℕ)), γ = Finsupp.single i0 (k + 3) := by
            intro γ hγ
            rw [Finset.mem_coe, MvPolynomial.mem_support_iff, hg, coeff_smul, coeff_X_pow] at hγ
            by_contra hne
            exact hγ (by rw [if_neg (Ne.symm hne)]; simp)
          rw [hsub α hα, hsub β hβ] at hi
          exact lt_irrefl _ hi
        · rw [hg, coeff_smul, coeff_X_pow, smul_eq_mul]
          split_ifs <;> simp [hc]
        · apply ih (k + 2) (by omega) (if j = i0 then c * (k + 3) else 0)
          · split_ifs <;> positivity
          · show pderiv j g.1 = _
            rw [hg, Derivation.map_smul, pderiv_pow]
            by_cases h : j = i0
            · subst h
              rw [pderiv_X_self, if_pos rfl, mul_one, smul_eq_C_mul, smul_eq_C_mul]
              simp only [map_mul]
              push_cast
              simp only [map_add, map_natCast, map_ofNat]
              ring
            · rw [pderiv_X_of_ne (Ne.symm h), if_neg h, mul_zero, smul_zero, zero_smul]
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos_aux_zero : ∀ (n d : ℕ) (hn : 0 < n) (f : H n (d + 3)) (hf0 : f.1 = 0), f ∈ closure (L n (d + 3) ∩ P n (d + 3)) :=
    fun (n d : ℕ) (hn : 0 < n) (f : H n (d + 3)) (hf0 : f.1 = 0) => by
      let i0 : Fin n := ⟨0, hn⟩
      let g0 : H n (d + 3) := (⟨X i0 ^ (d + 3), (mem_homogeneousSubmodule _ _).2
        (isHomogeneous_X_pow _ _)⟩ : homogeneousSubmodule (Fin n) ℝ (d + 3))
      have hg0 : g0 ∈ L n (d + 3) := LZpos_aux_pow n i0 (d + 3) 1 zero_le_one g0 (by
        show X i0 ^ (d + 3) = _
        rw [one_smul])
      have hg00 : g0.1 ≠ 0 := by
        show X i0 ^ (d + 3) ≠ 0
        exact pow_ne_zero _ (X_ne_zero _)
      have hg0n : ∀ m, 0 ≤ g0.1.coeff m := hg0.1.2
      have hex : ∀ c : ℝ, ∃ g : H n (d + 3), 0 < c →
          (g.1 = aeval (fun i => ∑ j, (fun _ _ => c : Matrix (Fin n) (Fin n) ℝ) i j •
            (X j : MvPolynomial (Fin n) ℝ)) g0.1 ∧ g ∈ L n (d + 3)) := by
        intro c
        by_cases hc : 0 < c
        · obtain ⟨g, hg⟩ := LZsubst n (d + 3) g0 hg0 (fun _ _ => c) (fun _ _ => hc)
          exact ⟨g, fun _ => hg⟩
        · exact ⟨f, fun h => absurd h hc⟩
      choose g hg using hex
      have hev : ∀ᶠ c in nhdsWithin (0:ℝ) (Set.Ioi 0), g c ∈ L n (d + 3) ∩ P n (d + 3) := by
        filter_upwards [self_mem_nhdsWithin] with c hc
        refine ⟨(hg c hc).2, fun m hm => ?_⟩
        rw [(hg c hc).1]
        exact LZpos_aux_pos n (d + 3) g0 hg00 hg0n _ (fun _ _ => hc) m hm
      have ht : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds f) := by
        apply LZtop
        intro m
        rw [hf0, coeff_zero]
        have e : ∀ c : ℝ, 0 < c → (g c).1.coeff m =
            c ^ (d + 3) * ((∑ j, (X j : MvPolynomial (Fin n) ℝ)) ^ (d + 3)).coeff m := by
          intro c hc
          have hg0v : g0.1 = X i0 ^ (d + 3) := rfl
          rw [(hg c hc).1, hg0v, map_pow, aeval_X, ← Finset.smul_sum, smul_pow, coeff_smul, smul_eq_mul]
        have h1 : Filter.Tendsto (fun c : ℝ => c ^ (d + 3) *
            ((∑ j, (X j : MvPolynomial (Fin n) ℝ)) ^ (d + 3)).coeff m) (nhds 0) (nhds 0) := by
          simpa using (((continuous_pow (d + 3)).tendsto (0:ℝ)).mul
            (tendsto_const_nhds (x := ((∑ j, (X j : MvPolynomial (Fin n) ℝ)) ^ (d + 3)).coeff m)))
        refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with c hc
        rw [e c hc]
      exact mem_closure_of_tendsto ht hev
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos : ∀ (n d : ℕ) (hn : 0 < n), L n (d + 3) ⊆ closure (L n (d + 3) ∩ P n (d + 3)) :=
    fun (n d : ℕ) (hn : 0 < n) => by
      intro f hf
      by_cases hf0 : f.1 = 0
      · exact LZpos_aux_zero n d hn f hf0
      · have hfn : ∀ m, 0 ≤ f.1.coeff m := hf.1.2
        have hA : ∀ θ ∈ Set.Ioo (0:ℝ) 1, ∀ i j : Fin n,
            0 < ((if i = j then 1 - θ else 0) + θ : ℝ) := by
          intro θ hθ i j
          split_ifs <;> linarith [hθ.1, hθ.2]
        have hex : ∀ θ : ℝ, ∃ g : H n (d + 3), θ ∈ Set.Ioo (0:ℝ) 1 →
            (g.1 = aeval (fun i => ∑ j, ((if i = j then 1 - θ else 0) + θ) •
              (X j : MvPolynomial (Fin n) ℝ)) f.1 ∧ g ∈ L n (d + 3)) := by
          intro θ
          by_cases hθ : θ ∈ Set.Ioo (0:ℝ) 1
          · obtain ⟨g, hg⟩ := LZsubst n (d + 3) f hf (fun i j => (if i = j then 1 - θ else 0) + θ)
              (hA θ hθ)
            exact ⟨g, fun _ => hg⟩
          · exact ⟨f, fun h => absurd h hθ⟩
        choose g hg using hex
        haveI : (nhdsWithin (0:ℝ) (Set.Ioo 0 1)).NeBot := left_nhdsWithin_Ioo_neBot zero_lt_one
        have hev : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioo 0 1), g θ ∈ L n (d + 3) ∩ P n (d + 3) := by
          filter_upwards [self_mem_nhdsWithin] with θ hθ
          refine ⟨(hg θ hθ).2, fun m hm => ?_⟩
          rw [(hg θ hθ).1]
          exact LZpos_aux_pos n (d + 3) f hf0 hfn _ (hA θ hθ) m hm
        have ht : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Ioo 0 1)) (nhds f) := by
          apply LZtop
          intro m
          have h1 := (LZpos_aux_cont n f.1 m).mono_left (nhdsWithin_le_nhds (s := Set.Ioo (0:ℝ) 1))
          refine h1.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with θ hθ
          rw [(hg θ hθ).1]
        exact mem_closure_of_tendsto ht hev
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZpos_aux_mul : ∀ (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
      (i : Fin n) (q : MvPolynomial (Fin n) ℝ) (hq0 : ∀ m, 0 ≤ q.coeff m)
      (hq : ∀ m : Fin n →₀ ℕ, weight 1 m = k → 0 < q.coeff m), (∀ m, 0 ≤ ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) * q).coeff m) ∧
      (∀ m : Fin n →₀ ℕ, weight 1 m = k + 1 →
        0 < ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) * q).coeff m) :=
    fun (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
        (i : Fin n) (q : MvPolynomial (Fin n) ℝ) (hq0 : ∀ m, 0 ≤ q.coeff m)
        (hq : ∀ m : Fin n →₀ ℕ, weight 1 m = k → 0 < q.coeff m) => by
      have e : ∀ m, ((∑ j, A i j • (X j : MvPolynomial (Fin n) ℝ)) * q).coeff m =
          ∑ j, A i j * (if j ∈ m.support then q.coeff (m - Finsupp.single j 1) else 0) := by
        intro m
        simp only [Finset.sum_mul, coeff_sum, smul_mul_assoc, coeff_smul, coeff_X_mul', smul_eq_mul]
      refine ⟨fun m => ?_, fun m hm => ?_⟩
      · rw [e]
        apply Finset.sum_nonneg
        intro j _
        apply mul_nonneg (hA i j).le
        split_ifs
        · exact hq0 _
        · exact le_rfl
      · rw [e]
        have hm0 : m ≠ 0 := by
          rintro rfl; simp at hm
        obtain ⟨j, hj⟩ : ∃ j, j ∈ m.support := by
          by_contra h
          push_neg at h
          exact hm0 (Finsupp.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
        apply Finset.sum_pos'
        · intro j _
          apply mul_nonneg (hA i j).le
          split_ifs
          · exact hq0 _
          · exact le_rfl
        · refine ⟨j, Finset.mem_univ _, ?_⟩
          rw [if_pos hj]
          apply mul_pos (hA i j)
          apply hq
          have hle : Finsupp.single j 1 ≤ m := by
            intro x
            rw [Finsupp.single_apply]
            split_ifs with h
            · subst h; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)
            · exact Nat.zero_le _
          have := congrArg (weight (1 : Fin n → ℕ)) (tsub_add_cancel_of_le hle)
          rw [map_add, hm] at this
          have hs : weight (1 : Fin n → ℕ) (Finsupp.single j 1) = 1 := by
            rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]; simp
          rw [hs] at this
          omega
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZstrict : ∀ (n d : ℕ) (hn : 0 < n), L n (d + 3) ∩ P n (d + 3) ⊆ closure (Ŀ n (d + 3)) :=
    fun (n d : ℕ) (hn : 0 < n) => by
      have LZstrict_aux_exp : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) (t : ℝ), (x + t • w) ⬝ᵥ (Q *ᵥ (x + t • w)) = x ⬝ᵥ (Q *ᵥ x) + t * (x ⬝ᵥ (Q *ᵥ w)) + t * (w ⬝ᵥ (Q *ᵥ x)) + t * t * (w ⬝ᵥ (Q *ᵥ w)) := by
        intro n Q x w t
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
          smul_dotProduct, smul_eq_mul]
        ring
      have LZstrict_aux_core : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQs : ∀ x y : Fin n → ℝ, x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x)) (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (Q *ᵥ u) → (u ⬝ᵥ (Q *ᵥ u)) * (v ⬝ᵥ (Q *ᵥ v)) ≤ (u ⬝ᵥ (Q *ᵥ v)) ^ 2) (x w : Fin n → ℝ) (hx : 0 < x ⬝ᵥ (Q *ᵥ x)) (hw : 0 < w ⬝ᵥ (Q *ᵥ w)) (hxw : ∀ t : ℝ, 0 < (x + t • w) ⬝ᵥ (Q *ᵥ (x + t • w))), False := by
        intro n Q hQs hN x w hx hw hxw
        have h1 := hN x w hx
        have hs := hQs w x
        set A := x ⬝ᵥ (Q *ᵥ x)
        set B := x ⬝ᵥ (Q *ᵥ w)
        set C := w ⬝ᵥ (Q *ᵥ w)
        have hB : B ≠ 0 := by
          intro hB; rw [hB] at h1; nlinarith
        have h2 := hxw (-A / B)
        rw [LZstrict_aux_exp, hs] at h2
        have h3 : A + -A / B * B + -A / B * B + -A / B * (-A / B) * C = A * (A * C - B ^ 2) / B ^ 2 := by
          field_simp; ring
        rw [h3] at h2
        have : A * (A * C - B ^ 2) / B ^ 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hx.le (by linarith)) (sq_nonneg _)
        linarith
      have LZstrict_aux_npd : ∀ (n : ℕ) (Q R : Matrix (Fin n) (Fin n) ℝ) (hQs : ∀ x y : Fin n → ℝ, x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x)) (hRs : ∀ x y : Fin n → ℝ, x ⬝ᵥ (R *ᵥ y) = y ⬝ᵥ (R *ᵥ x)) (hle : ∀ y : Fin n → ℝ, y ⬝ᵥ (R *ᵥ y) ≤ y ⬝ᵥ (Q *ᵥ y)) (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (Q *ᵥ u) → (u ⬝ᵥ (Q *ᵥ u)) * (v ⬝ᵥ (Q *ᵥ v)) ≤ (u ⬝ᵥ (Q *ᵥ v)) ^ 2), ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (R *ᵥ u) → (u ⬝ᵥ (R *ᵥ u)) * (v ⬝ᵥ (R *ᵥ v)) ≤ (u ⬝ᵥ (R *ᵥ v)) ^ 2 := by
        intro n Q R hQs hRs hle hN x v hx
        by_contra hlt
        push_neg at hlt
        set a := x ⬝ᵥ (R *ᵥ x)
        set b := x ⬝ᵥ (R *ᵥ v)
        set c := v ⬝ᵥ (R *ᵥ v)
        set w := a • v - b • x with hw
        have hxw : x ⬝ᵥ (R *ᵥ w) = 0 := by
          rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
            dotProduct_smul, smul_eq_mul, smul_eq_mul]
          ring
        have hwx : w ⬝ᵥ (R *ᵥ x) = 0 := by rw [hRs]; exact hxw
        have hww : w ⬝ᵥ (R *ᵥ w) = a * (a * c - b ^ 2) := by
          rw [hw, LZstab_aux_quad, hRs v x]; ring
        have hwwp : 0 < w ⬝ᵥ (R *ᵥ w) := by rw [hww]; exact mul_pos hx (by linarith)
        apply LZstrict_aux_core n Q hQs hN x w (lt_of_lt_of_le hx (hle x)) (lt_of_lt_of_le hwwp (hle w))
        intro t
        refine lt_of_lt_of_le ?_ (hle _)
        rw [LZstrict_aux_exp, hxw, hwx]
        nlinarith [mul_self_nonneg t]
      have LZstrict_aux_inv : ∀ (n : ℕ) (Q Pm : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 < ε) (hQs : ∀ x y : Fin n → ℝ, x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x)) (hPs : ∀ x y : Fin n → ℝ, x ⬝ᵥ (Pm *ᵥ y) = y ⬝ᵥ (Pm *ᵥ x)) (hPd : ∀ z : Fin n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (Pm *ᵥ z)) (hN : ∀ u v : Fin n → ℝ, 0 < u ⬝ᵥ (Q *ᵥ u) → (u ⬝ᵥ (Q *ᵥ u)) * (v ⬝ᵥ (Q *ᵥ v)) ≤ (u ⬝ᵥ (Q *ᵥ v)) ^ 2) (u : Fin n → ℝ) (hu : 0 < u ⬝ᵥ ((Q - ε • Pm) *ᵥ u)), IsUnit (Q - ε • Pm) := by
        intro n Q Pm ε hε hQs hPs hPd hN u hu
        have hPsd : ∀ z : Fin n → ℝ, 0 ≤ z ⬝ᵥ (Pm *ᵥ z) := by
          intro z
          by_cases hz : z = 0
          · subst hz; simp
          · exact (hPd z hz).le
        have hdec : ∀ y : Fin n → ℝ, y ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ ((Q - ε • Pm) *ᵥ y) + ε * (y ⬝ᵥ (Pm *ᵥ y)) := by
          intro y
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]; ring
        rw [← Matrix.mulVec_injective_iff_isUnit]
        intro x y hxy
        have hz : (Q - ε • Pm) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
        by_contra hne
        have hz0 : x - y ≠ 0 := sub_ne_zero.mpr hne
        set z := x - y
        have hRs : ∀ a b : Fin n → ℝ, a ⬝ᵥ ((Q - ε • Pm) *ᵥ b) = b ⬝ᵥ ((Q - ε • Pm) *ᵥ a) := by
          intro a b
          simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
          rw [hQs a b, hPs a b]
        apply LZstrict_aux_core n Q hQs hN u z
        · rw [hdec]; nlinarith [hPsd u]
        · rw [hdec, hz, dotProduct_zero]; nlinarith [hPd z hz0]
        · intro t
          rw [hdec, LZstrict_aux_exp, hRs z u]
          simp only [hz, dotProduct_zero]
          nlinarith [hPsd (u + t • z)]
      have LZstrict_aux_coeff_pderiv : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (m : Fin n →₀ ℕ), (pderiv i p).coeff m = p.coeff (m + Finsupp.single i 1) * ((m i : ℝ) + 1) := by
        intro n p i m
        induction p using MvPolynomial.induction_on' with
        | monomial s c =>
          rw [pderiv_monomial, coeff_monomial, coeff_monomial]
          by_cases h : s = m + Finsupp.single i 1
          · subst h
            rw [if_pos (add_tsub_cancel_right _ _), if_pos rfl]
            simp
          · rw [if_neg h, zero_mul]
            by_cases h2 : s - Finsupp.single i 1 = m
            · rw [if_pos h2]
              have : s i = 0 := by
                by_contra h3
                apply h
                rw [← h2]
                ext k
                simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
                by_cases hk : k = i
                · subst hk; simp; omega
                · simp [Ne.symm hk]
              simp [this]
            · rw [if_neg h2]
        | add p q hp hq =>
          rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]
      have LZstrict_aux_hess_sub : ∀ (n : ℕ) (f h : H n 2) (ε : ℝ) (hm : f.1 - ε • h.1 ∈ homogeneousSubmodule (Fin n) ℝ 2), H.hessian (⟨f.1 - ε • h.1, hm⟩ : H n 2) = H.hessian f - ε • H.hessian h := by
        intro n f h ε hm
        ext i j
        simp only [H.hessian, Matrix.sub_apply, Matrix.smul_apply, coeff_sub, coeff_smul, smul_eq_mul]
        split_ifs <;> ring
      have LZstrict_aux_evalq : ∀ (n : ℕ) (g : H n 2) (z : Fin n → ℝ), eval z g.1 = (z ⬝ᵥ (H.hessian g *ᵥ z)) / 2 := by
        intro n g z
        conv_lhs => rw [LZstab_aux_poly n g]
        rw [LZstab_aux_dot, div_eq_mul_inv, Finset.sum_mul]
        simp only [map_sum, map_mul, eval_C, eval_X]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _
        ring
      have LZstrict_aux_Pev : ∀ (n k : ℕ) (f h : H n k) (hf : f ∈ P n k), ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ m : Fin n →₀ ℕ, weight 1 m = k → 0 < f.1.coeff m - ε * h.1.coeff m := by
        intro n k f h hf
        have key : ∀ m ∈ h.1.support, ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            weight 1 m = k → 0 < f.1.coeff m - ε * h.1.coeff m := by
          intro m _
          by_cases hw : weight 1 m = k
          · have hp := hf m hw
            have hδ : (0 : ℝ) < f.1.coeff m / (|h.1.coeff m| + 1) := by positivity
            filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ),
              self_mem_nhdsWithin] with ε hε hε0 _
            have hε0' : 0 < ε := hε0
            rw [lt_div_iff₀ (by positivity)] at hε
            have : ε * h.1.coeff m ≤ ε * |h.1.coeff m| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hε0'.le
            nlinarith
          · exact Filter.Eventually.of_forall (fun _ h' => absurd h' hw)
        filter_upwards [(Finset.eventually_all h.1.support).2 key] with ε hε m hm
        by_cases hs : m ∈ h.1.support
        · exact hε m hs hm
        · rw [MvPolynomial.notMem_support_iff.1 hs, mul_zero, sub_zero]; exact hf m hm
      have LZstrict_aux_base : ∀ (n : ℕ) (hn : 0 < n) (f h : H n 2) (hf : f ∈ L n 2) (hfP : f ∈ P n 2) (hPd : ∀ z : Fin n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (H.hessian h *ᵥ z)), ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ hm : f.1 - ε • h.1 ∈ homogeneousSubmodule (Fin n) ℝ 2, (⟨f.1 - ε • h.1, hm⟩ : H n 2) ∈ Ŀ n 2 := by
        intro n hn f h hf hfP hPd
        have hfS : f ∈ S n 2 := hf
        have hN := (LZstab n f hfS.2).1 hfS.1
        set Q := H.hessian f
        set Pm := H.hessian h
        set u : Fin n → ℝ := fun _ => 1
        have hu0 : u ≠ 0 := by
          intro h0
          have := congrFun h0 ⟨0, hn⟩
          simp [u] at this
        have hPu : 0 < u ⬝ᵥ (Pm *ᵥ u) := hPd u hu0
        have hQu : 0 < u ⬝ᵥ (Q *ᵥ u) := by
          apply LZstab_aux_ypos n f hfS.2 ⟨0, hn⟩ ⟨0, hn⟩ _ u (fun _ => one_pos)
          show 0 < H.hessian f ⟨0, hn⟩ ⟨0, hn⟩
          simp only [H.hessian, if_true]
          have := hfP (Finsupp.single ⟨0, hn⟩ 2) (by simp [weight_apply])
          linarith
        have hδ : (0 : ℝ) < (u ⬝ᵥ (Q *ᵥ u)) / (u ⬝ᵥ (Pm *ᵥ u)) := div_pos hQu hPu
        filter_upwards [LZstrict_aux_Pev n 2 f h hfP, self_mem_nhdsWithin,
          eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with ε hεP hε0 hεδ hm
        have hε0' : 0 < ε := hε0
        rw [lt_div_iff₀ hPu] at hεδ
        rw [LZspec n hn, LZstrict_aux_hess_sub]
        have hQs := LZstab_aux_dotsymm n f
        have hPs := LZstab_aux_dotsymm n h
        have hdec : ∀ y : Fin n → ℝ, y ⬝ᵥ ((Q - ε • Pm) *ᵥ y) = y ⬝ᵥ (Q *ᵥ y) - ε * (y ⬝ᵥ (Pm *ᵥ y)) := by
          intro y
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        have hRs : ∀ a b : Fin n → ℝ, a ⬝ᵥ ((Q - ε • Pm) *ᵥ b) = b ⬝ᵥ ((Q - ε • Pm) *ᵥ a) := by
          intro a b
          simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
          rw [hQs a b, hPs a b]
        have hPsd : ∀ z : Fin n → ℝ, 0 ≤ z ⬝ᵥ (Pm *ᵥ z) := by
          intro z
          by_cases hz : z = 0
          · subst hz; simp
          · exact (hPd z hz).le
        refine ⟨?_, ?_, ?_⟩
        · intro m hmw
          have := hεP m hmw
          simpa [coeff_sub, coeff_smul] using this
        · apply LZstrict_aux_inv n Q Pm ε hε0' hQs hPs hPd hN u
          rw [hdec]; linarith
        · apply LZstrict_aux_npd n Q _ hQs hRs _ hN
          intro y
          rw [hdec]
          nlinarith [hPsd y]
      have LZstrict_aux_ind : ∀ (n : ℕ) (hn : 0 < n) (G : ℕ → MvPolynomial (Fin n) ℝ → Prop) (hG0 : ∀ h : H n 2, G 0 h.1 → ∀ z : Fin n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (H.hessian h *ᵥ z)) (hGs : ∀ (e : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n), G (e + 1) p → G e (pderiv i p)) (e : ℕ), ∀ f h : H n (e + 2), f ∈ L n (e + 2) → f ∈ P n (e + 2) → G e h.1 → ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ hm : f.1 - ε • h.1 ∈ homogeneousSubmodule (Fin n) ℝ (e + 2), (⟨f.1 - ε • h.1, hm⟩ : H n (e + 2)) ∈ Ŀ n (e + 2) := by
        intro n hn G hG0 hGs e
        induction e with
        | zero =>
          intro f h hf hfP hG
          exact LZstrict_aux_base n hn f h hf hfP (hG0 h hG)
        | succ e ih =>
          intro f h hf hfP hG
          have hfL : f ∈ M n (e + 3) ∧ ∀ i, (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (e + 2)) ∈ L n (e + 2) := hf
          have key : ∀ i : Fin n, ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              ∀ hm : (pderiv i f.1) - ε • (pderiv i h.1) ∈ homogeneousSubmodule (Fin n) ℝ (e + 2),
                (⟨(pderiv i f.1) - ε • (pderiv i h.1), hm⟩ : H n (e + 2)) ∈ Ŀ n (e + 2) := by
            intro i
            refine ih ⟨f.1.pderiv i, f.2.pderiv⟩ ⟨h.1.pderiv i, h.2.pderiv⟩ (hfL.2 i) ?_ (hGs e h.1 i hG)
            · intro m hm
              show 0 < (pderiv i f.1).coeff m
              rw [LZstrict_aux_coeff_pderiv]
              have : weight 1 (m + Finsupp.single i 1) = e + 1 + 2 := by
                rw [map_add, hm]; simp [weight_apply]
              exact mul_pos (hfP _ this) (by positivity)
          filter_upwards [LZstrict_aux_Pev n (e + 3) f h hfP, (Filter.eventually_all).2 key] with ε hεP hεi hm
          refine ⟨?_, ?_⟩
          · intro m hmw
            have := hεP m hmw
            simpa [coeff_sub, coeff_smul] using this
          · intro i
            have hmi : (pderiv i f.1) - ε • (pderiv i h.1) ∈ homogeneousSubmodule (Fin n) ℝ (e + 2) := by
              have := (⟨(f.1 - ε • h.1), hm⟩ : H n (e + 3)).2.pderiv (i := i)
              simpa [map_sub, map_smul] using this
            have := hεi i hmi
            convert this using 2
            simp [map_sub]
      intro g ⟨hgL, hgP⟩
      have LZstrict_aux_pd : ∀ (h : H n 2) (c : Fin n → ℝ) (hc : ∀ j, 0 < c j)
          (hh : h.1 = ∑ j : Fin n, C (c j) * (X j + ∑ k : Fin n, X k) ^ 2),
          ∀ z : Fin n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (H.hessian h *ᵥ z) := by
        intro h c hc hh z hz
        have he := LZstrict_aux_evalq n h z
        rw [hh] at he
        simp only [map_sum, map_mul, map_pow, map_add, eval_C, eval_X] at he
        have hnn : ∀ j ∈ Finset.univ, 0 ≤ c j * (z j + ∑ k, z k) ^ 2 :=
          fun j _ => mul_nonneg (hc j).le (sq_nonneg _)
        by_contra hle
        push_neg at hle
        have h0 : ∑ j, c j * (z j + ∑ k, z k) ^ 2 = 0 :=
          le_antisymm (by linarith) (Finset.sum_nonneg hnn)
        rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h0
        have hzj : ∀ j, z j + ∑ k, z k = 0 := by
          intro j
          have := h0 j (Finset.mem_univ j)
          rcases mul_eq_zero.1 this with h1 | h1
          · exact absurd h1 (hc j).ne'
          · exact pow_eq_zero_iff (two_ne_zero) |>.1 h1
        have hs : ∑ k, z k = 0 := by
          have : ∑ j, (z j + ∑ k, z k) = 0 := Finset.sum_eq_zero (fun j _ => hzj j)
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
          have h2 : ((n : ℝ) + 1) * ∑ k, z k = 0 := by linarith
          rcases mul_eq_zero.1 h2 with h3 | h3
          · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            linarith
          · exact h3
        apply hz
        funext j
        have := hzj j
        rw [hs] at this
        simpa using this
      have LZstrict_aux_pderivL : ∀ (e : ℕ) (c : Fin n → ℝ) (i : Fin n),
          pderiv i (∑ j : Fin n, C (c j) * (X j + ∑ k : Fin n, X k) ^ (e + 1)) =
            ∑ j : Fin n, C (c j * ((e : ℝ) + 1) * (if i = j then 2 else 1)) *
              (X j + ∑ k : Fin n, X k) ^ e := by
        intro e c i
        rw [map_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [Derivation.leibniz, Derivation.leibniz_pow, pderiv_C, smul_zero, add_zero, map_add, map_sum]
        simp only [pderiv_X, Pi.single_apply]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true, add_tsub_cancel_right, smul_eq_mul, nsmul_eq_mul]
        split_ifs with h1 h2 h2
        · subst h1; simp [map_mul, map_add, map_ofNat C 2]; ring
        · exact absurd h1.symm h2
        · exact absurd h2.symm h1
        · simp [map_mul]; ring
      have hG0 : ∀ h : H n 2, (∃ c : Fin n → ℝ, (∀ j, 0 < c j) ∧
          h.1 = ∑ j : Fin n, C (c j) * (X j + ∑ k : Fin n, X k) ^ (0 + 2)) →
          ∀ z : Fin n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (H.hessian h *ᵥ z) := by
        rintro h ⟨c, hc, hh⟩
        exact LZstrict_aux_pd h c hc hh
      have hGs : ∀ (e : ℕ) (p : MvPolynomial (Fin n) ℝ) (i : Fin n),
          (∃ c : Fin n → ℝ, (∀ j, 0 < c j) ∧ p = ∑ j : Fin n, C (c j) * (X j + ∑ k : Fin n, X k) ^ (e + 1 + 2)) →
          (∃ c : Fin n → ℝ, (∀ j, 0 < c j) ∧
            pderiv i p = ∑ j : Fin n, C (c j) * (X j + ∑ k : Fin n, X k) ^ (e + 2)) := by
        rintro e p i ⟨c, hc, rfl⟩
        refine ⟨fun j => c j * (((e + 2 : ℕ) : ℝ) + 1) * (if i = j then 2 else 1), ?_, ?_⟩
        · intro j
          have := hc j
          dsimp only
          split_ifs <;> positivity
        · exact LZstrict_aux_pderivL (e + 2) c i
      have hhom : (∑ j : Fin n, C (1 : ℝ) * (X j + ∑ k : Fin n, X k) ^ (d + 1 + 2) :
          MvPolynomial (Fin n) ℝ) ∈ homogeneousSubmodule (Fin n) ℝ (d + 3) := by
        rw [mem_homogeneousSubmodule]
        apply IsHomogeneous.sum
        intro j _
        have hL : (X j + ∑ k : Fin n, X k : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 :=
          (isHomogeneous_X ℝ j).add (IsHomogeneous.sum _ _ _ (fun k _ => isHomogeneous_X ℝ k))
        have := (hL.pow (d + 1 + 2)).C_mul (1 : ℝ)
        simpa using this
      let h : H n (d + 3) := ⟨_, hhom⟩
      have hev := LZstrict_aux_ind n hn
        (fun e p => ∃ c : Fin n → ℝ, (∀ j, 0 < c j) ∧ p = ∑ j : Fin n, C (c j) * (X j + ∑ k : Fin n, X k) ^ (e + 2))
        hG0 hGs (d + 1) g h hgL hgP ⟨fun _ => 1, fun _ => one_pos, rfl⟩
      have hmem : ∀ ε : ℝ, g.1 - ε • h.1 ∈ homogeneousSubmodule (Fin n) ℝ (d + 3) := fun ε =>
        Submodule.sub_mem _ g.2 (Submodule.smul_mem _ ε h.2)
      let F : ℝ → H n (d + 3) := fun ε => ⟨g.1 - ε • h.1, hmem ε⟩
      have hT : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds g) := by
        apply LZtop n (d + 3) ℝ _ F g
        intro m
        have hc : Filter.Tendsto (fun ε : ℝ => g.1.coeff m - ε * h.1.coeff m) (nhds 0)
            (nhds (g.1.coeff m - 0 * h.1.coeff m)) :=
          (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
        rw [zero_mul, sub_zero] at hc
        refine (hc.mono_left nhdsWithin_le_nhds).congr ?_
        intro ε
        simp [F, coeff_sub, coeff_smul]
      apply mem_closure_of_tendsto hT
      filter_upwards [hev] with ε hε
      exact hε (hmem ε)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZsub_aux_nonneg : ∀ (n d : ℕ) (f : H n d) (hf : f ∈ closure (Ŀ n d))
      (hsub : Ŀ n d ⊆ P n d) (m : Fin n →₀ ℕ), 0 ≤ f.1.coeff m :=
    fun (n d : ℕ) (f : H n d) (hf : f ∈ closure (Ŀ n d))
        (hsub : Ŀ n d ⊆ P n d) (m : Fin n →₀ ℕ) => by
      have hcl : IsClosed {g : H n d | 0 ≤ (MvPolynomial.lcoeff ℝ m) g.1} :=
        isClosed_le continuous_const (LZtop_lin n d (MvPolynomial.lcoeff ℝ m))
      have hsub2 : Ŀ n d ⊆ {g : H n d | 0 ≤ (MvPolynomial.lcoeff ℝ m) g.1} := by
        intro g hg
        have hgP := hsub hg
        show 0 ≤ g.1.coeff m
        by_cases hm : weight 1 m = d
        · exact (hgP m hm).le
        · have h0 : g.1.coeff m = 0 := by
            by_contra hne
            exact hm (((mem_homogeneousSubmodule _ _).1 g.2) hne)
          rw [h0]
      exact closure_minimal hsub2 hcl hf
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZsub_aux_step : ∀ (n d : ℕ) (hprev : closure (Ŀ n (d + 2)) ⊆ L n (d + 2)), closure (Ŀ n (d + 3)) ⊆ L n (d + 3) :=
    fun (n d : ℕ) (hprev : closure (Ŀ n (d + 2)) ⊆ L n (d + 2)) => by
      intro f hf
      have hsubP : Ŀ n (d + 3) ⊆ P n (d + 3) := fun g hg => hg.1
      refine ⟨⟨LZmconv n (d + 3) f hf, fun m => LZsub_aux_nonneg n (d + 3) f hf hsubP m⟩,
        fun i => ?_⟩
      apply hprev
      let D : H n (d + 3) → H n (d + 2) := fun g => ⟨g.1.pderiv i, g.2.pderiv⟩
      have hc : Continuous D := LZtop_pderiv n d i
      have himg : D '' Ŀ n (d + 3) ⊆ Ŀ n (d + 2) := by
        rintro _ ⟨g, hg, rfl⟩
        exact hg.2 i
      exact closure_mono himg (mem_closure_image hc.continuousAt hf)
  open LorentzianPolynomials Finsupp Matrix MvPolynomial UpperHalfPlane in
  have LZsub : ∀ (n d : ℕ) (hn : 0 < n), closure (Ŀ n (d + 3)) ⊆ L n (d + 3) :=
    fun (n d : ℕ) (hn : 0 < n) => by
      induction d with
      | zero => exact LZsub_aux_step n 0 (LZlow n 2 hn (le_refl _)).le
      | succ k ih => exact LZsub_aux_step n (k + 1) ih
  rcases Nat.lt_or_ge d 3 with h | h
  · exact LZlow n d hn (by omega)
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
    apply Set.Subset.antisymm (LZsub n e hn)
    intro f hf
    exact closure_minimal (LZstrict n e hn) isClosed_closure (LZpos n e hn hf)
)")
    let act : Lean.Elab.Tactic.TacticM Unit :=
      withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 })
        (do Lean.Elab.Tactic.evalTactic stx; Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing)
    controlAt (EIO Lean.Exception) fun runInBase => do
      let t ← EIO.asTask (runInBase act) Task.Priority.dedicated
      match ← IO.wait t with
      | .ok a => pure a
      | .error e => throw e

end Submission
