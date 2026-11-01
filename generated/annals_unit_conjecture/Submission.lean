import ChallengeDeps
import Submission.Helpers

open UnitConjecture

set_option autoImplicit false

namespace Submission

theorem theorem_A : (∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1) ∧ IsUnit u ∧ ¬ ∃ g : P, u = g := by
  open UnitConjecture in
  have L_act_trans : ∀ (σ : Equiv.Perm (ℤ × ℤ × ℤ)) (t₁ t₂ t₃ : ℤ)
      (hσ : ∀ v : ℤ × ℤ × ℤ, σ v = (v.1 + t₁, v.2.1 + t₂, v.2.2 + t₃)) (n : ℤ) (v : ℤ × ℤ × ℤ), (σ ^ n) v = (v.1 + n * t₁, v.2.1 + n * t₂, v.2.2 + n * t₃) :=
    fun (σ : Equiv.Perm (ℤ × ℤ × ℤ)) (t₁ t₂ t₃ : ℤ)
        (hσ : ∀ v : ℤ × ℤ × ℤ, σ v = (v.1 + t₁, v.2.1 + t₂, v.2.2 + t₃)) (n : ℤ) (v : ℤ × ℤ × ℤ) => by
      induction n using Int.induction_on generalizing v with
      | zero => simp
      | succ m ih =>
        rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hσ]
        simp only [Prod.mk.injEq, Int.add_mul, Int.one_mul]
        omega
      | pred m ih =>
        rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
        have h : σ⁻¹ v = (v.1 - t₁, v.2.1 - t₂, v.2.2 - t₃) := by
          rw [Equiv.Perm.inv_eq_iff_eq, hσ]
          simp
        rw [h]
        simp only [Prod.mk.injEq, Int.sub_mul, Int.one_mul]
        omega
  open UnitConjecture in
  have L_act : ∀ (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
      (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
      (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1))
      (c : ℤ × ℤ × ℤ × Bool × Bool) (v : ℤ × ℤ × ℤ), φ (x ^ c.1 * y ^ c.2.1 * z ^ c.2.2.1 * (if c.2.2.2.1 then a else 1 : P) *
          (if c.2.2.2.2 then b else 1 : P)) v =
        (if c.2.2.2.1 then
          (if c.2.2.2.2 then (1 - v.1 + 2 * c.1, -v.2.1 + 2 * c.2.1, v.2.2 - 1 - 2 * c.2.2.1)
           else (v.1 + 1 + 2 * c.1, -v.2.1 + 1 + 2 * c.2.1, -v.2.2 - 2 * c.2.2.1))
        else
          (if c.2.2.2.2 then (-v.1 + 2 * c.1, v.2.1 + 1 + 2 * c.2.1, -v.2.2 + 1 - 2 * c.2.2.1)
           else (v.1 + 2 * c.1, v.2.1 + 2 * c.2.1, v.2.2 - 2 * c.2.2.1))) :=
    fun (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
        (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
        (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1))
        (c : ℤ × ℤ × ℤ × Bool × Bool) (v : ℤ × ℤ × ℤ) => by
      have hx : ∀ v : ℤ × ℤ × ℤ, φ x v = (v.1 + 2, v.2.1 + 0, v.2.2 + 0) := by
        intro v
        rw [show (x : P) = (a : P) ^ 2 from rfl]
        simp only [pow_two, map_mul, Equiv.Perm.mul_apply, hA, Prod.mk.injEq]
        omega
      have hy : ∀ v : ℤ × ℤ × ℤ, φ y v = (v.1 + 0, v.2.1 + 2, v.2.2 + 0) := by
        intro v
        rw [show (y : P) = (b : P) ^ 2 from rfl]
        simp only [pow_two, map_mul, Equiv.Perm.mul_apply, hB, Prod.mk.injEq]
        omega
      have hz : ∀ v : ℤ × ℤ × ℤ, φ z v = (v.1 + 0, v.2.1 + 0, v.2.2 + -2) := by
        intro v
        rw [show (z : P) = ((a : P) * (b : P)) ^ 2 from rfl]
        simp only [pow_two, map_mul, Equiv.Perm.mul_apply, hA, hB, Prod.mk.injEq]
        omega
      obtain ⟨i, j, k, e, f⟩ := c
      simp only [map_mul, map_zpow, Equiv.Perm.mul_apply, L_act_trans _ _ _ _ hx,
        L_act_trans _ _ _ _ hy, L_act_trans _ _ _ _ hz]
      cases e <;> cases f <;> simp [hA, hB, Prod.ext_iff] <;> omega
  open UnitConjecture in
  have L_toggle : ∀ (l acc : List (ℤ × ℤ × ℤ)), ((l.foldl (fun (acc : List (ℤ × ℤ × ℤ)) v => if v ∈ acc then acc.erase v else v :: acc) acc).map
          (fun v => Finsupp.single v (1 : ZMod 2))).sum =
        (acc.map (fun v => Finsupp.single v (1 : ZMod 2))).sum +
          (l.map (fun v => Finsupp.single v (1 : ZMod 2))).sum :=
    fun (l acc : List (ℤ × ℤ × ℤ)) => by
      induction l generalizing acc with
      | nil => simp
      | cons v l ih =>
        rw [List.foldl_cons, ih]
        have hstep : ((if v ∈ acc then acc.erase v else v :: acc).map
            (fun v => Finsupp.single v (1 : ZMod 2))).sum =
            (acc.map (fun v => Finsupp.single v (1 : ZMod 2))).sum + Finsupp.single v (1 : ZMod 2) := by
          by_cases hv : v ∈ acc
          · rw [if_pos hv]
            have hp := (List.perm_cons_erase hv).map (fun v => Finsupp.single v (1 : ZMod 2))
            rw [hp.sum_eq, List.map_cons, List.sum_cons]
            have h2 : Finsupp.single v (1 : ZMod 2) + Finsupp.single v (1 : ZMod 2) = 0 := by
              rw [← Finsupp.single_add]
              have : (1 + 1 : ZMod 2) = 0 := by decide
              rw [this, Finsupp.single_zero]
            rw [add_comm (Finsupp.single v (1 : ZMod 2)) _, add_assoc, h2, add_zero]
          · rw [if_neg hv, List.map_cons, List.sum_cons, add_comm]
        rw [hstep, List.map_cons, List.sum_cons, add_assoc]
  open UnitConjecture in
  have L_crit : ∀ (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
      (N : ℤ × ℤ × ℤ × Bool × Bool → P) (T : ℤ × ℤ × ℤ × Bool × Bool → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ)
      (hT : ∀ c v, φ (N c) v = T c v)
      (hinj : Function.Injective (fun g : P => φ g (0, 0, 0)))
      (W₁ W₂ : List (ℤ × ℤ × ℤ × Bool × Bool))
      (hpar : (W₁.flatMap (fun c => W₂.map (fun c' => T c (T c' (0, 0, 0))))).foldl
        (fun (acc : List (ℤ × ℤ × ℤ)) v => if v ∈ acc then acc.erase v else v :: acc) [] = [(0, 0, 0)]), (W₁.map (fun c => ((N c : P) : R))).sum * (W₂.map (fun c => ((N c : P) : R))).sum = 1 :=
    fun (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
        (N : ℤ × ℤ × ℤ × Bool × Bool → P) (T : ℤ × ℤ × ℤ × Bool × Bool → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ)
        (hT : ∀ c v, φ (N c) v = T c v)
        (hinj : Function.Injective (fun g : P => φ g (0, 0, 0)))
        (W₁ W₂ : List (ℤ × ℤ × ℤ × Bool × Bool))
        (hpar : (W₁.flatMap (fun c => W₂.map (fun c' => T c (T c' (0, 0, 0))))).foldl
          (fun (acc : List (ℤ × ℤ × ℤ)) v => if v ∈ acc then acc.erase v else v :: acc) [] = [(0, 0, 0)]) => by
      let f : P → ℤ × ℤ × ℤ := fun g => φ g (0, 0, 0)
      let Ψ : R →+ ((ℤ × ℤ × ℤ) →₀ ZMod 2) := Finsupp.mapDomain.addMonoidHom f
      have hΨ1 : ∀ g : P, Ψ (g : R) = Finsupp.single (f g) 1 := by
        intro g
        show Finsupp.mapDomain f (MonoidAlgebra.of (ZMod 2) P g) = _
        rw [MonoidAlgebra.of_apply]
        exact Finsupp.mapDomain_single
      have hrow : ∀ c, Ψ (((N c : P) : R) * (W₂.map (fun c => ((N c : P) : R))).sum) =
          (W₂.map (fun c' => Finsupp.single (T c (T c' (0, 0, 0))) (1 : ZMod 2))).sum := by
        intro c
        rw [← List.sum_map_mul_left, map_list_sum, List.map_map]
        congr 1
        apply List.map_congr_left
        intro c' _
        show Ψ (MonoidAlgebra.of (ZMod 2) P (N c) * MonoidAlgebra.of (ZMod 2) P (N c')) = _
        rw [← map_mul]
        rw [hΨ1]
        simp only [f, map_mul, Equiv.Perm.mul_apply, hT]
      have hall : ∀ L : List (ℤ × ℤ × ℤ × Bool × Bool),
          Ψ ((L.map (fun c => ((N c : P) : R))).sum * (W₂.map (fun c => ((N c : P) : R))).sum) =
          ((L.flatMap (fun c => W₂.map (fun c' => T c (T c' (0, 0, 0))))).map
            (fun v => Finsupp.single v (1 : ZMod 2))).sum := by
        intro L
        induction L with
        | nil => simp
        | cons c L ih =>
          rw [List.map_cons, List.sum_cons, add_mul, map_add, ih, hrow, List.flatMap_cons,
            List.map_append, List.sum_append, List.map_map]
          rfl
      apply Finsupp.mapDomain_injective hinj
      change Ψ _ = Ψ 1
      rw [hall]
      have ht := L_toggle (W₁.flatMap (fun c => W₂.map (fun c' => T c (T c' (0, 0, 0))))) []
      rw [hpar] at ht
      simp only [List.map_nil, List.sum_nil, zero_add, List.map_cons, List.sum_cons, add_zero] at ht
      rw [← ht]
      have h1 : (1 : R) = ((1 : P) : R) := (map_one (MonoidAlgebra.of (ZMod 2) P)).symm
      rw [h1, hΨ1]
      simp [f]
  have L_rel_tail : ∀ (G : Type) [Group G] (u v u' v' : G) (h : u * v = u' * v') (w : G),
      u * (v * w) = u' * (v' * w) :=
    fun (G : Type) [Group G] (u v u' v' : G) (h : u * v = u' * v') (w : G) => by
      rw [← mul_assoc, h, mul_assoc]
  open UnitConjecture in
  have L_rel_grp : ∀ (G : Type) [Group G] (A B X Y : G) (hX : A * A = X) (hY : B * B = Y)
      (h1 : B⁻¹ * X * B * X = 1) (h2 : A⁻¹ * Y * A * Y = 1), X * Y = Y * X ∧ X * (A * B * (A * B)) = (A * B * (A * B)) * X ∧
      Y * (A * B * (A * B)) = (A * B * (A * B)) * Y ∧
      A * Y = Y⁻¹ * A ∧ A * (A * B * (A * B)) = (A * B * (A * B))⁻¹ * A ∧
      B * X = X⁻¹ * B ∧ B * (A * B * (A * B)) = (A * B * (A * B))⁻¹ * B ∧
      B * A = X⁻¹ * Y * (A * B * (A * B))⁻¹ * A * B :=
    fun (G : Type) [Group G] (A B X Y : G) (hX : A * A = X) (hY : B * B = Y)
        (h1 : B⁻¹ * X * B * X = 1) (h2 : A⁻¹ * Y * A * Y = 1) => by
      have hXB : X * B = B * X⁻¹ := by
        have := h1
        rw [mul_eq_one_iff_eq_inv, mul_assoc, inv_mul_eq_iff_eq_mul] at this
        exact this
      have hBX : B * X = X⁻¹ * B := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hXB, mul_assoc, inv_mul_cancel, mul_one]
      have hYA : Y * A = A * Y⁻¹ := by
        have := h2
        rw [mul_eq_one_iff_eq_inv, mul_assoc, inv_mul_eq_iff_eq_mul] at this
        exact this
      have hAY : A * Y = Y⁻¹ * A := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hYA, mul_assoc, inv_mul_cancel, mul_one]
      have hXA : X * A = A * X := by rw [← hX, mul_assoc]
      have hYB : Y * B = B * Y := by rw [← hY, mul_assoc]
      have hXiA : X⁻¹ * A = A * X⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hXA, mul_inv_cancel_right]
      have hYiB : Y⁻¹ * B = B * Y⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hYB, mul_inv_cancel_right]
      have hXiB : X⁻¹ * B = B * X := hBX.symm
      have hYiA : Y⁻¹ * A = A * Y := hAY.symm
      have hBXi : B * X⁻¹ = X * B := hXB.symm
      have hXY : X * Y = Y * X := by
        rw [← hY, ← mul_assoc, hXB, mul_assoc, hXiB, ← mul_assoc]
      have hYiX : Y⁻¹ * X = X * Y⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hXY, mul_assoc, mul_inv_cancel, mul_one]
      have hYBi : Y * B⁻¹ = B := by rw [← hY, mul_inv_cancel_right]
      have hAi : A⁻¹ = X⁻¹ * A := by rw [← hX, mul_inv_rev, inv_mul_cancel_right]
      have tXA := L_rel_tail G _ _ _ _ hXA
      have tXB := L_rel_tail G _ _ _ _ hXB
      have tBX := L_rel_tail G _ _ _ _ hBX
      have tXiA := L_rel_tail G _ _ _ _ hXiA
      have tYA := L_rel_tail G _ _ _ _ hYA
      have tAY := L_rel_tail G _ _ _ _ hAY
      have tYiB := L_rel_tail G _ _ _ _ hYiB
      have tYiA := L_rel_tail G _ _ _ _ hYiA
      have tXiB := L_rel_tail G _ _ _ _ hXiB
      have tBXi := L_rel_tail G _ _ _ _ hBXi
      have tYiX := L_rel_tail G _ _ _ _ hYiX
      have tYBi : ∀ w, Y * (B⁻¹ * w) = B * w := fun w => by rw [← mul_assoc, hYBi]
      have tX : ∀ w, A * (A * w) = X * w := fun w => by rw [← mul_assoc, hX]
      have tY : ∀ w, B * (B * w) = Y * w := fun w => by rw [← mul_assoc, hY]
      refine ⟨hXY, ?_, ?_, hAY, ?_, hBX, ?_, ?_⟩
      · simp only [mul_assoc]
        rw [tXA, tXB, tXiA, hXiB]
      · simp only [mul_assoc]
        rw [tYA, tYiB, tYiA, hYB]
      · rw [eq_inv_mul_iff_mul_eq]
        simp only [mul_assoc]
        rw [tX (B * (A * B)), tBX, tY (A * B), ← tXiA, tAY, tX B, tYiX, inv_mul_cancel_left, hYiB, tY]
        simp
      · rw [eq_inv_mul_iff_mul_eq]
        simp only [mul_assoc]
        rw [tY (A * (B * (A * B))), tAY, tX (B * (A * B)), tXB, tXiA, hXiB, tYiB, tY, mul_inv_cancel_left,
          tX, hBX, mul_inv_cancel_left]
      · simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        rw [tYBi, hAi, tBXi, inv_mul_cancel_left]
  open UnitConjecture in
  have L_rel : ∀ (A B : P) (hA : A = a) (hB : B = b), x * y = y * x ∧ x * z = z * x ∧ y * z = z * y ∧
      A * y = y⁻¹ * A ∧ A * z = z⁻¹ * A ∧
      B * x = x⁻¹ * B ∧ B * z = z⁻¹ * B ∧
      B * A = x⁻¹ * y * z⁻¹ * A * B :=
    fun (A B : P) (hA : A = a) (hB : B = b) => by
      have h1 := PresentedGroup.one_of_mem (show (b⁻¹ * a ^ 2 * b * a ^ 2 : FreeGroup generators) ∈ relations by simp [relations])
      have h2 := PresentedGroup.one_of_mem (show (a⁻¹ * b ^ 2 * a * b ^ 2 : FreeGroup generators) ∈ relations by simp [relations])
      subst hA hB
      simp only [map_mul, map_inv, map_pow] at h1 h2
      exact L_rel_grp P _ _ x y (pow_two _).symm (pow_two _).symm h1 h2
  open UnitConjecture in
  have L_nf_step : ∀ (G : Type) [Group G] (A B : G) (T : ℤ → ℤ → ℤ → G)
      (h1 : ∀ i j k i' j' k' : ℤ, T i j k * T i' j' k' = T (i + i') (j + j') (k + k'))
      (h2 : ∀ i j k : ℤ, A * T i j k = T i (-j) (-k) * A)
      (h3 : ∀ i j k : ℤ, B * T i j k = T (-i) j (-k) * B)
      (hAA : A * A = T 1 0 0) (hBB : B * B = T 0 1 0)
      (hBA : B * A = T (-1) 1 (-1) * (A * B))
      (g : G) (hg : g = A ∨ g = B ∨ ∃ i j k : ℤ, g = T i j k) (i j k : ℤ) (e f : Bool), ∃ c : ℤ × ℤ × ℤ × Bool × Bool,
        T i j k * ((if e then A else 1) * (if f then B else 1)) * g =
          T c.1 c.2.1 c.2.2.1 * ((if c.2.2.2.1 then A else 1) * (if c.2.2.2.2 then B else 1)) :=
    fun (G : Type) [Group G] (A B : G) (T : ℤ → ℤ → ℤ → G)
        (h1 : ∀ i j k i' j' k' : ℤ, T i j k * T i' j' k' = T (i + i') (j + j') (k + k'))
        (h2 : ∀ i j k : ℤ, A * T i j k = T i (-j) (-k) * A)
        (h3 : ∀ i j k : ℤ, B * T i j k = T (-i) j (-k) * B)
        (hAA : A * A = T 1 0 0) (hBB : B * B = T 0 1 0)
        (hBA : B * A = T (-1) 1 (-1) * (A * B))
        (g : G) (hg : g = A ∨ g = B ∨ ∃ i j k : ℤ, g = T i j k) (i j k : ℤ) (e f : Bool) => by
      rcases hg with h | h | ⟨i', j', k', h⟩ <;> rw [h]
      · cases e <;> cases f <;> simp only [if_true, if_false, Bool.false_eq_true, one_mul, mul_one]
        · exact ⟨(i, j, k, true, false), by simp⟩
        · exact ⟨(i + -1, j + 1, k + -1, true, true), by simp [mul_assoc, hBA, ← h1]⟩
        · exact ⟨(i + 1, j + 0, k + 0, false, false), by simp [mul_assoc, hAA, h1]⟩
        · refine ⟨(i + -1 + 1, j + - 1 + 0, k + 1 + 0, false, true), ?_⟩
          simp only [mul_assoc, hBA, if_true, if_false, Bool.false_eq_true, one_mul]
          rw [← mul_assoc A, h2, mul_assoc, ← mul_assoc A A, hAA, ← mul_assoc, ← mul_assoc, h1, h1]
          simp
      · cases e <;> cases f <;> simp only [if_true, if_false, Bool.false_eq_true, one_mul, mul_one]
        · exact ⟨(i, j, k, false, true), by simp⟩
        · exact ⟨(i + 0, j + 1, k + 0, false, false), by simp [mul_assoc, hBB, h1]⟩
        · exact ⟨(i, j, k, true, true), by simp [mul_assoc]⟩
        · refine ⟨(i + 0, j + -1, k + -0, true, false), ?_⟩
          simp only [mul_assoc, hBB, if_true, if_false, Bool.false_eq_true, mul_one]
          rw [h2, ← mul_assoc, h1]
      · cases e <;> cases f <;> simp only [if_true, if_false, Bool.false_eq_true, one_mul, mul_one]
        · exact ⟨(i + i', j + j', k + k', false, false), by simp [h1]⟩
        · exact ⟨(i + -i', j + j', k + -k', false, true), by simp [mul_assoc, h3, ← h1]⟩
        · exact ⟨(i + i', j + -j', k + -k', true, false), by simp [mul_assoc, h2, ← h1]⟩
        · refine ⟨(i + -i', j + -j', k + - -k', true, true), ?_⟩
          simp only [mul_assoc, h3, if_true]
          rw [← mul_assoc A, h2, mul_assoc, ← mul_assoc, h1]
  open UnitConjecture in
  have L_nf : ∀ (g : P), ∃ c : ℤ × ℤ × ℤ × Bool × Bool,
      g = x ^ c.1 * y ^ c.2.1 * z ^ c.2.2.1 * (if c.2.2.2.1 then a else 1 : P) *
        (if c.2.2.2.2 then b else 1 : P) :=
    fun (g : P) => by
      let ι : FreeGroup generators →* P := PresentedGroup.mk relations
      obtain ⟨A, hA⟩ : ∃ A : P, A = ι (FreeGroup.of generators.a) := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B : P, B = ι (FreeGroup.of generators.b) := ⟨_, rfl⟩
      obtain ⟨hxy, hxz, hyz, hAy, hAz, hBx, hBz, hBA⟩ := L_rel A B hA hB
      have hx : x = A * A := by rw [← pow_two, hA]; rfl
      have hy : y = B * B := by rw [← pow_two, hB]; rfl
      have hAx : A * x = x * A := by rw [hx, mul_assoc]
      have hBy : B * y = y * B := by rw [hy, mul_assoc]
      let T : ℤ → ℤ → ℤ → P := fun i j k => x ^ i * y ^ j * z ^ k
      have h1 : ∀ i j k i' j' k' : ℤ, T i j k * T i' j' k' = T (i + i') (j + j') (k + k') := by
        intro i j k i' j' k'
        simp only [T, zpow_add, mul_assoc]
        congr 1
        rw [((Commute.zpow_zpow hxz.symm k i')).left_comm, ((Commute.zpow_zpow hxy.symm j i')).left_comm]
        congr 1
        rw [((Commute.zpow_zpow hyz.symm k j')).left_comm]
      have h2 : ∀ i j k : ℤ, A * T i j k = T i (-j) (-k) * A := by
        intro i j k
        have s1 : SemiconjBy A (x ^ i) (x ^ i) := SemiconjBy.zpow_right (show SemiconjBy A x x from hAx) i
        have s2 : SemiconjBy A (y ^ j) (y⁻¹ ^ j) := SemiconjBy.zpow_right (show SemiconjBy A y y⁻¹ from hAy) j
        have s3 : SemiconjBy A (z ^ k) (z⁻¹ ^ k) := SemiconjBy.zpow_right (show SemiconjBy A z z⁻¹ from hAz) k
        have := (s1.mul_right s2).mul_right s3
        simp only [T]
        rw [this.eq, inv_zpow', inv_zpow']
      have h3 : ∀ i j k : ℤ, B * T i j k = T (-i) j (-k) * B := by
        intro i j k
        have s1 : SemiconjBy B (x ^ i) (x⁻¹ ^ i) := SemiconjBy.zpow_right (show SemiconjBy B x x⁻¹ from hBx) i
        have s2 : SemiconjBy B (y ^ j) (y ^ j) := SemiconjBy.zpow_right (show SemiconjBy B y y from hBy) j
        have s3 : SemiconjBy B (z ^ k) (z⁻¹ ^ k) := SemiconjBy.zpow_right (show SemiconjBy B z z⁻¹ from hBz) k
        have := (s1.mul_right s2).mul_right s3
        simp only [T]
        rw [this.eq, inv_zpow', inv_zpow']
      have hAA : A * A = T 1 0 0 := by simp [T, hx]
      have hBB : B * B = T 0 1 0 := by simp [T, hy]
      have hBA' : B * A = T (-1) 1 (-1) * (A * B) := by rw [hBA]; simp [T, mul_assoc]
      have hAi : A⁻¹ = T (-1) 0 0 * A := by simp [T, hx]
      have hBi : B⁻¹ = T 0 (-1) 0 * B := by simp [T, hy]
      have step := L_nf_step P A B T h1 h2 h3 hAA hBB hBA'
      have key : ∀ w : FreeGroup generators, ∀ (i j k : ℤ) (e f : Bool),
          ∃ c : ℤ × ℤ × ℤ × Bool × Bool,
            T i j k * ((if e then A else 1) * (if f then B else 1)) * ι w =
              T c.1 c.2.1 c.2.2.1 * ((if c.2.2.2.1 then A else 1) * (if c.2.2.2.2 then B else 1)) := by
        intro w
        refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
        · intro i j k e f; exact ⟨(i, j, k, e, f), by simp⟩
        · intro g i j k e f
          cases g
          · rw [← hA]; exact step A (Or.inl rfl) i j k e f
          · rw [← hB]; exact step B (Or.inr (Or.inl rfl)) i j k e f
        · intro g _ i j k e f
          cases g
          · obtain ⟨c, hc⟩ := step (T (-1) 0 0) (Or.inr (Or.inr ⟨_, _, _, rfl⟩)) i j k e f
            obtain ⟨c', hc'⟩ := step A (Or.inl rfl) c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2
            refine ⟨c', ?_⟩
            rw [← hc', ← hc, mul_assoc _ _ A, ← hAi, map_inv, ← hA]
          · obtain ⟨c, hc⟩ := step (T 0 (-1) 0) (Or.inr (Or.inr ⟨_, _, _, rfl⟩)) i j k e f
            obtain ⟨c', hc'⟩ := step B (Or.inr (Or.inl rfl)) c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2
            refine ⟨c', ?_⟩
            rw [← hc', ← hc, mul_assoc _ _ B, ← hBi, map_inv, ← hB]
        · intro u v hu hv i j k e f
          obtain ⟨c, hc⟩ := hu i j k e f
          obtain ⟨c', hc'⟩ := hv c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2
          refine ⟨c', ?_⟩
          rw [← hc', ← hc, map_mul]; simp only [mul_assoc]
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨c, hc⟩ := key w 0 0 0 false false
      refine ⟨c, ?_⟩
      have h0 : T 0 0 0 * ((if false = true then A else 1) * (if false = true then B else 1)) = 1 := by simp [T]
      rw [h0, one_mul] at hc
      change ι w = _
      rw [hc]
      simp only [T, mul_assoc]
      subst hA hB
      rfl
  open UnitConjecture in
  have L_inj : ∀ (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
      (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
      (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1)), Function.Injective (fun g : P => φ g (0, 0, 0)) :=
    fun (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
        (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
        (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1)) => by
      intro g h hgh
      obtain ⟨c, rfl⟩ := L_nf g
      obtain ⟨c', rfl⟩ := L_nf h
      simp only at hgh
      rw [L_act φ hA hB, L_act φ hA hB] at hgh
      obtain ⟨i, j, k, e, f⟩ := c
      obtain ⟨i', j', k', e', f'⟩ := c'
      have key : i = i' ∧ j = j' ∧ k = k' ∧ e = e' ∧ f = f' := by
        cases e <;> cases f <;> cases e' <;> cases f' <;>
          simp only [Prod.mk.injEq, if_true, if_false, Bool.false_eq_true] at hgh <;>
          simp only [and_true, true_and, and_false, false_and, Bool.false_eq_true, Bool.true_eq_false] <;>
          omega
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := key
      rfl
  open UnitConjecture in
  have L_model : ∃ φ : P →* Equiv.Perm (ℤ × ℤ × ℤ),
      (∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2)) ∧
      (∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1)) :=
    by
      let A : Equiv.Perm (ℤ × ℤ × ℤ) :=
        ⟨fun v => (v.1 + 1, -v.2.1 + 1, -v.2.2), fun v => (v.1 - 1, -v.2.1 + 1, -v.2.2),
          fun v => by ext <;> simp <;> omega, fun v => by ext <;> simp <;> omega⟩
      let B : Equiv.Perm (ℤ × ℤ × ℤ) :=
        ⟨fun v => (-v.1, v.2.1 + 1, -v.2.2 + 1), fun v => (-v.1, v.2.1 - 1, -v.2.2 + 1),
          fun v => by ext <;> simp <;> omega, fun v => by ext <;> simp <;> omega⟩
      let f : generators → Equiv.Perm (ℤ × ℤ × ℤ) := fun g => generators.rec A B g
      have hrel : ∀ r ∈ relations, FreeGroup.lift f r = 1 := by
        intro r hr
        simp only [relations, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
        rcases hr with rfl | rfl
        · ext v <;> simp [a, b, f, A, B, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Equiv.Perm.mul_apply,
            pow_two, Equiv.Perm.inv_def] <;> omega
        · ext v <;> simp [a, b, f, A, B, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Equiv.Perm.mul_apply,
            pow_two, Equiv.Perm.inv_def] <;> omega
      refine ⟨PresentedGroup.toGroup hrel, fun v => rfl, fun v => rfl⟩
  open UnitConjecture in
  have L_uexp_aux : ∀ (o X Y XY Z XZ YZ XYZ : R) (t : R), o + (X + (Y + (XY + (Z + (XZ + (YZ + (XYZ + t))))))) =
      o + (Z + (Y + (YZ + (X + (XZ + (XY + (XYZ + t))))))) :=
    fun (o X Y XY Z XZ YZ XYZ : R) (t : R) => by
      ac_rfl
  open UnitConjecture in
  have L_uexp : u = (List.map
      (fun c : ℤ × ℤ × ℤ × Bool × Bool => ((x ^ c.1 * y ^ c.2.1 * z ^ c.2.2.1 *
        (if c.2.2.2.1 then a else 1 : P) * (if c.2.2.2.2 then b else 1 : P) : P) : R))
      [(0, 0, 0, false, false), (0, 0, -1, false, false), (0, 1, 0, false, false), (0, 1, -1, false, false),
       (1, 0, 0, false, false), (1, 0, -1, false, false), (1, 1, 0, false, false), (1, 1, -1, false, false),
       (-1, -1, 0, true, false), (1, 0, 0, true, false), (0, -1, 1, true, false), (0, 0, 1, true, false),
       (0, 0, 0, false, true), (1, 0, 0, false, true), (0, -1, 1, false, true), (1, 1, 1, false, true),
       (0, 0, 0, true, true), (1, 0, -1, true, true), (-1, 0, -1, true, true), (0, 1, -1, true, true),
       (0, -1, -1, true, true)]).sum :=
    by
      simp only [u, p, q, r, s, mul_add, add_mul, one_mul, mul_one, ← map_mul]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zpow_zero, zpow_one,
        zpow_neg, if_true, Bool.false_eq_true, if_false, mul_one, one_mul, Int.reduceNeg, mul_assoc, map_one]
      simp only [add_assoc]
      exact L_uexp_aux _ _ _ _ _ _ _ _ _
  open UnitConjecture in
  have L_nontriv : ∀ (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
      (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
      (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1)), ¬ ∃ g : P, u = g :=
    fun (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
        (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
        (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1)) => by
      rintro ⟨g, hg⟩
      rw [L_uexp] at hg
      have key : ∀ p0 : ℤ × ℤ × ℤ,
          ((Finsupp.applyAddHom p0).comp
            (Finsupp.mapDomain.addMonoidHom (fun h : P => φ h (0, 0, 0)) :
              (P →₀ ZMod 2) →+ (ℤ × ℤ × ℤ →₀ ZMod 2))) (g : R) =
          if φ g (0, 0, 0) = p0 then 1 else 0 := by
        intro p0
        simp [MonoidAlgebra.of_apply, Finsupp.single_apply]
      have keyL : ∀ p0 : ℤ × ℤ × ℤ,
          ((Finsupp.applyAddHom p0).comp
            (Finsupp.mapDomain.addMonoidHom (fun h : P => φ h (0, 0, 0)) :
              (P →₀ ZMod 2) →+ (ℤ × ℤ × ℤ →₀ ZMod 2))) (List.map
        (fun c : ℤ × ℤ × ℤ × Bool × Bool => ((x ^ c.1 * y ^ c.2.1 * z ^ c.2.2.1 *
          (if c.2.2.2.1 then a else 1 : P) * (if c.2.2.2.2 then b else 1 : P) : P) : R))
        [(0, 0, 0, false, false), (0, 0, -1, false, false), (0, 1, 0, false, false), (0, 1, -1, false, false),
         (1, 0, 0, false, false), (1, 0, -1, false, false), (1, 1, 0, false, false), (1, 1, -1, false, false),
         (-1, -1, 0, true, false), (1, 0, 0, true, false), (0, -1, 1, true, false), (0, 0, 1, true, false),
         (0, 0, 0, false, true), (1, 0, 0, false, true), (0, -1, 1, false, true), (1, 1, 1, false, true),
         (0, 0, 0, true, true), (1, 0, -1, true, true), (-1, 0, -1, true, true), (0, 1, -1, true, true),
         (0, -1, -1, true, true)]).sum =
          (List.map (fun c : ℤ × ℤ × ℤ × Bool × Bool =>
            if (if c.2.2.2.1 then
            (if c.2.2.2.2 then ((1 : ℤ) - 0 + 2 * c.1, -0 + 2 * c.2.1, 0 - 1 - 2 * c.2.2.1)
             else (0 + 1 + 2 * c.1, -0 + 1 + 2 * c.2.1, -0 - 2 * c.2.2.1))
          else
            (if c.2.2.2.2 then (-0 + 2 * c.1, 0 + 1 + 2 * c.2.1, -0 + 1 - 2 * c.2.2.1)
             else (0 + 2 * c.1, 0 + 2 * c.2.1, 0 - 2 * c.2.2.1))) = p0 then (1 : ZMod 2) else 0)
        [(0, 0, 0, false, false), (0, 0, -1, false, false), (0, 1, 0, false, false), (0, 1, -1, false, false),
         (1, 0, 0, false, false), (1, 0, -1, false, false), (1, 1, 0, false, false), (1, 1, -1, false, false),
         (-1, -1, 0, true, false), (1, 0, 0, true, false), (0, -1, 1, true, false), (0, 0, 1, true, false),
         (0, 0, 0, false, true), (1, 0, 0, false, true), (0, -1, 1, false, true), (1, 1, 1, false, true),
         (0, 0, 0, true, true), (1, 0, -1, true, true), (-1, 0, -1, true, true), (0, 1, -1, true, true),
         (0, -1, -1, true, true)]).sum := by
        intro p0
        rw [map_list_sum, List.map_map]
        congr 1
        apply List.map_congr_left
        intro c _
        simp only [Function.comp_apply, AddMonoidHom.coe_comp, Finsupp.mapDomain.addMonoidHom_apply,
          Finsupp.applyAddHom_apply, MonoidAlgebra.of_apply]
        rw [Finsupp.mapDomain_single, Finsupp.single_apply, L_act φ hA hB c (0, 0, 0)]
      have h0 := congrArg (fun w => ((Finsupp.applyAddHom ((0, 0, 0) : ℤ × ℤ × ℤ)).comp
            (Finsupp.mapDomain.addMonoidHom (fun h : P => φ h (0, 0, 0)) :
              (P →₀ ZMod 2) →+ (ℤ × ℤ × ℤ →₀ ZMod 2))) w) hg
      have h2 := congrArg (fun w => ((Finsupp.applyAddHom ((2, 0, 0) : ℤ × ℤ × ℤ)).comp
            (Finsupp.mapDomain.addMonoidHom (fun h : P => φ h (0, 0, 0)) :
              (P →₀ ZMod 2) →+ (ℤ × ℤ × ℤ →₀ ZMod 2))) w) hg
      simp only at h0 h2
      rw [keyL, key] at h0 h2
      have e0 : φ g (0, 0, 0) = (0, 0, 0) := by
        by_contra hne
        rw [if_neg hne] at h0
        revert h0
        decide +kernel
      have e2 : φ g (0, 0, 0) = (2, 0, 0) := by
        by_contra hne
        rw [if_neg hne] at h2
        revert h2
        decide +kernel
      rw [e0] at e2
      revert e2
      decide
  open UnitConjecture in
  have L_torsion_iter : ∀ (F : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ) (p : ℤ × ℤ × ℤ → ℤ) (t : ℤ)
      (hF : ∀ w, p (F w) = p w + t) (m : ℕ) (w : ℤ × ℤ × ℤ), p (F^[m] w) = p w + (m : ℤ) * t :=
    fun (F : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ) (p : ℤ × ℤ × ℤ → ℤ) (t : ℤ)
        (hF : ∀ w, p (F w) = p w + t) (m : ℕ) (w : ℤ × ℤ × ℤ) => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Function.iterate_succ_apply', hF, ih]
        push_cast
        rw [Int.add_mul, Int.one_mul, Int.add_assoc]
  open UnitConjecture in
  have L_torsion_fix : ∀ (F : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ) (p : ℤ × ℤ × ℤ → ℤ) (t : ℤ) (m : ℕ)
      (hm : F^[m] (0, 0, 0) = (0, 0, 0)) (hF : ∀ w, p (F w) = p w + t), (m : ℤ) * t = 0 :=
    fun (F : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ) (p : ℤ × ℤ × ℤ → ℤ) (t : ℤ) (m : ℕ)
        (hm : F^[m] (0, 0, 0) = (0, 0, 0)) (hF : ∀ w, p (F w) = p w + t) => by
      have h := L_torsion_iter F p t hF m (0, 0, 0)
      rw [hm] at h
      omega
  open UnitConjecture in
  have L_torsion : ∀ (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
      (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
      (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1)), ∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1 :=
    fun (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
        (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
        (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1)) => by
      intro g n hn hg
      obtain ⟨⟨i, j, k, e, f⟩, rfl⟩ := L_nf g
      have hσ := funext (L_act φ hA hB (i, j, k, e, f))
      have h0 := congrArg (fun g => φ g (0, 0, 0)) hg
      simp only [map_one, Equiv.Perm.one_apply] at h0
      rw [map_pow, Equiv.Perm.coe_pow, hσ] at h0
      have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
      cases e <;> cases f
      · have h1 := L_torsion_fix _ (fun v => v.1) (2 * i) n h0 (fun w => by simp <;> omega)
        have h2 := L_torsion_fix _ (fun v => v.2.1) (2 * j) n h0 (fun w => by simp <;> omega)
        have h3 := L_torsion_fix _ (fun v => v.2.2) (-(2 * k)) n h0 (fun w => by simp <;> omega)
        have e1 := (Int.mul_eq_zero.mp h1).resolve_left hn'
        have e2 := (Int.mul_eq_zero.mp h2).resolve_left hn'
        have e3 := (Int.mul_eq_zero.mp h3).resolve_left hn'
        have hi : i = 0 := by omega
        have hj : j = 0 := by omega
        have hk : k = 0 := by omega
        subst hi hj hk
        simp
      · have h2 := L_torsion_fix _ (fun v => v.2.1) (2 * j + 1) n h0 (fun w => by simp <;> omega)
        have e2 := (Int.mul_eq_zero.mp h2).resolve_left hn'
        omega
      · have h1 := L_torsion_fix _ (fun v => v.1) (2 * i + 1) n h0 (fun w => by simp <;> omega)
        have e1 := (Int.mul_eq_zero.mp h1).resolve_left hn'
        omega
      · have h3 := L_torsion_fix _ (fun v => v.2.2) (-(2 * k + 1)) n h0 (fun w => by simp <;> omega)
        have e3 := (Int.mul_eq_zero.mp h3).resolve_left hn'
        omega
  open UnitConjecture in
  have L_unit : ∀ (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
      (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
      (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1))
      (hinj : Function.Injective (fun g : P => φ g (0, 0, 0))), IsUnit u :=
    fun (φ : P →* Equiv.Perm (ℤ × ℤ × ℤ))
        (hA : ∀ v : ℤ × ℤ × ℤ, φ (a : P) v = (v.1 + 1, -v.2.1 + 1, -v.2.2))
        (hB : ∀ v : ℤ × ℤ × ℤ, φ (b : P) v = (-v.1, v.2.1 + 1, -v.2.2 + 1))
        (hinj : Function.Injective (fun g : P => φ g (0, 0, 0))) => by
      rw [L_uexp]
      have h₁ := L_crit φ (fun c : ℤ × ℤ × ℤ × Bool × Bool => x ^ c.1 * y ^ c.2.1 * z ^ c.2.2.1 *
          (if c.2.2.2.1 then a else 1 : P) * (if c.2.2.2.2 then b else 1 : P))
        (fun (c : ℤ × ℤ × ℤ × Bool × Bool) (v : ℤ × ℤ × ℤ) =>
          (if c.2.2.2.1 then
            (if c.2.2.2.2 then (1 - v.1 + 2 * c.1, -v.2.1 + 2 * c.2.1, v.2.2 - 1 - 2 * c.2.2.1)
             else (v.1 + 1 + 2 * c.1, -v.2.1 + 1 + 2 * c.2.1, -v.2.2 - 2 * c.2.2.1))
          else
            (if c.2.2.2.2 then (-v.1 + 2 * c.1, v.2.1 + 1 + 2 * c.2.1, -v.2.2 + 1 - 2 * c.2.2.1)
             else (v.1 + 2 * c.1, v.2.1 + 2 * c.2.1, v.2.2 - 2 * c.2.2.1))))
        (L_act φ hA hB) hinj
        [(0, 0, 0, false, false), (0, 0, -1, false, false), (0, 1, 0, false, false), (0, 1, -1, false, false),
         (1, 0, 0, false, false), (1, 0, -1, false, false), (1, 1, 0, false, false), (1, 1, -1, false, false),
         (-1, -1, 0, true, false), (1, 0, 0, true, false), (0, -1, 1, true, false), (0, 0, 1, true, false),
         (0, 0, 0, false, true), (1, 0, 0, false, true), (0, -1, 1, false, true), (1, 1, 1, false, true),
         (0, 0, 0, true, true), (1, 0, -1, true, true), (-1, 0, -1, true, true), (0, 1, -1, true, true),
         (0, -1, -1, true, true)]
        [(-2, -1, 0, true, false), (-1, -1, 0, false, false), (-1, -1, 1, false, false), (-1, -1, 1, true, false),
         (-1, 0, 0, false, false), (-1, 0, 0, true, true), (-1, 0, 1, false, false), (-1, 0, 1, true, false),
         (0, -2, 1, false, true), (0, -1, 0, false, false), (0, -1, 0, false, true), (0, -1, 0, true, true),
         (0, -1, 1, false, false), (0, 0, -1, true, true), (0, 0, 0, false, false), (0, 0, 0, true, false),
         (0, 0, 1, false, false), (0, 1, 0, true, true), (1, -1, 0, false, true), (1, 0, 0, true, true),
         (1, 0, 1, false, true)]
        (by decide +kernel)
      have h₂ := L_crit φ (fun c : ℤ × ℤ × ℤ × Bool × Bool => x ^ c.1 * y ^ c.2.1 * z ^ c.2.2.1 *
          (if c.2.2.2.1 then a else 1 : P) * (if c.2.2.2.2 then b else 1 : P))
        (fun (c : ℤ × ℤ × ℤ × Bool × Bool) (v : ℤ × ℤ × ℤ) =>
          (if c.2.2.2.1 then
            (if c.2.2.2.2 then (1 - v.1 + 2 * c.1, -v.2.1 + 2 * c.2.1, v.2.2 - 1 - 2 * c.2.2.1)
             else (v.1 + 1 + 2 * c.1, -v.2.1 + 1 + 2 * c.2.1, -v.2.2 - 2 * c.2.2.1))
          else
            (if c.2.2.2.2 then (-v.1 + 2 * c.1, v.2.1 + 1 + 2 * c.2.1, -v.2.2 + 1 - 2 * c.2.2.1)
             else (v.1 + 2 * c.1, v.2.1 + 2 * c.2.1, v.2.2 - 2 * c.2.2.1))))
        (L_act φ hA hB) hinj
        [(-2, -1, 0, true, false), (-1, -1, 0, false, false), (-1, -1, 1, false, false), (-1, -1, 1, true, false),
         (-1, 0, 0, false, false), (-1, 0, 0, true, true), (-1, 0, 1, false, false), (-1, 0, 1, true, false),
         (0, -2, 1, false, true), (0, -1, 0, false, false), (0, -1, 0, false, true), (0, -1, 0, true, true),
         (0, -1, 1, false, false), (0, 0, -1, true, true), (0, 0, 0, false, false), (0, 0, 0, true, false),
         (0, 0, 1, false, false), (0, 1, 0, true, true), (1, -1, 0, false, true), (1, 0, 0, true, true),
         (1, 0, 1, false, true)]
        [(0, 0, 0, false, false), (0, 0, -1, false, false), (0, 1, 0, false, false), (0, 1, -1, false, false),
         (1, 0, 0, false, false), (1, 0, -1, false, false), (1, 1, 0, false, false), (1, 1, -1, false, false),
         (-1, -1, 0, true, false), (1, 0, 0, true, false), (0, -1, 1, true, false), (0, 0, 1, true, false),
         (0, 0, 0, false, true), (1, 0, 0, false, true), (0, -1, 1, false, true), (1, 1, 1, false, true),
         (0, 0, 0, true, true), (1, 0, -1, true, true), (-1, 0, -1, true, true), (0, 1, -1, true, true),
         (0, -1, -1, true, true)]
        (by decide +kernel)
      exact ⟨⟨_, _, h₁, h₂⟩, rfl⟩
  obtain ⟨φ, hA, hB⟩ := L_model
  exact ⟨L_torsion φ hA hB, L_unit φ hA hB (L_inj φ hA hB), L_nontriv φ hA hB⟩

end Submission
