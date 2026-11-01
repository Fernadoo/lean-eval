import ChallengeDeps
import Submission.Helpers
import Lean

open LeanEval.Combinatorics
open scoped BigOperators

namespace Submission

theorem szemeredi (A : Set ℕ) (h : 0 < upperDensity A) :
    ContainsArbitraryAPs A := by
  run_tac do
    let stx ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic r###"(
  have GRLines_mono : ∀ (k m N : ℕ) (hk : 1 ≤ k)
      (h : ∀ P : (Fin k → Fin N → Fin k) → Prop,
        ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin N),
          (∀ w : Combinatorics.Line (Fin k) (Fin m), P (fun a => V (w a))) ∨
          (∀ w : Combinatorics.Line (Fin k) (Fin m), ¬ P (fun a => V (w a))))
      (n : ℕ) (hn : N ≤ n) (P : (Fin k → Fin n → Fin k) → Prop), ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n),
        (∀ w : Combinatorics.Line (Fin k) (Fin m), P (fun a => V (w a))) ∨
        (∀ w : Combinatorics.Line (Fin k) (Fin m), ¬ P (fun a => V (w a))) :=
    fun (k m N : ℕ) (hk : 1 ≤ k)
        (h : ∀ P : (Fin k → Fin N → Fin k) → Prop,
          ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin N),
            (∀ w : Combinatorics.Line (Fin k) (Fin m), P (fun a => V (w a))) ∨
            (∀ w : Combinatorics.Line (Fin k) (Fin m), ¬ P (fun a => V (w a))))
        (n : ℕ) (hn : N ≤ n) (P : (Fin k → Fin n → Fin k) → Prop) => by
      obtain ⟨V, hV⟩ := h (fun f => P (fun a i => if hi : i.val < N then f a ⟨i.val, hi⟩ else ⟨0, hk⟩))
      let W : Combinatorics.Subspace (Fin m) (Fin k) (Fin n) :=
        ⟨fun i => if hi : i.val < N then V.idxFun ⟨i.val, hi⟩ else Sum.inl ⟨0, hk⟩, fun e => by
          obtain ⟨i, hi⟩ := V.proper e
          exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hn⟩, by simp [hi]⟩⟩
      have key : ∀ w : Combinatorics.Line (Fin k) (Fin m), (fun a => W (w a)) =
          (fun a i => if hi : i.val < N then V (w a) ⟨i.val, hi⟩ else ⟨0, hk⟩) := by
        intro w
        funext a i
        by_cases hi : i.val < N
        · simp [W, hi, Combinatorics.Subspace.coe_apply]
        · simp [W, hi, Combinatorics.Subspace.coe_apply]
      refine ⟨W, ?_⟩
      rcases hV with hV | hV
      · left
        intro w
        rw [key]
        exact hV w
      · right
        intro w
        rw [key]
        exact hV w
  have GRLines_first_var : ∀ (k M : ℕ) (κ : Type) [Finite κ], ∃ N : ℕ, ∀ c : (Fin k → Fin N → Fin k) → κ,
        ∃ Z : Combinatorics.Subspace (Fin (M + 1)) (Fin k) (Fin N), ∃ col : κ,
          ∀ w : Combinatorics.Line (Fin k) (Fin (M + 1)), w.idxFun 0 = none →
            c (fun a => Z (w a)) = col :=
    fun (k M : ℕ) (κ : Type) [Finite κ] => by
      obtain ⟨N, hN⟩ :=
        Combinatorics.Subspace.exists_mono_in_high_dimension_fin (Fin (k + 1)) κ (Fin (M + 1))
      refine ⟨N, fun c => ?_⟩
      obtain ⟨ζ, col, hζ⟩ :=
        hN (fun x => c (fun a i => if h : (x i).val < k then ⟨(x i).val, h⟩ else a))
      let Z : Combinatorics.Subspace (Fin (M + 1)) (Fin k) (Fin N) :=
        ⟨fun i => Sum.elim (fun b => if h : b.val < k then Sum.inl ⟨b.val, h⟩ else Sum.inr 0)
          Sum.inr (ζ.idxFun i), fun e => by
          obtain ⟨i, hi⟩ := ζ.proper e
          exact ⟨i, by simp [hi]⟩⟩
      refine ⟨Z, col, fun w hw => ?_⟩
      have key : (fun a => Z (w a)) = (fun a i =>
          if h : ((ζ (fun j => (w.idxFun j).elim (Fin.last k) Fin.castSucc)) i).val < k then
            ⟨((ζ (fun j => (w.idxFun j).elim (Fin.last k) Fin.castSucc)) i).val, h⟩ else a) := by
        funext a i
        cases hζi : ζ.idxFun i with
        | inl b =>
          by_cases hb : b.val < k
          · simp [Z, hζi, hb, Combinatorics.Subspace.coe_apply]
          · simp [Z, hζi, hb, Combinatorics.Subspace.coe_apply, hw]
        | inr j =>
          cases hwj : w.idxFun j with
          | none => simp [Z, hζi, hwj, Combinatorics.Subspace.coe_apply]
          | some b => simp [Z, hζi, hwj, Combinatorics.Subspace.coe_apply]
      rw [key]
      exact hζ _
  have GRLines_subspace_comp : ∀ (k a b n : ℕ)
      (Y : Combinatorics.Subspace (Fin b) (Fin k) (Fin n))
      (U : Combinatorics.Subspace (Fin a) (Fin k) (Fin b)), ∃ V : Combinatorics.Subspace (Fin a) (Fin k) (Fin n), ∀ x : Fin a → Fin k, V x = Y (U x) :=
    fun (k a b n : ℕ)
        (Y : Combinatorics.Subspace (Fin b) (Fin k) (Fin n))
        (U : Combinatorics.Subspace (Fin a) (Fin k) (Fin b)) => by
      refine ⟨⟨fun i => Sum.elim Sum.inl U.idxFun (Y.idxFun i), fun e => ?_⟩, fun x => ?_⟩
      · obtain ⟨j, hj⟩ := U.proper e
        obtain ⟨i, hi⟩ := Y.proper j
        exact ⟨i, by simp [hi, hj]⟩
      · funext i
        cases hi : Y.idxFun i with
        | inl c => simp [hi, Combinatorics.Subspace.coe_apply]
        | inr j => simp [hi, Combinatorics.Subspace.coe_apply]
  have GRLines_prefix : ∀ (k L : ℕ) (κ : Type) [Finite κ], ∃ N : ℕ, ∀ c : (Fin k → Fin N → Fin k) → κ,
        ∃ Y : Combinatorics.Subspace (Fin L) (Fin k) (Fin N),
          ∀ w w' : Combinatorics.Line (Fin k) (Fin L), ∀ j : Fin L,
            w.idxFun j = none → w'.idxFun j = none →
            (∀ i : Fin L, i < j → w.idxFun i ≠ none ∧ w.idxFun i = w'.idxFun i) →
            c (fun a => Y (w a)) = c (fun a => Y (w' a)) :=
    fun (k L : ℕ) (κ : Type) [Finite κ] => by
      induction L generalizing κ with
      | zero =>
        refine ⟨0, fun c => ⟨⟨Fin.elim0, fun e => e.elim0⟩, fun w w' j => j.elim0⟩⟩
      | succ L IH =>
        obtain ⟨NL, hL⟩ := IH (Fin k → κ)
        obtain ⟨N, hN⟩ := GRLines_first_var k NL κ
        refine ⟨N, fun c => ?_⟩
        obtain ⟨Z, col, hZ⟩ := hN c
        let c' : (Fin k → Fin NL → Fin k) → (Fin k → κ) := fun f b =>
          c (fun a => Z (Fin.cons (α := fun _ => Fin k) b (f a)))
        obtain ⟨Y', hY'⟩ := hL c'
        let Y0 : Combinatorics.Subspace (Fin (L + 1)) (Fin k) (Fin (NL + 1)) :=
          ⟨Fin.cons (α := fun _ => Fin k ⊕ Fin (L + 1)) (Sum.inr 0)
            (fun i => Sum.map id Fin.succ (Y'.idxFun i)), fun e => by
            refine Fin.cases ⟨0, rfl⟩ (fun s => ?_) e
            obtain ⟨i, hi⟩ := Y'.proper s
            exact ⟨i.succ, by simp [hi]⟩⟩
        have hY0 : ∀ x : Fin (L + 1) → Fin k,
            Y0 x = Fin.cons (α := fun _ => Fin k) (x 0) (Y' (fun i => x i.succ)) := by
          intro x
          funext i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp [Y0, Combinatorics.Subspace.coe_apply]
          · cases hi : Y'.idxFun i with
            | inl b => simp [Y0, hi, Combinatorics.Subspace.coe_apply]
            | inr e => simp [Y0, hi, Combinatorics.Subspace.coe_apply]
        obtain ⟨Y, hY⟩ := GRLines_subspace_comp k (L + 1) (NL + 1) N Z Y0
        refine ⟨Y, ?_⟩
        have hfirst : ∀ w : Combinatorics.Line (Fin k) (Fin (L + 1)), w.idxFun 0 = none →
            c (fun a => Z (Y0 (w a))) = col := by
          intro w hw
          let u : Combinatorics.Line (Fin k) (Fin (NL + 1)) :=
            ⟨fun i => (Y0.idxFun i).elim some w.idxFun, ⟨0, by simp [Y0, hw]⟩⟩
          have hu : (fun a => Z (Y0 (w a))) = fun a => Z (u a) := by
            funext a
            congr 1
            funext i
            cases hi : Y0.idxFun i with
            | inl b => simp [u, hi, Combinatorics.Subspace.coe_apply]
            | inr e => simp [u, hi, Combinatorics.Subspace.coe_apply]
          rw [hu]
          exact hZ u (by simp [u, Y0, hw])
        have htail : ∀ w : Combinatorics.Line (Fin k) (Fin (L + 1)), ∀ b : Fin k,
            w.idxFun 0 = some b → ∀ h : ∃ i : Fin L, w.idxFun i.succ = none,
            c (fun a => Z (Y0 (w a))) =
              c' (fun a => Y' ((⟨fun i => w.idxFun i.succ, h⟩ :
                Combinatorics.Line (Fin k) (Fin L)) a)) b := by
          intro w b hb h
          simp only [c']
          congr 1
          funext a
          rw [hY0]
          congr 2
          simp [hb]
        intro w w' j hw hw' hpre
        have e1 : (fun a => Y (w a)) = fun a => Z (Y0 (w a)) := by funext a; exact hY _
        have e2 : (fun a => Y (w' a)) = fun a => Z (Y0 (w' a)) := by funext a; exact hY _
        rw [e1, e2]
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨s, rfl⟩
        · rw [hfirst w hw, hfirst w' hw']
        · obtain ⟨hne, heq⟩ := hpre 0 (Fin.succ_pos s)
          obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
          have hb' : w'.idxFun 0 = some b := heq ▸ hb
          rw [htail w b hb ⟨s, hw⟩, htail w' b hb' ⟨s, hw'⟩]
          exact congrFun (hY' _ _ s hw hw' (fun i hi =>
            hpre i.succ (Fin.succ_lt_succ_iff.mpr hi))) b
  have GRL_line_comp : ∀ (k a n : ℕ) (V : Combinatorics.Subspace (Fin a) (Fin k) (Fin n))
      (w : Combinatorics.Line (Fin k) (Fin a)), ∃ u : Combinatorics.Line (Fin k) (Fin n),
        (∀ i, u.idxFun i = (V.idxFun i).elim some w.idxFun) ∧ ∀ x, u x = V (w x) :=
    fun (k a n : ℕ) (V : Combinatorics.Subspace (Fin a) (Fin k) (Fin n))
        (w : Combinatorics.Line (Fin k) (Fin a)) => by
      refine ⟨⟨fun i => (V.idxFun i).elim some w.idxFun, ?_⟩, fun i => rfl, fun x => ?_⟩
      · obtain ⟨e, he⟩ := w.proper
        obtain ⟨i, hi⟩ := V.proper e
        exact ⟨i, by simp [hi, he]⟩
      · funext i
        cases hi : V.idxFun i with
        | inl b => simp [hi, Combinatorics.Subspace.coe_apply]
        | inr e => simp [hi, Combinatorics.Subspace.coe_apply]
  have GRLines_level : ∀ (k : ℕ) (hk : 1 ≤ k) (M : ℕ) (κ : Type) [Finite κ], ∃ L : ℕ, ∀ F : (Fin k → Fin L → Fin k) → κ,
        (∀ w w' : Combinatorics.Line (Fin k) (Fin L), ∀ j : Fin L,
            w.idxFun j = none → w'.idxFun j = none →
            (∀ i : Fin L, i < j → w.idxFun i ≠ none ∧ w.idxFun i = w'.idxFun i) →
            F (fun a => w a) = F (fun a => w' a)) →
        ∃ U : Combinatorics.Subspace (Fin M) (Fin k) (Fin L), ∃ g : Fin M → κ,
          ∀ w : Combinatorics.Line (Fin k) (Fin M), ∀ t : Fin M,
            w.idxFun t = none → (∀ s : Fin M, s < t → w.idxFun s ≠ none) →
            F (fun a => U (w a)) = g t :=
    fun (k : ℕ) (hk : 1 ≤ k) (M : ℕ) (κ : Type) [Finite κ] => by
      induction M with
      | zero =>
        refine ⟨0, fun F _ => ⟨⟨Fin.elim0, fun e => e.elim0⟩, Fin.elim0, fun w t => t.elim0⟩⟩
      | succ M ih =>
        obtain ⟨L', hL'⟩ := ih
        obtain ⟨H, hH⟩ := Combinatorics.Subspace.exists_mono_in_high_dimension_fin (Fin k)
          ((Fin k → Fin L' → Fin k) → κ) (Fin 1)
        refine ⟨H + L', fun F hF => ?_⟩
        obtain ⟨ζ, col0, hζ⟩ := hH (fun x f => F (fun a => Fin.append x (f a)))
        let a₀ : Fin k := ⟨0, hk⟩
        let x₀ : Fin H → Fin k := ζ (fun _ => a₀)
        -- F* is prefix-determined
        have hFs : ∀ w w' : Combinatorics.Line (Fin k) (Fin L'), ∀ j : Fin L',
              w.idxFun j = none → w'.idxFun j = none →
              (∀ i : Fin L', i < j → w.idxFun i ≠ none ∧ w.idxFun i = w'.idxFun i) →
              F (fun a => Fin.append x₀ (w a)) = F (fun a => Fin.append x₀ (w' a)) := by
          intro w w' j hw hw' hpre
          let ext : Combinatorics.Line (Fin k) (Fin L') → Combinatorics.Line (Fin k) (Fin (H + L')) :=
            fun v => ⟨Fin.append (fun i => some (x₀ i)) v.idxFun, by
              obtain ⟨e, he⟩ := v.proper
              exact ⟨Fin.natAdd H e, by simp [he]⟩⟩
          have hext : ∀ v : Combinatorics.Line (Fin k) (Fin L'),
              (fun a => Fin.append x₀ (v a)) = (fun a => ext v a) := by
            intro v
            funext a i
            refine Fin.addCases (fun i => ?_) (fun i => ?_) i
            · simp [ext]
            · simp [ext]
          rw [hext w, hext w']
          refine hF (ext w) (ext w') (Fin.natAdd H j) (by simp [ext, hw]) (by simp [ext, hw']) ?_
          intro i hi
          revert hi
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i
          · intro _
            simp [ext]
          · intro hi
            have hi' : i < j := by
              rw [Fin.lt_def] at hi ⊢
              simp at hi
              exact hi
            simpa [ext] using hpre i hi'
        obtain ⟨U', g', hU'⟩ := hL' (fun f => F (fun a => Fin.append x₀ (f a))) hFs
        let U : Combinatorics.Subspace (Fin (M + 1)) (Fin k) (Fin (H + L')) :=
          ⟨Fin.append (fun i => Sum.map id (fun _ => (0 : Fin (M + 1))) (ζ.idxFun i))
            (fun i => Sum.map id Fin.succ (U'.idxFun i)), fun e => by
              refine Fin.cases ?_ (fun e => ?_) e
              · obtain ⟨i, hi⟩ := ζ.proper 0
                exact ⟨Fin.castAdd L' i, by simp [hi]⟩
              · obtain ⟨i, hi⟩ := U'.proper e
                exact ⟨Fin.natAdd H i, by simp [hi]⟩⟩
        have hUx : ∀ x : Fin (M + 1) → Fin k,
            U x = Fin.append (ζ (fun _ => x 0)) (U' (Fin.tail x)) := by
          intro x
          funext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i
          · cases hi : ζ.idxFun i with
            | inl b => simp [U, hi, Combinatorics.Subspace.coe_apply]
            | inr e => simp [U, hi, Combinatorics.Subspace.coe_apply]
          · cases hi : U'.idxFun i with
            | inl b => simp [U, hi, Combinatorics.Subspace.coe_apply]
            | inr e => simp [U, hi, Combinatorics.Subspace.coe_apply, Fin.tail]
        have hUl : ∀ i, U.idxFun (Fin.castAdd L' i) = Sum.map id (fun _ => (0 : Fin (M + 1))) (ζ.idxFun i) := by
          intro i
          simp only [U, Fin.append_left]
        let diag : Combinatorics.Line (Fin k) (Fin (M + 1)) := ⟨fun _ => none, ⟨0, rfl⟩⟩
        refine ⟨U, Fin.cases (F (fun a => U (diag a))) g', fun w t ht hmin => ?_⟩
        obtain ⟨u, hu1, hu2⟩ := GRL_line_comp k (M + 1) (H + L') U w
        refine Fin.cases (motive := fun t => w.idxFun t = none → (∀ s : Fin (M + 1), s < t → w.idxFun s ≠ none) →
          F (fun a => U (w a)) = Fin.cases (F (fun a => U (diag a))) g' t) ?_ (fun s => ?_) t ht hmin
        · beta_reduce
          intro h0 _
          obtain ⟨u', hu1', hu2'⟩ := GRL_line_comp k (M + 1) (H + L') U diag
          simp only [Fin.cases_zero]
          have e1 : (fun a => U (w a)) = (fun a => u a) := by funext a; rw [hu2]
          have e2 : (fun a => U (diag a)) = (fun a => u' a) := by funext a; rw [hu2']
          rw [e1, e2]
          obtain ⟨p, hp, hpmin⟩ := WellFounded.has_min wellFounded_lt
            {i : Fin H | ζ.idxFun i = Sum.inr 0} (ζ.proper 0)
          have hp' : ζ.idxFun p = Sum.inr 0 := hp
          refine hF u u' (Fin.castAdd L' p) (by rw [hu1, hUl, hp']; exact h0)
            (by rw [hu1', hUl, hp']; rfl) ?_
          intro i hi
          revert hi
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i
          · intro hi
            have hi' : i < p := hi
            have hne : ζ.idxFun i ≠ Sum.inr 0 := fun h => hpmin i h hi'
            cases hz : ζ.idxFun i with
            | inl b => rw [hu1, hu1', hUl, hz]; simp
            | inr e =>
              exact absurd (by rw [hz, Subsingleton.elim e 0]) hne
          · intro hi
            exfalso
            rw [Fin.lt_def] at hi
            simp at hi
            omega
        · beta_reduce
          intro hs hmin'
          simp only [Fin.cases_succ]
          obtain ⟨b, hb⟩ : ∃ b, w.idxFun 0 = some b := by
            cases h : w.idxFun 0 with
            | none => exact absurd h (hmin' 0 (Fin.succ_pos s))
            | some b => exact ⟨b, rfl⟩
          let tw : Combinatorics.Line (Fin k) (Fin M) := ⟨fun i => w.idxFun i.succ, ⟨s, hs⟩⟩
          have e1 : (fun a => U (w a)) = (fun a => Fin.append (ζ (fun _ => b)) (U' (tw a))) := by
            funext a
            rw [hUx]
            congr 1
            · congr 1
              funext _
              simp [hb]
          rw [e1]
          have h1 := hζ (fun _ => b)
          have h2 := hζ (fun _ => a₀)
          have e2 := congrFun (h1.trans h2.symm) (fun a => U' (tw a))
          simp only at e2
          rw [e2]
          exact hU' tw s hs (fun s' hs' => hmin' s'.succ (Fin.succ_lt_succ_iff.mpr hs'))
  have GRLines_pigeon : ∀ (k m : ℕ) (hk : 1 ≤ k) (κ : Type) [Finite κ], ∃ M : ℕ, ∀ G : (Fin k → Fin M → Fin k) → κ, ∀ g : Fin M → κ,
        (∀ w : Combinatorics.Line (Fin k) (Fin M), ∀ t : Fin M,
            w.idxFun t = none → (∀ s : Fin M, s < t → w.idxFun s ≠ none) →
            G (fun a => w a) = g t) →
        ∃ E : Combinatorics.Subspace (Fin m) (Fin k) (Fin M), ∃ col : κ,
          ∀ w : Combinatorics.Line (Fin k) (Fin m), G (fun a => E (w a)) = col :=
    fun (k m : ℕ) (hk : 1 ≤ k) (κ : Type) [Finite κ] => by
      classical
      cases nonempty_fintype κ
      refine ⟨Fintype.card κ * m, fun G g hG => ?_⟩
      haveI : Nonempty κ := ⟨G (fun _ _ => ⟨0, hk⟩)⟩
      obtain ⟨col, hcol⟩ := Fintype.exists_le_card_fiber_of_mul_le_card g (n := m) (by simp)
      obtain ⟨s, hsS, hscard⟩ := Finset.exists_subset_card_eq hcol
      set e := s.orderIsoOfFin hscard with he
      let E : Combinatorics.Subspace (Fin m) (Fin k) (Fin (Fintype.card κ * m)) :=
        ⟨fun i => if h : i ∈ s then Sum.inr (e.symm ⟨i, h⟩) else Sum.inl ⟨0, hk⟩,
          fun t => ⟨(e t : Fin _), by simp⟩⟩
      refine ⟨E, col, fun w => ?_⟩
      obtain ⟨t₀, ht₀, hmin⟩ := WellFounded.has_min wellFounded_lt {t | w.idxFun t = none}
        ⟨_, w.proper.choose_spec⟩
      have ht₀' : w.idxFun t₀ = none := ht₀
      let u : Combinatorics.Line (Fin k) (Fin (Fintype.card κ * m)) :=
        ⟨fun i => if h : i ∈ s then w.idxFun (e.symm ⟨i, h⟩) else some ⟨0, hk⟩,
          ⟨(e t₀ : Fin _), by simp [ht₀']⟩⟩
      have hu : (fun a => E (w a)) = (fun a => u a) := by
        funext a i
        by_cases h : i ∈ s
        · simp [E, u, h, Combinatorics.Subspace.coe_apply]
        · simp [E, u, h, Combinatorics.Subspace.coe_apply]
      rw [hu]
      have hcolt : g (e t₀ : Fin _) = col := by
        have := hsS (e t₀).2
        simpa using this
      rw [← hcolt]
      refine hG u (e t₀) (by simp [u, ht₀']) (fun s' hs' => ?_)
      by_cases h : s' ∈ s
      · simp only [u, h, dite_true]
        intro hnone
        have hlt : e.symm ⟨s', h⟩ < t₀ := by
          rw [OrderIso.symm_apply_lt]
          exact hs'
        exact hmin _ hnone hlt
      · simp [u, h]
  have GRLines_col : ∀ (k m : ℕ) (hk : 1 ≤ k) (κ : Type) [Finite κ], ∃ N : ℕ, ∀ c : (Fin k → Fin N → Fin k) → κ,
        ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin N), ∃ col : κ,
          ∀ w : Combinatorics.Line (Fin k) (Fin m), c (fun a => V (w a)) = col :=
    fun (k m : ℕ) (hk : 1 ≤ k) (κ : Type) [Finite κ] => by
      obtain ⟨M, hM⟩ := GRLines_pigeon k m hk κ
      obtain ⟨L, hL⟩ := GRLines_level k hk M κ
      obtain ⟨N, hN⟩ := GRLines_prefix k L κ
      refine ⟨N, fun c => ?_⟩
      obtain ⟨Y, hY⟩ := hN c
      obtain ⟨U, g, hU⟩ := hL (fun f => c (fun a => Y (f a))) hY
      obtain ⟨E, col, hE⟩ := hM (fun f => c (fun a => Y (U (f a)))) g hU
      obtain ⟨YU, hYU⟩ := GRLines_subspace_comp k M L N Y U
      obtain ⟨V, hV⟩ := GRLines_subspace_comp k m M N YU E
      refine ⟨V, col, fun w => ?_⟩
      have h1 : (fun a => V (w a)) = (fun a => Y (U (E (w a)))) := by
        funext a
        rw [hV, hYU]
      rw [h1]
      exact hE w
  have GRLines : ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : (Fin k → Fin n → Fin k) → Prop,
        ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n),
          (∀ w : Combinatorics.Line (Fin k) (Fin m), P (fun a => V (w a))) ∨
          (∀ w : Combinatorics.Line (Fin k) (Fin m), ¬ P (fun a => V (w a))) :=
    fun (k m : ℕ) (hk : 1 ≤ k) => by
      obtain ⟨N, hN⟩ := GRLines_col k m hk Prop
      refine ⟨N, fun n hn P => GRLines_mono k m N hk (fun Q => ?_) n hn P⟩
      obtain ⟨V, col, hV⟩ := hN Q
      refine ⟨V, ?_⟩
      by_cases hc : col
      · left
        intro w
        rw [hV w]
        exact hc
      · right
        intro w
        rw [hV w]
        exact hc
  have Uniformize_bound : ∀ (K n L : ℕ) (hL : L ≤ n) (p : Fin n → Fin K)
      (A : Finset (Fin n → Fin K)), (A.filter (fun x => ∀ i : Fin n, i.val < L → x i = p i)).card ≤ K ^ (n - L) :=
    fun (K n L : ℕ) (hL : L ≤ n) (p : Fin n → Fin K)
        (A : Finset (Fin n → Fin K)) => by
      classical
      calc (A.filter (fun x => ∀ i : Fin n, i.val < L → x i = p i)).card
          ≤ (Finset.univ : Finset (Fin (n - L) → Fin K)).card := by
            apply Finset.card_le_card_of_injOn
              (fun x => fun t : Fin (n - L) => x ⟨L + t.val, by have := t.isLt; omega⟩)
            · intro x _; exact Finset.mem_univ _
            · intro x hx y hy hxy
              simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
              funext i
              by_cases hi : i.val < L
              · rw [hx.2 i hi, hy.2 i hi]
              · have := congrFun hxy ⟨i.val - L, by omega⟩
                simp only at this
                have e : (⟨L + (i.val - L), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
                rw [e] at this
                exact this
        _ = K ^ (n - L) := by simp
  have Uniformize_split : ∀ (K n L m : ℕ) (hLm : L + m ≤ n) (p : Fin n → Fin K)
      (A : Finset (Fin n → Fin K)), ((A.filter (fun x => ∀ i : Fin n, i.val < L → x i = p i)).card : ℝ) =
        ∑ a : Fin m → Fin K,
          ((A.filter (fun x => (∀ i : Fin n, i.val < L → x i = p i) ∧
              ∀ t : Fin m, x (Fin.castLE hLm (Fin.natAdd L t)) = a t)).card : ℝ) :=
    fun (K n L m : ℕ) (hLm : L + m ≤ n) (p : Fin n → Fin K)
        (A : Finset (Fin n → Fin K)) => by
      classical
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun x => fun t : Fin m => x (Fin.castLE hLm (Fin.natAdd L t)))
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      push_cast
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.filter_filter]
      simp only [funext_iff]
  have Uniformize_next : ∀ (K n L m : ℕ) (hLm : L + m ≤ n) (p : Fin n → Fin K)
      (A : Finset (Fin n → Fin K)) (a : Fin m → Fin K), ∃ p' : Fin n → Fin K,
        A.filter (fun x => ∀ i : Fin n, i.val < L + m → x i = p' i) =
        A.filter (fun x => (∀ i : Fin n, i.val < L → x i = p i) ∧
              ∀ t : Fin m, x (Fin.castLE hLm (Fin.natAdd L t)) = a t) :=
    fun (K n L m : ℕ) (hLm : L + m ≤ n) (p : Fin n → Fin K)
        (A : Finset (Fin n → Fin K)) (a : Fin m → Fin K) => by
      classical
      refine ⟨fun i => if h : i.val < L then p i
        else if h' : i.val < L + m then a ⟨i.val - L, by omega⟩ else p i, ?_⟩
      apply Finset.filter_congr
      intro x _
      constructor
      · intro hx
        refine ⟨fun i hi => ?_, fun t => ?_⟩
        · rw [hx i (by omega)]; simp [hi]
        · rw [hx _ (by simp)]
          simp
      · rintro ⟨h1, h2⟩ i hi
        by_cases hiL : i.val < L
        · simp [hiL, h1 i hiL]
        · simp only [hiL, hi, dif_neg, not_false_eq_true, dif_pos]
          have := h2 ⟨i.val - L, by omega⟩
          have e : Fin.castLE hLm (Fin.natAdd L ⟨i.val - L, by omega⟩) = i :=
            Fin.ext (by simp; omega)
          rw [e] at this; exact this
  have Uniformize_phi : ∀ (K n L m : ℕ) (hLm : L + m ≤ n) (p : Fin n → Fin K)
      (A : Finset (Fin n → Fin K)), ∃ Φ : Combinatorics.Subspace (Fin m ⊕ Fin (n - (L + m))) (Fin K) (Fin n),
        ∀ a : Fin m → Fin K,
          (Finset.univ.filter (fun y : Fin (n - (L + m)) → Fin K => Φ (Sum.elim a y) ∈ A)).card =
            (A.filter (fun x => (∀ i : Fin n, i.val < L → x i = p i) ∧
              ∀ t : Fin m, x (Fin.castLE hLm (Fin.natAdd L t)) = a t)).card :=
    fun (K n L m : ℕ) (hLm : L + m ≤ n) (p : Fin n → Fin K)
        (A : Finset (Fin n → Fin K)) => by
      classical
      let idx : Fin n → Fin K ⊕ (Fin m ⊕ Fin (n - (L + m))) := fun i =>
        if h : i.val < L then Sum.inl (p i)
        else if h' : i.val < L + m then Sum.inr (Sum.inl ⟨i.val - L, by omega⟩)
        else Sum.inr (Sum.inr ⟨i.val - (L + m), by omega⟩)
      have hproper : ∀ e, ∃ i, idx i = Sum.inr e := by
        rintro (t | s)
        · refine ⟨⟨L + t.val, by have := t.isLt; omega⟩, ?_⟩
          have h1 : ¬ (L + t.val < L) := by omega
          have h2 : L + t.val < L + m := by have := t.isLt; omega
          simp only [idx, h1, h2, dif_neg, dif_pos, not_false_eq_true]
          congr 2
          ext; simp
        · refine ⟨⟨L + m + s.val, by have := s.isLt; omega⟩, ?_⟩
          have h1 : ¬ (L + m + s.val < L) := by omega
          have h2 : ¬ (L + m + s.val < L + m) := by omega
          simp only [idx, h1, h2, dif_neg, not_false_eq_true]
          congr 2
          ext; simp
      let Φ : Combinatorics.Subspace (Fin m ⊕ Fin (n - (L + m))) (Fin K) (Fin n) := ⟨idx, hproper⟩
      have hev : ∀ (a : Fin m → Fin K) (y : Fin (n - (L + m)) → Fin K) (i : Fin n),
          Φ (Sum.elim a y) i = if h : i.val < L then p i
            else if h' : i.val < L + m then a ⟨i.val - L, by omega⟩
            else y ⟨i.val - (L + m), by omega⟩ := by
        intro a y i
        simp only [Φ, Combinatorics.Subspace.coe_apply, idx]
        split_ifs <;> rfl
      refine ⟨Φ, fun a => ?_⟩
      apply Finset.card_nbij' (fun y => Φ (Sum.elim a y))
        (fun x => fun s => x ⟨L + m + s.val, by have := s.isLt; omega⟩)
      · intro y hy
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
        refine ⟨hy, fun i hi => ?_, fun t => ?_⟩
        · rw [hev]; simp [hi]
        · rw [hev]
          have h1 : ¬ ((Fin.castLE hLm (Fin.natAdd L t)).val < L) := by simp
          have h2 : (Fin.castLE hLm (Fin.natAdd L t)).val < L + m := by simp
          rw [dif_neg h1, dif_pos h2]
          congr 1; ext; simp
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
        obtain ⟨hxA, h1, h2⟩ := hx
        convert hxA using 1
        funext i
        rw [hev]
        by_cases hiL : i.val < L
        · rw [dif_pos hiL, h1 i hiL]
        · rw [dif_neg hiL]
          by_cases hiLm : i.val < L + m
          · rw [dif_pos hiLm]
            have := h2 ⟨i.val - L, by omega⟩
            have e : Fin.castLE hLm (Fin.natAdd L ⟨i.val - L, by omega⟩) = i :=
              Fin.ext (by simp; omega)
            rw [e] at this; exact this.symm
          · rw [dif_neg hiLm]
            congr 1; ext; simp; omega
      · intro y _
        funext s
        simp only
        rw [hev]
        have h1 : ¬ (L + m + s.val < L) := by omega
        have h2 : ¬ (L + m + s.val < L + m) := by omega
        simp only [h1, h2, dif_neg, not_false_eq_true]
        congr 1; ext; simp
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
        obtain ⟨hxA, h1, h2⟩ := hx
        funext i
        simp only
        rw [hev]
        by_cases hiL : i.val < L
        · rw [dif_pos hiL, h1 i hiL]
        · rw [dif_neg hiL]
          by_cases hiLm : i.val < L + m
          · rw [dif_pos hiLm]
            have := h2 ⟨i.val - L, by omega⟩
            have e : Fin.castLE hLm (Fin.natAdd L ⟨i.val - L, by omega⟩) = i :=
              Fin.ext (by simp; omega)
            rw [e] at this; exact this.symm
          · rw [dif_neg hiLm]
            congr 1; ext; simp; omega
  have Uniformize : ∀ (K m : ℕ) (hK : 1 ≤ K) (ε : ℝ) (hε : 0 < ε), ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin K),
        ∃ q : ℕ, ∃ Φ : Combinatorics.Subspace (Fin m ⊕ Fin q) (Fin K) (Fin n),
          ∀ a : Fin m → Fin K,
            ((A.card : ℝ) / (K : ℝ) ^ n - ε) * (K : ℝ) ^ q ≤
              ((Finset.univ.filter (fun y : Fin q → Fin K => Φ (Sum.elim a y) ∈ A)).card : ℝ) :=
    fun (K m : ℕ) (hK : 1 ≤ K) (ε : ℝ) (hε : 0 < ε) => by
      classical
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
      set P : ℝ := (K : ℝ) ^ m with hP
      have hPpos : 0 < P := pow_pos hKpos m
      set ρ : ℝ := ε / P with hρ
      have hρpos : 0 < ρ := div_pos hε hPpos
      have hρP : ρ * P = ε := by rw [hρ]; field_simp
      obtain ⟨T, hT⟩ := exists_nat_gt (1 / ρ)
      have hTρ : 1 < (T : ℝ) * ρ := by
        have := (div_lt_iff₀ hρpos).1 hT
        linarith
      refine ⟨T * m, fun n hn A => ?_⟩
      set β : ℝ := (A.card : ℝ) / (K : ℝ) ^ n with hβ
      have hβ0 : 0 ≤ β := by positivity
      have claim : ∀ t : ℕ, ∀ j : ℕ, j + t = T → ∀ p : Fin n → Fin K,
          (β + (j : ℝ) * ρ) * (K : ℝ) ^ (n - j * m) ≤
            ((A.filter (fun x => ∀ i : Fin n, i.val < j * m → x i = p i)).card : ℝ) →
          ∃ q : ℕ, ∃ Φ : Combinatorics.Subspace (Fin m ⊕ Fin q) (Fin K) (Fin n),
            ∀ a : Fin m → Fin K,
              (β - ε) * (K : ℝ) ^ q ≤
                ((Finset.univ.filter (fun y : Fin q → Fin K => Φ (Sum.elim a y) ∈ A)).card : ℝ) := by
        intro t
        induction t with
        | zero =>
          intro j hj p hp
          simp only [add_zero] at hj
          subst hj
          have hb := Uniformize_bound K n (j * m) hn p A
          have hb' : ((A.filter (fun x => ∀ i : Fin n, i.val < j * m → x i = p i)).card : ℝ) ≤
              (K : ℝ) ^ (n - j * m) := by exact_mod_cast hb
          have hR : 0 < (K : ℝ) ^ (n - j * m) := pow_pos hKpos _
          nlinarith
        | succ t ih =>
          intro j hj p hp
          have hjT : j + 1 ≤ T := by omega
          have hLm : j * m + m ≤ n := by
            have : (j + 1) * m ≤ T * m := Nat.mul_le_mul_right m hjT
            rw [add_mul, one_mul] at this; omega
          by_cases hall : ∀ a : Fin m → Fin K, (β - ε) * (K : ℝ) ^ (n - (j * m + m)) ≤
              ((A.filter (fun x => (∀ i : Fin n, i.val < j * m → x i = p i) ∧
                ∀ t : Fin m, x (Fin.castLE hLm (Fin.natAdd (j * m) t)) = a t)).card : ℝ)
          · obtain ⟨Φ, hΦ⟩ := Uniformize_phi K n (j * m) m hLm p A
            refine ⟨n - (j * m + m), Φ, fun a => ?_⟩
            rw [hΦ a]; exact hall a
          · push_neg at hall
            obtain ⟨a₀, ha₀⟩ := hall
            set R : ℝ := (K : ℝ) ^ (n - (j * m + m)) with hR
            have hRpos : 0 < R := pow_pos hKpos _
            have hpow : (K : ℝ) ^ (n - j * m) = P * R := by
              rw [hP, hR, ← pow_add]; congr 1; omega
            have hex : ∃ a : Fin m → Fin K, (β + ((j : ℝ) + 1) * ρ) * R ≤
              ((A.filter (fun x => (∀ i : Fin n, i.val < j * m → x i = p i) ∧
                ∀ t : Fin m, x (Fin.castLE hLm (Fin.natAdd (j * m) t)) = a t)).card : ℝ) := by
              by_contra hcon
              push_neg at hcon
              have hsplit := Uniformize_split K n (j * m) m hLm p A
              set F : (Fin m → Fin K) → ℝ := fun a =>
                ((A.filter (fun x => (∀ i : Fin n, i.val < j * m → x i = p i) ∧
                  ∀ t : Fin m, x (Fin.castLE hLm (Fin.natAdd (j * m) t)) = a t)).card : ℝ) with hF
              set c : ℝ := (β + ((j : ℝ) + 1) * ρ) * R with hc
              have hsingle : c - F a₀ ≤ ∑ a, (c - F a) :=
                Finset.single_le_sum (f := fun a => c - F a)
                  (fun a _ => by have := hcon a; linarith) (Finset.mem_univ a₀)
              have hsum : ∑ a, (c - F a) = P * c - ∑ a, F a := by
                rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
                  Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, hP]
                push_cast; ring
              rw [hpow, hsplit] at hp
              have h1 : ρ * P * R = ε * R := by rw [hρP]
              have h2 : 0 < ρ * R := mul_pos hρpos hRpos
              have h3 : 0 ≤ (j : ℝ) * ρ * R := by positivity
              rw [hc] at hsingle hsum
              nlinarith
            obtain ⟨a, ha⟩ := hex
            obtain ⟨p', hp'⟩ := Uniformize_next K n (j * m) m hLm p A a
            apply ih (j + 1) (by omega) p'
            have e1 : (j + 1) * m = j * m + m := by ring
            rw [e1, hp']
            push_cast
            exact ha
      obtain ⟨q, Φ, hΦ⟩ := claim T 0 (by simp) (fun _ => ⟨0, hK⟩) (by
        simp only [Nat.cast_zero, zero_mul, add_zero, Nat.sub_zero, not_lt_zero', false_imp_iff,
          implies_true, Finset.filter_true]
        rw [hβ, div_mul_cancel₀]
        exact (pow_pos hKpos n).ne')
      exact ⟨q, Φ, hΦ⟩
  have ManyLines_lineCount : ∀ (k m : ℕ), ((Finset.univ.filter (fun f : Fin m → Option (Fin k) => ∃ r : Fin m, f r = none)).card : ℝ) =
        ((k : ℝ) + 1) ^ m - (k : ℝ) ^ m :=
    fun (k m : ℕ) => by
      have h1 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin m → Option (Fin k)))) (fun f => ∃ r : Fin m, f r = none)
      have h2 : Finset.univ.filter (fun f : Fin m → Option (Fin k) => ¬ ∃ r : Fin m, f r = none) =
          Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Option (Fin k))).erase none) := by
        ext f
        simp [Fintype.mem_piFinset]
      rw [h2, Fintype.card_piFinset] at h1
      simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_option,
        Fintype.card_fin, Finset.prod_const, Fintype.card_pi, Nat.add_sub_cancel] at h1
      have h3 : (((Finset.univ.filter (fun f : Fin m → Option (Fin k) => ∃ r : Fin m, f r = none)).card
          + k ^ m : ℕ) : ℝ) = (((k + 1) ^ m : ℕ) : ℝ) := by
        rw [h1]
      push_cast at h3
      linarith
  have ManyLines_powGap : ∀ (k m : ℕ) (hm : 1 ≤ m), (1 : ℝ) ≤ ((k : ℝ) + 1) ^ m - (k : ℝ) ^ m :=
    fun (k m : ℕ) (hm : 1 ≤ m) => by
      have h : k ^ m < (k + 1) ^ m := Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by omega)
      have h' : ((k ^ m + 1 : ℕ) : ℝ) ≤ (((k + 1) ^ m : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
  have ManyLines_fixTail : ∀ (K m q n : ℕ)
      (Φ : Combinatorics.Subspace (Fin m ⊕ Fin q) (Fin K) (Fin n)) (y : Fin q → Fin K), ∃ W : Combinatorics.Subspace (Fin m) (Fin K) (Fin n),
        ∀ x : Fin m → Fin K, W x = Φ (Sum.elim x y) :=
    fun (K m q n : ℕ)
        (Φ : Combinatorics.Subspace (Fin m ⊕ Fin q) (Fin K) (Fin n)) (y : Fin q → Fin K) => by
      refine ⟨⟨fun i => (Φ.idxFun i).elim Sum.inl
        (fun s => s.elim Sum.inr (fun t => Sum.inl (y t))), ?_⟩, ?_⟩
      · intro j
        obtain ⟨i, hi⟩ := Φ.proper (Sum.inl j)
        exact ⟨i, by simp [hi]⟩
      · intro x
        funext i
        simp only [Combinatorics.Subspace.coe_apply]
        rcases h : Φ.idxFun i with c | (j | t) <;> simp
  have ManyLines_comp : ∀ (K m G n : ℕ) (Ψ : Combinatorics.Subspace (Fin G) (Fin K) (Fin n))
      (V : Combinatorics.Subspace (Fin m) (Fin K) (Fin G)), ∃ W : Combinatorics.Subspace (Fin m) (Fin K) (Fin n), ∀ x : Fin m → Fin K, W x = Ψ (V x) :=
    fun (K m G n : ℕ) (Ψ : Combinatorics.Subspace (Fin G) (Fin K) (Fin n))
        (V : Combinatorics.Subspace (Fin m) (Fin K) (Fin G)) => by
      refine ⟨⟨fun i => (Ψ.idxFun i).elim Sum.inl V.idxFun, ?_⟩, ?_⟩
      · intro j
        obtain ⟨g, hg⟩ := V.proper j
        obtain ⟨i, hi⟩ := Ψ.proper g
        exact ⟨i, by simp [hi, hg]⟩
      · intro x
        funext i
        simp only [Combinatorics.Subspace.coe_apply]
        rcases h : Ψ.idxFun i with c | g <;> simp [Combinatorics.Subspace.coe_apply]
  have ManyLines_lineComp : ∀ (K m G : ℕ) (V : Combinatorics.Subspace (Fin m) (Fin K) (Fin G))
      (l : Combinatorics.Line (Fin K) (Fin m)), ∃ L : Combinatorics.Line (Fin K) (Fin G), ∀ a : Fin K, L a = V (l a) :=
    fun (K m G : ℕ) (V : Combinatorics.Subspace (Fin m) (Fin K) (Fin G))
        (l : Combinatorics.Line (Fin K) (Fin m)) => by
      refine ⟨⟨fun i => (V.idxFun i).elim some l.idxFun, ?_⟩, ?_⟩
      · obtain ⟨j, hj⟩ := l.proper
        obtain ⟨i, hi⟩ := V.proper j
        exact ⟨i, by simp [hi, hj]⟩
      · intro a
        funext i
        rw [Combinatorics.Line.coe_apply, Combinatorics.Subspace.coe_apply]
        cases h : V.idxFun i with
        | inl c => simp [h]
        | inr j => simp [h, Combinatorics.Line.coe_apply]
  have ManyLines_lift : ∀ (k m G : ℕ) (V : Combinatorics.Subspace (Fin m) (Fin k) (Fin G)), ∃ U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin G),
        ∀ x : Fin m → Fin k, U (fun r => Fin.castSucc (x r)) = fun i => Fin.castSucc (V x i) :=
    fun (k m G : ℕ) (V : Combinatorics.Subspace (Fin m) (Fin k) (Fin G)) => by
      refine ⟨⟨fun i => (V.idxFun i).elim (fun c => Sum.inl (Fin.castSucc c)) Sum.inr, ?_⟩, ?_⟩
      · intro j
        obtain ⟨i, hi⟩ := V.proper j
        exact ⟨i, by simp [hi]⟩
      · intro x
        funext i
        simp only [Combinatorics.Subspace.coe_apply]
        rcases h : V.idxFun i with c | j <;> simp
  have ManyLines_subSubspace : ∀ (k m₀ m : ℕ) (hk : 1 ≤ k) (hm : m₀ ≤ m), Nonempty (Combinatorics.Subspace (Fin m₀) (Fin k) (Fin m)) :=
    fun (k m₀ m : ℕ) (hk : 1 ≤ k) (hm : m₀ ≤ m) => by
      refine ⟨⟨fun r => if h : r.val < m₀ then Sum.inr ⟨r.val, h⟩ else Sum.inl ⟨0, hk⟩, ?_⟩⟩
      intro j
      refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hm⟩, ?_⟩
      simp [j.isLt]
  have ManyLines_avg : ∀ (k q : ℕ) (g h : (Fin q → Fin (k + 1)) → ℝ) (s L α θ η : ℝ)
      (hs : 0 < s) (hL : 0 < L) (hη : 0 < η) (hηθ : η < θ / 2) (hθ : θ ≤ 1)
      (hg : (α - η ^ 2 / 2) * s * ((k : ℝ) + 1) ^ q ≤ ∑ y, g y)
      (hg' : ∀ y, g y < (α + η ^ 2 / 2) * s)
      (hh : θ * L * ((k : ℝ) + 1) ^ q ≤ ∑ y, h y)
      (hh' : ∀ y, h y ≤ L), ∃ y, (α - 2 * η) * s ≤ g y ∧ θ / 2 * L ≤ h y :=
    fun (k q : ℕ) (g h : (Fin q → Fin (k + 1)) → ℝ) (s L α θ η : ℝ)
        (hs : 0 < s) (hL : 0 < L) (hη : 0 < η) (hηθ : η < θ / 2) (hθ : θ ≤ 1)
        (hg : (α - η ^ 2 / 2) * s * ((k : ℝ) + 1) ^ q ≤ ∑ y, g y)
        (hg' : ∀ y, g y < (α + η ^ 2 / 2) * s)
        (hh : θ * L * ((k : ℝ) + 1) ^ q ≤ ∑ y, h y)
        (hh' : ∀ y, h y ≤ L) => by
      by_contra hcon
      push_neg at hcon
      have hθpos : 0 < θ := by linarith
      have hc1 : 0 < 1 - θ / 2 := by linarith
      have hpt : ∀ y, (1 - θ / 2) * L * (g y - (α + η ^ 2 / 2) * s) + 2 * η * s * (h y - L) ≤
          -(2 * η * s * ((1 - θ / 2) * L)) := by
        intro y
        have h1 := hg' y
        have h2 := hh' y
        by_cases hc : (α - 2 * η) * s ≤ g y
        · have h3 := hcon y hc
          have e1 : (1 - θ / 2) * L * (g y - (α + η ^ 2 / 2) * s) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
          have e2 : 2 * η * s * (h y - L) ≤ 2 * η * s * (-((1 - θ / 2) * L)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          linarith
        · push_neg at hc
          have e1 : (1 - θ / 2) * L * (g y - (α + η ^ 2 / 2) * s) ≤ (1 - θ / 2) * L * (-(2 * η * s)) :=
            mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
          have e2 : 2 * η * s * (h y - L) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
          linarith
      have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Fin q → Fin (k + 1)))) => hpt y)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hsum
      simp only [nsmul_eq_mul] at hsum
      push_cast at hsum
      set T : ℝ := ((k : ℝ) + 1) ^ q with hT
      have hTpos : 0 < T := by positivity
      have i1 : (1 - θ / 2) * L * (-(η ^ 2 * s * T)) ≤
          (1 - θ / 2) * L * (∑ y, g y - T * ((α + η ^ 2 / 2) * s)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have i2 : 2 * η * s * (-((1 - θ) * L * T)) ≤ 2 * η * s * (∑ y, h y - T * L) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have key : 0 < s * L * T * η * (θ - (1 - θ / 2) * η) := by
        have : 0 < θ - (1 - θ / 2) * η := by nlinarith
        positivity
      nlinarith [i1, i2, hsum, key]
  have ManyLines_lemma8 : ∀ (k m q n : ℕ) (hm : 1 ≤ m)
      (W : (Fin q → Fin (k + 1)) → Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
      (A : Finset (Fin n → Fin (k + 1))) (α θ η : ℝ) (hη : 0 < η) (hηθ : η < θ / 2) (hθ : θ ≤ 1)
      (ha : ∀ u : Fin m → Fin (k + 1), (α - η ^ 2 / 2) * ((k : ℝ) + 1) ^ q ≤
        ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) => W y u ∈ A)).card : ℝ))
      (hb : ∀ f : Fin m → Option (Fin k), (∃ r : Fin m, f r = none) →
        θ * ((k : ℝ) + 1) ^ q ≤ ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
          ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ))
      (hno : ∀ X : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => X x ∈ A)).card : ℝ) <
          (α + η ^ 2 / 2) * ((k : ℝ) + 1) ^ m), ∃ y : Fin q → Fin (k + 1),
        (α - 2 * η) * ((k : ℝ) + 1) ^ m ≤
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => W y x ∈ A)).card : ℝ) ∧
          θ / 2 * (((k : ℝ) + 1) ^ m - (k : ℝ) ^ m) ≤
            ((Finset.univ.filter (fun f : Fin m → Option (Fin k) =>
              (∃ r : Fin m, f r = none) ∧
              ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ) :=
    fun (k m q n : ℕ) (hm : 1 ≤ m)
        (W : (Fin q → Fin (k + 1)) → Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
        (A : Finset (Fin n → Fin (k + 1))) (α θ η : ℝ) (hη : 0 < η) (hηθ : η < θ / 2) (hθ : θ ≤ 1)
        (ha : ∀ u : Fin m → Fin (k + 1), (α - η ^ 2 / 2) * ((k : ℝ) + 1) ^ q ≤
          ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) => W y u ∈ A)).card : ℝ))
        (hb : ∀ f : Fin m → Option (Fin k), (∃ r : Fin m, f r = none) →
          θ * ((k : ℝ) + 1) ^ q ≤ ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
            ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ))
        (hno : ∀ X : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => X x ∈ A)).card : ℝ) <
            (α + η ^ 2 / 2) * ((k : ℝ) + 1) ^ m) => by
      have hs : (0 : ℝ) < ((k : ℝ) + 1) ^ m := by positivity
      have hLc := ManyLines_powGap k m hm
      obtain ⟨Ls, hLs⟩ : ∃ Ls : Finset (Fin m → Option (Fin k)),
          Ls = Finset.univ.filter (fun f : Fin m → Option (Fin k) => ∃ r : Fin m, f r = none) :=
        ⟨_, rfl⟩
      have hLs_card : (Ls.card : ℝ) = ((k : ℝ) + 1) ^ m - (k : ℝ) ^ m := by
        rw [hLs]; exact ManyLines_lineCount k m
      refine ManyLines_avg k q
        (fun y => ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => W y x ∈ A)).card : ℝ))
        (fun y => ((Finset.univ.filter (fun f : Fin m → Option (Fin k) =>
                (∃ r : Fin m, f r = none) ∧
                ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ))
        (((k : ℝ) + 1) ^ m) (((k : ℝ) + 1) ^ m - (k : ℝ) ^ m) α θ η hs (by linarith) hη hηθ hθ
        ?_ (fun y => hno (W y)) ?_ ?_
      · beta_reduce
        have e : (∑ y : Fin q → Fin (k + 1),
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => W y x ∈ A)).card : ℝ)) =
            ∑ x : Fin m → Fin (k + 1),
              ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) => W y x ∈ A)).card : ℝ) := by
          have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := (Finset.univ : Finset (Fin q → Fin (k + 1))))
            (t := (Finset.univ : Finset (Fin m → Fin (k + 1))))
            (r := fun y x => W y x ∈ A)
          simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at this
          exact_mod_cast this
        rw [e]
        calc (α - η ^ 2 / 2) * ((k : ℝ) + 1) ^ m * ((k : ℝ) + 1) ^ q
            = ∑ _x : Fin m → Fin (k + 1), (α - η ^ 2 / 2) * ((k : ℝ) + 1) ^ q := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
          _ ≤ _ := Finset.sum_le_sum (fun x _ => ha x)
      · beta_reduce
        have e : ∀ y : Fin q → Fin (k + 1), (Finset.univ.filter (fun f : Fin m → Option (Fin k) =>
                (∃ r : Fin m, f r = none) ∧
                ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)) =
              Ls.filter (fun f => ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A) := by
          intro y
          rw [hLs, Finset.filter_filter]
        simp only [e]
        have e2 := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := (Finset.univ : Finset (Fin q → Fin (k + 1)))) (t := Ls)
            (r := fun y f => ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)
        simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at e2
        have e3 : (∑ y : Fin q → Fin (k + 1), ((Ls.filter (fun f =>
              ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ)) =
            ∑ f ∈ Ls, ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
              ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ) := by
          exact_mod_cast e2
        rw [e3]
        calc θ * (((k : ℝ) + 1) ^ m - (k : ℝ) ^ m) * ((k : ℝ) + 1) ^ q
            = ∑ _f ∈ Ls, θ * ((k : ℝ) + 1) ^ q := by
              rw [Finset.sum_const, nsmul_eq_mul, hLs_card]
              ring
          _ ≤ _ := Finset.sum_le_sum (fun f hf => by
              rw [hLs, Finset.mem_filter] at hf
              exact hb f hf.2)
      · intro y
        beta_reduce
        rw [← hLs_card]
        have hsub : (Finset.univ.filter (fun f : Fin m → Option (Fin k) =>
                (∃ r : Fin m, f r = none) ∧
                ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)) ⊆ Ls := by
          intro f hf
          rw [Finset.mem_filter] at hf
          rw [hLs, Finset.mem_filter]
          exact ⟨hf.1, hf.2.1⟩
        exact_mod_cast Finset.card_le_card hsub
  have ManyLines_goodLine : ∀ (k m₀ q : ℕ) (hk : 1 ≤ k) (hm₀ : 1 ≤ m₀) (δ' θ : ℝ) (hδ' : 0 < δ')
      (hθ : θ * (((k : ℝ) + 1) ^ m₀ - (k : ℝ) ^ m₀) = δ' / 4)
      (hDHJ : ∀ B : Finset (Fin m₀ → Fin k), δ' / 4 * (k : ℝ) ^ m₀ ≤ (B.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin k) (Fin m₀), ∀ a : Fin k, l a ∈ B)
      (R : (Fin m₀ → Fin k) → Finset (Fin q → Fin (k + 1)))
      (hR : ∀ x, δ' / 2 * ((k : ℝ) + 1) ^ q ≤ ((R x).card : ℝ)), ∃ l : Combinatorics.Line (Fin k) (Fin m₀),
        θ * ((k : ℝ) + 1) ^ q ≤
          ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) => ∀ a : Fin k, y ∈ R (l a))).card : ℝ) :=
    fun (k m₀ q : ℕ) (hk : 1 ≤ k) (hm₀ : 1 ≤ m₀) (δ' θ : ℝ) (hδ' : 0 < δ')
        (hθ : θ * (((k : ℝ) + 1) ^ m₀ - (k : ℝ) ^ m₀) = δ' / 4)
        (hDHJ : ∀ B : Finset (Fin m₀ → Fin k), δ' / 4 * (k : ℝ) ^ m₀ ≤ (B.card : ℝ) →
          ∃ l : Combinatorics.Line (Fin k) (Fin m₀), ∀ a : Fin k, l a ∈ B)
        (R : (Fin m₀ → Fin k) → Finset (Fin q → Fin (k + 1)))
        (hR : ∀ x, δ' / 2 * ((k : ℝ) + 1) ^ q ≤ ((R x).card : ℝ)) => by
      have hT : (0 : ℝ) < ((k : ℝ) + 1) ^ q := by positivity
      have hkpos : (0 : ℝ) < (k : ℝ) ^ m₀ := by
        have : (0 : ℝ) < k := by exact_mod_cast hk
        positivity
      obtain ⟨B, hB⟩ : ∃ B : Finset (Fin q → Fin (k + 1)), B = Finset.univ.filter (fun y =>
          δ' / 4 * (k : ℝ) ^ m₀ ≤ ((Finset.univ.filter (fun x : Fin m₀ → Fin k => y ∈ R x)).card : ℝ)) :=
        ⟨_, rfl⟩
      have hdc : (∑ y : Fin q → Fin (k + 1),
          ((Finset.univ.filter (fun x : Fin m₀ → Fin k => y ∈ R x)).card : ℝ)) =
          ∑ x : Fin m₀ → Fin k, ((R x).card : ℝ) := by
        have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := (Finset.univ : Finset (Fin q → Fin (k + 1))))
            (t := (Finset.univ : Finset (Fin m₀ → Fin k)))
            (r := fun y x => y ∈ R x)
        simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, Finset.filter_univ_mem] at this
        exact_mod_cast this
      have hlow : (k : ℝ) ^ m₀ * (δ' / 2 * ((k : ℝ) + 1) ^ q) ≤ ∑ x : Fin m₀ → Fin k, ((R x).card : ℝ) := by
        calc (k : ℝ) ^ m₀ * (δ' / 2 * ((k : ℝ) + 1) ^ q)
            = ∑ _x : Fin m₀ → Fin k, δ' / 2 * ((k : ℝ) + 1) ^ q := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
          _ ≤ _ := Finset.sum_le_sum (fun x _ => hR x)
      have hpt : ∀ y : Fin q → Fin (k + 1),
          ((Finset.univ.filter (fun x : Fin m₀ → Fin k => y ∈ R x)).card : ℝ) ≤
            (k : ℝ) ^ m₀ * (if y ∈ B then 1 else 0) + δ' / 4 * (k : ℝ) ^ m₀ := by
        intro y
        have hle : ((Finset.univ.filter (fun x : Fin m₀ → Fin k => y ∈ R x)).card : ℝ) ≤
            (k : ℝ) ^ m₀ := by
          have := Finset.card_le_univ (Finset.univ.filter (fun x : Fin m₀ → Fin k => y ∈ R x))
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
          exact_mod_cast this
        by_cases hy : y ∈ B
        · rw [if_pos hy]
          have : 0 ≤ δ' / 4 * (k : ℝ) ^ m₀ := by positivity
          linarith
        · rw [if_neg hy]
          rw [hB, Finset.mem_filter] at hy
          push_neg at hy
          have := hy (Finset.mem_univ _)
          linarith
      have hup := Finset.sum_le_sum
        (fun y (_ : y ∈ (Finset.univ : Finset (Fin q → Fin (k + 1)))) => hpt y)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul,
        Finset.filter_univ_mem, hdc] at hup
      push_cast at hup
      have hBcard : δ' / 4 * ((k : ℝ) + 1) ^ q ≤ (B.card : ℝ) := by
        have : (k : ℝ) ^ m₀ * (δ' / 4 * ((k : ℝ) + 1) ^ q) ≤ (k : ℝ) ^ m₀ * (B.card : ℝ) := by
          nlinarith
        exact le_of_mul_le_mul_left this hkpos
      have hL : ∀ y : Fin q → Fin (k + 1), ∃ l : Combinatorics.Line (Fin k) (Fin m₀),
          y ∈ B → ∀ a : Fin k, y ∈ R (l a) := by
        intro y
        by_cases hy : y ∈ B
        · have hy' := hy
          rw [hB, Finset.mem_filter] at hy'
          obtain ⟨l, hl⟩ := hDHJ _ hy'.2
          exact ⟨l, fun _ a => (Finset.mem_filter.mp (hl a)).2⟩
        · exact ⟨⟨fun _ => none, ⟨⟨0, hm₀⟩, rfl⟩⟩, fun h => absurd h hy⟩
      choose Lf hLf using hL
      obtain ⟨Ls, hLs⟩ : ∃ Ls : Finset (Fin m₀ → Option (Fin k)),
          Ls = Finset.univ.filter (fun f : Fin m₀ → Option (Fin k) => ∃ r : Fin m₀, f r = none) :=
        ⟨_, rfl⟩
      have hLs_card : (Ls.card : ℝ) = ((k : ℝ) + 1) ^ m₀ - (k : ℝ) ^ m₀ := by
        rw [hLs]; exact ManyLines_lineCount k m₀
      have hmaps : ∀ y ∈ B, (Lf y).idxFun ∈ Ls := by
        intro y _
        rw [hLs, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (Lf y).proper⟩
      have hne : Ls.Nonempty := ⟨fun _ => none, by
        rw [hLs, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, ⟨⟨0, hm₀⟩, rfl⟩⟩⟩
      have hcardcond : Ls.card • (θ * ((k : ℝ) + 1) ^ q) ≤ (B.card : ℝ) := by
        rw [nsmul_eq_mul, hLs_card]
        calc (((k : ℝ) + 1) ^ m₀ - (k : ℝ) ^ m₀) * (θ * ((k : ℝ) + 1) ^ q)
            = δ' / 4 * ((k : ℝ) + 1) ^ q := by rw [← hθ]; ring
          _ ≤ _ := hBcard
      obtain ⟨f₀, hf₀, hfib⟩ :=
        Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps hne hcardcond
      have hf₀' : ∃ r : Fin m₀, f₀ r = none := by
        rw [hLs, Finset.mem_filter] at hf₀
        exact hf₀.2
      refine ⟨⟨f₀, hf₀'⟩, le_trans hfib ?_⟩
      have hsub : B.filter (fun y => (Lf y).idxFun = f₀) ⊆
          Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
            ∀ a : Fin k, y ∈ R ((⟨f₀, hf₀'⟩ : Combinatorics.Line (Fin k) (Fin m₀)) a)) := by
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun a => ?_⟩
        have h1 := hLf y hy.1 a
        have h2 : Lf y = ⟨f₀, hf₀'⟩ := Combinatorics.Line.ext hy.2
        rw [h2] at h1
        exact h1
      exact_mod_cast Finset.card_le_card hsub
  have ManyLines_lemma7 : ∀ (k : ℕ) (hk : 1 ≤ k) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (δ' θ : ℝ)
      (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1)
      (hθ : θ * (((k : ℝ) + 1) ^ m₀ - (k : ℝ) ^ m₀) = δ' / 4)
      (hDHJ : ∀ B : Finset (Fin m₀ → Fin k), δ' / 4 * (k : ℝ) ^ m₀ ≤ (B.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin k) (Fin m₀), ∀ a : Fin k, l a ∈ B)
      (η : ℝ) (hη : 0 < η) (hηθ : η < θ / 2) (m : ℕ) (hm : m₀ ≤ m), ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ α : ℝ, δ' ≤ α → ∀ A : Finset (Fin n → Fin (k + 1)),
        α * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
        ∃ q : ℕ, ∃ W : (Fin q → Fin (k + 1)) → Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          (∀ u : Fin m → Fin (k + 1), (α - η ^ 2 / 2) * ((k : ℝ) + 1) ^ q ≤
            ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) => W y u ∈ A)).card : ℝ)) ∧
          (∀ f : Fin m → Option (Fin k), (∃ r : Fin m, f r = none) →
            θ * ((k : ℝ) + 1) ^ q ≤ ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
              ∀ a : Fin k, W y (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ)) :=
    fun (k : ℕ) (hk : 1 ≤ k) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (δ' θ : ℝ)
        (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1)
        (hθ : θ * (((k : ℝ) + 1) ^ m₀ - (k : ℝ) ^ m₀) = δ' / 4)
        (hDHJ : ∀ B : Finset (Fin m₀ → Fin k), δ' / 4 * (k : ℝ) ^ m₀ ≤ (B.card : ℝ) →
          ∃ l : Combinatorics.Line (Fin k) (Fin m₀), ∀ a : Fin k, l a ∈ B)
        (η : ℝ) (hη : 0 < η) (hηθ : η < θ / 2) (m : ℕ) (hm : m₀ ≤ m) => by
      obtain ⟨G, hG⟩ := GRLines k m hk
      obtain ⟨N, hN⟩ := Uniformize (k + 1) G (by omega) (η ^ 2 / 2) (by positivity)
      refine ⟨N, fun n hn α hα A hA => ?_⟩
      obtain ⟨q, Φ, hΦ⟩ := hN n hn A
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      simp only [hcast] at hΦ
      have hTn : (0 : ℝ) < ((k : ℝ) + 1) ^ n := by positivity
      have hT : (0 : ℝ) < ((k : ℝ) + 1) ^ q := by positivity
      have hdens : α ≤ (A.card : ℝ) / ((k : ℝ) + 1) ^ n := by
        rw [le_div_iff₀ hTn]; exact hA
      have hfib : ∀ a : Fin G → Fin (k + 1), (α - η ^ 2 / 2) * ((k : ℝ) + 1) ^ q ≤
          ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) => Φ (Sum.elim a y) ∈ A)).card : ℝ) :=
        fun a => le_trans (mul_le_mul_of_nonneg_right (by linarith) hT.le) (hΦ a)
      obtain ⟨V, hV⟩ := hG G le_rfl (fun ℓ => θ * ((k : ℝ) + 1) ^ q ≤
          ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
            ∀ a : Fin k, Φ (Sum.elim (fun i => Fin.castSucc (ℓ a i)) y) ∈ A)).card : ℝ))
      have hgood : ∀ w : Combinatorics.Line (Fin k) (Fin m), θ * ((k : ℝ) + 1) ^ q ≤
          ((Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
            ∀ a : Fin k, Φ (Sum.elim (fun i => Fin.castSucc (V (w a) i)) y) ∈ A)).card : ℝ) := by
        rcases hV with hV | hV
        · exact hV
        · exfalso
          obtain ⟨Z⟩ := ManyLines_subSubspace k m₀ m hk hm
          have hθpos : 0 < θ := by linarith
          have hgap := ManyLines_powGap k m₀ hm₀
          have hθle : θ ≤ δ' / 4 := by nlinarith
          have hηsq : η ^ 2 / 2 ≤ δ' / 2 := by
            have h1 : η ≤ 1 := by linarith
            have h2 : η ^ 2 ≤ η := by nlinarith
            linarith
          obtain ⟨l, hl⟩ := ManyLines_goodLine k m₀ q hk hm₀ δ' θ hδ' hθ hDHJ
            (fun x => Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
              Φ (Sum.elim (fun i => Fin.castSucc (V (Z x) i)) y) ∈ A))
            (fun x => le_trans (mul_le_mul_of_nonneg_right (by linarith) hT.le) (hfib _))
          obtain ⟨w, hw⟩ := ManyLines_lineComp k m₀ m Z l
          apply hV w
          beta_reduce
          have e : (Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
              ∀ a : Fin k, Φ (Sum.elim (fun i => Fin.castSucc (V (w a) i)) y) ∈ A)) =
              (Finset.univ.filter (fun y : Fin q → Fin (k + 1) => ∀ a : Fin k,
                y ∈ Finset.univ.filter (fun y : Fin q → Fin (k + 1) =>
                  Φ (Sum.elim (fun i => Fin.castSucc (V (Z (l a)) i)) y) ∈ A))) := by
            ext y
            simp [hw]
          rw [e]
          exact hl
      obtain ⟨U, hU⟩ := ManyLines_lift k m G V
      have hW : ∀ y : Fin q → Fin (k + 1), ∃ W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          ∀ x, W x = Φ (Sum.elim (U x) y) := by
        intro y
        obtain ⟨Ψ, hΨ⟩ := ManyLines_fixTail (k + 1) G q n Φ y
        obtain ⟨W, hW⟩ := ManyLines_comp (k + 1) m G n Ψ U
        exact ⟨W, fun x => by rw [hW, hΨ]⟩
      choose W hW using hW
      refine ⟨q, W, ?_, ?_⟩
      · intro u
        simp only [hW]
        exact hfib (U u)
      · intro f hf
        have h1 := hgood ⟨f, hf⟩
        have e : ∀ (y : Fin q → Fin (k + 1)) (a : Fin k), W y (fun r => Fin.castSucc ((f r).getD a)) =
            Φ (Sum.elim (fun i => Fin.castSucc
              (V ((⟨f, hf⟩ : Combinatorics.Line (Fin k) (Fin m)) a) i)) y) := by
          intro y a
          rw [hW]
          have h2 := hU (fun r => (f r).getD a)
          exact congrArg (fun z => Φ (Sum.elim z y)) h2
        simp only [e]
        exact h1
  have ManyLines : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (δ : ℝ) (hδ : 0 < δ), ∃ θ : ℝ, 0 < θ ∧ ∀ η : ℝ, 0 < η → η < θ / 2 → ∃ M0 : ℕ, ∀ m : ℕ, M0 ≤ m → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ α : ℝ, δ ≤ α → ∀ A : Finset (Fin n → Fin (k + 1)),
        α * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
        (∃ X : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          (α + η ^ 2 / 2) * ((k : ℝ) + 1) ^ m ≤
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => X x ∈ A)).card : ℝ)) ∨
        (∃ W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          (α - 2 * η) * ((k : ℝ) + 1) ^ m ≤
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => W x ∈ A)).card : ℝ) ∧
          θ / 2 * (((k : ℝ) + 1) ^ m - (k : ℝ) ^ m) ≤
            ((Finset.univ.filter (fun f : Fin m → Option (Fin k) =>
              (∃ r : Fin m, f r = none) ∧
              ∀ a : Fin k, W (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ)) :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (δ : ℝ) (hδ : 0 < δ) => by
      have hδ'pos : 0 < min δ 1 := lt_min hδ one_pos
      have hδ'1 : min δ 1 ≤ 1 := min_le_right _ _
      have hδ'δ : min δ 1 ≤ δ := min_le_left _ _
      obtain ⟨N₀, hN₀⟩ := hD (min δ 1 / 4) (by positivity)
      have hm₀ : 1 ≤ max N₀ 1 := le_max_right _ _
      have hDHJ := hN₀ (max N₀ 1) (le_max_left _ _)
      have hgap := ManyLines_powGap k (max N₀ 1) hm₀
      obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ,
          θ = min δ 1 / 4 / (((k : ℝ) + 1) ^ (max N₀ 1) - (k : ℝ) ^ (max N₀ 1)) := ⟨_, rfl⟩
      have hgap0 : (0 : ℝ) < ((k : ℝ) + 1) ^ (max N₀ 1) - (k : ℝ) ^ (max N₀ 1) := by linarith
      have hθ : θ * (((k : ℝ) + 1) ^ (max N₀ 1) - (k : ℝ) ^ (max N₀ 1)) = min δ 1 / 4 := by
        rw [hθdef, div_mul_cancel₀ _ (ne_of_gt hgap0)]
      have hθpos : 0 < θ := by rw [hθdef]; positivity
      have hθ1 : θ ≤ 1 := by
        have : θ ≤ min δ 1 / 4 := by
          rw [hθdef]
          exact div_le_self (by positivity) hgap
        linarith
      refine ⟨θ, hθpos, ?_⟩
      intro η hη hηθ
      refine ⟨max N₀ 1, fun m hm => ?_⟩
      obtain ⟨N, hN⟩ := ManyLines_lemma7 k hk (max N₀ 1) hm₀ (min δ 1) θ hδ'pos hδ'1 hθ hDHJ η hη hηθ m hm
      refine ⟨N, fun n hn α hα A hA => ?_⟩
      by_cases hX : ∃ X : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          (α + η ^ 2 / 2) * ((k : ℝ) + 1) ^ m ≤
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => X x ∈ A)).card : ℝ)
      · exact Or.inl hX
      · right
        push_neg at hX
        obtain ⟨q, W, ha, hb⟩ := hN n hn α (le_trans hδ'δ hα) A hA
        obtain ⟨y, hy1, hy2⟩ :=
          ManyLines_lemma8 k m q n (le_trans hm₀ hm) W A α θ η hη hηθ hθ1 ha hb hX
        exact ⟨W y, hy1, hy2⟩
  have Correlate_line_comp : ∀ {α η ι : Type} (V : Combinatorics.Subspace η α ι)
      (l : Combinatorics.Line α η), ∃ L : Combinatorics.Line α ι, ∀ a, L a = V (l a) :=
    fun {α η ι : Type} (V : Combinatorics.Subspace η α ι)
        (l : Combinatorics.Line α η) => by
      refine ⟨⟨fun i => (V.idxFun i).elim some l.idxFun, ?_⟩, ?_⟩
      · obtain ⟨j, hj⟩ := l.proper
        obtain ⟨i, hi⟩ := V.proper j
        exact ⟨i, by simp [hi, hj]⟩
      · intro a
        funext i
        rw [Combinatorics.Line.coe_apply, Combinatorics.Subspace.coe_apply]
        cases h : V.idxFun i with
        | inl c => simp [h]
        | inr j => simp [h, Combinatorics.Line.coe_apply]
  have Correlate_card_split : ∀ {β : Type} [Fintype β] (p q : β → Prop) [DecidablePred p]
      [DecidablePred q], ((Finset.univ.filter p).card : ℝ) =
        ((Finset.univ.filter (fun x => p x ∧ q x)).card : ℝ) +
        ((Finset.univ.filter (fun x => p x ∧ ¬ q x)).card : ℝ) :=
    fun {β : Type} [Fintype β] (p q : β → Prop) [DecidablePred p]
        [DecidablePred q] => by
      have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter p) q
      rw [Finset.filter_filter, Finset.filter_filter] at h
      exact_mod_cast h.symm
  have Correlate_card_compl : ∀ {β : Type} [Fintype β] (p : β → Prop) [DecidablePred p], ((Finset.univ.filter p).card : ℝ) + ((Finset.univ.filter (fun x => ¬ p x)).card : ℝ) =
        ((Finset.univ : Finset β).card : ℝ) :=
    fun {β : Type} [Fintype β] (p : β → Prop) [DecidablePred p] => by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := Finset.univ) p
  have Correlate_card_le_filter : ∀ {β : Type} [Fintype β] (p q : β → Prop) [DecidablePred p]
      [DecidablePred q] (h : ∀ x, p x → q x), ((Finset.univ.filter p).card : ℝ) ≤ ((Finset.univ.filter q).card : ℝ) :=
    fun {β : Type} [Fintype β] (p q : β → Prop) [DecidablePred p]
        [DecidablePred q] (h : ∀ x, p x → q x) => by
      have : Finset.univ.filter p ⊆ Finset.univ.filter q := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact h x hx
      exact_mod_cast Finset.card_le_card this
  have Correlate_card_congr : ∀ {β : Type} [Fintype β] (p q : β → Prop) [DecidablePred p]
      [DecidablePred q] (h : ∀ x, p x ↔ q x), ((Finset.univ.filter p).card : ℝ) = ((Finset.univ.filter q).card : ℝ) :=
    fun {β : Type} [Fintype β] (p q : β → Prop) [DecidablePred p]
        [DecidablePred q] (h : ∀ x, p x ↔ q x) => by
      have : Finset.univ.filter p = Finset.univ.filter q := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h x
      rw [this]
  have Correlate_card_noLast : ∀ (k m : ℕ), ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ r, x r ≠ Fin.last k)).card : ℝ) ≤
        (k : ℝ) ^ m :=
    fun (k m : ℕ) => by
      have hsub : Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ r, x r ≠ Fin.last k) ⊆
          (Finset.univ : Finset (Fin m → Fin k)).image (fun y r => Fin.castSucc (y r)) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨fun r => (x r).castPred (hx r), ?_⟩
        funext r
        simp
      have h1 := Finset.card_le_card hsub
      have h2 := (Finset.card_image_le (s := (Finset.univ : Finset (Fin m → Fin k)))
        (f := fun y r => Fin.castSucc (y r)))
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h2
      have h3 : (Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ r, x r ≠ Fin.last k)).card
          ≤ k ^ m := le_trans h1 h2
      exact_mod_cast h3
  have Correlate_arith : ∀ (k α δ' θ θ' η γ N K a ac c gl : ℝ) (hk : 1 ≤ k) (hδ'0 : 0 < δ')
      (hδ'1 : δ' ≤ 1) (hα : δ' ≤ α) (hθ'0 : 0 < θ') (hθ'1 : θ' ≤ 1) (hθ'θ : θ' ≤ θ)
      (hη : η = δ' * θ' / 48) (hkγ : k * γ = δ' * η ^ 2 / 2) (hγ0 : 0 < γ) (hγη : γ ≤ η)
      (hN : 0 < N) (hK0 : 0 ≤ K) (hKN : K ≤ η * N) (h1 : (α - 2 * η) * N ≤ a)
      (h2 : θ / 2 * (N - K) ≤ gl) (h3 : gl ≤ c) (h4 : ac ≤ K)
      (h6 : a - ac ≤ (α + γ) * (N - c) + k * γ * N) (h7 : a - ac ≤ N - c), False :=
    fun (k α δ' θ θ' η γ N K a ac c gl : ℝ) (hk : 1 ≤ k) (hδ'0 : 0 < δ')
        (hδ'1 : δ' ≤ 1) (hα : δ' ≤ α) (hθ'0 : 0 < θ') (hθ'1 : θ' ≤ 1) (hθ'θ : θ' ≤ θ)
        (hη : η = δ' * θ' / 48) (hkγ : k * γ = δ' * η ^ 2 / 2) (hγ0 : 0 < γ) (hγη : γ ≤ η)
        (hN : 0 < N) (hK0 : 0 ≤ K) (hKN : K ≤ η * N) (h1 : (α - 2 * η) * N ≤ a)
        (h2 : θ / 2 * (N - K) ≤ gl) (h3 : gl ≤ c) (h4 : ac ≤ K)
        (h6 : a - ac ≤ (α + γ) * (N - c) + k * γ * N) (h7 : a - ac ≤ N - c) => by
      have hη0 : 0 < η := by rw [hη]; positivity
      have hδθ : δ' * θ' ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hδ'1 hθ'0.le
        linarith only [this, hθ'1]
      have hη1 : η ≤ 1 / 48 := by rw [hη]; linarith only [hδθ]
      have hNK : 0 ≤ N - K := by
        have := mul_le_mul_of_nonneg_right (hη1.trans (by norm_num : (1 : ℝ) / 48 ≤ 1)) hN.le
        linarith only [this, hKN]
      have hc : θ' / 4 * N ≤ c := by
        have e1 : θ' / 2 * (N - K) ≤ θ / 2 * (N - K) :=
          mul_le_mul_of_nonneg_right (by linarith only [hθ'θ]) hNK
        have e2 : θ' / 2 * (N - η * N) ≤ θ' / 2 * (N - K) :=
          mul_le_mul_of_nonneg_left (by linarith only [hKN]) (by linarith only [hθ'0])
        have e3 : 0 ≤ (θ' * N) * (1 / 4 - η / 2) :=
          mul_nonneg (mul_pos hθ'0 hN).le (by linarith only [hη1])
        linarith only [e1, e2, e3, h2, h3]
      have hP : (α - 3 * η) * N ≤ a - ac := by linarith only [h1, h4, hKN]
      have hαpos : 0 < α := lt_of_lt_of_le hδ'0 hα
      have hPc : (α + 6 * η) * (N - c) ≤ a - ac := by
        have e1 : (α + 6 * η) * (N - c) ≤ (α + 6 * η) * (N - θ' / 4 * N) :=
          mul_le_mul_of_nonneg_left (by linarith only [hc]) (by linarith only [hαpos, hη0])
        have e9 : 9 * η ≤ α * θ' / 4 := by
          rw [hη]
          have := mul_le_mul_of_nonneg_right hα hθ'0.le
          have := mul_pos hαpos hθ'0
          linarith
        have e2 : 0 ≤ (α * θ' / 4 - 9 * η) * N := mul_nonneg (by linarith only [e9]) hN.le
        have e3 : 0 ≤ η * θ' * N := by positivity
        linarith only [e1, e2, e3, hP]
      have hfin : (6 * η - γ) * (N - c) ≤ k * γ * N := by linarith only [hPc, h6]
      have e2 : (α - 3 * η) * N ≤ N - c := le_trans hP h7
      have e5 : 15 / 16 * δ' ≤ α - 3 * η := by
        have : 3 * η ≤ δ' / 16 := by
          rw [hη]
          have := mul_le_mul_of_nonneg_left hθ'1 hδ'0.le
          linarith only [this]
        linarith only [this, hα]
      have hNc : 0 ≤ N - c := by
        have : 0 ≤ (α - 3 * η) * N := mul_nonneg (by linarith only [e5, hδ'0]) hN.le
        linarith only [this, e2]
      have e3 : 5 * η * ((α - 3 * η) * N) ≤ (6 * η - γ) * (N - c) := by
        calc 5 * η * ((α - 3 * η) * N) ≤ 5 * η * (N - c) :=
              mul_le_mul_of_nonneg_left e2 (by linarith only [hη0])
          _ ≤ (6 * η - γ) * (N - c) := mul_le_mul_of_nonneg_right (by linarith only [hγη]) hNc
      have e6 : 5 * η * (15 / 16 * δ' * N) ≤ 5 * η * ((α - 3 * η) * N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e5 hN.le) (by linarith only [hη0])
      have hpos : 0 < δ' * η * N := by positivity
      have e7 : k * γ * N ≤ δ' * η * N / 96 := by
        have e8 : k * γ * N = δ' * η ^ 2 / 2 * N := by rw [hkγ]
        have := mul_le_mul_of_nonneg_left hη1 hpos.le
        rw [e8]
        linarith only [this]
      linarith only [e3, e6, e7, hpos, hfin]
  have Correlate_caseW : ∀ (k : ℕ) (hk : 1 ≤ k) (m n : ℕ) (α δ' θ θ' η γ : ℝ)
      (A : Finset (Fin n → Fin (k + 1)))
      (W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
      (hLine : ∀ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∃ a : Fin (k + 1), l a ∉ A)
      (hk1 : (1 : ℝ) ≤ (k : ℝ)) (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (hαδ' : δ' ≤ α)
      (hθ'0 : 0 < θ') (hθ'1 : θ' ≤ 1) (hθ'θ : θ' ≤ θ) (hηdef : η = δ' * θ' / 48)
      (hkγ : (k : ℝ) * γ = δ' * η ^ 2 / 2) (hγ0 : 0 < γ) (hγη : γ ≤ η)
      (hKle : (k : ℝ) ^ m ≤ η * ((k : ℝ) + 1) ^ m)
      (hW1 : (α - 2 * η) * ((k : ℝ) + 1) ^ m ≤
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => W x ∈ A)).card : ℝ))
      (hW2 : θ / 2 * (((k : ℝ) + 1) ^ m - (k : ℝ) ^ m) ≤
            ((Finset.univ.filter (fun f : Fin m → Option (Fin k) =>
              (∃ r : Fin m, f r = none) ∧
              ∀ a : Fin k, W (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ)), ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
          (∀ i : Fin k, ∀ x ∈ D i, ∀ y : Fin m → Fin (k + 1),
            (∀ r : Fin m, x r = y r ∨
              ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
            y ∈ D i) ∧
          γ * ((k : ℝ) + 1) ^ m ≤
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ i : Fin k, x ∈ D i)).card : ℝ) ∧
          (α + γ) * ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ i : Fin k, x ∈ D i)).card : ℝ) ≤
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => (∀ i : Fin k, x ∈ D i) ∧ W x ∈ A)).card : ℝ) :=
    fun (k : ℕ) (hk : 1 ≤ k) (m n : ℕ) (α δ' θ θ' η γ : ℝ)
        (A : Finset (Fin n → Fin (k + 1)))
        (W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
        (hLine : ∀ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∃ a : Fin (k + 1), l a ∉ A)
        (hk1 : (1 : ℝ) ≤ (k : ℝ)) (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (hαδ' : δ' ≤ α)
        (hθ'0 : 0 < θ') (hθ'1 : θ' ≤ 1) (hθ'θ : θ' ≤ θ) (hηdef : η = δ' * θ' / 48)
        (hkγ : (k : ℝ) * γ = δ' * η ^ 2 / 2) (hγ0 : 0 < γ) (hγη : γ ≤ η)
        (hKle : (k : ℝ) ^ m ≤ η * ((k : ℝ) + 1) ^ m)
        (hW1 : (α - 2 * η) * ((k : ℝ) + 1) ^ m ≤
              ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => W x ∈ A)).card : ℝ))
        (hW2 : θ / 2 * (((k : ℝ) + 1) ^ m - (k : ℝ) ^ m) ≤
              ((Finset.univ.filter (fun f : Fin m → Option (Fin k) =>
                (∃ r : Fin m, f r = none) ∧
                ∀ a : Fin k, W (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ)) => by
      have hNpos : (0 : ℝ) < ((k : ℝ) + 1) ^ m := by positivity
      have hcard_univ : ((Finset.univ : Finset (Fin m → Fin (k + 1))).card : ℝ) =
          ((k : ℝ) + 1) ^ m := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
      obtain ⟨rep, hrep⟩ : ∃ rep : (Fin m → Fin (k + 1)) → Fin k → (Fin m → Fin (k + 1)),
          ∀ x i r, rep x i r = if x r = Fin.last k then Fin.castSucc i else x r :=
        ⟨fun x i r => if x r = Fin.last k then Fin.castSucc i else x r, fun _ _ _ => rfl⟩
      -- rep 对 (i, last)-等价不变
      have hrep_ins : ∀ (i : Fin k) (x y : Fin m → Fin (k + 1)),
          (∀ r : Fin m, x r = y r ∨
            ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
          rep x i = rep y i := by
        intro i x y h
        funext r
        rw [hrep, hrep]
        rcases h r with h1 | ⟨h2, h3⟩
        · rw [h1]
        · rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
            simp [h2, h3, Fin.castSucc_ne_last]
      -- 无线 ⟹ C ∩ A 中的点不含 last
      have hnolast : ∀ x : Fin m → Fin (k + 1), (∀ i, W (rep x i) ∈ A) → W x ∈ A →
          ∀ r, x r ≠ Fin.last k := by
        intro x hC hx r₀ hr₀
        obtain ⟨l, hl⟩ : ∃ l : Combinatorics.Line (Fin (k + 1)) (Fin m),
            ∀ a r, l a r = if x r = Fin.last k then a else x r :=
          ⟨⟨fun r => if x r = Fin.last k then none else some (x r), ⟨r₀, by simp [hr₀]⟩⟩,
            fun a r => by
              rw [Combinatorics.Line.coe_apply]
              by_cases h : x r = Fin.last k <;> simp [h]⟩
        obtain ⟨L, hL⟩ := Correlate_line_comp W l
        obtain ⟨a, ha⟩ := hLine L
        rw [hL] at ha
        apply ha
        rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
        · have : l (Fin.castSucc i) = rep x i := by
            funext r; rw [hl, hrep]
          rw [this]; exact hC i
        · have : l (Fin.last k) = x := by
            funext r; rw [hl]; split_ifs with h
            · exact h.symm
            · rfl
          rw [this]; exact hx
      -- 好线 ↦ 顶点 单射进 C
      obtain ⟨top, htop⟩ : ∃ top : (Fin m → Option (Fin k)) → (Fin m → Fin (k + 1)),
          ∀ f r, top f r = (f r).elim (Fin.last k) Fin.castSucc :=
        ⟨fun f r => (f r).elim (Fin.last k) Fin.castSucc, fun _ _ => rfl⟩
      have htop_rep : ∀ f i, rep (top f) i = fun r => Fin.castSucc ((f r).getD i) := by
        intro f i; funext r
        rw [hrep, htop]
        cases h : f r with
        | none => simp
        | some c => simp [Fin.castSucc_ne_last]
      have htop_inj : Function.Injective top := by
        intro f g hfg
        funext r
        have h := congrFun hfg r
        rw [htop, htop] at h
        revert h
        cases f r with
        | none =>
          cases g r with
          | none => intro _; rfl
          | some d => intro h; exact absurd h.symm (Fin.castSucc_ne_last d)
        | some c =>
          cases g r with
          | none => intro h; exact absurd h (Fin.castSucc_ne_last c)
          | some d => intro h; simp only [Option.elim_some] at h; rw [Fin.castSucc_inj.mp h]
      have hgl_le : ((Finset.univ.filter (fun f : Fin m → Option (Fin k) =>
              (∃ r : Fin m, f r = none) ∧
              ∀ a : Fin k, W (fun r => Fin.castSucc ((f r).getD a)) ∈ A)).card : ℝ) ≤
          ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ i, W (rep x i) ∈ A)).card : ℝ) := by
        have := Finset.card_le_card_of_injOn top
          (s := Finset.univ.filter (fun f : Fin m → Option (Fin k) =>
              (∃ r : Fin m, f r = none) ∧
              ∀ a : Fin k, W (fun r => Fin.castSucc ((f r).getD a)) ∈ A))
          (t := Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ i, W (rep x i) ∈ A))
          (by
            intro f hf
            rw [Finset.mem_coe, Finset.mem_filter] at hf ⊢
            refine ⟨Finset.mem_univ _, fun i => ?_⟩
            rw [htop_rep]
            exact hf.2.2 i)
          (htop_inj.injOn)
        exact_mod_cast this
      have hac_le : ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
            (∀ i, W (rep x i) ∈ A) ∧ W x ∈ A)).card : ℝ) ≤ (k : ℝ) ^ m := by
        refine le_trans (Correlate_card_le_filter _
          (fun x : Fin m → Fin (k + 1) => ∀ r, x r ≠ Fin.last k) ?_) (Correlate_card_noLast k m)
        intro x hx
        exact hnolast x hx.1 hx.2
      -- 链 Q_t
      have hstep : ∀ (t : ℕ) (ht : t < k) (x : Fin m → Fin (k + 1)),
          (∀ j : Fin k, j.val < t + 1 → W (rep x j) ∈ A) ↔
            ((∀ j : Fin k, j.val < t → W (rep x j) ∈ A) ∧ W (rep x ⟨t, ht⟩) ∈ A) := by
        intro t ht x
        constructor
        · intro h
          exact ⟨fun j hj => h j (by omega), h ⟨t, ht⟩ (by simp)⟩
        · rintro ⟨h1, h2⟩ j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · exact h1 j hj
          · have : j = ⟨t, ht⟩ := Fin.ext hj
            rw [this]; exact h2
      obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, ∀ t, q t = ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
          ∀ j : Fin k, j.val < t → W (rep x j) ∈ A)).card : ℝ) := ⟨_, fun t => rfl⟩
      obtain ⟨qa, hqa⟩ : ∃ qa : ℕ → ℝ, ∀ t, qa t = ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
          (∀ j : Fin k, j.val < t → W (rep x j) ∈ A) ∧ W x ∈ A)).card : ℝ) := ⟨_, fun t => rfl⟩
      obtain ⟨S, hS⟩ : ∃ S : Fin k → ℝ, ∀ i₀ : Fin k, S i₀ =
          ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
          (∀ j : Fin k, j.val < i₀.val → W (rep x j) ∈ A) ∧ W (rep x i₀) ∉ A)).card : ℝ) :=
        ⟨_, fun t => rfl⟩
      obtain ⟨SA, hSA⟩ : ∃ SA : Fin k → ℝ, ∀ i₀ : Fin k, SA i₀ =
          ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
          ((∀ j : Fin k, j.val < i₀.val → W (rep x j) ∈ A) ∧ W (rep x i₀) ∉ A) ∧ W x ∈ A)).card : ℝ) :=
        ⟨_, fun t => rfl⟩
      have hq_step : ∀ (t : ℕ) (ht : t < k), q t = q (t + 1) + S ⟨t, ht⟩ := by
        intro t ht
        have e1 := Correlate_card_split
          (fun x : Fin m → Fin (k + 1) => ∀ j : Fin k, j.val < t → W (rep x j) ∈ A)
          (fun x => W (rep x ⟨t, ht⟩) ∈ A)
        have e2 := Correlate_card_congr
          (fun x : Fin m → Fin (k + 1) =>
            (∀ j : Fin k, j.val < t → W (rep x j) ∈ A) ∧ W (rep x ⟨t, ht⟩) ∈ A)
          (fun x => ∀ j : Fin k, j.val < t + 1 → W (rep x j) ∈ A) (fun x => (hstep t ht x).symm)
        rw [hq, hq, hS]
        linarith only [e1, e2]
      have hqa_step : ∀ (t : ℕ) (ht : t < k), qa t = qa (t + 1) + SA ⟨t, ht⟩ := by
        intro t ht
        have e1 := Correlate_card_split
          (fun x : Fin m → Fin (k + 1) => (∀ j : Fin k, j.val < t → W (rep x j) ∈ A) ∧ W x ∈ A)
          (fun x => W (rep x ⟨t, ht⟩) ∈ A)
        have e2 := Correlate_card_congr
          (fun x : Fin m → Fin (k + 1) =>
            ((∀ j : Fin k, j.val < t → W (rep x j) ∈ A) ∧ W x ∈ A) ∧ W (rep x ⟨t, ht⟩) ∈ A)
          (fun x => (∀ j : Fin k, j.val < t + 1 → W (rep x j) ∈ A) ∧ W x ∈ A)
          (fun x => by dsimp only; rw [hstep t ht x]; tauto)
        have e3 := Correlate_card_congr
          (fun x : Fin m → Fin (k + 1) =>
            ((∀ j : Fin k, j.val < t → W (rep x j) ∈ A) ∧ W x ∈ A) ∧ ¬ W (rep x ⟨t, ht⟩) ∈ A)
          (fun x => ((∀ j : Fin k, j.val < t → W (rep x j) ∈ A) ∧ W (rep x ⟨t, ht⟩) ∉ A) ∧ W x ∈ A)
          (fun x => by dsimp only; tauto)
        rw [hqa, hqa, hSA]
        linarith only [e1, e2, e3]
      have hq0 : q 0 = ((k : ℝ) + 1) ^ m := by
        rw [hq, Finset.filter_true_of_mem (fun x _ j hj => absurd hj (Nat.not_lt_zero _)),
          hcard_univ]
      have hqa0 : qa 0 = ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => W x ∈ A)).card : ℝ) := by
        rw [hqa]
        exact Correlate_card_congr _ _
          (fun x => ⟨fun h => h.2, fun h => ⟨fun j hj => absurd hj (Nat.not_lt_zero _), h⟩⟩)
      have hqk : q k = ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
          ∀ i : Fin k, W (rep x i) ∈ A)).card : ℝ) := by
        rw [hq]
        exact Correlate_card_congr _ _ (fun x => ⟨fun h j => h j j.isLt, fun h j _ => h j⟩)
      have hqak : qa k = ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
          (∀ i : Fin k, W (rep x i) ∈ A) ∧ W x ∈ A)).card : ℝ) := by
        rw [hqa]
        exact Correlate_card_congr _ _
          (fun x => ⟨fun h => ⟨fun j => h.1 j j.isLt, h.2⟩, fun h => ⟨fun j _ => h.1 j, h.2⟩⟩)
      -- W∖C 中 A 的点数 ≤ |W∖C|
      have hout : ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => W x ∈ A)).card : ℝ) -
          ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
            (∀ i : Fin k, W (rep x i) ∈ A) ∧ W x ∈ A)).card : ℝ) ≤
          ((k : ℝ) + 1) ^ m - ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
            ∀ i : Fin k, W (rep x i) ∈ A)).card : ℝ) := by
        have e1 := Correlate_card_split (fun x : Fin m → Fin (k + 1) => W x ∈ A)
          (fun x => ∀ i : Fin k, W (rep x i) ∈ A)
        have e2 := Correlate_card_congr
          (fun x : Fin m → Fin (k + 1) => W x ∈ A ∧ ∀ i : Fin k, W (rep x i) ∈ A)
          (fun x => (∀ i : Fin k, W (rep x i) ∈ A) ∧ W x ∈ A) (fun x => and_comm)
        have e3 := Correlate_card_le_filter
          (fun x : Fin m → Fin (k + 1) => W x ∈ A ∧ ¬ ∀ i : Fin k, W (rep x i) ∈ A)
          (fun x => ¬ ∀ i : Fin k, W (rep x i) ∈ A) (fun x h => h.2)
        have e4 := Correlate_card_compl (fun x : Fin m → Fin (k + 1) => ∀ i : Fin k, W (rep x i) ∈ A)
        rw [hcard_univ] at e4
        linarith only [e1, e2, e3, e4]
      -- 鸽巢
      suffices hex : ∃ i₀ : Fin k, γ * ((k : ℝ) + 1) ^ m ≤ S i₀ ∧ (α + γ) * S i₀ ≤ SA i₀ by
        obtain ⟨i₀, h1, h2⟩ := hex
        have hiff : ∀ x : Fin m → Fin (k + 1),
            (∀ i : Fin k, x ∈ Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
              (i.val < i₀.val → W (rep x i) ∈ A) ∧ (i = i₀ → W (rep x i) ∉ A))) ↔
            ((∀ j : Fin k, j.val < i₀.val → W (rep x j) ∈ A) ∧ W (rep x i₀) ∉ A) := by
          intro x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h
            exact ⟨fun j hj => (h j).1 hj, (h i₀).2 rfl⟩
          · rintro ⟨h1, h2⟩ i
            refine ⟨fun hi => h1 i hi, fun hi => ?_⟩
            subst hi; exact h2
        have eS := Correlate_card_congr _ _ hiff
        have eSA := Correlate_card_congr
          (fun x : Fin m → Fin (k + 1) => (∀ i : Fin k, x ∈ Finset.univ.filter
            (fun x : Fin m → Fin (k + 1) =>
              (i.val < i₀.val → W (rep x i) ∈ A) ∧ (i = i₀ → W (rep x i) ∉ A))) ∧ W x ∈ A)
          (fun x => ((∀ j : Fin k, j.val < i₀.val → W (rep x j) ∈ A) ∧ W (rep x i₀) ∉ A) ∧ W x ∈ A)
          (fun x => and_congr_left (fun _ => hiff x))
        rw [hS] at h1 h2
        rw [hSA] at h2
        refine ⟨fun i => Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
              (i.val < i₀.val → W (rep x i) ∈ A) ∧ (i = i₀ → W (rep x i) ∉ A)), ?_, ?_, ?_⟩
        · intro i x hx y hxy
          have hr := hrep_ins i x y hxy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          rw [← hr]; exact hx
        · rw [eS]; exact h1
        · rw [eS, eSA]; exact h2
      by_contra hne
      push_neg at hne
      have hbad : ∀ i₀ : Fin k, SA i₀ ≤ (α + γ) * S i₀ + γ * ((k : ℝ) + 1) ^ m := by
        intro i₀
        have hSA_le : SA i₀ ≤ S i₀ := by
          rw [hSA, hS]
          exact Correlate_card_le_filter _ _ (fun x hx => hx.1)
        have hS0 : 0 ≤ S i₀ := by rw [hS]; positivity
        have hαγ : 0 ≤ (α + γ) * S i₀ := mul_nonneg (by linarith only [hγ0, hαδ', hδ'0]) hS0
        have hγN : 0 ≤ γ * ((k : ℝ) + 1) ^ m := by positivity
        by_cases hSc : γ * ((k : ℝ) + 1) ^ m ≤ S i₀
        · have := hne i₀ hSc
          linarith only [this, hγN]
        · push_neg at hSc
          linarith only [hSc, hSA_le, hαγ]
      have htel : ∀ t : ℕ, t ≤ k → qa 0 - qa t ≤ (α + γ) * (q 0 - q t) +
          (t : ℝ) * γ * ((k : ℝ) + 1) ^ m := by
        intro t
        induction t with
        | zero => intro _; simp
        | succ t ih =>
          intro ht
          have ht' : t < k := by omega
          have e1 := hq_step t ht'
          have e2 := hqa_step t ht'
          have e3 := hbad ⟨t, ht'⟩
          have e4 := ih (by omega)
          have e5 : (α + γ) * q t = (α + γ) * (q (t + 1) + S ⟨t, ht'⟩) := by rw [e1]
          push_cast
          linarith only [e5, e2, e3, e4]
      have hfinal := htel k le_rfl
      rw [hq0, hqa0, hqk, hqak] at hfinal
      exact Correlate_arith (k : ℝ) α δ' θ θ' η γ (((k : ℝ) + 1) ^ m) ((k : ℝ) ^ m)
        _ _ _ _ hk1 hδ'0 hδ'1 hαδ' hθ'0 hθ'1 hθ'θ hηdef hkγ hγ0 hγη hNpos (by positivity) hKle
        hW1 hW2 hgl_le hac_le hfinal hout
  have Correlate : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (δ : ℝ) (hδ : 0 < δ), ∃ γ : ℝ, 0 < γ ∧ ∃ M0 : ℕ, ∀ m : ℕ, M0 ≤ m → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ α : ℝ, δ ≤ α → ∀ A : Finset (Fin n → Fin (k + 1)),
        α * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
        (∀ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∃ a : Fin (k + 1), l a ∉ A) →
        ∃ W : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
          (∀ i : Fin k, ∀ x ∈ D i, ∀ y : Fin m → Fin (k + 1),
            (∀ r : Fin m, x r = y r ∨
              ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
            y ∈ D i) ∧
          γ * ((k : ℝ) + 1) ^ m ≤
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ i : Fin k, x ∈ D i)).card : ℝ) ∧
          (α + γ) * ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ i : Fin k, x ∈ D i)).card : ℝ) ≤
            ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => (∀ i : Fin k, x ∈ D i) ∧ W x ∈ A)).card : ℝ) :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (δ : ℝ) (hδ : 0 < δ) => by
      -- 常数
      obtain ⟨δ', hδ'def⟩ : ∃ δ' : ℝ, δ' = min δ 1 := ⟨_, rfl⟩
      have hδ'0 : 0 < δ' := by rw [hδ'def]; exact lt_min hδ one_pos
      have hδ'1 : δ' ≤ 1 := by rw [hδ'def]; exact min_le_right _ _
      have hδ'δ : δ' ≤ δ := by rw [hδ'def]; exact min_le_left _ _
      obtain ⟨θ, hθ, hML⟩ := ManyLines k hk hD δ' hδ'0
      obtain ⟨θ', hθ'def⟩ : ∃ θ' : ℝ, θ' = min θ 1 := ⟨_, rfl⟩
      have hθ'0 : 0 < θ' := by rw [hθ'def]; exact lt_min hθ one_pos
      have hθ'1 : θ' ≤ 1 := by rw [hθ'def]; exact min_le_right _ _
      have hθ'θ : θ' ≤ θ := by rw [hθ'def]; exact min_le_left _ _
      obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = δ' * θ' / 48 := ⟨_, rfl⟩
      have hη0 : 0 < η := by rw [hηdef]; positivity
      have hδθ' : δ' * θ' ≤ θ' := by
        have := mul_le_mul_of_nonneg_right hδ'1 hθ'0.le
        linarith only [this]
      have hδθ : δ' * θ' ≤ 1 := le_trans hδθ' hθ'1
      have hη1 : η ≤ 1 / 48 := by rw [hηdef]; linarith only [hδθ]
      have hηθ : η < θ / 2 := by
        rw [hηdef]; linarith only [hδθ', hθ'θ, hθ'0]
      obtain ⟨M1, hM1⟩ := hML η hη0 hηθ
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hrat : (k : ℝ) / ((k : ℝ) + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith only
      obtain ⟨M2, hM2⟩ := exists_pow_lt_of_lt_one hη0 hrat
      obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = δ' * η ^ 2 / (2 * k) := ⟨_, rfl⟩
      have hγ0 : 0 < γ := by rw [hγdef]; positivity
      have hkγ : (k : ℝ) * γ = δ' * η ^ 2 / 2 := by
        rw [hγdef]; field_simp
      have hγη2 : γ ≤ η ^ 2 / 2 := by
        have h1 : (k : ℝ) * γ ≤ (k : ℝ) * (η ^ 2 / 2) := by
          rw [hkγ]
          have : 0 ≤ η ^ 2 := sq_nonneg η
          have h2 := mul_le_mul_of_nonneg_right hδ'1 this
          have h3 := mul_le_mul_of_nonneg_right hk1 this
          linarith only [h2, h3]
        exact le_of_mul_le_mul_left h1 hkpos
      have hγη : γ ≤ η := by
        have := mul_le_mul_of_nonneg_right (hη1.trans (by norm_num : (1 : ℝ) / 48 ≤ 1)) hη0.le
        have e : η ^ 2 = η * η := sq η
        linarith only [this, e, hγη2, hη0]
      refine ⟨γ, hγ0, max M1 M2, fun m hm => ?_⟩
      obtain ⟨N, hN⟩ := hM1 m (le_trans (le_max_left _ _) hm)
      refine ⟨N, fun n hn α hα A hA hLine => ?_⟩
      have hαδ' : δ' ≤ α := le_trans hδ'δ hα
      have hNpos : (0 : ℝ) < ((k : ℝ) + 1) ^ m := by positivity
      have hcard_univ : ((Finset.univ : Finset (Fin m → Fin (k + 1))).card : ℝ) =
          ((k : ℝ) + 1) ^ m := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
      have hKle : (k : ℝ) ^ m ≤ η * ((k : ℝ) + 1) ^ m := by
        have h1 : ((k : ℝ) / ((k : ℝ) + 1)) ^ m ≤ ((k : ℝ) / ((k : ℝ) + 1)) ^ M2 :=
          pow_le_pow_of_le_one (by positivity) hrat.le (le_trans (le_max_right _ _) hm)
        have h2 : (k : ℝ) ^ m = ((k : ℝ) / ((k : ℝ) + 1)) ^ m * ((k : ℝ) + 1) ^ m := by
          rw [div_pow, div_mul_cancel₀]; positivity
        rw [h2]
        exact mul_le_mul_of_nonneg_right (by linarith only [h1, hM2]) hNpos.le
      rcases hN n hn α hαδ' A hA with ⟨X, hX⟩ | ⟨W, hW1, hW2⟩
      · -- 情形 X：密度增量直接给出
        refine ⟨X, fun _ => Finset.univ, ?_, ?_, ?_⟩
        · intro i x _ y _; exact Finset.mem_univ y
        · have e : ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
              ∀ i : Fin k, x ∈ (Finset.univ : Finset (Fin m → Fin (k + 1))))).card : ℝ) =
              ((k : ℝ) + 1) ^ m := by
            rw [Finset.filter_true_of_mem (fun x _ i => Finset.mem_univ x), hcard_univ]
          rw [e]
          have : γ ≤ 1 := by linarith only [hγη, hη1]
          have := mul_le_mul_of_nonneg_right this hNpos.le
          linarith only [this]
        · have e : ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
              ∀ i : Fin k, x ∈ (Finset.univ : Finset (Fin m → Fin (k + 1))))).card : ℝ) =
              ((k : ℝ) + 1) ^ m := by
            rw [Finset.filter_true_of_mem (fun x _ i => Finset.mem_univ x), hcard_univ]
          rw [e]
          have e2 : ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) =>
              (∀ i : Fin k, x ∈ (Finset.univ : Finset (Fin m → Fin (k + 1)))) ∧ X x ∈ A)).card : ℝ) =
              ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => X x ∈ A)).card : ℝ) :=
            Correlate_card_congr _ _ (fun x => ⟨fun h => h.2, fun h => ⟨fun i => Finset.mem_univ x, h⟩⟩)
          rw [e2]
          have := mul_le_mul_of_nonneg_right (add_le_add_left hγη2 α) hNpos.le
          linarith only [this, hX]
      · obtain ⟨D, hD1, hD2, hD3⟩ := Correlate_caseW k hk m n α δ' θ θ' η γ A W hLine hk1 hδ'0 hδ'1
          hαδ' hθ'0 hθ'1 hθ'θ hηdef hkγ hγ0 hγη hKle hW1 hW2
        exact ⟨W, D, hD1, hD2, hD3⟩
  have DHJone : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin 1),
        δ * ((1 : ℕ) : ℝ) ^ n ≤ (A.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin 1) (Fin n), ∀ a : Fin 1, l a ∈ A :=
    by
      intro δ hδ
      refine ⟨1, fun n hn A hA => ?_⟩
      have hpos : (0 : ℝ) < (A.card : ℝ) := by
        have h1 : δ * ((1 : ℕ) : ℝ) ^ n = δ := by simp
        rw [h1] at hA
        linarith
      have hcard : 0 < A.card := by exact_mod_cast hpos
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
      refine ⟨⟨fun _ => none, ⟨⟨0, by omega⟩, rfl⟩⟩, fun a => ?_⟩
      have heq : (⟨fun _ => none, ⟨⟨0, by omega⟩, rfl⟩⟩ : Combinatorics.Line (Fin 1) (Fin n)) a = x :=
        Subsingleton.elim _ _
      rw [heq]
      exact hx
  have MDHJstar_card_fiber : ∀ (K a b : ℕ) (A : Finset (Fin (a + b) → Fin K)), (A.card : ℝ) = ∑ x : Fin a → Fin K,
        ((Finset.univ.filter (fun y : Fin b → Fin K => Fin.append x y ∈ A)).card : ℝ) :=
    fun (K a b : ℕ) (A : Finset (Fin (a + b) → Fin K)) => by
      have h : ∀ x : Fin a → Fin K,
          ((Finset.univ.filter (fun y : Fin b → Fin K => Fin.append x y ∈ A)).card : ℝ) =
            ∑ y : Fin b → Fin K, if Fin.append x y ∈ A then (1 : ℝ) else 0 := by
        intro x; rw [Finset.sum_boole]
      simp_rw [h]
      rw [← Fintype.sum_prod_type' (f := fun x y => if Fin.append x y ∈ A then (1:ℝ) else 0)]
      rw [show (∑ p : (Fin a → Fin K) × (Fin b → Fin K),
          if Fin.append p.1 p.2 ∈ A then (1:ℝ) else 0) =
          ∑ z : Fin (a + b) → Fin K, if z ∈ A then (1:ℝ) else 0 from
        (Fin.appendEquiv a b).sum_comp (fun z => if z ∈ A then (1:ℝ) else 0)]
      rw [Finset.sum_boole]
      congr 2
      ext z; simp
  have MDHJstar_sub_line : ∀ (K m n₁ n₂ : ℕ) (W : Combinatorics.Subspace (Fin m) (Fin K) (Fin n₁))
      (ℓ : Combinatorics.Line (Fin K) (Fin n₂)), ∃ V : Combinatorics.Subspace (Fin (m + 1)) (Fin K) (Fin (n₁ + n₂)),
        ∀ a : Fin (m + 1) → Fin K,
          V a = Fin.append (W (fun j => a (Fin.castSucc j))) (ℓ (a (Fin.last m))) :=
    fun (K m n₁ n₂ : ℕ) (W : Combinatorics.Subspace (Fin m) (Fin K) (Fin n₁))
        (ℓ : Combinatorics.Line (Fin K) (Fin n₂)) => by
      refine ⟨⟨Fin.append (fun i => (W.idxFun i).map id Fin.castSucc)
          (fun i => (ℓ.idxFun i).elim (Sum.inr (Fin.last m)) Sum.inl), ?_⟩, ?_⟩
      · intro e
        induction e using Fin.lastCases with
        | last =>
          obtain ⟨i, hi⟩ := ℓ.proper
          exact ⟨Fin.natAdd n₁ i, by simp [hi]⟩
        | cast j =>
          obtain ⟨i, hi⟩ := W.proper j
          exact ⟨Fin.castAdd n₂ i, by simp [hi]⟩
      · intro a
        funext i
        induction i using Fin.addCases with
        | left i =>
          simp only [Combinatorics.Subspace.coe_apply, Fin.append_left]
          rcases h : W.idxFun i with c | j <;> simp
        | right i =>
          simp only [Combinatorics.Subspace.coe_apply, Fin.append_right, Combinatorics.Line.coe_apply]
          rcases h : ℓ.idxFun i with _ | c <;> simp
  have MDHJstar_pt_sub : ∀ (K m n₁ n₂ : ℕ) (x : Fin n₁ → Fin K)
      (V' : Combinatorics.Subspace (Fin m) (Fin K) (Fin n₂)), ∃ V : Combinatorics.Subspace (Fin m) (Fin K) (Fin (n₁ + n₂)),
        ∀ a : Fin m → Fin K, V a = Fin.append x (V' a) :=
    fun (K m n₁ n₂ : ℕ) (x : Fin n₁ → Fin K)
        (V' : Combinatorics.Subspace (Fin m) (Fin K) (Fin n₂)) => by
      refine ⟨⟨Fin.append (fun i => Sum.inl (x i)) V'.idxFun, fun e => ?_⟩, fun a => ?_⟩
      · obtain ⟨i, hi⟩ := V'.proper e
        exact ⟨Fin.natAdd n₁ i, by simp [hi]⟩
      · funext i
        induction i using Fin.addCases with
        | left i => simp [Combinatorics.Subspace.coe_apply]
        | right i => simp [Combinatorics.Subspace.coe_apply]
  have MDHJstar_lift_pt : ∀ (k m n₁ n₂ : ℕ) (U : Combinatorics.Subspace (Fin m) (Fin k) (Fin n₁))
      (y : Fin n₂ → Fin (k + 1)), ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin (n₁ + n₂)),
        ∀ b : Fin m → Fin k,
          V (fun j => Fin.castSucc (b j)) = Fin.append (fun i => Fin.castSucc (U b i)) y :=
    fun (k m n₁ n₂ : ℕ) (U : Combinatorics.Subspace (Fin m) (Fin k) (Fin n₁))
        (y : Fin n₂ → Fin (k + 1)) => by
      refine ⟨⟨Fin.append (fun i => (U.idxFun i).map Fin.castSucc id) (fun i => Sum.inl (y i)),
        fun e => ?_⟩, fun b => ?_⟩
      · obtain ⟨i, hi⟩ := U.proper e
        exact ⟨Fin.castAdd n₂ i, by simp [hi]⟩
      · funext i
        induction i using Fin.addCases with
        | left i =>
          simp only [Combinatorics.Subspace.coe_apply, Fin.append_left]
          rcases h : U.idxFun i with c | j <;> simp
        | right i => simp [Combinatorics.Subspace.coe_apply]
  have MDHJstar_popular : ∀ {ι : Type} (s : Finset ι) (f : ι → ℝ) (K δ : ℝ) (hK : 0 < K)
      (hδ : 0 ≤ δ) (hf : ∀ i ∈ s, f i ≤ K) (h : δ * s.card * K ≤ ∑ i ∈ s, f i), δ / 2 * s.card ≤ ((s.filter (fun i => δ / 2 * K ≤ f i)).card : ℝ) :=
    fun {ι : Type} (s : Finset ι) (f : ι → ℝ) (K δ : ℝ) (hK : 0 < K)
        (hδ : 0 ≤ δ) (hf : ∀ i ∈ s, f i ≤ K) (h : δ * s.card * K ≤ ∑ i ∈ s, f i) => by
      have h1 : ∑ i ∈ s, f i = ∑ i ∈ s.filter (fun i => δ / 2 * K ≤ f i), f i +
          ∑ i ∈ s.filter (fun i => ¬ (δ / 2 * K ≤ f i)), f i :=
        (Finset.sum_filter_add_sum_filter_not s _ f).symm
      have h2 : ∑ i ∈ s.filter (fun i => δ / 2 * K ≤ f i), f i ≤
          ((s.filter (fun i => δ / 2 * K ≤ f i)).card : ℝ) * K := by
        have := Finset.sum_le_card_nsmul (s.filter (fun i => δ / 2 * K ≤ f i)) f K
          (fun i hi => hf i (Finset.mem_filter.1 hi).1)
        simpa [nsmul_eq_mul] using this
      have h3 : ∑ i ∈ s.filter (fun i => ¬ (δ / 2 * K ≤ f i)), f i ≤ s.card * (δ / 2 * K) := by
        have := Finset.sum_le_card_nsmul (s.filter (fun i => ¬ (δ / 2 * K ≤ f i))) f (δ / 2 * K)
          (fun i hi => le_of_lt (not_le.1 (Finset.mem_filter.1 hi).2))
        have h4 : ((s.filter (fun i => ¬ (δ / 2 * K ≤ f i))).card : ℝ) ≤ s.card := by
          exact_mod_cast Finset.card_filter_le _ _
        rw [nsmul_eq_mul] at this
        have h5 : 0 ≤ δ / 2 * K := by positivity
        nlinarith
      have h6 : δ / 2 * s.card * K ≤ ((s.filter (fun i => δ / 2 * K ≤ f i)).card : ℝ) * K := by
        nlinarith
      exact le_of_mul_le_mul_right h6 hK
  have MDHJstar_mdhj_step : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (m : ℕ)
      (ih : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) →
        ∃ U : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), ∀ a, U a ∈ A)
      (δ : ℝ) (hδ : 0 < δ), ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) →
        ∃ U : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin n), ∀ a, U a ∈ A :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (m : ℕ)
        (ih : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) →
          ∃ U : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), ∀ a, U a ∈ A)
        (δ : ℝ) (hδ : 0 < δ) => by
      obtain ⟨M, hM⟩ := hD (δ / 2) (by linarith)
      obtain ⟨N', hN'⟩ := ih (δ / 2 / ((k : ℝ) + 1) ^ M) (by positivity)
      refine ⟨N' + M, fun n hn A hA => ?_⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + M := ⟨n - M, by omega⟩
      have hn' : N' ≤ n' := by omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      have hcard := MDHJstar_card_fiber k n' M A
      have hBcard : δ / 2 * (k : ℝ) ^ n' ≤ ((Finset.univ.filter (fun x : Fin n' → Fin k =>
          δ / 2 * (k : ℝ) ^ M ≤ ((Finset.univ.filter
            (fun y : Fin M → Fin k => Fin.append x y ∈ A)).card : ℝ))).card : ℝ) := by
        have := MDHJstar_popular (Finset.univ : Finset (Fin n' → Fin k))
          (fun x => ((Finset.univ.filter (fun y : Fin M → Fin k => Fin.append x y ∈ A)).card : ℝ))
          ((k : ℝ) ^ M) δ (by positivity) hδ.le ?_ ?_
        · simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using this
        · intro x _
          have := Finset.card_le_univ (Finset.univ.filter (fun y : Fin M → Fin k => Fin.append x y ∈ A))
          simp only [Fintype.card_fun, Fintype.card_fin] at this
          dsimp only
          exact_mod_cast this
        · rw [← hcard]
          simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
          push_cast
          rw [pow_add] at hA
          linarith
      set B := Finset.univ.filter (fun x : Fin n' → Fin k =>
        δ / 2 * (k : ℝ) ^ M ≤ ((Finset.univ.filter
          (fun y : Fin M → Fin k => Fin.append x y ∈ A)).card : ℝ)) with hB
      have hl : ∀ x ∈ B, ∃ g : Fin M → Option (Fin k), (∃ i, g i = none) ∧
          ∀ a : Fin k, Fin.append x (fun i => (g i).getD a) ∈ A := by
        intro x hx
        rw [hB, Finset.mem_filter] at hx
        obtain ⟨l, hl⟩ := hM M le_rfl _ hx.2
        refine ⟨l.idxFun, l.proper, fun a => ?_⟩
        have := hl a
        rw [Finset.mem_filter] at this
        exact this.2
      choose! g hg using hl
      have hbound : (Finset.univ : Finset (Fin M → Option (Fin k))).card •
          (δ / 2 / ((k : ℝ) + 1) ^ M * (k : ℝ) ^ n') ≤ (B.card : ℝ) := by
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        have hpos : (0 : ℝ) < ((k : ℝ) + 1) ^ M := by positivity
        rw [← mul_assoc, mul_div_cancel₀ _ hpos.ne']
        exact hBcard
      obtain ⟨f, -, hf⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
        (s := B) (t := (Finset.univ : Finset (Fin M → Option (Fin k)))) (f := g)
        (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty hbound
      obtain ⟨W, hW⟩ := hN' n' hn' _ hf
      have hWmem := hW (fun _ => ⟨0, by omega⟩)
      rw [Finset.mem_filter] at hWmem
      have hfproper : ∃ i, f i = none := by
        obtain ⟨i, hi⟩ := (hg _ hWmem.1).1
        exact ⟨i, by rw [← hWmem.2]; exact hi⟩
      obtain ⟨V, hV⟩ := MDHJstar_sub_line k m n' M W ⟨f, hfproper⟩
      refine ⟨V, fun a => ?_⟩
      rw [hV]
      have hmem := hW (fun j => a (Fin.castSucc j))
      rw [Finset.mem_filter] at hmem
      have := (hg _ hmem.1).2 (a (Fin.last m))
      rw [hmem.2] at this
      exact this
  have MDHJstar_mdhj : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (m : ℕ), ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) →
        ∃ U : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), ∀ a, U a ∈ A :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (m : ℕ) => by
      induction m with
      | zero =>
        intro δ hδ
        refine ⟨0, fun n _ A hA => ?_⟩
        have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
        have hpos : (0 : ℝ) < A.card := by
          have : (0:ℝ) < δ * (k : ℝ) ^ n := by positivity
          linarith
        obtain ⟨x, hx⟩ : A.Nonempty := by
          rw [← Finset.card_pos]; exact_mod_cast hpos
        exact ⟨⟨fun i => Sum.inl (x i), fun e => e.elim0⟩, fun a => hx⟩
      | succ m ih =>
        intro δ hδ
        exact MDHJstar_mdhj_step k hk hD m ih δ hδ
  have MDHJstar_incr : ∀ (k m M : ℕ) (δ c : ℝ) (hδ : 0 < δ) (hc : δ ≤ c)
      (hU : ∀ B : Finset (Fin M → Fin k), δ / 2 * (k : ℝ) ^ M ≤ (B.card : ℝ) →
        ∃ U : Combinatorics.Subspace (Fin m) (Fin k) (Fin M), ∀ a, U a ∈ B)
      (hP : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
        (c + δ / 2 / ((k : ℝ) + 1) ^ M) * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          ∀ a : Fin m → Fin k, V (fun j => Fin.castSucc (a j)) ∈ A), ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
        c * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          ∀ a : Fin m → Fin k, V (fun j => Fin.castSucc (a j)) ∈ A :=
    fun (k m M : ℕ) (δ c : ℝ) (hδ : 0 < δ) (hc : δ ≤ c)
        (hU : ∀ B : Finset (Fin M → Fin k), δ / 2 * (k : ℝ) ^ M ≤ (B.card : ℝ) →
          ∃ U : Combinatorics.Subspace (Fin m) (Fin k) (Fin M), ∀ a, U a ∈ B)
        (hP : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
          (c + δ / 2 / ((k : ℝ) + 1) ^ M) * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
          ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
            ∀ a : Fin m → Fin k, V (fun j => Fin.castSucc (a j)) ∈ A) => by
      obtain ⟨N₁, hN₁⟩ := hP
      refine ⟨M + N₁, fun n hn A hA => ?_⟩
      obtain ⟨r, rfl⟩ : ∃ r, n = M + r := ⟨n - M, by omega⟩
      have hr : N₁ ≤ r := by omega
      have hQ : (0 : ℝ) < ((k : ℝ) + 1) ^ M := by positivity
      have hR : (0 : ℝ) < ((k : ℝ) + 1) ^ r := by positivity
      have hcard := MDHJstar_card_fiber (k + 1) M r A
      by_cases hinc : ∃ x : Fin M → Fin (k + 1),
          (c + δ / 2 / ((k : ℝ) + 1) ^ M) * ((k : ℝ) + 1) ^ r ≤
            ((Finset.univ.filter (fun y : Fin r → Fin (k + 1) => Fin.append x y ∈ A)).card : ℝ)
      · obtain ⟨x, hx⟩ := hinc
        obtain ⟨V', hV'⟩ := hN₁ r hr _ hx
        obtain ⟨V, hV⟩ := MDHJstar_pt_sub (k + 1) m M r x V'
        refine ⟨V, fun a => ?_⟩
        rw [hV]
        have := hV' a
        rw [Finset.mem_filter] at this
        exact this.2
      · push_neg at hinc
        have hall : ∀ x : Fin M → Fin (k + 1),
            δ / 2 * ((k : ℝ) + 1) ^ r ≤
              ((Finset.univ.filter (fun y : Fin r → Fin (k + 1) => Fin.append x y ∈ A)).card : ℝ) := by
          intro x₀
          by_contra hlt
          push_neg at hlt
          have hsplit : ∑ x : Fin M → Fin (k + 1),
              ((Finset.univ.filter (fun y : Fin r → Fin (k + 1) => Fin.append x y ∈ A)).card : ℝ) =
              ((Finset.univ.filter (fun y : Fin r → Fin (k + 1) => Fin.append x₀ y ∈ A)).card : ℝ) +
              ∑ x ∈ (Finset.univ : Finset (Fin M → Fin (k + 1))).erase x₀,
                ((Finset.univ.filter (fun y : Fin r → Fin (k + 1) => Fin.append x y ∈ A)).card : ℝ) :=
            (Finset.add_sum_erase _ _ (Finset.mem_univ x₀)).symm
          have hrest : ∑ x ∈ (Finset.univ : Finset (Fin M → Fin (k + 1))).erase x₀,
              ((Finset.univ.filter (fun y : Fin r → Fin (k + 1) => Fin.append x y ∈ A)).card : ℝ) ≤
              (((k : ℝ) + 1) ^ M - 1) * ((c + δ / 2 / ((k : ℝ) + 1) ^ M) * ((k : ℝ) + 1) ^ r) := by
            have := Finset.sum_le_card_nsmul ((Finset.univ : Finset (Fin M → Fin (k + 1))).erase x₀)
              (fun x => ((Finset.univ.filter
                (fun y : Fin r → Fin (k + 1) => Fin.append x y ∈ A)).card : ℝ))
              ((c + δ / 2 / ((k : ℝ) + 1) ^ M) * ((k : ℝ) + 1) ^ r)
              (fun x _ => (hinc x).le)
            rw [nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
            have h1 : 1 ≤ (k + 1) ^ M := Nat.one_le_pow _ _ (by omega)
            push_cast [Nat.cast_sub h1] at this
            exact this
          have hA' : c * (((k : ℝ) + 1) ^ M * ((k : ℝ) + 1) ^ r) ≤ (A.card : ℝ) := by
            rw [← pow_add]; exact hA
          have hρQ : δ / 2 / ((k : ℝ) + 1) ^ M * ((k : ℝ) + 1) ^ M = δ / 2 :=
            div_mul_cancel₀ _ hQ.ne'
          have hρ : 0 < δ / 2 / ((k : ℝ) + 1) ^ M := by positivity
          have hρR : 0 < δ / 2 / ((k : ℝ) + 1) ^ M * ((k : ℝ) + 1) ^ r := mul_pos hρ hR
          have hρQR : δ / 2 / ((k : ℝ) + 1) ^ M * ((k : ℝ) + 1) ^ M * ((k : ℝ) + 1) ^ r =
              δ / 2 * ((k : ℝ) + 1) ^ r := by rw [hρQ]
          have hcR : δ * ((k : ℝ) + 1) ^ r ≤ c * ((k : ℝ) + 1) ^ r :=
            mul_le_mul_of_nonneg_right hc hR.le
          rw [hcard, hsplit] at hA'
          nlinarith
        have hswap : ∑ a : Fin M → Fin k,
            ((Finset.univ.filter (fun y : Fin r → Fin (k + 1) =>
              Fin.append (fun i => Fin.castSucc (a i)) y ∈ A)).card : ℝ) =
            ∑ y : Fin r → Fin (k + 1), ((Finset.univ.filter (fun a : Fin M → Fin k =>
              Fin.append (fun i => Fin.castSucc (a i)) y ∈ A)).card : ℝ) := by
          simp only [Finset.card_filter]
          push_cast
          exact Finset.sum_comm
        have hsum : ∑ _y : Fin r → Fin (k + 1), δ / 2 * (k : ℝ) ^ M ≤
            ∑ y : Fin r → Fin (k + 1), ((Finset.univ.filter (fun a : Fin M → Fin k =>
              Fin.append (fun i => Fin.castSucc (a i)) y ∈ A)).card : ℝ) := by
          rw [← hswap]
          have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin M → Fin k))
            (fun a => ((Finset.univ.filter (fun y : Fin r → Fin (k + 1) =>
              Fin.append (fun i => Fin.castSucc (a i)) y ∈ A)).card : ℝ))
            (δ / 2 * ((k : ℝ) + 1) ^ r) (fun a _ => hall (fun i => Fin.castSucc (a i)))
          rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin] at this
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast at this ⊢
          linarith
        obtain ⟨y₀, -, hy₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
        obtain ⟨U, hU'⟩ := hU _ hy₀
        obtain ⟨V, hV⟩ := MDHJstar_lift_pt k m M r U y₀
        refine ⟨V, fun b => ?_⟩
        rw [hV]
        have := hU' b
        rw [Finset.mem_filter] at this
        exact this.2
  have MDHJstar : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (m : ℕ) (δ : ℝ) (hδ : 0 < δ), ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
        δ * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          ∀ a : Fin m → Fin k, V (fun j => Fin.castSucc (a j)) ∈ A :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (m : ℕ) (δ : ℝ) (hδ : 0 < δ) => by
      obtain ⟨M, hM⟩ := MDHJstar_mdhj k hk hD m (δ / 2) (by linarith)
      have hU : ∀ B : Finset (Fin M → Fin k), δ / 2 * (k : ℝ) ^ M ≤ (B.card : ℝ) →
          ∃ U : Combinatorics.Subspace (Fin m) (Fin k) (Fin M), ∀ a, U a ∈ B :=
        fun B hB => hM M le_rfl B hB
      have hρpos : (0 : ℝ) < δ / 2 / ((k : ℝ) + 1) ^ M := by positivity
      have key : ∀ t : ℕ, ∀ c : ℝ, δ ≤ c → 1 < c + t * (δ / 2 / ((k : ℝ) + 1) ^ M) →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
            c * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
            ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
              ∀ a : Fin m → Fin k, V (fun j => Fin.castSucc (a j)) ∈ A := by
        intro t
        induction t with
        | zero =>
          intro c _ hc1
          refine ⟨0, fun n _ A hA => ?_⟩
          exfalso
          have h1 : (A.card : ℝ) ≤ ((k : ℝ) + 1) ^ n := by
            have := Finset.card_le_univ A
            simp only [Fintype.card_fun, Fintype.card_fin] at this
            exact_mod_cast this
          have h2 : (0 : ℝ) < ((k : ℝ) + 1) ^ n := by positivity
          norm_num at hc1
          nlinarith
        | succ t ih =>
          intro c hc hc1
          apply MDHJstar_incr k m M δ c hδ hc hU
          apply ih
          · linarith
          · push_cast at hc1
            linarith
      obtain ⟨t, ht⟩ := exists_nat_gt (1 / (δ / 2 / ((k : ℝ) + 1) ^ M))
      apply key t δ le_rfl
      have : 1 < (t : ℝ) * (δ / 2 / ((k : ℝ) + 1) ^ M) := by
        rw [div_lt_iff₀ hρpos] at ht
        linarith
      linarith
  have Tiling_sub_inj : ∀ {η α ι : Type} (V : Combinatorics.Subspace η α ι)
      (a b : η → α) (h : V a = V b), a = b :=
    fun {η α ι : Type} (V : Combinatorics.Subspace η α ι)
        (a b : η → α) (h : V a = V b) => by
      funext e
      obtain ⟨i, hi⟩ := V.proper e
      have := congrFun h i
      rwa [Combinatorics.Subspace.apply_inr hi, Combinatorics.Subspace.apply_inr hi] at this
  have Tiling_comp : ∀ {η η' α ι : Type} (W : Combinatorics.Subspace η' α ι)
      (V : Combinatorics.Subspace η α η'), ∃ U : Combinatorics.Subspace η α ι, ∀ a, U a = W (V a) :=
    fun {η η' α ι : Type} (W : Combinatorics.Subspace η' α ι)
        (V : Combinatorics.Subspace η α η') => by
      refine ⟨⟨fun i => Sum.elim Sum.inl V.idxFun (W.idxFun i), fun e => ?_⟩, fun a => ?_⟩
      · obtain ⟨j, hj⟩ := V.proper e
        obtain ⟨i, hi⟩ := W.proper j
        exact ⟨i, by simp [hi, hj]⟩
      · funext i
        simp only [Combinatorics.Subspace.coe_apply]
        cases W.idxFun i <;> simp [Combinatorics.Subspace.coe_apply]
  have Tiling_block : ∀ {M n : ℕ} {α : Type} (emb : Fin M → Fin n) (hemb : Function.Injective emb)
      (p : Fin n → α), ∃ W : Combinatorics.Subspace (Fin M) α (Fin n), ∀ w, W w = Function.extend emb w p :=
    fun {M n : ℕ} {α : Type} (emb : Fin M → Fin n) (hemb : Function.Injective emb)
        (p : Fin n → α) => by
      refine ⟨⟨Function.extend emb Sum.inr (fun r => Sum.inl (p r)),
        fun e => ⟨emb e, hemb.extend_apply _ _ e⟩⟩, fun w => ?_⟩
      funext r
      rw [Combinatorics.Subspace.coe_apply]
      dsimp only
      by_cases h : ∃ j, emb j = r
      · obtain ⟨j, rfl⟩ := h
        rw [hemb.extend_apply, hemb.extend_apply]
        rfl
      · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
        rfl
  have Tiling_pullback_ins : ∀ {d n : ℕ} {α : Type} (u v : α)
      (W : Combinatorics.Subspace (Fin d) α (Fin n)) (D : Finset (Fin n → α))
      (hD : ∀ x ∈ D, ∀ y : Fin n → α, (∀ r : Fin n, x r = y r ∨
          ((x r = u ∨ x r = v) ∧ (y r = u ∨ y r = v))) → y ∈ D)
      (P : Finset (Fin d → α)) (hP : ∀ a, a ∈ P ↔ W a ∈ D), ∀ x ∈ P, ∀ y : Fin d → α, (∀ r : Fin d, x r = y r ∨
          ((x r = u ∨ x r = v) ∧ (y r = u ∨ y r = v))) → y ∈ P :=
    fun {d n : ℕ} {α : Type} (u v : α)
        (W : Combinatorics.Subspace (Fin d) α (Fin n)) (D : Finset (Fin n → α))
        (hD : ∀ x ∈ D, ∀ y : Fin n → α, (∀ r : Fin n, x r = y r ∨
            ((x r = u ∨ x r = v) ∧ (y r = u ∨ y r = v))) → y ∈ D)
        (P : Finset (Fin d → α)) (hP : ∀ a, a ∈ P ↔ W a ∈ D) => by
      intro x hx y hxy
      rw [hP] at hx ⊢
      refine hD _ hx _ (fun r => ?_)
      rw [Combinatorics.Subspace.coe_apply, Combinatorics.Subspace.coe_apply]
      cases W.idxFun r with
      | inl c => exact Or.inl rfl
      | inr e => exact hxy e
  have Tiling_lift_ins : ∀ {k M d : ℕ} (i : Fin k)
      (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin M))
      (A : Finset (Fin M → Fin (k + 1)))
      (hA : ∀ x ∈ A, ∀ y : Fin M → Fin (k + 1), (∀ r : Fin M, x r = y r ∨
          ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
          y ∈ A)
      (hV : ∀ a : Fin d → Fin k, V (fun j => Fin.castSucc (a j)) ∈ A), ∀ b : Fin d → Fin (k + 1), V b ∈ A :=
    fun {k M d : ℕ} (i : Fin k)
        (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin M))
        (A : Finset (Fin M → Fin (k + 1)))
        (hA : ∀ x ∈ A, ∀ y : Fin M → Fin (k + 1), (∀ r : Fin M, x r = y r ∨
            ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
            y ∈ A)
        (hV : ∀ a : Fin d → Fin k, V (fun j => Fin.castSucc (a j)) ∈ A) => by
      intro b
      refine hA _ (hV (fun j => if h : b j = Fin.last k then i else (b j).castPred h)) _
        (fun r => ?_)
      rw [Combinatorics.Subspace.coe_apply, Combinatorics.Subspace.coe_apply]
      cases V.idxFun r with
      | inl c => exact Or.inl rfl
      | inr e =>
        simp only [Sum.elim_inr]
        by_cases h : b e = Fin.last k
        · right
          rw [dif_pos h, h]
          exact ⟨Or.inl rfl, Or.inr rfl⟩
        · left
          rw [dif_neg h, Fin.castSucc_castPred]
  have Tiling_card_le : ∀ (k n : ℕ) (A : Finset (Fin n → Fin (k + 1))), (A.card : ℝ) ≤ ((k : ℝ) + 1) ^ n :=
    fun (k n : ℕ) (A : Finset (Fin n → Fin (k + 1))) => by
      have h := Finset.card_le_univ A
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
      have h' : ((A.card : ℕ) : ℝ) ≤ (((k + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
  have Tiling_union_card : ∀ {k d n T : ℕ}
      (V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n))
      (hdisj : ∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t), (Finset.univ.image (fun p : Fin T × (Fin d → Fin (k + 1)) => V p.1 p.2)).card =
        T * (k + 1) ^ d :=
    fun {k d n T : ℕ}
        (V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n))
        (hdisj : ∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) => by
      rw [Finset.card_image_of_injective]
      · simp [Finset.card_univ, Fintype.card_prod]
      · rintro ⟨s, a⟩ ⟨t, b⟩ h
        simp only at h
        obtain rfl := hdisj s t a b h
        obtain rfl := Tiling_sub_inj (V s) a b h
        rfl
  have Tiling_reindex : ∀ {κ : Type} [Fintype κ] {d n : ℕ} {α : Type}
      (V : κ → Combinatorics.Subspace (Fin d) α (Fin n))
      (hdisj : ∀ s t : κ, ∀ a b : Fin d → α, V s a = V t b → s = t), ∃ V' : Fin (Fintype.card κ) → Combinatorics.Subspace (Fin d) α (Fin n),
        (∀ s t : Fin (Fintype.card κ), ∀ a b : Fin d → α, V' s a = V' t b → s = t) ∧
        (∀ t, ∃ s, V' t = V s) :=
    fun {κ : Type} [Fintype κ] {d n : ℕ} {α : Type}
        (V : κ → Combinatorics.Subspace (Fin d) α (Fin n))
        (hdisj : ∀ s t : κ, ∀ a b : Fin d → α, V s a = V t b → s = t) => by
      refine ⟨fun t => V ((Fintype.equivFin κ).symm t), fun s t a b h => ?_, fun t => ⟨_, rfl⟩⟩
      exact (Fintype.equivFin κ).symm.injective (hdisj _ _ a b h)
  have Tiling_append : ∀ {d n T₁ T₂ : ℕ} {α : Type}
      (V₁ : Fin T₁ → Combinatorics.Subspace (Fin d) α (Fin n))
      (V₂ : Fin T₂ → Combinatorics.Subspace (Fin d) α (Fin n))
      (h₁ : ∀ s t : Fin T₁, ∀ a b : Fin d → α, V₁ s a = V₁ t b → s = t)
      (h₂ : ∀ s t : Fin T₂, ∀ a b : Fin d → α, V₂ s a = V₂ t b → s = t)
      (h₁₂ : ∀ s : Fin T₁, ∀ t : Fin T₂, ∀ a b : Fin d → α, V₁ s a ≠ V₂ t b), ∃ V : Fin (T₁ + T₂) → Combinatorics.Subspace (Fin d) α (Fin n),
        (∀ s t : Fin (T₁ + T₂), ∀ a b : Fin d → α, V s a = V t b → s = t) ∧
        (∀ t, (∃ s, V t = V₁ s) ∨ (∃ s, V t = V₂ s)) :=
    fun {d n T₁ T₂ : ℕ} {α : Type}
        (V₁ : Fin T₁ → Combinatorics.Subspace (Fin d) α (Fin n))
        (V₂ : Fin T₂ → Combinatorics.Subspace (Fin d) α (Fin n))
        (h₁ : ∀ s t : Fin T₁, ∀ a b : Fin d → α, V₁ s a = V₁ t b → s = t)
        (h₂ : ∀ s t : Fin T₂, ∀ a b : Fin d → α, V₂ s a = V₂ t b → s = t)
        (h₁₂ : ∀ s : Fin T₁, ∀ t : Fin T₂, ∀ a b : Fin d → α, V₁ s a ≠ V₂ t b) => by
      refine ⟨Fin.append V₁ V₂, ?_, ?_⟩
      · intro s t a b h
        induction s using Fin.addCases with
        | left s =>
          induction t using Fin.addCases with
          | left t =>
            rw [Fin.append_left, Fin.append_left] at h
            rw [h₁ s t a b h]
          | right t =>
            rw [Fin.append_left, Fin.append_right] at h
            exact absurd h (h₁₂ s t a b)
        | right s =>
          induction t using Fin.addCases with
          | left t =>
            rw [Fin.append_right, Fin.append_left] at h
            exact absurd h.symm (h₁₂ t s b a)
          | right t =>
            rw [Fin.append_right, Fin.append_right] at h
            rw [h₂ s t a b h]
      · intro t
        induction t using Fin.addCases with
        | left s => exact Or.inl ⟨s, Fin.append_left _ _ _⟩
        | right s => exact Or.inr ⟨s, Fin.append_right _ _ _⟩
  have Tiling_small : ∀ (k n d : ℕ) (E : Finset (Fin n → Fin (k + 1)))
      (P : (Fin n → Fin (k + 1)) → Prop) (e : ℝ) (hE : (E.card : ℝ) ≤ e), ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
        (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), P (V t a)) ∧
        (E.card : ℝ) ≤ (T : ℝ) * ((k : ℝ) + 1) ^ d + e :=
    fun (k n d : ℕ) (E : Finset (Fin n → Fin (k + 1)))
        (P : (Fin n → Fin (k + 1)) → Prop) (e : ℝ) (hE : (E.card : ℝ) ≤ e) => ⟨0, fun t => t.elim0, fun s => s.elim0, fun t => t.elim0, by simpa using hE⟩
  have Tiling_count : ∀ {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
      (Φ : Y → X) (hΦ : Function.Injective Φ) (Dc G : Finset X) (P : X → Prop) [DecidablePred P]
      (hU : ∀ y, Φ y ∈ Dc) (hG : ∀ x ∈ G, x ∈ Dc ∧ P x), G.card + Fintype.card Y ≤ (Finset.univ.filter (fun y => P (Φ y))).card + Dc.card ∧
      Fintype.card Y ≤ Dc.card :=
    fun {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
        (Φ : Y → X) (hΦ : Function.Injective Φ) (Dc G : Finset X) (P : X → Prop) [DecidablePred P]
        (hU : ∀ y, Φ y ∈ Dc) (hG : ∀ x ∈ G, x ∈ Dc ∧ P x) => by
      set U : Finset X := Finset.univ.image Φ with hUdef
      have hUcard : U.card = Fintype.card Y := by
        rw [hUdef, Finset.card_image_of_injective _ hΦ, Finset.card_univ]
      have hUsub : U ⊆ Dc := by
        intro x hx
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
        exact hU y
      set S := Finset.univ.filter (fun y => P (Φ y)) with hSdef
      have hsub : G ⊆ S.image Φ ∪ (Dc \ U) := by
        intro x hx
        obtain ⟨hxD, hxP⟩ := hG x hx
        by_cases hxU : x ∈ U
        · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hxU
          apply Finset.mem_union_left
          exact Finset.mem_image_of_mem Φ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxP⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxD, hxU⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (S.image Φ) (Dc \ U)
      have h3 : (S.image Φ).card ≤ S.card := Finset.card_image_le
      have h4 : (Dc \ U).card + U.card = Dc.card := Finset.card_sdiff_add_card_eq_card hUsub
      have h5 := Finset.card_le_card hUsub
      constructor <;> omega
  have Tiling_sum : ∀ {T : ℕ} {β : Type} [Fintype β] (Q : Fin T → β → Prop)
      [∀ t, DecidablePred (Q t)], (Finset.univ.filter (fun p : Fin T × β => Q p.1 p.2)).card =
        ∑ t, (Finset.univ.filter (fun b => Q t b)).card :=
    fun {T : ℕ} {β : Type} [Fintype β] (Q : Fin T → β → Prop)
        [∀ t, DecidablePred (Q t)] => by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [Finset.card_filter]
  have Tiling_fiber_sum : ∀ {n M : ℕ} {α : Type} [Fintype α] [DecidableEq α] (z : α)
      (emb : Fin M → Fin n) (hemb : Function.Injective emb) (D : Finset (Fin n → α)), D.card = ∑ p ∈ Finset.univ.filter (fun p : Fin n → α => ∀ j, p (emb j) = z),
        (Finset.univ.filter (fun w : Fin M → α => Function.extend emb w p ∈ D)).card :=
    fun {n M : ℕ} {α : Type} [Fintype α] [DecidableEq α] (z : α)
        (emb : Fin M → Fin n) (hemb : Function.Injective emb) (D : Finset (Fin n → α)) => by
      classical
      set R := Finset.univ.filter (fun p : Fin n → α => ∀ j, p (emb j) = z) with hR
      have hmap : ∀ x ∈ D, Function.extend emb (fun _ => z) x ∈ R := by
        intro x _
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
        intro j
        rw [hemb.extend_apply]
      rw [Finset.card_eq_sum_card_fiberwise hmap]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      symm
      refine Finset.card_nbij' (fun w => Function.extend emb w p) (fun x => x ∘ emb) ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw ⊢
        refine ⟨hw, ?_⟩
        funext r
        by_cases h : ∃ j, emb j = r
        · obtain ⟨j, rfl⟩ := h
          rw [hemb.extend_apply, hp j]
        · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
        obtain ⟨hxD, hxp⟩ := hx
        convert hxD using 1
        funext r
        by_cases h : ∃ j, emb j = r
        · obtain ⟨j, rfl⟩ := h
          rw [hemb.extend_apply]
          rfl
        · rw [Function.extend_apply' _ _ _ h, ← hxp, Function.extend_apply' _ _ _ h]
      · intro w _
        funext j
        simp [hemb.extend_apply]
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
        obtain ⟨_, hxp⟩ := hx
        funext r
        dsimp only
        by_cases h : ∃ j, emb j = r
        · obtain ⟨j, rfl⟩ := h
          rw [hemb.extend_apply]
          rfl
        · rw [Function.extend_apply' _ _ _ h, ← hxp, Function.extend_apply' _ _ _ h]
  have Tiling_fiber_ins : ∀ {k n M : ℕ} (i : Fin k) (S : Finset (Fin n)) (emb : Fin M → Fin n)
      (hemb : Function.Injective emb) (hS : ∀ j, emb j ∈ S) (D : Finset (Fin n → Fin (k + 1)))
      (hDi : ∀ x ∈ D, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
          (r ∈ S ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
            (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D)
      (p : Fin n → Fin (k + 1)) (A : Finset (Fin M → Fin (k + 1)))
      (hA : ∀ w, w ∈ A ↔ Function.extend emb w p ∈ D), ∀ x ∈ A, ∀ y : Fin M → Fin (k + 1), (∀ r : Fin M, x r = y r ∨
          ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
          y ∈ A :=
    fun {k n M : ℕ} (i : Fin k) (S : Finset (Fin n)) (emb : Fin M → Fin n)
        (hemb : Function.Injective emb) (hS : ∀ j, emb j ∈ S) (D : Finset (Fin n → Fin (k + 1)))
        (hDi : ∀ x ∈ D, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
            (r ∈ S ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
              (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D)
        (p : Fin n → Fin (k + 1)) (A : Finset (Fin M → Fin (k + 1)))
        (hA : ∀ w, w ∈ A ↔ Function.extend emb w p ∈ D) => by
      intro x hx y hxy
      rw [hA] at hx ⊢
      refine hDi _ hx _ (fun r => ?_)
      by_cases h : ∃ j, emb j = r
      · obtain ⟨j, rfl⟩ := h
        rw [hemb.extend_apply, hemb.extend_apply]
        rcases hxy j with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨hS j, h'⟩
      · left
        rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
  have Tiling_round : ∀ (k n d M : ℕ) (i : Fin k) (β : ℝ) (hβ : 0 < β)
      (hM : ∀ A : Finset (Fin M → Fin (k + 1)), β * ((k : ℝ) + 1) ^ M ≤ (A.card : ℝ) →
        ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin M),
          ∀ a : Fin d → Fin k, V (fun j => Fin.castSucc (a j)) ∈ A)
      (S : Finset (Fin n)) (emb : Fin M → Fin n) (hemb : Function.Injective emb)
      (hS : ∀ j, emb j ∈ S) (D : Finset (Fin n → Fin (k + 1)))
      (hDi : ∀ x ∈ D, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
          (r ∈ S ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
            (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D)
      (hdens : 2 * β * ((k : ℝ) + 1) ^ n ≤ (D.card : ℝ)), ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
        (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), V t a ∈ D) ∧
        β * ((k : ℝ) + 1) ^ d / ((((k : ℝ) + 1 + d) ^ M) * ((k : ℝ) + 1) ^ M) *
            ((k : ℝ) + 1) ^ n ≤ (T : ℝ) * ((k : ℝ) + 1) ^ d ∧
        (∀ x ∈ D, (∀ t a, V t a ≠ x) → ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
          ((r ∈ S ∧ ∀ j, emb j ≠ r) ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
            (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D ∧ ∀ t a, V t a ≠ y) :=
    fun (k n d M : ℕ) (i : Fin k) (β : ℝ) (hβ : 0 < β)
        (hM : ∀ A : Finset (Fin M → Fin (k + 1)), β * ((k : ℝ) + 1) ^ M ≤ (A.card : ℝ) →
          ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin M),
            ∀ a : Fin d → Fin k, V (fun j => Fin.castSucc (a j)) ∈ A)
        (S : Finset (Fin n)) (emb : Fin M → Fin n) (hemb : Function.Injective emb)
        (hS : ∀ j, emb j ∈ S) (D : Finset (Fin n → Fin (k + 1)))
        (hDi : ∀ x ∈ D, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
            (r ∈ S ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
              (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D)
        (hdens : 2 * β * ((k : ℝ) + 1) ^ n ≤ (D.card : ℝ)) => by
      classical
      have hK : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      set R := Finset.univ.filter (fun p : Fin n → Fin (k + 1) => ∀ j, p (emb j) = 0) with hRdef
      -- |R|·(k+1)^M = (k+1)^n
      have hRcard : (R.card : ℝ) * ((k : ℝ) + 1) ^ M = ((k : ℝ) + 1) ^ n := by
        have h := Tiling_fiber_sum (0 : Fin (k + 1)) emb hemb Finset.univ
        simp only [Finset.mem_univ, Finset.filter_True, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, Finset.sum_const, smul_eq_mul] at h
        rw [← hRdef] at h
        have h' : (((k + 1) ^ n : ℕ) : ℝ) = ((R.card * (k + 1) ^ M : ℕ) : ℝ) := by
          exact_mod_cast h
        push_cast at h'
        linarith
      have hsum : (D.card : ℝ) = ∑ p ∈ R,
          ((Finset.univ.filter (fun w : Fin M → Fin (k + 1) => Function.extend emb w p ∈ D)).card : ℝ) := by
        rw [Tiling_fiber_sum (0 : Fin (k + 1)) emb hemb D]
        push_cast
        rfl
      set G₀ := R.filter (fun p => β * ((k : ℝ) + 1) ^ M ≤
        ((Finset.univ.filter (fun w : Fin M → Fin (k + 1) => Function.extend emb w p ∈ D)).card : ℝ))
        with hG₀def
      have hG₀ : β * ((k : ℝ) + 1) ^ n ≤ (G₀.card : ℝ) * ((k : ℝ) + 1) ^ M := by
        have hsplit := Finset.sum_filter_add_sum_filter_not R (fun p => β * ((k : ℝ) + 1) ^ M ≤
          ((Finset.univ.filter (fun w : Fin M → Fin (k + 1) => Function.extend emb w p ∈ D)).card : ℝ))
          (fun p => ((Finset.univ.filter (fun w : Fin M → Fin (k + 1) =>
            Function.extend emb w p ∈ D)).card : ℝ))
        rw [← hG₀def] at hsplit
        have h1 := Finset.sum_le_card_nsmul G₀ (fun p => ((Finset.univ.filter
          (fun w : Fin M → Fin (k + 1) => Function.extend emb w p ∈ D)).card : ℝ)) (((k : ℝ) + 1) ^ M)
          (fun p _ => Tiling_card_le k M _)
        have h2 := Finset.sum_le_card_nsmul (R.filter (fun p => ¬ (β * ((k : ℝ) + 1) ^ M ≤
          ((Finset.univ.filter (fun w : Fin M → Fin (k + 1) => Function.extend emb w p ∈ D)).card : ℝ))))
          (fun p => ((Finset.univ.filter
          (fun w : Fin M → Fin (k + 1) => Function.extend emb w p ∈ D)).card : ℝ)) (β * ((k : ℝ) + 1) ^ M)
          (fun p hp => le_of_lt (not_le.1 (Finset.mem_filter.1 hp).2))
        have h3 : ((R.filter (fun p => ¬ (β * ((k : ℝ) + 1) ^ M ≤
          ((Finset.univ.filter (fun w : Fin M → Fin (k + 1) => Function.extend emb w p ∈ D)).card : ℝ)))).card : ℝ)
            ≤ R.card := by exact_mod_cast Finset.card_filter_le _ _
        rw [nsmul_eq_mul] at h1 h2
        have h4 : ((R.filter (fun p => ¬ (β * ((k : ℝ) + 1) ^ M ≤
          ((Finset.univ.filter (fun w : Fin M → Fin (k + 1) => Function.extend emb w p ∈ D)).card : ℝ)))).card : ℝ)
            * (β * ((k : ℝ) + 1) ^ M) ≤ R.card * (β * ((k : ℝ) + 1) ^ M) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
        nlinarith
      -- 每个好基点 p 的纤维含一个 d 维子空间
      have hex : ∀ p ∈ G₀, ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin M),
          ∀ b, Function.extend emb (V b) p ∈ D := by
        intro p hp
        rw [hG₀def, Finset.mem_filter] at hp
        obtain ⟨V, hV⟩ := hM _ hp.2
        refine ⟨V, fun b => ?_⟩
        have hA := Tiling_fiber_ins i S emb hemb hS D hDi p
          (Finset.univ.filter (fun w : Fin M → Fin (k + 1) => Function.extend emb w p ∈ D))
          (fun w => by simp)
        have := Tiling_lift_ins i V _ hA hV b
        simpa using this
      choose Vp hVp using hex
      set f : (Fin n → Fin (k + 1)) → (Fin M → Fin (k + 1) ⊕ Fin d) :=
        fun p => if h : p ∈ G₀ then (Vp p h).idxFun else fun _ => Sum.inl 0 with hfdef
      have hpig := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to (s := G₀)
        (t := (Finset.univ : Finset (Fin M → Fin (k + 1) ⊕ Fin d))) (f := f)
        (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty
        (b := (G₀.card : ℝ) / (((k : ℝ) + 1 + d) ^ M)) (by
          rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin,
            Fintype.card_fin, Fintype.card_fin]
          push_cast
          rw [mul_div_cancel₀]
          positivity)
      obtain ⟨y, -, hy⟩ := hpig
      set F := G₀.filter (fun p => f p = y) with hFdef
      have hG₀pos : (0 : ℝ) < G₀.card := by
        have : (0 : ℝ) < β * ((k : ℝ) + 1) ^ n := by positivity
        by_contra hc
        push_neg at hc
        nlinarith [pow_pos hK M]
      have hFpos : (0 : ℝ) < F.card := lt_of_lt_of_le (by positivity) hy
      obtain ⟨p₀, hp₀⟩ : F.Nonempty := by
        rw [← Finset.card_pos]; exact_mod_cast hFpos
      have hp₀G : p₀ ∈ G₀ := (Finset.mem_filter.1 hp₀).1
      set V := Vp p₀ hp₀G with hVdef
      have hFV : ∀ p ∈ F, ∀ b, Function.extend emb (V b) p ∈ D := by
        intro p hp b
        have hpG : p ∈ G₀ := (Finset.mem_filter.1 hp).1
        have hidx : (Vp p hpG).idxFun = V.idxFun := by
          have e1 : f p = y := (Finset.mem_filter.1 hp).2
          have e2 : f p₀ = y := (Finset.mem_filter.1 hp₀).2
          rw [hfdef] at e1 e2
          simp only [dif_pos hpG, dif_pos hp₀G] at e1 e2
          rw [e1, e2]
        have hb : V b = Vp p hpG b := by
          funext r
          rw [Combinatorics.Subspace.coe_apply, Combinatorics.Subspace.coe_apply, hidx]
        rw [hb]
        exact hVp p hpG b
      set G := R.filter (fun p => ∀ a, Function.extend emb (V a) p ∈ D) with hGdef
      have hFG : F ⊆ G := by
        intro p hp
        rw [hGdef, Finset.mem_filter]
        exact ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1, hFV p hp⟩
      have hU : ∀ p : Fin n → Fin (k + 1), ∃ U : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
          ∀ a, U a = Function.extend emb (V a) p := by
        intro p
        obtain ⟨W, hW⟩ := Tiling_block emb hemb p
        obtain ⟨U, hU⟩ := Tiling_comp W V
        exact ⟨U, fun a => by rw [hU, hW]⟩
      choose U hU using hU
      -- 基点可由砖中的点恢复
      have hrec : ∀ p ∈ R, ∀ a, Function.extend emb (fun _ => (0 : Fin (k + 1)))
          (Function.extend emb (V a) p) = p := by
        intro p hp a
        rw [hRdef, Finset.mem_filter] at hp
        funext r
        by_cases h : ∃ j, emb j = r
        · obtain ⟨j, rfl⟩ := h
          rw [hemb.extend_apply, hp.2 j]
        · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      let κ := {p // p ∈ G}
      let e := Fintype.equivFin κ
      refine ⟨Fintype.card κ, fun t => U (e.symm t).1, ?_, ?_, ?_, ?_⟩
      · intro s t a b h
        simp only [hU] at h
        have hs := (Finset.mem_filter.1 (e.symm s).2).1
        have ht := (Finset.mem_filter.1 (e.symm t).2).1
        have := hrec _ hs a
        rw [h, hrec _ ht b] at this
        exact e.symm.injective (Subtype.ext this.symm)
      · intro t a
        rw [hU]
        exact (Finset.mem_filter.1 (e.symm t).2).2 a
      · have hA : (0 : ℝ) < ((k : ℝ) + 1 + d) ^ M := by positivity
        have hB : (0 : ℝ) < ((k : ℝ) + 1) ^ M := by positivity
        have hFGc : (F.card : ℝ) ≤ G.card := by exact_mod_cast Finset.card_le_card hFG
        have hκ : Fintype.card κ = G.card := Fintype.card_coe G
        rw [hκ]
        have key : β * ((k : ℝ) + 1) ^ n / ((((k : ℝ) + 1 + d) ^ M) * ((k : ℝ) + 1) ^ M) ≤ G.card := by
          have : β * ((k : ℝ) + 1) ^ n / ((((k : ℝ) + 1 + d) ^ M) * ((k : ℝ) + 1) ^ M) ≤
              (G₀.card : ℝ) / (((k : ℝ) + 1 + d) ^ M) := by
            rw [div_le_div_iff₀ (by positivity) hA]
            nlinarith
          linarith
        have hKd : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ d := by positivity
        calc β * ((k : ℝ) + 1) ^ d / ((((k : ℝ) + 1 + d) ^ M) * ((k : ℝ) + 1) ^ M) * ((k : ℝ) + 1) ^ n
            = β * ((k : ℝ) + 1) ^ n / ((((k : ℝ) + 1 + d) ^ M) * ((k : ℝ) + 1) ^ M) *
                ((k : ℝ) + 1) ^ d := by ring
          _ ≤ (G.card : ℝ) * ((k : ℝ) + 1) ^ d := mul_le_mul_of_nonneg_right key hKd
      · intro x hx hxcov y hxy
        have hyD : y ∈ D := hDi x hx y (fun r => (hxy r).imp id (fun h => ⟨h.1.1, h.2⟩))
        refine ⟨hyD, fun t a hta => ?_⟩
        simp only [hU] at hta
        have hqG := (e.symm t).2
        set q := (e.symm t).1 with hqdef
        have hblock : ∀ j, x (emb j) = V a j := by
          intro j
          rcases hxy (emb j) with h | h
          · rw [h, ← hta, hemb.extend_apply]
          · exact absurd rfl (h.1.2 j)
        have hoff : ∀ r, (¬∃ j, emb j = r) → q r = y r := by
          intro r h
          rw [← hta, Function.extend_apply' _ _ _ h]
        set p := Function.extend emb (fun _ => (0 : Fin (k + 1))) x with hpdef
        have hpR : p ∈ R := by
          rw [hRdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, fun j => by rw [hpdef, hemb.extend_apply]⟩
        have hpG : p ∈ G := by
          rw [hGdef, Finset.mem_filter]
          refine ⟨hpR, fun a' => ?_⟩
          have hq := (Finset.mem_filter.1 hqG).2 a'
          refine hDi _ hq _ (fun r => ?_)
          by_cases h : ∃ j, emb j = r
          · obtain ⟨j, rfl⟩ := h
            left
            rw [hemb.extend_apply, hemb.extend_apply]
          · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, hoff r h, hpdef,
              Function.extend_apply' _ _ _ h]
            rcases hxy r with h' | h'
            · exact Or.inl h'.symm
            · exact Or.inr ⟨h'.1.1, h'.2.2, h'.2.1⟩
        have hxe : Function.extend emb (V a) p = x := by
          funext r
          by_cases h : ∃ j, emb j = r
          · obtain ⟨j, rfl⟩ := h
            rw [hemb.extend_apply, hblock j]
          · rw [Function.extend_apply' _ _ _ h, hpdef, Function.extend_apply' _ _ _ h]
        refine hxcov (e ⟨p, hpG⟩) a ?_
        simp only [Equiv.symm_apply_apply, hU]
        exact hxe
  have Tiling_iter : ∀ (k n d M : ℕ) (i : Fin k) (β Θ : ℝ) (hβ : 0 < β) (hΘ : 0 < Θ)
      (hround : ∀ (S : Finset (Fin n)) (emb : Fin M → Fin n), Function.Injective emb →
        (∀ j, emb j ∈ S) → ∀ D : Finset (Fin n → Fin (k + 1)),
        (∀ x ∈ D, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
          (r ∈ S ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
            (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D) →
        2 * β * ((k : ℝ) + 1) ^ n ≤ (D.card : ℝ) →
        ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
          (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
          (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), V t a ∈ D) ∧
          Θ * ((k : ℝ) + 1) ^ n ≤ (T : ℝ) * ((k : ℝ) + 1) ^ d ∧
          (∀ x ∈ D, (∀ t a, V t a ≠ x) → ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
            ((r ∈ S ∧ ∀ j, emb j ≠ r) ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
              (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D ∧ ∀ t a, V t a ≠ y)), ∀ j : ℕ, ∀ S : Finset (Fin n), j * M ≤ S.card → ∀ D : Finset (Fin n → Fin (k + 1)),
        (∀ x ∈ D, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
          (r ∈ S ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
            (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D) →
        (D.card : ℝ) < (2 * β + (j : ℝ) * Θ) * ((k : ℝ) + 1) ^ n →
        ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
          (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
          (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), V t a ∈ D) ∧
          (D.card : ℝ) ≤ (T : ℝ) * ((k : ℝ) + 1) ^ d + 2 * β * ((k : ℝ) + 1) ^ n :=
    fun (k n d M : ℕ) (i : Fin k) (β Θ : ℝ) (hβ : 0 < β) (hΘ : 0 < Θ)
        (hround : ∀ (S : Finset (Fin n)) (emb : Fin M → Fin n), Function.Injective emb →
          (∀ j, emb j ∈ S) → ∀ D : Finset (Fin n → Fin (k + 1)),
          (∀ x ∈ D, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
            (r ∈ S ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
              (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D) →
          2 * β * ((k : ℝ) + 1) ^ n ≤ (D.card : ℝ) →
          ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
            (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
            (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), V t a ∈ D) ∧
            Θ * ((k : ℝ) + 1) ^ n ≤ (T : ℝ) * ((k : ℝ) + 1) ^ d ∧
            (∀ x ∈ D, (∀ t a, V t a ≠ x) → ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
              ((r ∈ S ∧ ∀ j, emb j ≠ r) ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
                (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D ∧ ∀ t a, V t a ≠ y)) => by
      intro j
      induction j with
      | zero =>
        intro S _ D _ hlt
        refine Tiling_small k n d D (fun x => x ∈ D) _ ?_
        push_cast at hlt
        linarith
      | succ j ih =>
        intro S hS D hDi hlt
        by_cases hsmall : (D.card : ℝ) < 2 * β * ((k : ℝ) + 1) ^ n
        · exact Tiling_small k n d D (fun x => x ∈ D) _ hsmall.le
        push_neg at hsmall
        -- 选新块 emb ⊆ S
        have hMS : M ≤ S.card := by
          have := Nat.zero_le (j * M)
          rw [Nat.succ_mul] at hS
          omega
        obtain ⟨S₀, hS₀S, hS₀c⟩ := Finset.exists_subset_card_eq hMS
        set emb : Fin M → Fin n := fun t => S₀.orderEmbOfFin hS₀c t with hembdef
        have hemb : Function.Injective emb := fun a b h => (S₀.orderEmbOfFin hS₀c).injective h
        have hembS : ∀ t, emb t ∈ S := fun t => hS₀S (S₀.orderEmbOfFin_mem hS₀c t)
        obtain ⟨T₁, V₁, h1, h2, h3, h4⟩ := hround S emb hemb hembS D hDi hsmall
        -- 剩余集与剩余自由坐标
        set D' := D.filter (fun x => ∀ t : Fin T₁, ∀ a : Fin d → Fin (k + 1), V₁ t a ≠ x)
          with hD'def
        set S' := S.filter (fun r => ∀ t : Fin M, emb t ≠ r) with hS'def
        have hS'card : S'.card + M = S.card := by
          have h := Finset.card_filter_add_card_filter_not (s := S)
            (fun r => ∀ t : Fin M, emb t ≠ r)
          have himg : S.filter (fun r => ¬ ∀ t : Fin M, emb t ≠ r) = Finset.univ.image emb := by
            ext r
            simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, not_forall,
              not_not]
            constructor
            · rintro ⟨-, t, ht⟩
              exact ⟨t, ht⟩
            · rintro ⟨t, rfl⟩
              exact ⟨hembS t, t, rfl⟩
          rw [himg, Finset.card_image_of_injective _ hemb, Finset.card_univ, Fintype.card_fin] at h
          exact h
        have hS'j : j * M ≤ S'.card := by
          rw [Nat.succ_mul] at hS
          omega
        have hD'i : ∀ x ∈ D', ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
            (r ∈ S' ∧ (x r = Fin.castSucc i ∨ x r = Fin.last k) ∧
              (y r = Fin.castSucc i ∨ y r = Fin.last k))) → y ∈ D' := by
          intro x hx y hxy
          rw [Finset.mem_filter] at hx
          have := h4 x hx.1 hx.2 y (fun r => by
            rcases hxy r with h | ⟨hr, h⟩
            · exact Or.inl h
            · rw [Finset.mem_filter] at hr
              exact Or.inr ⟨hr, h⟩)
          exact Finset.mem_filter.mpr this
        have hDcard : D'.card + T₁ * (k + 1) ^ d = D.card := by
          have h := Finset.card_filter_add_card_filter_not (s := D)
            (fun x => ∀ t : Fin T₁, ∀ a : Fin d → Fin (k + 1), V₁ t a ≠ x)
          have himg : D.filter (fun x => ¬ ∀ t : Fin T₁, ∀ a : Fin d → Fin (k + 1), V₁ t a ≠ x) =
              Finset.univ.image (fun p : Fin T₁ × (Fin d → Fin (k + 1)) => V₁ p.1 p.2) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, not_forall,
              not_not, Prod.exists]
            constructor
            · rintro ⟨-, t, a, h⟩
              exact ⟨t, a, h⟩
            · rintro ⟨t, a, rfl⟩
              exact ⟨h2 t a, t, a, rfl⟩
          rw [himg, Tiling_union_card V₁ h1] at h
          exact h
        have hDcardR : (D'.card : ℝ) + (T₁ : ℝ) * ((k : ℝ) + 1) ^ d = (D.card : ℝ) := by
          exact_mod_cast hDcard
        have hlt' : (D'.card : ℝ) < (2 * β + (j : ℝ) * Θ) * ((k : ℝ) + 1) ^ n := by
          push_cast at hlt
          nlinarith
        obtain ⟨T₂, V₂, g1, g2, g3⟩ := ih S' hS'j D' hD'i hlt'
        obtain ⟨V, hV1, hV2⟩ := Tiling_append V₁ V₂ h1 g1
          (fun s t a b h => (Finset.mem_filter.mp (g2 t b)).2 s a h)
        refine ⟨T₁ + T₂, V, hV1, fun t a => ?_, ?_⟩
        · rcases hV2 t with ⟨s, hs⟩ | ⟨s, hs⟩
          · rw [hs]
            exact h2 s a
          · rw [hs]
            exact (Finset.mem_filter.mp (g2 s a)).1
        · push_cast
          nlinarith
  have Tiling_lemma12 : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (d : ℕ) (ε : ℝ) (hε : 0 < ε), ∃ F : ℕ, ∀ n : ℕ, F ≤ n → ∀ i : Fin k, ∀ D : Finset (Fin n → Fin (k + 1)),
        (∀ x ∈ D, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
          ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
          y ∈ D) →
        ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
          (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
          (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), V t a ∈ D) ∧
          (D.card : ℝ) ≤ (T : ℝ) * ((k : ℝ) + 1) ^ d + ε * ((k : ℝ) + 1) ^ n :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (d : ℕ) (ε : ℝ) (hε : 0 < ε) => by
      obtain ⟨M, hM⟩ := MDHJstar k hk hD d (ε / 2) (by positivity)
      set Θ : ℝ := ε / 2 * ((k : ℝ) + 1) ^ d / ((((k : ℝ) + 1 + d) ^ M) * ((k : ℝ) + 1) ^ M)
        with hΘdef
      have hΘ : 0 < Θ := by positivity
      obtain ⟨j, hj⟩ := exists_nat_gt (1 / Θ)
      refine ⟨j * M, fun n hn i D hDi => ?_⟩
      have hround := Tiling_round k n d M i (ε / 2) (by positivity) (hM M le_rfl)
      have hjΘ : 1 < (j : ℝ) * Θ := by
        rw [div_lt_iff₀ hΘ] at hj
        exact hj
      have hcard := Tiling_card_le k n D
      have hpos : 0 < ((k : ℝ) + 1) ^ n := by positivity
      obtain ⟨T, V, h1, h2, h3⟩ := Tiling_iter k n d M i (ε / 2) Θ (by positivity) hΘ hround j
        Finset.univ (by rw [Finset.card_univ, Fintype.card_fin]; exact hn) D
        (fun x hx y hxy => hDi x hx y (fun r => by
          rcases hxy r with h | ⟨-, h⟩
          · exact Or.inl h
          · exact Or.inr h))
        (by nlinarith)
      refine ⟨T, V, h1, h2, ?_⟩
      have e : 2 * (ε / 2) * ((k : ℝ) + 1) ^ n = ε * ((k : ℝ) + 1) ^ n := by ring
      linarith
  have Tiling_refine : ∀ (k n d F : ℕ) (ε : ℝ)
      (hL : ∀ i : Fin k, ∀ D : Finset (Fin F → Fin (k + 1)),
        (∀ x ∈ D, ∀ y : Fin F → Fin (k + 1), (∀ r : Fin F, x r = y r ∨
          ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
          y ∈ D) →
        ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin F),
          (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
          (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), V t a ∈ D) ∧
          (D.card : ℝ) ≤ (T : ℝ) * ((k : ℝ) + 1) ^ d + ε * ((k : ℝ) + 1) ^ F)
      (hε : 0 ≤ ε) (E : Finset (Fin n → Fin (k + 1))) (e₁ : ℝ) (T₁ : ℕ)
      (W : Fin T₁ → Combinatorics.Subspace (Fin F) (Fin (k + 1)) (Fin n))
      (hW1 : ∀ s t : Fin T₁, ∀ a b : Fin F → Fin (k + 1), W s a = W t b → s = t)
      (hW2 : ∀ t : Fin T₁, ∀ a : Fin F → Fin (k + 1), W t a ∈ E)
      (hW3 : (E.card : ℝ) ≤ (T₁ : ℝ) * ((k : ℝ) + 1) ^ F + e₁)
      (i : Fin k) (Dn : Finset (Fin n → Fin (k + 1)))
      (hDn : ∀ x ∈ Dn, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
          ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
          y ∈ Dn)
      (E' : Finset (Fin n → Fin (k + 1))) (hE' : ∀ x, x ∈ E' ↔ x ∈ E ∧ x ∈ Dn), ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
        (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), V t a ∈ E') ∧
        (E'.card : ℝ) ≤ (T : ℝ) * ((k : ℝ) + 1) ^ d + (e₁ + ε * ((k : ℝ) + 1) ^ n) :=
    fun (k n d F : ℕ) (ε : ℝ)
        (hL : ∀ i : Fin k, ∀ D : Finset (Fin F → Fin (k + 1)),
          (∀ x ∈ D, ∀ y : Fin F → Fin (k + 1), (∀ r : Fin F, x r = y r ∨
            ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
            y ∈ D) →
          ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin F),
            (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
            (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), V t a ∈ D) ∧
            (D.card : ℝ) ≤ (T : ℝ) * ((k : ℝ) + 1) ^ d + ε * ((k : ℝ) + 1) ^ F)
        (hε : 0 ≤ ε) (E : Finset (Fin n → Fin (k + 1))) (e₁ : ℝ) (T₁ : ℕ)
        (W : Fin T₁ → Combinatorics.Subspace (Fin F) (Fin (k + 1)) (Fin n))
        (hW1 : ∀ s t : Fin T₁, ∀ a b : Fin F → Fin (k + 1), W s a = W t b → s = t)
        (hW2 : ∀ t : Fin T₁, ∀ a : Fin F → Fin (k + 1), W t a ∈ E)
        (hW3 : (E.card : ℝ) ≤ (T₁ : ℝ) * ((k : ℝ) + 1) ^ F + e₁)
        (i : Fin k) (Dn : Finset (Fin n → Fin (k + 1)))
        (hDn : ∀ x ∈ Dn, ∀ y : Fin n → Fin (k + 1), (∀ r : Fin n, x r = y r ∨
            ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
            y ∈ Dn)
        (E' : Finset (Fin n → Fin (k + 1))) (hE' : ∀ x, x ∈ E' ↔ x ∈ E ∧ x ∈ Dn) => by
      -- 每块上的拉回与 Lemma 12 铺砖
      have hP : ∀ s : Fin T₁, ∃ T' : ℕ,
          ∃ B : Fin T' → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin F),
          (∀ s' t : Fin T', ∀ a b : Fin d → Fin (k + 1), B s' a = B t b → s' = t) ∧
          (∀ t : Fin T', ∀ a : Fin d → Fin (k + 1), W s (B t a) ∈ Dn) ∧
          ((Finset.univ.filter (fun a : Fin F → Fin (k + 1) => W s a ∈ Dn)).card : ℝ) ≤
            (T' : ℝ) * ((k : ℝ) + 1) ^ d + ε * ((k : ℝ) + 1) ^ F := by
        intro s
        obtain ⟨T', B, hB1, hB2, hB3⟩ :=
          hL i (Finset.univ.filter (fun a : Fin F → Fin (k + 1) => W s a ∈ Dn))
            (Tiling_pullback_ins _ _ (W s) Dn hDn _ (fun a => by simp))
        refine ⟨T', B, hB1, fun t a => ?_, hB3⟩
        have := hB2 t a
        simpa using this
      choose T' B hB1 hB2 hB3 using hP
      -- 复合族 W_s ∘ B_{s,t}
      have hU : ∀ p : (Σ s : Fin T₁, Fin (T' s)),
          ∃ U : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
          ∀ a, U a = W p.1 (B p.1 p.2 a) := fun p => Tiling_comp (W p.1) (B p.1 p.2)
      choose U hU using hU
      have hUd : ∀ p q : (Σ s : Fin T₁, Fin (T' s)), ∀ a b : Fin d → Fin (k + 1),
          U p a = U q b → p = q := by
        rintro ⟨s, t⟩ ⟨s', t'⟩ a b h
        rw [hU, hU] at h
        obtain rfl := hW1 s s' _ _ h
        have h' := Tiling_sub_inj (W s) _ _ h
        obtain rfl := hB1 s t t' a b h'
        rfl
      obtain ⟨V, hV1, hV2⟩ := Tiling_reindex U hUd
      refine ⟨_, V, hV1, fun t a => ?_, ?_⟩
      · obtain ⟨p, hp⟩ := hV2 t
        rw [hp, hU, hE']
        exact ⟨hW2 _ _, hB2 _ _ _⟩
      · -- 计数
        have hΦ : Function.Injective
            (fun p : Fin T₁ × (Fin F → Fin (k + 1)) => W p.1 p.2) := by
          rintro ⟨s, a⟩ ⟨t, b⟩ h
          simp only at h
          obtain rfl := hW1 s t a b h
          obtain rfl := Tiling_sub_inj (W s) a b h
          rfl
        obtain ⟨hc1, hc2⟩ := Tiling_count
          (fun p : Fin T₁ × (Fin F → Fin (k + 1)) => W p.1 p.2) hΦ E E'
          (fun x => x ∈ Dn) (fun p => hW2 p.1 p.2) (fun x hx => (hE' x).mp hx)
        have hsumEq := Tiling_sum (fun (s : Fin T₁) (a : Fin F → Fin (k + 1)) => W s a ∈ Dn)
        have hcardY : Fintype.card (Fin T₁ × (Fin F → Fin (k + 1))) = T₁ * (k + 1) ^ F := by
          simp [Fintype.card_prod]
        rw [hcardY] at hc1 hc2
        have hcardκ : Fintype.card (Σ s : Fin T₁, Fin (T' s)) = ∑ s, T' s := by
          simp [Fintype.card_sigma]
        rw [hcardκ]
        have hc1' : E'.card + T₁ * (k + 1) ^ F ≤
            (∑ s, (Finset.univ.filter (fun a : Fin F → Fin (k + 1) => W s a ∈ Dn)).card) +
              E.card := by
          rw [← hsumEq]
          exact hc1
        have hc1R : (E'.card : ℝ) + (T₁ : ℝ) * ((k : ℝ) + 1) ^ F ≤
            (∑ s : Fin T₁,
              ((Finset.univ.filter (fun a : Fin F → Fin (k + 1) => W s a ∈ Dn)).card : ℝ)) +
              (E.card : ℝ) := by
          exact_mod_cast hc1'
        have hc2R : (T₁ : ℝ) * ((k : ℝ) + 1) ^ F ≤ (E.card : ℝ) := by exact_mod_cast hc2
        have hsum : (∑ s : Fin T₁,
              ((Finset.univ.filter (fun a : Fin F → Fin (k + 1) => W s a ∈ Dn)).card : ℝ)) ≤
            ((∑ s, T' s : ℕ) : ℝ) * ((k : ℝ) + 1) ^ d + (T₁ : ℝ) * (ε * ((k : ℝ) + 1) ^ F) := by
          push_cast
          rw [Finset.sum_mul]
          calc _ ≤ ∑ s : Fin T₁, ((T' s : ℝ) * ((k : ℝ) + 1) ^ d + ε * ((k : ℝ) + 1) ^ F) :=
                Finset.sum_le_sum (fun s _ => hB3 s)
            _ = _ := by
                rw [Finset.sum_add_distrib]
                simp [Finset.sum_const, Finset.card_univ]
        have hEn := Tiling_card_le k n E
        have hTε : (T₁ : ℝ) * (ε * ((k : ℝ) + 1) ^ F) ≤ ε * ((k : ℝ) + 1) ^ n := by
          have := mul_le_mul_of_nonneg_left (hc2R.trans hEn) hε
          nlinarith
        linarith
  have Tiling_cor13 : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (ε : ℝ) (hε : 0 < ε), ∀ r d : ℕ, ∃ F : ℕ, ∀ n : ℕ, F ≤ n → ∀ c : Fin r → Fin k,
        ∀ D : Fin r → Finset (Fin n → Fin (k + 1)),
        (∀ j : Fin r, ∀ x ∈ D j, ∀ y : Fin n → Fin (k + 1), (∀ s : Fin n, x s = y s ∨
          ((x s = Fin.castSucc (c j) ∨ x s = Fin.last k) ∧
            (y s = Fin.castSucc (c j) ∨ y s = Fin.last k))) → y ∈ D j) →
        ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
          (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
          (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), ∀ j : Fin r, V t a ∈ D j) ∧
          ((Finset.univ.filter (fun x : Fin n → Fin (k + 1) => ∀ j : Fin r, x ∈ D j)).card : ℝ) ≤
            (T : ℝ) * ((k : ℝ) + 1) ^ d + ((r : ℝ) + 1) * ε * ((k : ℝ) + 1) ^ n :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (ε : ℝ) (hε : 0 < ε) => by
      intro r
      induction r with
      | zero =>
        intro d
        obtain ⟨F, hF⟩ := Tiling_lemma12 k hk hD d ε hε
        refine ⟨F, fun n hn c D _ => ?_⟩
        obtain ⟨T, V, h1, -, h3⟩ := hF n hn ⟨0, hk⟩
          (Finset.univ.filter (fun x : Fin n → Fin (k + 1) => ∀ j : Fin 0, x ∈ D j))
          (fun x _ y _ => by simp)
        refine ⟨T, V, h1, fun t a j => j.elim0, ?_⟩
        simpa using h3
      | succ r ih =>
        intro d
        obtain ⟨F₁, hF₁⟩ := Tiling_lemma12 k hk hD d ε hε
        obtain ⟨F₂, hF₂⟩ := ih F₁
        refine ⟨F₂, fun n hn c D hDi => ?_⟩
        obtain ⟨T₁, W, hW1, hW2, hW3⟩ := hF₂ n hn (fun j => c j.castSucc) (fun j => D j.castSucc)
          (fun j => hDi j.castSucc)
        obtain ⟨T, V, h1, h2, h3⟩ := Tiling_refine k n d F₁ ε (hF₁ F₁ le_rfl) hε.le
          (Finset.univ.filter (fun x : Fin n → Fin (k + 1) => ∀ j : Fin r, x ∈ D j.castSucc))
          (((r : ℝ) + 1) * ε * ((k : ℝ) + 1) ^ n) T₁ W hW1
          (fun t a => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW2 t a⟩) hW3
          (c (Fin.last r)) (D (Fin.last r)) (hDi (Fin.last r))
          (Finset.univ.filter (fun x : Fin n → Fin (k + 1) => ∀ j : Fin (r + 1), x ∈ D j))
          (fun x => by simp [Fin.forall_fin_succ'])
        refine ⟨T, V, h1, fun t a j => ?_, ?_⟩
        · have := h2 t a
          rw [Finset.mem_filter] at this
          exact this.2 j
        · push_cast
          linarith
  have Tiling : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (ε : ℝ) (hε : 0 < ε) (d : ℕ), ∃ F : ℕ, ∀ m : ℕ, F ≤ m → ∀ D : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i : Fin k, ∀ x ∈ D i, ∀ y : Fin m → Fin (k + 1),
          (∀ r : Fin m, x r = y r ∨
            ((x r = Fin.castSucc i ∨ x r = Fin.last k) ∧ (y r = Fin.castSucc i ∨ y r = Fin.last k))) →
          y ∈ D i) →
        ∃ T : ℕ, ∃ V : Fin T → Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m),
          (∀ s t : Fin T, ∀ a b : Fin d → Fin (k + 1), V s a = V t b → s = t) ∧
          (∀ t : Fin T, ∀ a : Fin d → Fin (k + 1), ∀ i : Fin k, V t a ∈ D i) ∧
          ((Finset.univ.filter (fun x : Fin m → Fin (k + 1) => ∀ i : Fin k, x ∈ D i)).card : ℝ) ≤
            (T : ℝ) * ((k : ℝ) + 1) ^ d + ε * ((k : ℝ) + 1) ^ m :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (ε : ℝ) (hε : 0 < ε) (d : ℕ) => by
      obtain ⟨F, hF⟩ := Tiling_cor13 k hk hD (ε / ((k : ℝ) + 1)) (by positivity) k d
      refine ⟨F, fun m hm D hDi => ?_⟩
      obtain ⟨T, V, h1, h2, h3⟩ := hF m hm (fun i => i) D hDi
      refine ⟨T, V, h1, h2, ?_⟩
      have e : ((k : ℝ) + 1) * (ε / ((k : ℝ) + 1)) = ε := by field_simp
      rw [e] at h3
      exact h3
  have IncStep_subspace_inj : ∀ {η α ι : Type} (V : Combinatorics.Subspace η α ι)
      (a b : η → α) (h : V a = V b), a = b :=
    fun {η α ι : Type} (V : Combinatorics.Subspace η α ι)
        (a b : η → α) (h : V a = V b) => by
      funext e
      obtain ⟨i, hi⟩ := V.proper e
      have := congrFun h i
      rwa [Combinatorics.Subspace.apply_inr hi, Combinatorics.Subspace.apply_inr hi] at this
  have IncStep_comp : ∀ {η η' α ι : Type} (W : Combinatorics.Subspace η' α ι)
      (V : Combinatorics.Subspace η α η'), ∃ U : Combinatorics.Subspace η α ι, ∀ a, U a = W (V a) :=
    fun {η η' α ι : Type} (W : Combinatorics.Subspace η' α ι)
        (V : Combinatorics.Subspace η α η') => by
      refine ⟨⟨fun i => Sum.elim Sum.inl V.idxFun (W.idxFun i), fun e => ?_⟩, fun a => ?_⟩
      · obtain ⟨j, hj⟩ := V.proper e
        obtain ⟨i, hi⟩ := W.proper j
        exact ⟨i, by simp [hi, hj]⟩
      · funext i
        simp only [Combinatorics.Subspace.coe_apply]
        cases W.idxFun i <;> simp [Combinatorics.Subspace.coe_apply]
  have IncStep_count : ∀ {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
      (Φ : Y → X) (hΦ : Function.Injective Φ) (Dc G : Finset X) (P : X → Prop) [DecidablePred P]
      (hU : ∀ y, Φ y ∈ Dc) (hG : ∀ x ∈ G, x ∈ Dc ∧ P x), G.card + Fintype.card Y ≤ (Finset.univ.filter (fun y => P (Φ y))).card + Dc.card ∧
      Fintype.card Y ≤ Dc.card :=
    fun {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
        (Φ : Y → X) (hΦ : Function.Injective Φ) (Dc G : Finset X) (P : X → Prop) [DecidablePred P]
        (hU : ∀ y, Φ y ∈ Dc) (hG : ∀ x ∈ G, x ∈ Dc ∧ P x) => by
      set U : Finset X := Finset.univ.image Φ with hUdef
      have hUcard : U.card = Fintype.card Y := by
        rw [hUdef, Finset.card_image_of_injective _ hΦ, Finset.card_univ]
      have hUsub : U ⊆ Dc := by
        intro x hx
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
        exact hU y
      set S := Finset.univ.filter (fun y => P (Φ y)) with hSdef
      have hsub : G ⊆ S.image Φ ∪ (Dc \ U) := by
        intro x hx
        obtain ⟨hxD, hxP⟩ := hG x hx
        by_cases hxU : x ∈ U
        · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hxU
          apply Finset.mem_union_left
          exact Finset.mem_image_of_mem Φ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxP⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxD, hxU⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (S.image Φ) (Dc \ U)
      have h3 : (S.image Φ).card ≤ S.card := Finset.card_image_le
      have h4 : (Dc \ U).card + U.card = Dc.card := Finset.card_sdiff_add_card_eq_card hUsub
      have h5 := Finset.card_le_card hUsub
      constructor <;> omega
  have IncStep_sum : ∀ {T : ℕ} {β : Type} [Fintype β] (Q : Fin T → β → Prop)
      [∀ t, DecidablePred (Q t)], (Finset.univ.filter (fun p : Fin T × β => Q p.1 p.2)).card =
        ∑ t, (Finset.univ.filter (fun b => Q t b)).card :=
    fun {T : ℕ} {β : Type} [Fintype β] (Q : Fin T → β → Prop)
        [∀ t, DecidablePred (Q t)] => by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [Finset.card_filter]
  have IncrementStep : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (δ : ℝ) (hδ : 0 < δ), ∃ γ : ℝ, 0 < γ ∧ ∀ d : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ α : ℝ, δ ≤ α → ∀ A : Finset (Fin n → Fin (k + 1)),
        α * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
        (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a : Fin (k + 1), l a ∈ A) ∨
        ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
          (α + γ) * ((k : ℝ) + 1) ^ d ≤
            ((Finset.univ.filter (fun x : Fin d → Fin (k + 1) => V x ∈ A)).card : ℝ) :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (δ : ℝ) (hδ : 0 < δ) => by
      obtain ⟨γc, hγc, M0, hC⟩ := Correlate k hk hD δ hδ
      refine ⟨γc / 2, by positivity, fun d => ?_⟩
      obtain ⟨F, hF⟩ := Tiling k hk hD (γc ^ 2 / 4) (by positivity) d
      obtain ⟨N, hN⟩ := hC (max M0 F) (le_max_left _ _)
      refine ⟨N, fun n hn α hα A hA => ?_⟩
      by_cases hline : ∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a : Fin (k + 1), l a ∈ A
      · exact Or.inl hline
      right
      push_neg at hline
      obtain ⟨W, D, hins, hDc, hG⟩ := hN n hn α hα A hA hline
      obtain ⟨T, V, hdisj, hin, htile⟩ := hF (max M0 F) (le_max_right _ _) D hins
      -- 计数
      have hΦ : Function.Injective
          (fun p : Fin T × (Fin d → Fin (k + 1)) => V p.1 p.2) := by
        rintro ⟨s, a⟩ ⟨t, b⟩ h
        simp only at h
        have hst : s = t := hdisj s t a b h
        subst hst
        have hab : a = b := IncStep_subspace_inj (V s) a b h
        subst hab
        rfl
      obtain ⟨hcnt, hUD⟩ := IncStep_count
        (fun p : Fin T × (Fin d → Fin (k + 1)) => V p.1 p.2) hΦ
        (Finset.univ.filter (fun x : Fin (max M0 F) → Fin (k + 1) => ∀ i : Fin k, x ∈ D i))
        (Finset.univ.filter (fun x : Fin (max M0 F) → Fin (k + 1) => (∀ i : Fin k, x ∈ D i) ∧ W x ∈ A))
        (fun x => W x ∈ A)
        (fun p => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hin p.1 p.2 i⟩)
        (fun x hx => by
          rw [Finset.mem_filter] at hx
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2.1⟩, hx.2.2⟩)
      rw [IncStep_sum (fun (t : Fin T) (a : Fin d → Fin (k + 1)) => W (V t a) ∈ A)] at hcnt
      have hcardY : Fintype.card (Fin T × (Fin d → Fin (k + 1))) = T * (k + 1) ^ d := by
        simp [Fintype.card_prod]
      rw [hcardY] at hcnt hUD
      have key : ∃ t : Fin T, (α + γc / 2) * ((k : ℝ) + 1) ^ d ≤
          ((Finset.univ.filter (fun a : Fin d → Fin (k + 1) => W (V t a) ∈ A)).card : ℝ) := by
        by_contra hcon
        push_neg at hcon
        have hsum : ((∑ t : Fin T,
            (Finset.univ.filter (fun a : Fin d → Fin (k + 1) => W (V t a) ∈ A)).card : ℕ) : ℝ) ≤
            (T : ℝ) * ((α + γc / 2) * ((k : ℝ) + 1) ^ d) := by
          push_cast
          calc (∑ t : Fin T,
                ((Finset.univ.filter (fun a : Fin d → Fin (k + 1) => W (V t a) ∈ A)).card : ℝ))
              ≤ ∑ _t : Fin T, (α + γc / 2) * ((k : ℝ) + 1) ^ d :=
                Finset.sum_le_sum (fun t _ => (hcon t).le)
            _ = (T : ℝ) * ((α + γc / 2) * ((k : ℝ) + 1) ^ d) := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hcntR : ((Finset.univ.filter (fun x : Fin (max M0 F) → Fin (k + 1) =>
              (∀ i : Fin k, x ∈ D i) ∧ W x ∈ A)).card : ℝ) + (T : ℝ) * ((k : ℝ) + 1) ^ d ≤
            ((∑ t : Fin T,
              (Finset.univ.filter (fun a : Fin d → Fin (k + 1) => W (V t a) ∈ A)).card : ℕ) : ℝ) +
            ((Finset.univ.filter (fun x : Fin (max M0 F) → Fin (k + 1) =>
              ∀ i : Fin k, x ∈ D i)).card : ℝ) := by
          exact_mod_cast hcnt
        have hUDR : (T : ℝ) * ((k : ℝ) + 1) ^ d ≤
            ((Finset.univ.filter (fun x : Fin (max M0 F) → Fin (k + 1) =>
              ∀ i : Fin k, x ∈ D i)).card : ℝ) := by
          exact_mod_cast hUD
        set X := ((Finset.univ.filter (fun x : Fin (max M0 F) → Fin (k + 1) =>
              ∀ i : Fin k, x ∈ D i)).card : ℝ) with hXdef
        set Y := ((Finset.univ.filter (fun x : Fin (max M0 F) → Fin (k + 1) =>
              (∀ i : Fin k, x ∈ D i) ∧ W x ∈ A)).card : ℝ) with hYdef
        set Z := ((∑ t : Fin T,
              (Finset.univ.filter (fun a : Fin d → Fin (k + 1) => W (V t a) ∈ A)).card : ℕ) : ℝ)
          with hZdef
        set P := ((k : ℝ) + 1) ^ (max M0 F) with hPdef
        set Q := ((k : ℝ) + 1) ^ d with hQdef
        have hP : 0 < P := by positivity
        have hQ : 0 < Q := by positivity
        have hXpos : 0 < X := lt_of_lt_of_le (mul_pos hγc hP) hDc
        have hc : 0 ≤ α + γc / 2 := by linarith
        have e1 : γc ^ 2 / 4 * P ≤ γc / 4 * X := by
          have := mul_le_mul_of_nonneg_left hDc (by positivity : (0 : ℝ) ≤ γc / 4)
          nlinarith
        have e2 : (T : ℝ) * ((α + γc / 2) * Q) ≤ (α + γc / 2) * X := by
          have := mul_le_mul_of_nonneg_left hUDR hc
          nlinarith
        have e3 : 0 < γc * X := mul_pos hγc hXpos
        nlinarith
      obtain ⟨t, ht⟩ := key
      obtain ⟨U, hU⟩ := IncStep_comp W (V t)
      refine ⟨U, ?_⟩
      simp only [hU]
      exact ht
  have IterateStep_line_comp : ∀ {α η ι : Type} (V : Combinatorics.Subspace η α ι)
      (l : Combinatorics.Line α η), ∃ L : Combinatorics.Line α ι, ∀ a, L a = V (l a) :=
    fun {α η ι : Type} (V : Combinatorics.Subspace η α ι)
        (l : Combinatorics.Line α η) => by
      refine ⟨⟨fun i => (V.idxFun i).elim some l.idxFun, ?_⟩, ?_⟩
      · obtain ⟨j, hj⟩ := l.proper
        obtain ⟨i, hi⟩ := V.proper j
        exact ⟨i, by simp [hi, hj]⟩
      · intro a
        funext i
        rw [Combinatorics.Line.coe_apply, Combinatorics.Subspace.coe_apply]
        cases h : V.idxFun i with
        | inl c => simp [h]
        | inr j => simp [h, Combinatorics.Line.coe_apply]
  have IterateStep_card_le : ∀ (k n : ℕ) (A : Finset (Fin n → Fin (k + 1))), (A.card : ℝ) ≤ ((k : ℝ) + 1) ^ n :=
    fun (k n : ℕ) (A : Finset (Fin n → Fin (k + 1))) => by
      have h := Finset.card_le_univ A
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
      have h' : ((A.card : ℕ) : ℝ) ≤ (((k + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
  have IterateStep_aux : ∀ (k : ℕ) (δ γ : ℝ) (hγ : 0 < γ) (Nf : ℕ → ℕ)
      (hNf : ∀ d n, Nf d ≤ n → ∀ α : ℝ, δ ≤ α → ∀ A : Finset (Fin n → Fin (k + 1)),
        α * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
        (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a : Fin (k + 1), l a ∈ A) ∨
        ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
          (α + γ) * ((k : ℝ) + 1) ^ d ≤
            ((Finset.univ.filter (fun x : Fin d → Fin (k + 1) => V x ∈ A)).card : ℝ)), ∀ m : ℕ, ∀ α : ℝ, δ ≤ α → 1 < α + (m : ℝ) * γ → ∀ n : ℕ, Nf^[m] 0 ≤ n →
        ∀ A : Finset (Fin n → Fin (k + 1)), α * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a : Fin (k + 1), l a ∈ A :=
    fun (k : ℕ) (δ γ : ℝ) (hγ : 0 < γ) (Nf : ℕ → ℕ)
        (hNf : ∀ d n, Nf d ≤ n → ∀ α : ℝ, δ ≤ α → ∀ A : Finset (Fin n → Fin (k + 1)),
          α * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) →
          (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a : Fin (k + 1), l a ∈ A) ∨
          ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
            (α + γ) * ((k : ℝ) + 1) ^ d ≤
              ((Finset.univ.filter (fun x : Fin d → Fin (k + 1) => V x ∈ A)).card : ℝ)) => by
      intro m
      induction m with
      | zero =>
        intro α _ h1 n _ A hA
        exfalso
        have hc := IterateStep_card_le k n A
        have hpos : (0 : ℝ) < ((k : ℝ) + 1) ^ n := by positivity
        have h1' : 1 < α := by simpa using h1
        nlinarith
      | succ m ih =>
        intro α hα h1 n hn A hA
        rw [Function.iterate_succ_apply'] at hn
        rcases hNf (Nf^[m] 0) n hn α hα A hA with hl | ⟨V, hV⟩
        · exact hl
        · have h1' : 1 < (α + γ) + (m : ℝ) * γ := by push_cast at h1; linarith
          obtain ⟨l, hl⟩ := ih (α + γ) (by linarith) h1' (Nf^[m] 0) le_rfl _ hV
          obtain ⟨L, hL⟩ := IterateStep_line_comp V l
          refine ⟨L, fun a => ?_⟩
          rw [hL]
          have := hl a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this
  have IterateStep : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A), ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
        δ * ((k + 1 : ℕ) : ℝ) ^ n ≤ (A.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a : Fin (k + 1), l a ∈ A :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A) => by
      intro δ hδ
      obtain ⟨γ, hγ, hInc⟩ := IncrementStep k hk hD δ hδ
      choose Nf hNf using hInc
      obtain ⟨T, hT⟩ := exists_nat_gt (1 / γ)
      refine ⟨Nf^[T] 0, fun n hn A hA => ?_⟩
      have hA' : δ * ((k : ℝ) + 1) ^ n ≤ (A.card : ℝ) := by
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hA
        exact hA
      have hTγ : 1 < (T : ℝ) * γ := by
        rw [div_lt_iff₀ hγ] at hT
        exact hT
      exact IterateStep_aux k δ γ hγ Nf hNf T δ le_rfl (by linarith) n hn A hA'
  have DHJall : ∀ (k : ℕ) (hk : 1 ≤ k), ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A :=
    fun (k : ℕ) (hk : 1 ≤ k) => by
      induction k, hk using Nat.le_induction with
      | base => exact DHJone
      | succ k hk ih => exact IterateStep k hk ih
  have SzOfDHJ_shift : ∀ (A : Set ℕ) (n : ℕ) (s : ℕ), (∑ t ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) t) - (s : ℝ) ≤
        ∑ t ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) (t + s) :=
    fun (A : Set ℕ) (n : ℕ) (s : ℕ) => by
      classical
      induction s with
      | zero => simp
      | succ s ih =>
        have h1 : ∑ t ∈ Finset.range (n + 1 + 1), A.indicator (fun _ => (1 : ℝ)) (t + s) =
            ∑ t ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) (t + s) +
              A.indicator (fun _ => (1 : ℝ)) (n + 1 + s) :=
          Finset.sum_range_succ _ _
        have h2 : ∑ t ∈ Finset.range (n + 1 + 1), A.indicator (fun _ => (1 : ℝ)) (t + s) =
            ∑ t ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) (t + 1 + s) +
              A.indicator (fun _ => (1 : ℝ)) (0 + s) :=
          Finset.sum_range_succ' _ _
        have h3 : (0 : ℝ) ≤ A.indicator (fun _ => (1 : ℝ)) (n + 1 + s) := by
          rw [Set.indicator_apply]; split_ifs <;> norm_num
        have h4 : A.indicator (fun _ => (1 : ℝ)) (0 + s) ≤ 1 := by
          rw [Set.indicator_apply]; split_ifs <;> norm_num
        have h5 : ∑ t ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) (t + (s + 1)) =
            ∑ t ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) (t + 1 + s) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show i + (s + 1) = i + 1 + s by omega]
        push_cast
        linarith
  have SzOfDHJ_avg : ∀ (k N n : ℕ) (A : Set ℕ) (δ : ℝ)
      (hS : δ * ((n : ℝ) + 1) ≤ ∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j)
      (hDn : 2 * ((k * N : ℕ) : ℝ) ≤ δ * ((n : ℝ) + 1)), ∃ t : ℕ, δ / 2 * (k : ℝ) ^ N ≤
        ∑ x : Fin N → Fin k, A.indicator (fun _ => (1 : ℝ)) (t + ∑ i, (x i).val) :=
    fun (k N n : ℕ) (A : Set ℕ) (δ : ℝ)
        (hS : δ * ((n : ℝ) + 1) ≤ ∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j)
        (hDn : 2 * ((k * N : ℕ) : ℝ) ≤ δ * ((n : ℝ) + 1)) => by
      have h2 : ∀ x : Fin N → Fin k,
          (∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j) - ((k * N : ℕ) : ℝ) ≤
          ∑ t ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) (t + ∑ i, (x i).val) := by
        intro x
        have hx : ∑ i, (x i).val ≤ k * N := by
          calc ∑ i, (x i).val ≤ ∑ _i : Fin N, k := Finset.sum_le_sum (fun i _ => (x i).isLt.le)
            _ = k * N := by simp [mul_comm]
        have h := SzOfDHJ_shift A n (∑ i, (x i).val)
        have hx' : ((∑ i, (x i).val : ℕ) : ℝ) ≤ ((k * N : ℕ) : ℝ) := by exact_mod_cast hx
        linarith
      have htot : ∑ t ∈ Finset.range (n + 1), δ / 2 * (k : ℝ) ^ N ≤
          ∑ t ∈ Finset.range (n + 1), ∑ x : Fin N → Fin k,
            A.indicator (fun _ => (1 : ℝ)) (t + ∑ i, (x i).val) := by
        rw [Finset.sum_comm]
        have hK : (0 : ℝ) ≤ (k : ℝ) ^ N := by positivity
        have hb : ((n : ℝ) + 1) * (δ / 2) ≤
            (∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j) - ((k * N : ℕ) : ℝ) := by
          linarith
        calc ∑ t ∈ Finset.range (n + 1), δ / 2 * (k : ℝ) ^ N
            = (k : ℝ) ^ N * (((n : ℝ) + 1) * (δ / 2)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
          _ ≤ (k : ℝ) ^ N * ((∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j) -
                ((k * N : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hb hK
          _ = ∑ x : Fin N → Fin k, ((∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j) -
                ((k * N : ℕ) : ℝ)) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp
          _ ≤ _ := Finset.sum_le_sum (fun x _ => h2 x)
      obtain ⟨t, -, ht⟩ := Finset.exists_le_of_sum_le Finset.nonempty_range_add_one htot
      exact ⟨t, ht⟩
  have SzOfDHJ_lineSum : ∀ {k N : ℕ} (l : Combinatorics.Line (Fin k) (Fin N)) (a0 : Fin k), ∃ c b : ℕ, 1 ≤ b ∧ ∀ a : Fin k, ∑ i, (l a i).val = c + b * a.val :=
    fun {k N : ℕ} (l : Combinatorics.Line (Fin k) (Fin N)) (a0 : Fin k) => by
      classical
      obtain ⟨S, hS⟩ : ∃ S : Finset (Fin N), S = Finset.univ.filter (fun i => l.idxFun i = none) :=
        ⟨_, rfl⟩
      have hmem : ∀ i, i ∈ S ↔ l.idxFun i = none := by intro i; simp [hS]
      refine ⟨∑ i ∈ Sᶜ, (l a0 i).val, S.card, ?_, ?_⟩
      · obtain ⟨i₀, hi₀⟩ := l.proper
        exact Finset.card_pos.mpr ⟨i₀, (hmem i₀).2 hi₀⟩
      · intro a
        have e1 : ∑ i ∈ S, (l a i).val = S.card * a.val := by
          rw [← smul_eq_mul, ← Finset.sum_const]
          apply Finset.sum_congr rfl
          intro i hi
          rw [l.apply_none _ _ ((hmem i).1 hi)]
        have e2 : ∑ i ∈ Sᶜ, (l a i).val = ∑ i ∈ Sᶜ, (l a0 i).val := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : l.idxFun i ≠ none := fun h => (Finset.mem_compl.1 hi) ((hmem i).2 h)
          obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi'
          rw [l.apply_some hy.symm, l.apply_some hy.symm]
        rw [← Finset.sum_add_sum_compl S, e1, e2]
        ring
  have SzOfDHJ : ∀ (k : ℕ) (hk : 1 ≤ k)
      (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
        δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
      (A : Set ℕ) (δ : ℝ) (hδ : 0 < δ), ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
        δ ≤ (∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j) / ((n : ℝ) + 1) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A :=
    fun (k : ℕ) (hk : 1 ≤ k)
        (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin k),
          δ * (k : ℝ) ^ n ≤ (A.card : ℝ) → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a : Fin k, l a ∈ A)
        (A : Set ℕ) (δ : ℝ) (hδ : 0 < δ) => by
      classical
      obtain ⟨N₀, hN₀⟩ := hD (δ / 2) (by linarith)
      refine ⟨⌈2 * ((k * N₀ : ℕ) : ℝ) / δ⌉₊, fun n hn hdens => ?_⟩
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hSge : δ * ((n : ℝ) + 1) ≤ ∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j := by
        rwa [le_div_iff₀ hn1] at hdens
      have hMn : 2 * ((k * N₀ : ℕ) : ℝ) / δ ≤ n := Nat.ceil_le.mp hn
      have hD2 : 2 * ((k * N₀ : ℕ) : ℝ) ≤ δ * ((n : ℝ) + 1) := by
        rw [div_le_iff₀ hδ] at hMn; nlinarith
      obtain ⟨t, ht⟩ := SzOfDHJ_avg k N₀ n A δ hSge hD2
      have hcard : ((Finset.univ.filter (fun x : Fin N₀ → Fin k => t + ∑ i, (x i).val ∈ A)).card : ℝ) =
          ∑ x : Fin N₀ → Fin k, A.indicator (fun _ => (1 : ℝ)) (t + ∑ i, (x i).val) := by
        rw [Finset.card_filter, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Set.indicator_apply]
        split_ifs <;> simp
      obtain ⟨l, hl⟩ := hN₀ N₀ le_rfl
        (Finset.univ.filter (fun x : Fin N₀ → Fin k => t + ∑ i, (x i).val ∈ A))
        (by rw [hcard]; exact ht)
      obtain ⟨c, b, hb, hcb⟩ := SzOfDHJ_lineSum l ⟨0, hk⟩
      refine ⟨t + c, b, hb, fun j hj => ?_⟩
      have h2 : t + ∑ i, (l ⟨j, hj⟩ i).val ∈ A := (Finset.mem_filter.mp (hl ⟨j, hj⟩)).2
      rw [hcb ⟨j, hj⟩] at h2
      have h3 : t + (c + b * j) ∈ A := h2
      rwa [← add_assoc] at h3
  open LeanEval.Combinatorics in
  have SzWindow : ∀ (A : Set ℕ) (h : 0 < upperDensity A), ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        δ ≤ (∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j) / ((n : ℝ) + 1) :=
    fun (A : Set ℕ) (h : 0 < upperDensity A) => by
      have hnonneg : ∀ n : ℕ, (0 : ℝ) ≤
          (∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j) / ((n : ℝ) + 1) := by
        intro n
        apply div_nonneg
        · apply Finset.sum_nonneg
          intro j _
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) j
        · positivity
      refine ⟨upperDensity A / 2, by positivity, fun N => ?_⟩
      by_contra hcon
      push_neg at hcon
      have hev : ∀ᶠ n in Filter.atTop,
          (∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j) / ((n : ℝ) + 1)
            ≤ upperDensity A / 2 := by
        rw [Filter.eventually_atTop]
        exact ⟨N, fun n hn => (hcon n hn).le⟩
      have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
          (fun n : ℕ =>
            (∑ j ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) j) / ((n : ℝ) + 1)) :=
        Filter.isCoboundedUnder_le_of_le Filter.atTop hnonneg
      have hle : upperDensity A ≤ upperDensity A / 2 := Filter.limsup_le_of_le hcob hev
      linarith
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact ⟨0, 1, le_refl 1, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  · obtain ⟨δ, hδ, hwin⟩ := SzWindow A h
    obtain ⟨M, hM⟩ := SzOfDHJ k hk (DHJall k hk) A δ hδ
    obtain ⟨n, hn, hdens⟩ := hwin M
    exact hM n hn hdens)"###)
    let act : Lean.Elab.Tactic.TacticM Unit :=
      withTheReader Lean.Core.Context (fun c => { c with maxHeartbeats := 0 })
        (do Lean.Elab.Tactic.evalTactic stx; Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing)
    controlAt (EIO Lean.Exception) fun runInBase => do
      let t ← EIO.asTask (runInBase act) Task.Priority.dedicated
      match ← IO.wait t with
      | .ok a => pure a
      | .error e => throw e

end Submission
