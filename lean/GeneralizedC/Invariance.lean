/-
GeneralizedC/Invariance.lean: c* is invariant under its own Lorentz group (T14, CP4).

  T14a isCausal_frame_iff, isTimelike_frame_iff, isLightlike_frame_iff
                                   Λ preserves Q_c ⇒ a chord of the new table is c-causal
                                   (timelike, lightlike) ⇔ the old chord is
  T14b frameTime_injective         Λ preserves Q_c and every chord is c-causal ⇒ new times distinct
  T14  critSpeed_frame             Λ ∈ O(1,3; c*) ⇒ the new table is a table with the same c*
       critSpeed_frame_G           the same for a diagonal state metric G (via G^{1/2}, T9d)
       rapidityBoost               explicit boost along the first state axis (rapidity η), in O(1,3; c)

Design (PROGRESS D-029 C6, C7; cp4_breakdown T14): the whole group O(1,3; c*) as
`formGroup (minkowskiQ c*)` (boosts, rotations, reflections, time reversal), G = I first with a
diagonal-G corollary. The proof needs only linearity and E1 (no limits, no T6).
-/
import GeneralizedC.Tables
import GeneralizedC.Gauge
import GeneralizedC.Hyperbolic

open NNReal

namespace GeneralizedC

variable {ι : Type*}

/-! ### A table seen in another frame -/

/-- The time stamps of the table in the frame `Λ`: `t′ᵢ = (Λ(tᵢ, xᵢ)).1`. -/
def frameTime (Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)) (t : ι → ℝ) (x : ι → State) (i : ι) : ℝ :=
  (Λ (t i, x i)).1

/-- The states of the table in the frame `Λ`: `x′ᵢ = (Λ(tᵢ, xᵢ)).2`. -/
def frameState (Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)) (t : ι → ℝ) (x : ι → State) (i : ι) :
    State :=
  (Λ (t i, x i)).2

/-- `Λ` is linear, so a chord of the new table is `Λ` applied to the old chord. -/
theorem tableChord_frame (Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)) (t : ι → ℝ) (x : ι → State)
    (i j : ι) :
    tableChord (frameTime Λ t x) (frameState Λ t x) i j = Λ (tableChord t x i j) := by
  have : tableChord t x i j = (t j, x j) - (t i, x i) := rfl
  rw [this, map_sub]
  rfl

/-- Membership in `formGroup Q`, used as an equation. -/
theorem formGroup_apply {Q : ℝ × State → ℝ} {Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)}
    (hΛ : Λ ∈ formGroup Q) (p : ℝ × State) : Q (Λ p) = Q p :=
  hΛ p

/-! ### T14a: causality is frame-independent -/

/-- **T14a (causal).** For any `c` and any `Λ` preserving `Q_c`: a chord of the new table is
`c`-causal ⇔ the original chord is (cp3_breakdown T6 B3). -/
theorem isCausal_frame_iff {c : ℝ} {Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)}
    (hΛ : Λ ∈ formGroup (minkowskiQ c)) (t : ι → ℝ) (x : ι → State) (i j : ι) :
    IsCausal c (tableChord (frameTime Λ t x) (frameState Λ t x) i j) ↔
      IsCausal c (tableChord t x i j) := by
  unfold IsCausal
  rw [tableChord_frame, formGroup_apply hΛ]

/-- **T14a (timelike).** -/
theorem isTimelike_frame_iff {c : ℝ} {Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)}
    (hΛ : Λ ∈ formGroup (minkowskiQ c)) (t : ι → ℝ) (x : ι → State) (i j : ι) :
    IsTimelike c (tableChord (frameTime Λ t x) (frameState Λ t x) i j) ↔
      IsTimelike c (tableChord t x i j) := by
  unfold IsTimelike
  rw [tableChord_frame, formGroup_apply hΛ]

/-- **T14a (lightlike).** -/
theorem isLightlike_frame_iff {c : ℝ} {Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)}
    (hΛ : Λ ∈ formGroup (minkowskiQ c)) (t : ι → ℝ) (x : ι → State) (i j : ι) :
    IsLightlike c (tableChord (frameTime Λ t x) (frameState Λ t x) i j) ↔
      IsLightlike c (tableChord t x i j) := by
  unfold IsLightlike
  rw [tableChord_frame, formGroup_apply hΛ]

/-! ### T14b: the new table is a table -/

/-- **T14b.** If `Λ` preserves `Q_c`, the times are distinct and every chord is `c`-causal, then
the new times are distinct. A non-zero causal vector cannot have `Δt′ = 0`, since then
`−‖Δx′‖² ≥ 0` forces `Δx′ = 0`. Holds for every real `c`. -/
theorem frameTime_injective {c : ℝ} {Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)}
    (hΛ : Λ ∈ formGroup (minkowskiQ c)) {t : ι → ℝ} (ht : Function.Injective t)
    {x : ι → State} (hcaus : ∀ i j, IsCausal c (tableChord t x i j)) :
    Function.Injective (frameTime Λ t x) := by
  intro i j hij
  by_contra hne
  set q := tableChord (frameTime Λ t x) (frameState Λ t x) i j with hq_def
  have h1 : q.1 = 0 := by
    show frameTime Λ t x j - frameTime Λ t x i = 0
    rw [hij, sub_self]
  have h2 : IsCausal c q := (isCausal_frame_iff hΛ t x i j).2 (hcaus i j)
  unfold IsCausal minkowskiQ at h2
  rw [h1] at h2
  have h3 : ‖q.2‖ = 0 := by nlinarith [norm_nonneg q.2]
  have hq0 : Λ (tableChord t x i j) = 0 := by
    rw [← tableChord_frame, ← hq_def]
    exact Prod.ext h1 (norm_eq_zero.1 h3)
  have h4 := congrArg Prod.fst ((LinearEquiv.map_eq_zero_iff Λ).1 hq0)
  change t j - t i = 0 at h4
  exact hne (ht (sub_eq_zero.1 h4).symm)

/-! ### T14: invariance of c* -/

/-- **T14.** Let a finite table have distinct times and critical speed `c*` (E1, all pairs), and
let `Λ ∈ O(1,3; c*)`, i.e. `Λ` preserves `Q_{c*}`. Then the table seen in the frame `Λ` again
has distinct times (T14b) and the same critical speed `c*`. The table version of "every inertial
observer measures the same `c`". No `c* > 0` and no "at least two samples" is needed: for a
degenerate table both sides are `0` (a cone without geometry, T8). -/
theorem critSpeed_frame [Fintype ι] {t : ι → ℝ} (ht : Function.Injective t) {x : ι → State}
    {Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)} (hΛ : Λ ∈ formGroup (minkowskiQ (critSpeed t x))) :
    Function.Injective (frameTime Λ t x) ∧
      critSpeed (frameTime Λ t x) (frameState Λ t x) = critSpeed t x := by
  have hcaus : ∀ i j, IsCausal (critSpeed t x) (tableChord t x i j) := fun i j =>
    allCausalOn_critSpeedOn ht x Finset.univ (i, j) (Finset.mem_univ _)
  have ht' := frameTime_injective hΛ ht hcaus
  refine ⟨ht', le_antisymm ?_ ?_⟩
  · -- every new chord is c*-causal (T14a), so the new c* ≤ c* (E1b)
    rw [← NNReal.coe_le_coe]
    exact (allCausalOn_iff (critSpeed t x).coe_nonneg ht' _ Finset.univ).1 fun p _ =>
      (isCausal_frame_iff hΛ t x p.1 p.2).2 (hcaus p.1 p.2)
  · -- the old steepest chord is lightlike (E1c); so is its image, whose slope is then c*
    rcases isEmpty_or_nonempty ι with hι | hι
    · have : critSpeed t x = 0 := by
        simp [critSpeed, critSpeedOn, Finset.univ_eq_empty]
      rw [this]
      exact zero_le
    · obtain ⟨p, -, hsl, hlight⟩ :=
        exists_isLightlike_critSpeedOn ht x (Finset.univ_nonempty (α := ι × ι))
      rcases eq_or_ne p.1 p.2 with heq | hne
      · have : critSpeed t x = 0 := by
          change critSpeedOn t x Finset.univ = 0
          rw [← hsl]
          ext
          simp [heq]
        rw [this]
        exact zero_le
      · have hl' := (isLightlike_frame_iff hΛ t x p.1 p.2).2 hlight
        have hsl' := slope_eq_of_isLightlike (critSpeed t x).coe_nonneg ht' _ hne hl'
        rw [← NNReal.coe_le_coe, ← hsl']
        exact NNReal.coe_le_coe.2 (slope_le_critSpeedOn _ _ (Finset.mem_univ p))

/-- **T14 (diagonal G).** With a diagonal state metric `G ≻ 0`, the critical speed is that of
the table `G^{1/2} x`. For `Λ ∈ O_G(1,3; c*)` (T9c's `lorentzGroupG`), the table seen in the
frame `Λ` has the same `G`-critical speed. Derived from the `G = I` version through `G^{1/2}`
(D-003, T9d). -/
theorem critSpeed_frame_G [Fintype ι] {t : ι → ℝ} (ht : Function.Injective t) {x : ι → State}
    {g : Fin 3 → ℝ} (hg : ∀ i, 0 < g i) {Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)}
    (hΛ : Λ ∈ lorentzGroupG (critSpeed t fun i => sqrtG g hg (x i)) g) :
    critSpeed (frameTime Λ t x) (fun i => sqrtG g hg (frameState Λ t x i))
      = critSpeed t fun i => sqrtG g hg (x i) := by
  set c : ℝ := ((critSpeed t fun i => sqrtG g hg (x i) : ℝ≥0) : ℝ)
  set E : (ℝ × State) ≃ₗ[ℝ] (ℝ × State) := (LinearEquiv.refl ℝ ℝ).prodCongr (sqrtG g hg)
  have hE : ∀ p, minkowskiQ c (E p) = minkowskiQG c g p := fun p =>
    (minkowskiQG_eq c hg p).symm
  have hM : E * Λ * E⁻¹ ∈ formGroup (minkowskiQ c) := by
    intro q
    show minkowskiQ c (E (Λ (E.symm q))) = minkowskiQ c q
    rw [hE, formGroup_apply hΛ, ← hE, LinearEquiv.apply_symm_apply]
  have hEx : ∀ i, E.symm (t i, sqrtG g hg (x i)) = (t i, x i) := fun i =>
    E.symm_apply_apply (t i, x i)
  have key := (critSpeed_frame ht hM).2
  have h1 : frameTime (E * Λ * E⁻¹) t (fun i => sqrtG g hg (x i)) = frameTime Λ t x := by
    funext i
    show (E (Λ (E.symm (t i, sqrtG g hg (x i))))).1 = _
    rw [hEx]
    rfl
  have h2 : frameState (E * Λ * E⁻¹) t (fun i => sqrtG g hg (x i))
      = fun i => sqrtG g hg (frameState Λ t x i) := by
    funext i
    show (E (Λ (E.symm (t i, sqrtG g hg (x i))))).2 = _
    rw [hEx]
    rfl
  rw [h1, h2] at key
  exact key

/-! ### An explicit boost (C7) and the D-014 examples -/

/-- The rapidity boost along the first state axis, for `c ≠ 0`:
`t′ = cosh η · t − (sinh η / c) · x₀`,  `x′₀ = cosh η · x₀ − c sinh η · t`,  other axes fixed.
Written as `x′ = x + ((cosh η − 1) x₀ − c sinh η t) e₁`. As a linear map; `rapidityBoost`
below is the equivalence (inverse: the boost at `−η`). -/
noncomputable def rapidityBoostLin (c η : ℝ) : (ℝ × State) →ₗ[ℝ] (ℝ × State) where
  toFun p := (Real.cosh η * p.1 - Real.sinh η / c * p.2 0,
    p.2 + ((Real.cosh η - 1) * p.2 0 - c * Real.sinh η * p.1) • e₁)
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply]
      ring
    · simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply]
      rw [show ((Real.cosh η - 1) * (p.2 0 + q.2 0) - c * Real.sinh η * (p.1 + q.1))
          = ((Real.cosh η - 1) * p.2 0 - c * Real.sinh η * p.1)
            + ((Real.cosh η - 1) * q.2 0 - c * Real.sinh η * q.1) by ring, add_smul]
      abel
  map_smul' r p := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
        smul_add, smul_smul]
      congr 2
      ring

theorem rapidityBoostLin_apply (c η : ℝ) (p : ℝ × State) :
    rapidityBoostLin c η p = (Real.cosh η * p.1 - Real.sinh η / c * p.2 0,
      p.2 + ((Real.cosh η - 1) * p.2 0 - c * Real.sinh η * p.1) • e₁) :=
  rfl

/-- Components of `e₁`. -/
theorem e₁_apply (i : Fin 3) : e₁ i = if i = 0 then 1 else 0 := by
  simp [e₁, EuclideanSpace.single]

/-- The boost at `−η` undoes the boost at `η` (needs `c ≠ 0` and `cosh² − sinh² = 1`). -/
theorem rapidityBoostLin_neg_comp {c : ℝ} (hc : c ≠ 0) (η : ℝ) :
    (rapidityBoostLin c (-η)).comp (rapidityBoostLin c η) = LinearMap.id := by
  have key := Real.cosh_sq η
  refine LinearMap.ext fun p => Prod.ext ?_ ?_
  · simp only [LinearMap.comp_apply, rapidityBoostLin_apply, LinearMap.id_apply, Real.cosh_neg,
      Real.sinh_neg, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, e₁_apply]
    simp
    field_simp
    linear_combination (c * p.1) * key
  · ext i
    simp only [LinearMap.comp_apply, rapidityBoostLin_apply, LinearMap.id_apply, Real.cosh_neg,
      Real.sinh_neg, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, e₁_apply]
    fin_cases i
    · simp
      field_simp
      linear_combination (p.2 0) * key
    · simp
    · simp

/-- **The rapidity boost** as a linear equivalence, for `c ≠ 0`. -/
noncomputable def rapidityBoost {c : ℝ} (hc : c ≠ 0) (η : ℝ) :
    (ℝ × State) ≃ₗ[ℝ] (ℝ × State) :=
  LinearEquiv.ofLinearMap (rapidityBoostLin c η) (rapidityBoostLin c (-η))
    (by simpa using rapidityBoostLin_neg_comp hc (-η)) (rapidityBoostLin_neg_comp hc η)

/-- The rapidity boost is in `O(1,3; c)`: it preserves `Q_c` (`cosh² − sinh² = 1`). -/
theorem rapidityBoost_mem {c : ℝ} (hc : c ≠ 0) (η : ℝ) :
    rapidityBoost hc η ∈ formGroup (minkowskiQ c) := by
  intro p
  have key := Real.cosh_sq η
  show minkowskiQ c (rapidityBoostLin c η p) = minkowskiQ c p
  simp only [minkowskiQ, rapidityBoostLin_apply, norm_sq_state, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, e₁_apply]
  simp
  field_simp
  linear_combination (c ^ 2 * p.1 ^ 2 - p.2 0 ^ 2) * key

/-- Point reflection `p ↦ −p` (time reversal and space reflection) is in `O(1,3; c)`. -/
theorem neg_mem_formGroup (c : ℝ) : LinearEquiv.neg ℝ ∈ formGroup (minkowskiQ c) := by
  intro p
  simp [minkowskiQ]

/-- D-014 for T14, trivial case: reversing time and space (`Λ = −I`) keeps every table's c*. -/
example [Fintype ι] {t : ι → ℝ} (ht : Function.Injective t) (x : ι → State) :
    critSpeed (frameTime (LinearEquiv.neg ℝ) t x) (frameState (LinearEquiv.neg ℝ) t x)
      = critSpeed t x :=
  (critSpeed_frame ht (neg_mem_formGroup _)).2

/-- A two-sample table on the first axis, `(0, 0)` and `(1, e₁)`: its critical speed is `1`. -/
theorem critSpeed_twoSample :
    critSpeed (fun k : Fin 2 => (k : ℝ)) (fun k => (k : ℝ) • e₁) = 1 := by
  have ht : Function.Injective fun k : Fin 2 => (k : ℝ) :=
    Nat.cast_injective.comp Fin.val_injective
  apply le_antisymm
  · rw [← NNReal.coe_le_coe, NNReal.coe_one]
    have h := (allCausalOn_iff (norm_nonneg e₁) ht (fun k : Fin 2 => (k : ℝ) • e₁)
      Finset.univ).1 fun p _ => isCausal_tableChord_smul _ e₁ p.1 p.2
    rwa [show ‖e₁‖ = 1 by simpa using norm_smul_e₁ 1] at h
  · have h := slope_le_critSpeedOn (fun k : Fin 2 => (k : ℝ)) (fun k => (k : ℝ) • e₁)
      (Finset.mem_univ ((0 : Fin 2), (1 : Fin 2)))
    refine le_trans (le_of_eq ?_) h
    ext
    simp [show ‖e₁‖ = 1 by simpa using norm_smul_e₁ 1]

/-- D-014 for T14, non-trivial case: boosting the two-sample table with rapidity `η` (in units
`c = c* = 1`) keeps its critical speed `1`, and its new times are distinct. -/
example (η : ℝ) :
    critSpeed (frameTime (rapidityBoost one_ne_zero η) (fun k : Fin 2 => (k : ℝ))
      (fun k => (k : ℝ) • e₁))
      (frameState (rapidityBoost one_ne_zero η) (fun k : Fin 2 => (k : ℝ))
        (fun k => (k : ℝ) • e₁)) = 1 := by
  have ht : Function.Injective fun k : Fin 2 => (k : ℝ) :=
    Nat.cast_injective.comp Fin.val_injective
  have hΛ : rapidityBoost one_ne_zero η ∈
      formGroup (minkowskiQ (critSpeed (fun k : Fin 2 => (k : ℝ)) (fun k => (k : ℝ) • e₁))) := by
    rw [critSpeed_twoSample, NNReal.coe_one]
    exact rapidityBoost_mem one_ne_zero η
  rw [(critSpeed_frame ht hΛ).2, critSpeed_twoSample]

/-- D-014 for T14 (diagonal G): `Λ = −I` lies in every `O_G(1,3; c)` (T9c), so it keeps the
`G`-critical speed, here with `G = diag(4, 4, 4)`. -/
example [Fintype ι] {t : ι → ℝ} (ht : Function.Injective t) (x : ι → State) :
    critSpeed (frameTime (LinearEquiv.neg ℝ) t x)
      (fun i => sqrtG (fun _ => 4) (fun _ => by norm_num) (frameState (LinearEquiv.neg ℝ) t x i))
      = critSpeed t fun i => sqrtG (fun _ => 4) (fun _ => by norm_num) (x i) :=
  critSpeed_frame_G ht _ (neg_mem_lorentzGroupG _ _)

end GeneralizedC
