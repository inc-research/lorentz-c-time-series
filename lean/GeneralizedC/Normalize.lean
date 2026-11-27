/-
GeneralizedC/Normalize.lean: c = 1 in the observer's own units (CP5: T15).

  T15a critSpeedOn_smul                c*_S(t, a·x) = |a| · c*_S(t, x)
       critSpeedOn_normalize           c*_S > 0 ⇒ c*_S(t, x / c*_S) = 1
  T15b isCausal_normalize_iff (+ timelike, lightlike)
                                       a chord of x is c-causal ⇔ the chord of x/c is 1-causal
  T15c mem_formGroup_iff_normalized    Λ ∈ O(1,3; c) ⇔ S_c Λ S_c⁻¹ ∈ O(1,3), S_c = 1 ⊕ c⁻¹·I
  T15d critSpeed_frame_normalized      every Λ ∈ O(1,3) keeps the normalized table's c* = 1

Design (PROGRESS D-034 C7, cp5_breakdown T15): the **state** is rescaled by 1/c*, not the time,
so tick time τₖ = k stays an integer grid (D-031 R3).
-/
import GeneralizedC.Invariance

open NNReal

namespace GeneralizedC

variable {ι : Type*}

/-! ### T15a: the value -/

/-- Every chord slope scales by `|a|` when the state is scaled by `a`. -/
theorem coe_slope_smul (t : ι → ℝ) (x : ι → State) (a : ℝ) (i j : ι) :
    (slope t (fun k => a • x k) i j : ℝ) = |a| * slope t x i j := by
  simp only [coe_slope, ← smul_sub, norm_smul, Real.norm_eq_abs, mul_div_assoc]

/-- **T15a.** Scaling the state by `a` scales the critical speed by `|a|`. -/
theorem critSpeedOn_smul (t : ι → ℝ) (x : ι → State) (S : Finset (ι × ι)) (a : ℝ) :
    (critSpeedOn t (fun k => a • x k) S : ℝ) = |a| * critSpeedOn t x S := by
  have hc := (critSpeedOn t x S).coe_nonneg
  apply le_antisymm
  · rw [critSpeedOn_le_iff (by positivity)]
    intro p hp
    rw [coe_slope_smul]
    exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (slope_le_critSpeedOn t x hp))
      (abs_nonneg a)
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have ha' : 0 < |a| := abs_pos.2 ha
      rw [← le_div_iff₀' ha', critSpeedOn_le_iff (by positivity)]
      intro p hp
      rw [le_div_iff₀' ha', ← coe_slope_smul]
      exact NNReal.coe_le_coe.2 (slope_le_critSpeedOn t _ hp)

/-- **T15a (normalization).** If `c*_S > 0`, the state rescaled by `1/c*_S` has `c*_S = 1`. -/
theorem critSpeedOn_normalize (t : ι → ℝ) (x : ι → State) (S : Finset (ι × ι))
    (h : 0 < (critSpeedOn t x S : ℝ)) :
    critSpeedOn t (fun k => (critSpeedOn t x S : ℝ)⁻¹ • x k) S = 1 := by
  apply NNReal.coe_injective
  rw [critSpeedOn_smul, abs_inv, abs_of_pos h, inv_mul_cancel₀ h.ne', NNReal.coe_one]

/-! ### T15b: the causal structure -/

/-- `Q₁(Δt, c⁻¹Δx) = c⁻² Q_c(Δt, Δx)`. -/
theorem minkowskiQ_one_smul {c : ℝ} (hc : c ≠ 0) (Δt : ℝ) (Δx : State) :
    minkowskiQ 1 (Δt, c⁻¹ • Δx) = (c⁻¹) ^ 2 * minkowskiQ c (Δt, Δx) := by
  simp only [minkowskiQ, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, one_pow, one_mul]
  field_simp

/-- The chord of the rescaled table is `(Δt, c⁻¹Δx)`. -/
theorem tableChord_smul (t : ι → ℝ) (x : ι → State) (a : ℝ) (i j : ι) :
    tableChord t (fun k => a • x k) i j = ((tableChord t x i j).1, a • (tableChord t x i j).2) := by
  simp only [tableChord, smul_sub]

/-- **T15b (causal).** For `c ≠ 0`: a chord of `x` is `c`-causal ⇔ the chord of `x/c` is
`1`-causal. (T2b with `α = 1`, `β = 1/c`.) -/
theorem isCausal_normalize_iff {c : ℝ} (hc : c ≠ 0) (t : ι → ℝ) (x : ι → State) (i j : ι) :
    IsCausal c (tableChord t x i j) ↔ IsCausal 1 (tableChord t (fun k => c⁻¹ • x k) i j) := by
  have h2 : 0 < (c⁻¹) ^ 2 := by positivity
  unfold IsCausal
  rw [tableChord_smul, minkowskiQ_one_smul hc]
  exact (mul_nonneg_iff_of_pos_left h2).symm

/-- **T15b (timelike).** -/
theorem isTimelike_normalize_iff {c : ℝ} (hc : c ≠ 0) (t : ι → ℝ) (x : ι → State) (i j : ι) :
    IsTimelike c (tableChord t x i j) ↔ IsTimelike 1 (tableChord t (fun k => c⁻¹ • x k) i j) := by
  have h2 : 0 < (c⁻¹) ^ 2 := by positivity
  unfold IsTimelike
  rw [tableChord_smul, minkowskiQ_one_smul hc]
  exact (mul_pos_iff_of_pos_left h2).symm

/-- **T15b (lightlike).** -/
theorem isLightlike_normalize_iff {c : ℝ} (hc : c ≠ 0) (t : ι → ℝ) (x : ι → State) (i j : ι) :
    IsLightlike c (tableChord t x i j) ↔
      IsLightlike 1 (tableChord t (fun k => c⁻¹ • x k) i j) := by
  have h2 : (c⁻¹) ^ 2 ≠ 0 := by positivity
  unfold IsLightlike
  rw [tableChord_smul, minkowskiQ_one_smul hc, mul_eq_zero, or_iff_right h2]

/-! ### T15c: the group -/

/-- `S_c = 1 ⊕ c⁻¹·I`: time unchanged, state scaled by `1/c` (the observer's natural units). -/
noncomputable def stateScaleC {c : ℝ} (hc : c ≠ 0) : (ℝ × State) ≃ₗ[ℝ] (ℝ × State) :=
  (LinearEquiv.refl ℝ ℝ).prodCongr (LinearEquiv.smulOfNeZero ℝ State c⁻¹ (inv_ne_zero hc))

theorem minkowskiQ_one_stateScaleC {c : ℝ} (hc : c ≠ 0) (p : ℝ × State) :
    minkowskiQ 1 (stateScaleC hc p) = (c⁻¹) ^ 2 * minkowskiQ c p :=
  minkowskiQ_one_smul hc p.1 p.2

/-- **T15c.** For `c ≠ 0`: `Λ ∈ O(1,3; c)` ⇔ `S_c Λ S_c⁻¹ ∈ O(1,3)`. In the observer's natural
units the generalized Lorentz group is the textbook one. (The scalar case of T9c.) -/
theorem mem_formGroup_iff_normalized {c : ℝ} (hc : c ≠ 0) (Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)) :
    Λ ∈ formGroup (minkowskiQ c) ↔
      stateScaleC hc * Λ * (stateScaleC hc)⁻¹ ∈ lorentzGroup := by
  set S := stateScaleC hc
  have h2 : (c⁻¹) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h q
    show minkowskiQ 1 (S (Λ (S.symm q))) = minkowskiQ 1 q
    rw [minkowskiQ_one_stateScaleC, formGroup_apply h, ← minkowskiQ_one_stateScaleC hc,
      LinearEquiv.apply_symm_apply]
  · intro h p
    have := h (S p)
    change minkowskiQ 1 (S (Λ (S.symm (S p)))) = minkowskiQ 1 (S p) at this
    rw [LinearEquiv.symm_apply_apply, minkowskiQ_one_stateScaleC, minkowskiQ_one_stateScaleC] at this
    exact mul_left_cancel₀ h2 this

/-! ### T15d: T14 in standard form -/

/-- **T15d.** Normalize a table by its critical speed (`c* > 0`). Every `Λ` in the textbook
Lorentz group `O(1,3)` leaves the normalized table's critical speed equal to `1`. -/
theorem critSpeed_frame_normalized [Fintype ι] {t : ι → ℝ} (ht : Function.Injective t)
    {x : ι → State} (h : 0 < (critSpeed t x : ℝ)) {Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)}
    (hΛ : Λ ∈ lorentzGroup) :
    critSpeed (frameTime Λ t fun k => (critSpeed t x : ℝ)⁻¹ • x k)
      (frameState Λ t fun k => (critSpeed t x : ℝ)⁻¹ • x k) = 1 := by
  have h1 : critSpeed t (fun k => (critSpeed t x : ℝ)⁻¹ • x k) = 1 :=
    critSpeedOn_normalize t x Finset.univ h
  have hΛ' : Λ ∈ formGroup (minkowskiQ (critSpeed t fun k => (critSpeed t x : ℝ)⁻¹ • x k)) := by
    rw [h1, NNReal.coe_one]
    exact hΛ
  rw [(critSpeed_frame ht hΛ').2, h1]

/-- D-014 for T15a: the two-sample table of `Invariance.lean` (c* = 1) with its state doubled
has c* = 2. -/
example : (critSpeed (fun k : Fin 2 => (k : ℝ)) (fun k => (2 : ℝ) • ((k : ℝ) • e₁)) : ℝ) = 2 := by
  rw [critSpeed, critSpeedOn_smul, ← critSpeed, critSpeed_twoSample]
  norm_num

/-- D-014 for T15a (normalization) and T15d: normalizing that doubled table gives c* = 1, and the
rapidity boost of `O(1,3)` keeps it at 1. -/
example (η : ℝ) :
    critSpeed (frameTime (rapidityBoost one_ne_zero η) (fun k : Fin 2 => (k : ℝ))
        fun k => (critSpeed (fun k : Fin 2 => (k : ℝ)) (fun k => (2 : ℝ) • ((k : ℝ) • e₁)) : ℝ)⁻¹
          • ((2 : ℝ) • ((k : ℝ) • e₁)))
      (frameState (rapidityBoost one_ne_zero η) (fun k : Fin 2 => (k : ℝ))
        fun k => (critSpeed (fun k : Fin 2 => (k : ℝ)) (fun k => (2 : ℝ) • ((k : ℝ) • e₁)) : ℝ)⁻¹
          • ((2 : ℝ) • ((k : ℝ) • e₁))) = 1 := by
  have ht : Function.Injective fun k : Fin 2 => (k : ℝ) :=
    Nat.cast_injective.comp Fin.val_injective
  have h2 : (critSpeed (fun k : Fin 2 => (k : ℝ)) (fun k => (2 : ℝ) • ((k : ℝ) • e₁)) : ℝ) = 2 := by
    rw [critSpeed, critSpeedOn_smul, ← critSpeed, critSpeed_twoSample]
    norm_num
  exact critSpeed_frame_normalized ht (by rw [h2]; norm_num) (rapidityBoost_mem one_ne_zero η)

/-- D-014 for T15c: the rapidity boost at `c = 2` becomes an element of `O(1,3)` in natural units. -/
example (η : ℝ) :
    stateScaleC two_ne_zero * rapidityBoost two_ne_zero η * (stateScaleC two_ne_zero)⁻¹
      ∈ lorentzGroup :=
  (mem_formGroup_iff_normalized two_ne_zero _).1 (rapidityBoost_mem two_ne_zero η)

/-- D-014 for T15b: uniform motion with velocity `v ≠ 0`, sampled at any times, is causal at
`‖v‖`; in units of `‖v‖` it is causal at `1`. -/
example (t : ι → ℝ) {v : State} (hv : v ≠ 0) (i j : ι) :
    IsCausal 1 (tableChord t (fun k => ‖v‖⁻¹ • (t k • v)) i j) :=
  (isCausal_normalize_iff (norm_ne_zero_iff.2 hv) t _ i j).1 (isCausal_tableChord_smul t v i j)

end GeneralizedC
