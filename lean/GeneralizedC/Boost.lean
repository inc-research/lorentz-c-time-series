/-
GeneralizedC/Boost.lean: boosted time orders the data (T6).

  T6   boostTime_strictMono_surjective   (core: ‖v‖·L < c² ⇒ τ strictly increasing and onto ℝ)
       boostTime_of_allChordsCausal      (corollary: c-causal path, ‖v‖ < c)
       boostTime_of_allChordsTimelike    (corollary: c-timelike path, ‖v‖ < c)
  A2   boostTime_uniformMotion_self      (at ‖v‖ = c a lightlike path collapses to one instant)

Design (PROGRESS D-017, cp3_breakdown T6): the core theorem takes the weakest hypothesis
`‖v‖·L < c²`; `boostTime` omits the Lorentz factor γ > 0, which changes neither property.
-/
import GeneralizedC.SpeedBounds
import Mathlib.Topology.Order.IntermediateValue

open NNReal
open scoped InnerProductSpace

namespace GeneralizedC

/-- Boosted time of the event `(t, x t)` for a boost with velocity `v` and invariant speed `c`,
without the factor γ: `τ(t) = t − ⟨v, x t⟩ / c²`. The full boost is `γ · τ(t)`. -/
noncomputable def boostTime (c : ℝ) (v : State) (x : ℝ → State) (t : ℝ) : ℝ :=
  t - ⟪v, x t⟫_ℝ / c ^ 2

/-- The increment of boosted time: `τ(t) − τ(s) = (t − s) − ⟨v, x t − x s⟩ / c²`. -/
theorem boostTime_sub (c : ℝ) (v : State) (x : ℝ → State) (s t : ℝ) :
    boostTime c v x t - boostTime c v x s = (t - s) - ⟪v, x t - x s⟫_ℝ / c ^ 2 := by
  simp only [boostTime, inner_sub_right]
  ring

/-- The key bound: for `s ≤ t`, `τ(t) − τ(s) ≥ k (t − s)` with `k = 1 − ‖v‖L/c²`.
Cauchy–Schwarz gives `⟨v, x t − x s⟩ ≤ ‖v‖ ‖x t − x s‖`, and Lipschitz gives
`‖x t − x s‖ ≤ L (t − s)`. -/
theorem boostTime_sub_ge {c : ℝ} (hc : c ≠ 0) {L : ℝ≥0} {x : ℝ → State}
    (hx : LipschitzWith L x) (v : State) {s t : ℝ} (hst : s ≤ t) :
    (1 - ‖v‖ * L / c ^ 2) * (t - s) ≤ boostTime c v x t - boostTime c v x s := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hlip : ‖x t - x s‖ ≤ L * (t - s) := by
    have h := hx.dist_le_mul t s
    rwa [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)] at h
  have hcs : ⟪v, x t - x s⟫_ℝ ≤ ‖v‖ * (L * (t - s)) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hlip (norm_nonneg v))
  have hdiv : ⟪v, x t - x s⟫_ℝ / c ^ 2 ≤ ‖v‖ * (L * (t - s)) / c ^ 2 :=
    div_le_div_of_nonneg_right hcs hc2.le
  rw [boostTime_sub]
  have hk : (1 - ‖v‖ * L / c ^ 2) * (t - s) = (t - s) - ‖v‖ * (L * (t - s)) / c ^ 2 := by ring
  linarith

/-- **T6 (core).** Let `c ≠ 0`, let `x` be `L`-Lipschitz and `‖v‖·L < c²`. Then boosted time
is strictly increasing (every boosted observer sees the samples in the same order) and maps
ℝ onto ℝ (the boosted series is again a complete worldline, D-002). -/
theorem boostTime_strictMono_surjective {c : ℝ} (hc : c ≠ 0) {L : ℝ≥0} {x : ℝ → State}
    (hx : LipschitzWith L x) {v : State} (hv : ‖v‖ * L < c ^ 2) :
    StrictMono (boostTime c v x) ∧ Function.Surjective (boostTime c v x) := by
  set τ := boostTime c v x with hτ
  have hc2 : 0 < c ^ 2 := by positivity
  -- the slope bound k = 1 − ‖v‖L/c² is positive
  set k := 1 - ‖v‖ * L / c ^ 2 with hk_def
  have hk : 0 < k := by
    have : ‖v‖ * L / c ^ 2 < 1 := (div_lt_one hc2).mpr hv
    linarith
  have hbound : ∀ s t, s ≤ t → k * (t - s) ≤ τ t - τ s :=
    fun s t hst => boostTime_sub_ge hc hx v hst
  refine ⟨fun s t hst => ?_, fun y => ?_⟩
  · -- strictly increasing: τ t − τ s ≥ k (t − s) > 0
    have := hbound s t hst.le
    have : 0 < k * (t - s) := mul_pos hk (sub_pos.mpr hst)
    linarith
  · -- onto: τ is continuous and moves by at least k·R over [−R, 0] and [0, R]
    have hcont : Continuous τ :=
      continuous_id.sub ((continuous_const.inner hx.continuous).div_const _)
    set R := |y - τ 0| / k with hR_def
    have hR : 0 ≤ R := div_nonneg (abs_nonneg _) hk.le
    have hkR : k * R = |y - τ 0| := mul_div_cancel₀ _ hk.ne'
    have hup : y ≤ τ R := by
      have := hbound 0 R hR
      rw [sub_zero, hkR] at this
      linarith [le_abs_self (y - τ 0)]
    have hdown : τ (-R) ≤ y := by
      have := hbound (-R) 0 (neg_nonpos.mpr hR)
      rw [zero_sub, neg_neg, hkR] at this
      linarith [neg_abs_le (y - τ 0)]
    obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc (neg_le_self hR) hcont.continuousOn ⟨hdown, hup⟩
    exact ⟨t, ht⟩

/-- D-014 for T6, trivial case: a constant path (`L = 0`), any boost velocity `v`, `c = 1`. -/
example (p v : State) :
    StrictMono (boostTime 1 v (fun _ => p)) ∧ Function.Surjective (boostTime 1 v (fun _ => p)) :=
  boostTime_strictMono_surjective one_ne_zero (LipschitzWith.const p : LipschitzWith 0 _) (by simp)

/-- **T6 (causal corollary).** A `c`-causal path (D-015), boosted with `‖v‖ < c`: here the
path's speed may reach `c`, and only the boost must stay strictly below it. -/
theorem boostTime_of_allChordsCausal {c : ℝ} {x : ℝ → State} {v : State}
    (hx : AllChordsCausal c x) (hv : ‖v‖ < c) :
    StrictMono (boostTime c v x) ∧ Function.Surjective (boostTime c v x) := by
  have hc : 0 < c := (norm_nonneg v).trans_lt hv
  refine boostTime_strictMono_surjective hc.ne'
    ((lipschitzWith_iff_allChordsCausal hc.le).2 hx) ?_
  show ‖v‖ * c < c ^ 2
  nlinarith

/-- **T6 (timelike corollary).** A `c`-timelike path, boosted with `‖v‖ < c`. -/
theorem boostTime_of_allChordsTimelike {c : ℝ} {x : ℝ → State} {v : State}
    (hx : AllChordsTimelike c x) (hv : ‖v‖ < c) :
    StrictMono (boostTime c v x) ∧ Function.Surjective (boostTime c v x) :=
  boostTime_of_allChordsCausal (fun s t hst => (hx s t hst).isCausal) hv

/-- D-014 for the corollaries: uniform motion with velocity `v` is causal at its own speed
`‖v‖`, hence at `c = ‖v‖ + 1` (T2a); boosting it by `v` itself (`‖v‖ < c`) keeps the order. -/
example (v : State) :
    StrictMono (boostTime (‖v‖ + 1) v (uniformMotion v)) ∧
      Function.Surjective (boostTime (‖v‖ + 1) v (uniformMotion v)) :=
  boostTime_of_allChordsCausal
    ((allChordsCausal_uniformMotion v).mono (norm_nonneg v) (lt_add_one _).le) (lt_add_one _)

/-- D-014 for the timelike corollary: a constant path at `c = 1`, boost `v = 0`. -/
example (p : State) :
    StrictMono (boostTime 1 0 (fun _ => p)) ∧ Function.Surjective (boostTime 1 0 (fun _ => p)) :=
  boostTime_of_allChordsTimelike
    (allChordsTimelike_of_lipschitzWith (L := 0) zero_lt_one (LipschitzWith.const p)) (by simp)

/-- **Why `‖v‖ < c` must be strict (cp3_breakdown T6 A2).** Uniform motion at speed `c = ‖v‖`
(a lightlike path), boosted with its own velocity `v`, has constant boosted time `0`: the whole
series collapses to one instant. "No frame moves with light." -/
theorem boostTime_uniformMotion_self {v : State} (hv : v ≠ 0) (t : ℝ) :
    boostTime ‖v‖ v (uniformMotion v) t = 0 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [boostTime, uniformMotion, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

end GeneralizedC
