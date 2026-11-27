/-
GeneralizedC/Hyperbolic.lean: hyperbolic motion, the gap between T1 and T2.

  T3  hyperbolicPath_allChordsTimelike, hyperbolicPath_not_lipschitz_lt
      (every chord timelike at c, yet no Lipschitz constant L < c)

Hyperbolic motion (constant proper acceleration a) is `x(t) = (c²/a)(√(1 + (at/c)²) − 1)`.
We take `a = c`, so `x(t) = c(√(1 + t²) − 1)`, along the first axis `e₁`. Its speed
`c·t/√(1 + t²)` stays below `c` but tends to `c`: the best Lipschitz constant is `c`, and no
chord attains it. So T1 cannot be applied (no `L < c`), yet the conclusion of T1 holds; and T2
can only give `≤ c`, never `< c`.
-/
import GeneralizedC.SpeedBounds

open NNReal

namespace GeneralizedC

/-- The unit vector `e₁` of the state space. -/
noncomputable def e₁ : State := EuclideanSpace.single 0 1

theorem norm_smul_e₁ (r : ℝ) : ‖r • e₁‖ = |r| := by
  simp [e₁, norm_smul, EuclideanSpace.single, PiLp.norm_single]

/-- Hyperbolic motion with proper acceleration `c` (see the file header). -/
noncomputable def hyperbolicPath (c : ℝ) : ℝ → State :=
  fun t => (c * (√(1 + t ^ 2) - 1)) • e₁

/-- `|t| < √(1 + t²)`. -/
theorem abs_lt_sqrt_one_add_sq (t : ℝ) : |t| < √(1 + t ^ 2) := by
  rw [← pow_lt_pow_iff_left₀ (abs_nonneg t) (Real.sqrt_nonneg _) two_ne_zero, sq_abs,
    Real.sq_sqrt (by positivity)]
  linarith

/-- The key inequality: `t ↦ √(1 + t²)` has every chord slope strictly below `1`.
Proof: `(a − b)(a + b) = t² − s² = (t − s)(t + s)` and `|t + s| < a + b`. -/
theorem abs_sqrt_sub_sqrt_lt {s t : ℝ} (hst : s ≠ t) :
    |√(1 + t ^ 2) - √(1 + s ^ 2)| < |t - s| := by
  set a := √(1 + t ^ 2) with ha_def
  set b := √(1 + s ^ 2) with hb_def
  have ha : a ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hb : b ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hta : |t| < a := abs_lt_sqrt_one_add_sq t
  have hsb : |s| < b := abs_lt_sqrt_one_add_sq s
  have hab : 0 < a + b := by linarith [abs_nonneg t, abs_nonneg s]
  have hts : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hst))
  -- |a − b|·(a + b) = |t − s|·|t + s|
  have key : |a - b| * (a + b) = |t - s| * |t + s| := by
    rw [← abs_of_pos hab, ← abs_mul, ← abs_mul]
    congr 1
    linear_combination ha - hb
  have hsum : |t + s| < a + b := (abs_add_le t s).trans_lt (by linarith)
  have : |a - b| * (a + b) < |t - s| * (a + b) := by
    rw [key]
    exact mul_lt_mul_of_pos_left hsum hts
  exact lt_of_mul_lt_mul_right this hab.le

/-- **T3, part 1.** For `c > 0`, every chord of hyperbolic motion is strictly `c`-timelike. -/
theorem hyperbolicPath_allChordsTimelike {c : ℝ} (hc : 0 < c) :
    AllChordsTimelike c (hyperbolicPath c) := by
  intro s t hst
  rw [isTimelike_iff hc.le]
  show ‖hyperbolicPath c t - hyperbolicPath c s‖ < c * |t - s|
  simp only [hyperbolicPath, ← sub_smul, norm_smul_e₁]
  rw [show c * (√(1 + t ^ 2) - 1) - c * (√(1 + s ^ 2) - 1)
        = c * (√(1 + t ^ 2) - √(1 + s ^ 2)) by ring, abs_mul, abs_of_pos hc]
  exact mul_lt_mul_of_pos_left (abs_sqrt_sub_sqrt_lt hst) hc

/-- **T3, part 2.** For `c > 0`, hyperbolic motion has no Lipschitz constant `L < c`.
The chord from `0` to `T = c/(c − L)` has `‖Δx‖ = c(√(1 + T²) − 1) > c(T − 1) = L·T`. -/
theorem hyperbolicPath_not_lipschitz_lt {c : ℝ} (hc : 0 < c) :
    ¬ ∃ L : ℝ≥0, (L : ℝ) < c ∧ LipschitzWith L (hyperbolicPath c) := by
  rintro ⟨L, hLc, hL⟩
  set T := c / (c - L) with hT_def
  have hcL : 0 < c - L := sub_pos.mpr hLc
  have hT : 0 < T := div_pos hc hcL
  have hTeq : (c - L) * T = c := mul_div_cancel₀ _ hcL.ne'
  have hlip := hL.dist_le_mul T 0
  rw [dist_eq_norm, Real.dist_eq, sub_zero, abs_of_pos hT] at hlip
  have hx0 : hyperbolicPath c 0 = 0 := by simp [hyperbolicPath]
  rw [hx0, sub_zero, hyperbolicPath, norm_smul_e₁] at hlip
  -- √(1 + T²) > T, so c(√(1 + T²) − 1) > c(T − 1) = L·T
  have hsq : T < √(1 + T ^ 2) := (le_abs_self T).trans_lt (abs_lt_sqrt_one_add_sq T)
  have hgt : (L : ℝ) * T < c * (√(1 + T ^ 2) - 1) := by nlinarith
  have := hlip.trans' (le_abs_self _)
  linarith

/-- **T3.** For `c > 0`, hyperbolic motion is `c`-timelike along every chord, yet has no
Lipschitz constant `L < c`. So the converse of T1 fails, and T2's `≤ c` cannot be improved. -/
theorem hyperbolic_gap {c : ℝ} (hc : 0 < c) :
    AllChordsTimelike c (hyperbolicPath c) ∧
      ¬ ∃ L : ℝ≥0, (L : ℝ) < c ∧ LipschitzWith L (hyperbolicPath c) :=
  ⟨hyperbolicPath_allChordsTimelike hc, hyperbolicPath_not_lipschitz_lt hc⟩

/-- D-014 for T3: `c = 1`. -/
example : AllChordsTimelike 1 (hyperbolicPath 1) ∧
    ¬ ∃ L : ℝ≥0, (L : ℝ) < 1 ∧ LipschitzWith L (hyperbolicPath 1) :=
  hyperbolic_gap one_pos

/-- Combined with T2: hyperbolic motion is exactly `c`-Lipschitz (its critical speed is `c`,
attained by no chord, so `c` lies in the strict admissible set A°; cf. D-015). -/
example {c : ℝ} (hc : 0 < c) : LipschitzWith ⟨c, hc.le⟩ (hyperbolicPath c) :=
  lipschitzWith_of_allChordsTimelike hc.le (hyperbolicPath_allChordsTimelike hc)

end GeneralizedC
