/-
GeneralizedC/UniformGrid.lean: when does a boost keep a uniform sampling grid uniform? (T7)

  T7   boostedStamps_uniform_iff   (boosted time stamps uniformly spaced ⇔ ⟨v, Δ²yₙ⟩ = 0 ∀ n)

Data sampled on the grid `tₙ = n·Δt` (`n ∈ ℤ`) with values `yₙ`. A boost with velocity `v`
moves the time stamps to `τₙ = n·Δt − ⟨v, yₙ⟩/c²` (γ omitted, as in `boostTime`).
-/
import GeneralizedC.Boost

open scoped InnerProductSpace

namespace GeneralizedC

/-- Boosted time stamps of a series `y` sampled at `tₙ = n·Δt`. -/
noncomputable def boostedStamps (c : ℝ) (v : State) (Δt : ℝ) (y : ℤ → State) (n : ℤ) : ℝ :=
  n * Δt - ⟪v, y n⟫_ℝ / c ^ 2

/-- For samples of a worldline, `yₙ = x(n·Δt)`, the stamps are the boosted times of T6. -/
theorem boostedStamps_eq_boostTime (c : ℝ) (v : State) (Δt : ℝ) (x : ℝ → State) (n : ℤ) :
    boostedStamps c v Δt (fun k => x (k * Δt)) n = boostTime c v x (n * Δt) :=
  rfl

/-- The second difference `Δ²yₙ = yₙ₊₁ − 2yₙ + yₙ₋₁` (discrete acceleration). -/
def secondDiff (y : ℤ → State) (n : ℤ) : State :=
  y (n + 1) - (2 : ℝ) • y n + y (n - 1)

/-- A sequence of time stamps is uniformly spaced: one common gap `d`. -/
def IsUniformlySpaced (τ : ℤ → ℝ) : Prop :=
  ∃ d, ∀ n, τ (n + 1) - τ n = d

/-- Uniform spacing ⇔ every two consecutive gaps agree. (⇐ is an induction over ℤ.) -/
theorem isUniformlySpaced_iff (τ : ℤ → ℝ) :
    IsUniformlySpaced τ ↔ ∀ n, τ (n + 1) - τ n = τ n - τ (n - 1) := by
  constructor
  · rintro ⟨d, hd⟩ n
    rw [hd n, ← hd (n - 1), sub_add_cancel]
  · intro h
    refine ⟨τ 1 - τ 0, fun n => ?_⟩
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih => rw [h, add_sub_cancel_right, ih]
    | pred i ih =>
      -- h at −i: τ(−i+1) − τ(−i) = τ(−i) − τ(−i−1), and the left side is the common gap
      rw [sub_add_cancel, ← h (-(i : ℤ)), ih]

/-- The change of gap is minus the boost component of the discrete acceleration:
`(τₙ₊₁ − τₙ) − (τₙ − τₙ₋₁) = −⟨v, Δ²yₙ⟩ / c²`. The grid part cancels exactly. -/
theorem boostedStamps_gap_change (c : ℝ) (v : State) (Δt : ℝ) (y : ℤ → State) (n : ℤ) :
    (boostedStamps c v Δt y (n + 1) - boostedStamps c v Δt y n)
      - (boostedStamps c v Δt y n - boostedStamps c v Δt y (n - 1))
      = -⟪v, secondDiff y n⟫_ℝ / c ^ 2 := by
  simp only [boostedStamps, secondDiff, inner_add_right, inner_sub_right, inner_smul_right]
  push_cast
  ring

/-- **T7 (uniform-grid lemma).** For `c ≠ 0`, the boosted time stamps of a uniformly sampled
series are uniformly spaced exactly when the series has no discrete acceleration along the
boost: `⟨v, Δ²yₙ⟩ = 0` for every `n`. -/
theorem boostedStamps_uniform_iff {c : ℝ} (hc : c ≠ 0) (v : State) (Δt : ℝ) (y : ℤ → State) :
    IsUniformlySpaced (boostedStamps c v Δt y) ↔ ∀ n, ⟪v, secondDiff y n⟫_ℝ = 0 := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [isUniformlySpaced_iff]
  refine forall_congr' fun n => ?_
  rw [← sub_eq_zero, boostedStamps_gap_change, neg_div, neg_eq_zero, div_eq_zero_iff,
    or_iff_left hc2]

/-- D-014 for T7: samples of uniform motion, `yₙ = (n·Δt) • w`, have `Δ²y = 0`, so their
boosted stamps are uniform for every boost `v`. -/
example (v w : State) (Δt : ℝ) :
    IsUniformlySpaced (boostedStamps 1 v Δt (fun n => ((n : ℝ) * Δt) • w)) := by
  rw [boostedStamps_uniform_iff one_ne_zero]
  intro n
  simp only [secondDiff, ← smul_assoc, smul_eq_mul, ← sub_smul, ← add_smul]
  push_cast
  ring_nf
  simp

/-- D-014 for T7, the other direction: `yₙ = n² • v` with `v ≠ 0` accelerates along `v`
(`Δ²y = 2 • v`), so boosting by `v` destroys the uniform grid. -/
example {v : State} (hv : v ≠ 0) (Δt : ℝ) :
    ¬ IsUniformlySpaced (boostedStamps 1 v Δt (fun n => ((n : ℝ) ^ 2) • v)) := by
  rw [boostedStamps_uniform_iff one_ne_zero]
  intro h
  have h0 := h 0
  simp only [secondDiff, ← smul_assoc, smul_eq_mul, ← sub_smul, ← add_smul, inner_smul_right,
    real_inner_self_eq_norm_sq] at h0
  push_cast at h0
  norm_num at h0
  exact hv h0

end GeneralizedC
