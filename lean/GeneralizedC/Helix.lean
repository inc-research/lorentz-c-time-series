/-
GeneralizedC/Helix.lean: the helix, c̃ = 1 at every non-aliasing tick (CP5b: N1g).

  helix r ω v                      xₖ = (r cos ωk, r sin ωk, vk)
  N1g (a) helix_secondMoment       whole turns, sin ω ≠ 0 ⇒ M = diag(ρ²/2, ρ²/2, v²), ρ² = r²(2 − 2cos ω)
  N1g (b) helix_mahal_eq_three     r, v ≠ 0 ⇒ every step has mahal 3
          helix_tickCritSpeed      ⇒ c° = √3 (c̃ = 1) for every L with Lᵀ L = M⁻¹
          helix_exists_unit        such an L exists
  N1g (c) helix_decimate           the m-tick observer sees the helix (r, mω, mv)
          helix_decimate_tickCritSpeed   so c̃ = 1 at every tick with sin mω ≠ 0 over whole turns
  N1g (d) helix_not_isUnit         v = 0 (planar) or sin ω = 0 (aliased) ⇒ no unit of change

Design (PROGRESS D-047, answering Q-031; cp5b_breakdown N1g): real ω with sin ω ≠ 0 and
whole turns `(b − a)ω ∈ 2πℤ` (C6); new file after N1f (C7); (a)–(d) (C8). The proof uses only
real trigonometry: telescoping sums over the window and three per-step identities.
Honest scope: the helix is an analogue of the ISS (drift instead of precession), not a model.
-/
import GeneralizedC.Window
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Matrix WithLp NNReal Real

namespace GeneralizedC

/-- The helix `xₖ = (r cos ωk, r sin ωk, vk)`, sampled at integer ticks. -/
noncomputable def helix (r ω v : ℝ) : ℤ → State :=
  fun k => toLp 2 ![r * cos (ω * k), r * sin (ω * k), v * k]

/-- First in-plane component of step `k`: `r (cos ω(k+1) − cos ωk)`. -/
noncomputable def helixC (r ω : ℝ) (k : ℤ) : ℝ := r * (cos (ω * ((k : ℝ) + 1)) - cos (ω * k))

/-- Second in-plane component of step `k`: `r (sin ω(k+1) − sin ωk)`. -/
noncomputable def helixS (r ω : ℝ) (k : ℤ) : ℝ := r * (sin (ω * ((k : ℝ) + 1)) - sin (ω * k))

/-- `ρ²`, the squared chord length per tick: `r² (2 − 2 cos ω)`. -/
noncomputable def helixRho2 (r ω : ℝ) : ℝ := r ^ 2 * (2 - 2 * cos ω)

theorem windowSteps_helix (r ω v : ℝ) (a b : ℤ) (k : {k // k ∈ Finset.Ico a b}) :
    windowSteps (helix r ω v) a b k = ![helixC r ω k.1, helixS r ω k.1, v] := by
  ext i
  fin_cases i <;> simp [windowSteps, helix, helixC, helixS] <;> ring

/-! ### Telescoping over a window -/

/-- `Σ_{k ∈ [a, b)} (f(k+1) − f k) = f b − f a`. -/
theorem sum_Ico_sub_int {G : Type*} [AddCommGroup G] (f : ℤ → G) {a b : ℤ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) = f b - f a := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
    have hI : Finset.Ico a (a + ((n + 1 : ℕ) : ℤ)) = insert (a + n) (Finset.Ico a (a + n)) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      push_cast
      omega
    rw [hI, Finset.sum_insert (by simp), ih]
    push_cast
    abel_nf

/-- Whole turns move the angle `cωa + φ` to `cωb + φ` by a multiple of `2π` (for `c ∈ ℤ`). -/
theorem helix_angle_shift {ω : ℝ} {a b j : ℤ} (hj : ((b - a : ℤ) : ℝ) * ω = 2 * π * j) (c : ℤ)
    (φ : ℝ) : c * ω * (b : ℝ) + φ = (c * ω * a + φ) + ((c * j : ℤ) : ℝ) * (2 * π) := by
  push_cast at hj ⊢
  linear_combination (c : ℝ) * hj

/-- Over whole turns, `Σ cos(2ωk + φ) = 0` (needs `sin ω ≠ 0`). -/
theorem sum_cos_two_mul {ω : ℝ} (hω : sin ω ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) (φ : ℝ) :
    ∑ k ∈ Finset.Ico a b, cos (2 * ω * k + φ) = 0 := by
  obtain ⟨j, hj⟩ := hN
  have key : ∀ k : ℤ, sin (2 * ω * ((k + 1 : ℤ) : ℝ) + (φ - ω)) - sin (2 * ω * (k : ℝ) + (φ - ω))
      = 2 * sin ω * cos (2 * ω * k + φ) := by
    intro k
    have h1 : 2 * ω * ((k + 1 : ℤ) : ℝ) + (φ - ω) = (2 * ω * k + φ) + ω := by push_cast; ring
    have h2 : 2 * ω * (k : ℝ) + (φ - ω) = (2 * ω * k + φ) - ω := by ring
    rw [h1, h2, sin_add, sin_sub]
    ring
  have tel := sum_Ico_sub_int (fun k : ℤ => sin (2 * ω * (k : ℝ) + (φ - ω))) hab
  rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.mul_sum] at tel
  have hper : sin (2 * ω * (b : ℝ) + (φ - ω)) = sin (2 * ω * (a : ℝ) + (φ - ω)) := by
    rw [show 2 * ω * (b : ℝ) + (φ - ω) = (2 * ω * a + (φ - ω)) + ((2 * j : ℤ) : ℝ) * (2 * π) by
      push_cast at hj ⊢; linear_combination 2 * hj, sin_add_int_mul_two_pi]
  rw [hper, sub_self] at tel
  exact (mul_eq_zero.1 tel).resolve_left (mul_ne_zero two_ne_zero hω)

/-- Over whole turns, `Σ sin(2ωk + φ) = 0` (needs `sin ω ≠ 0`). -/
theorem sum_sin_two_mul {ω : ℝ} (hω : sin ω ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) (φ : ℝ) :
    ∑ k ∈ Finset.Ico a b, sin (2 * ω * k + φ) = 0 := by
  obtain ⟨j, hj⟩ := hN
  have key : ∀ k : ℤ, -cos (2 * ω * ((k + 1 : ℤ) : ℝ) + (φ - ω)) - -cos (2 * ω * (k : ℝ) + (φ - ω))
      = 2 * sin ω * sin (2 * ω * k + φ) := by
    intro k
    have h1 : 2 * ω * ((k + 1 : ℤ) : ℝ) + (φ - ω) = (2 * ω * k + φ) + ω := by push_cast; ring
    have h2 : 2 * ω * (k : ℝ) + (φ - ω) = (2 * ω * k + φ) - ω := by ring
    rw [h1, h2, cos_add, cos_sub]
    ring
  have tel := sum_Ico_sub_int (fun k : ℤ => -cos (2 * ω * (k : ℝ) + (φ - ω))) hab
  rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.mul_sum] at tel
  have hper : cos (2 * ω * (b : ℝ) + (φ - ω)) = cos (2 * ω * (a : ℝ) + (φ - ω)) := by
    rw [show 2 * ω * (b : ℝ) + (φ - ω) = (2 * ω * a + (φ - ω)) + ((2 * j : ℤ) : ℝ) * (2 * π) by
      push_cast at hj ⊢; linear_combination 2 * hj, cos_add_int_mul_two_pi]
  rw [hper, sub_self] at tel
  exact (mul_eq_zero.1 tel).resolve_left (mul_ne_zero two_ne_zero hω)

/-- Over whole turns, the in-plane steps sum to zero (the orbit closes). -/
theorem sum_helixC {r ω : ℝ} {a b : ℤ} (hab : a ≤ b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    ∑ k ∈ Finset.Ico a b, helixC r ω k = 0 := by
  obtain ⟨j, hj⟩ := hN
  have tel := sum_Ico_sub_int (fun k : ℤ => r * cos (ω * (k : ℝ))) hab
  have hper : cos (ω * (b : ℝ)) = cos (ω * (a : ℝ)) := by
    have := helix_angle_shift hj 1 0
    push_cast at this
    rw [show ω * (b : ℝ) = ω * a + (j : ℝ) * (2 * π) by linarith, cos_add_int_mul_two_pi]
  rw [hper, sub_self] at tel
  rw [← tel]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [helixC]
  push_cast
  ring

theorem sum_helixS {r ω : ℝ} {a b : ℤ} (hab : a ≤ b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    ∑ k ∈ Finset.Ico a b, helixS r ω k = 0 := by
  obtain ⟨j, hj⟩ := hN
  have tel := sum_Ico_sub_int (fun k : ℤ => r * sin (ω * (k : ℝ))) hab
  have hper : sin (ω * (b : ℝ)) = sin (ω * (a : ℝ)) := by
    have := helix_angle_shift hj 1 0
    push_cast at this
    rw [show ω * (b : ℝ) = ω * a + (j : ℝ) * (2 * π) by linarith, sin_add_int_mul_two_pi]
  rw [hper, sub_self] at tel
  rw [← tel]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [helixS]
  push_cast
  ring

/-! ### Per-step identities -/

/-- Every step has the same in-plane length: `C² + S² = ρ²`. -/
theorem helixC_sq_add_helixS_sq (r ω : ℝ) (k : ℤ) :
    helixC r ω k ^ 2 + helixS r ω k ^ 2 = helixRho2 r ω := by
  have hP := sin_sq_add_cos_sq (ω * ((k : ℝ) + 1))
  have hA := sin_sq_add_cos_sq (ω * (k : ℝ))
  have hc : cos ω = cos (ω * ((k : ℝ) + 1)) * cos (ω * k) + sin (ω * ((k : ℝ) + 1)) * sin (ω * k) := by
    rw [← cos_sub]; congr 1; ring
  simp only [helixC, helixS, helixRho2]
  linear_combination r ^ 2 * hP + r ^ 2 * hA + 2 * r ^ 2 * hc

/-- `C² − S² = r² (cos(2ωk + 2ω) + cos(2ωk + 0) − 2 cos(2ωk + ω))`. -/
theorem helixC_sq_sub_helixS_sq (r ω : ℝ) (k : ℤ) :
    helixC r ω k ^ 2 - helixS r ω k ^ 2
      = r ^ 2 * (cos (2 * ω * k + 2 * ω) + cos (2 * ω * k + 0) - 2 * cos (2 * ω * k + ω)) := by
  set P := ω * ((k : ℝ) + 1)
  set A := ω * (k : ℝ)
  have hP := sin_sq_add_cos_sq P
  have hA := sin_sq_add_cos_sq A
  have e1 : cos (2 * ω * k + 2 * ω) = 2 * cos P ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; simp only [P]; ring
  have e2 : cos (2 * ω * k + 0) = 2 * cos A ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; simp only [A]; ring
  have e3 : cos (2 * ω * k + ω) = cos P * cos A - sin P * sin A := by
    rw [← cos_add]; congr 1; simp only [P, A]; ring
  simp only [helixC, helixS]
  rw [e1, e2, e3]
  linear_combination (-r ^ 2) * hP + (-r ^ 2) * hA

/-- `2CS = r² (sin(2ωk + 2ω) + sin(2ωk + 0) − 2 sin(2ωk + ω))`. -/
theorem two_helixC_mul_helixS (r ω : ℝ) (k : ℤ) :
    2 * (helixC r ω k * helixS r ω k)
      = r ^ 2 * (sin (2 * ω * k + 2 * ω) + sin (2 * ω * k + 0) - 2 * sin (2 * ω * k + ω)) := by
  set P := ω * ((k : ℝ) + 1)
  set A := ω * (k : ℝ)
  have e1 : sin (2 * ω * k + 2 * ω) = 2 * sin P * cos P := by
    rw [← sin_two_mul]; congr 1; simp only [P]; ring
  have e2 : sin (2 * ω * k + 0) = 2 * sin A * cos A := by
    rw [← sin_two_mul]; congr 1; simp only [A]; ring
  have e3 : sin (2 * ω * k + ω) = sin P * cos A + cos P * sin A := by
    rw [← sin_add]; congr 1; simp only [P, A]; ring
  simp only [helixC, helixS]
  rw [e1, e2, e3]
  ring

/-! ### The window sums -/

theorem card_Ico_real {a b : ℤ} (hab : a ≤ b) :
    ((Finset.Ico a b).card : ℝ) = ((b - a : ℤ) : ℝ) := by
  rw [Int.card_Ico]
  exact_mod_cast Int.toNat_of_nonneg (by omega)

theorem sum_helixC_sub_sq {r ω : ℝ} (hω : sin ω ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    ∑ k ∈ Finset.Ico a b, (helixC r ω k ^ 2 - helixS r ω k ^ 2) = 0 := by
  simp only [helixC_sq_sub_helixS_sq, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_cos_two_mul hω hab hN, ← Finset.mul_sum]
  simp

theorem sum_helixC_mul_helixS {r ω : ℝ} (hω : sin ω ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    ∑ k ∈ Finset.Ico a b, helixC r ω k * helixS r ω k = 0 := by
  have h : ∑ k ∈ Finset.Ico a b, 2 * (helixC r ω k * helixS r ω k) = 0 := by
    simp only [two_helixC_mul_helixS, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, sum_sin_two_mul hω hab hN, ← Finset.mul_sum]
    simp
  rw [← Finset.mul_sum] at h
  exact (mul_eq_zero.1 h).resolve_left two_ne_zero

theorem sum_helixC_sq {r ω : ℝ} (hω : sin ω ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    ∑ k ∈ Finset.Ico a b, helixC r ω k ^ 2 = ((b - a : ℤ) : ℝ) * (helixRho2 r ω / 2) := by
  have h1 : ∑ k ∈ Finset.Ico a b, (helixC r ω k ^ 2 + helixS r ω k ^ 2)
      = ((b - a : ℤ) : ℝ) * helixRho2 r ω := by
    simp only [helixC_sq_add_helixS_sq, Finset.sum_const, nsmul_eq_mul, card_Ico_real hab]
  have h2 := sum_helixC_sub_sq (r := r) hω hab hN
  rw [Finset.sum_add_distrib] at h1
  rw [Finset.sum_sub_distrib] at h2
  linarith

theorem sum_helixS_sq {r ω : ℝ} (hω : sin ω ≠ 0) {a b : ℤ} (hab : a ≤ b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    ∑ k ∈ Finset.Ico a b, helixS r ω k ^ 2 = ((b - a : ℤ) : ℝ) * (helixRho2 r ω / 2) := by
  have h1 : ∑ k ∈ Finset.Ico a b, (helixC r ω k ^ 2 + helixS r ω k ^ 2)
      = ((b - a : ℤ) : ℝ) * helixRho2 r ω := by
    simp only [helixC_sq_add_helixS_sq, Finset.sum_const, nsmul_eq_mul, card_Ico_real hab]
  have h2 := sum_helixC_sub_sq (r := r) hω hab hN
  rw [Finset.sum_add_distrib] at h1
  rw [Finset.sum_sub_distrib] at h2
  linarith

/-! ### N1g (a): the unit of change of the helix -/

/-- Entries of the second moment as averages over the steps. -/
theorem secondMoment_apply {n : ℕ} {ι : Type*} [Fintype ι] (u : ι → Fin n → ℝ) (i j : Fin n) :
    secondMoment u i j = (Fintype.card ι : ℝ)⁻¹ * ∑ k, u k i * u k j := by
  simp [secondMoment, Matrix.sum_apply, vecMulVec_apply]

/-- **N1g (a).** Over whole turns (`(b − a)ω ∈ 2πℤ`, `a < b`) with `sin ω ≠ 0`, the window's unit of
change is `M = diag(ρ²/2, ρ²/2, v²)`. No hypothesis on `r` or `v`. -/
theorem helix_secondMoment {r ω v : ℝ} (hω : sin ω ≠ 0) {a b : ℤ} (hab : a < b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    secondMoment (windowSteps (helix r ω v) a b)
      = diagonal ![helixRho2 r ω / 2, helixRho2 r ω / 2, v ^ 2] := by
  have hab' := hab.le
  have hcard : (Fintype.card {k // k ∈ Finset.Ico a b} : ℝ) = ((b - a : ℤ) : ℝ) := by
    rw [Fintype.card_coe, card_Ico_real hab']
  have hN0 : ((b - a : ℤ) : ℝ) ≠ 0 := by
    have : (0 : ℤ) < b - a := by omega
    exact_mod_cast this.ne'
  have hN0' : (b : ℝ) - (a : ℝ) ≠ 0 := by push_cast at hN0; exact hN0
  have htn : ((b - a).toNat : ℝ) = (b : ℝ) - (a : ℝ) := by
    have := card_Ico_real hab'
    rw [Int.card_Ico] at this
    push_cast at this
    exact this
  have sC := sum_helixC (r := r) hab' hN
  have sS := sum_helixS (r := r) hab' hN
  have sCC := sum_helixC_sq (r := r) hω hab' hN
  have sSS := sum_helixS_sq (r := r) hω hab' hN
  have sCS := sum_helixC_mul_helixS (r := r) hω hab' hN
  have sSC : ∑ k ∈ Finset.Ico a b, helixS r ω k * helixC r ω k = 0 := by
    rw [← sCS]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  ext i j
  rw [secondMoment_apply, hcard]
  simp only [windowSteps_helix]
  rw [Finset.sum_coe_sort (Finset.Ico a b)
    (fun k => (![helixC r ω k, helixS r ω k, v] : Fin 3 → ℝ) i * ![helixC r ω k, helixS r ω k, v] j)]
  fin_cases i <;> fin_cases j <;>
    simp [← sq, ← Finset.mul_sum, ← Finset.sum_mul, sCC, sSS, sCS, sSC, sC, sS, htn] <;> field_simp

/-! ### N1g (b): every step has length √3 -/

theorem helixRho2_pos {r ω : ℝ} (hr : r ≠ 0) (hω : sin ω ≠ 0) : 0 < helixRho2 r ω := by
  have hc : cos ω < 1 := by
    rcases (cos_le_one ω).lt_or_eq with h | h
    · exact h
    · exfalso
      have := sin_sq_add_cos_sq ω
      rw [h] at this
      exact hω (by nlinarith [sq_nonneg (sin ω)])
  unfold helixRho2
  have : 0 < r ^ 2 := by positivity
  nlinarith

theorem helix_inv_secondMoment {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0) {a b : ℤ}
    (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    (secondMoment (windowSteps (helix r ω v) a b))⁻¹
      = diagonal ![2 / helixRho2 r ω, 2 / helixRho2 r ω, 1 / v ^ 2] := by
  have hρ := (helixRho2_pos hr hω).ne'
  rw [helix_secondMoment hω hab hN]
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]
  all_goals first | exact hρ | exact inv_mul_cancel₀ (pow_ne_zero 2 hv)

theorem isUnit_det_helix {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0) {a b : ℤ}
    (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    IsUnit (secondMoment (windowSteps (helix r ω v) a b)).det := by
  have hρ := (helixRho2_pos hr hω).ne'
  rw [helix_secondMoment hω hab hN, det_diagonal, isUnit_iff_ne_zero]
  simp [Fin.prod_univ_succ, hρ, hv]

/-- **N1g (b).** For `r, v ≠ 0`, `sin ω ≠ 0`, over whole turns: every step of the window has
squared length exactly 3 in the window's own unit of change (the light-ray case). -/
theorem helix_mahal_eq_three {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0) {a b : ℤ}
    (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j)
    (k : {k // k ∈ Finset.Ico a b}) :
    mahal (secondMoment (windowSteps (helix r ω v) a b)) (windowSteps (helix r ω v) a b k) = 3 := by
  have hρ := (helixRho2_pos hr hω).ne'
  have hlen := helixC_sq_add_helixS_sq r ω k.1
  rw [mahal, helix_inv_secondMoment hr hv hω hab hN, windowSteps_helix]
  simp [dotProduct, Fin.sum_univ_succ, mulVec_diagonal]
  field_simp
  linear_combination 2 * hlen

/-- **N1g (b), c°.** Hence `c° = √3` (`c̃ = 1`) for every factor `L` of the window's `M⁻¹`. -/
theorem helix_tickCritSpeed {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0) {a b : ℤ}
    (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j)
    {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : Lᵀ * L = (secondMoment (windowSteps (helix r ω v) a b))⁻¹) :
    (tickCritSpeed L (helix r ω v) a b : ℝ) = √3 := by
  obtain ⟨k, hak, hkb, hk⟩ := exists_mahal_eq_tickCritSpeed hL (helix r ω v) hab
  rw [← hk]
  have : ofLp (helix r ω v (k + 1) - helix r ω v k)
      = windowSteps (helix r ω v) a b ⟨k, Finset.mem_Ico.2 ⟨hak, hkb⟩⟩ := rfl
  rw [this, helix_mahal_eq_three hr hv hω hab hN]

/-- A diagonal matrix with non-negative entries has the factor `L = diag(√dᵢ)`. -/
theorem exists_factor_diagonal (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∃ L : Matrix (Fin 3) (Fin 3) ℝ, Lᵀ * L = diagonal d :=
  ⟨diagonal fun i => √(d i), by
    rw [diagonal_transpose, diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hd i)⟩

/-- **N1g (b), existence form.** The helix window has a unit of change, and with it `c° = √3`. -/
theorem helix_exists_unit {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0) {a b : ℤ}
    (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    ∃ L : Matrix (Fin 3) (Fin 3) ℝ,
      Lᵀ * L = (secondMoment (windowSteps (helix r ω v) a b))⁻¹ ∧
      (tickCritSpeed L (helix r ω v) a b : ℝ) = √3 := by
  have hρ := helixRho2_pos hr hω
  obtain ⟨L, hL⟩ := exists_factor_diagonal ![2 / helixRho2 r ω, 2 / helixRho2 r ω, 1 / v ^ 2]
    (fun i => by fin_cases i <;> simp <;> positivity)
  rw [← helix_inv_secondMoment hr hv hω hab hN] at hL
  exact ⟨L, hL, helix_tickCritSpeed hr hv hω hab hN hL⟩

/-! ### N1g (c): every tick -/

/-- **N1g (c).** The `m`-tick observer of a helix sees the helix `(r, mω, mv)`. -/
theorem helix_decimate (r ω v : ℝ) (m : ℤ) :
    (fun k : ℤ => helix r ω v (m * k)) = helix r (m * ω) (m * v) := by
  funext k
  simp only [helix]
  push_cast
  congr 2 <;> simp [mul_assoc, mul_left_comm]

/-- **N1g (c), c̃ = 1 at every non-aliasing tick.** If `sin mω ≠ 0` and the `m`-tick window covers
whole turns of `mω`, the `m`-tick observer also has `c° = √3`. All such observers agree exactly. -/
theorem helix_decimate_tickCritSpeed {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) {m : ℤ}
    (hmω : sin (m * ω) ≠ 0) {a b : ℤ} (hab : a < b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * (m * ω) = 2 * π * j)
    {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : Lᵀ * L = (secondMoment (windowSteps (fun k => helix r ω v (m * k)) a b))⁻¹) :
    (tickCritSpeed L (fun k => helix r ω v (m * k)) a b : ℝ) = √3 := by
  have hm : (m : ℝ) ≠ 0 := by
    rintro h
    rw [h, zero_mul, sin_zero] at hmω
    exact hmω rfl
  rw [helix_decimate] at hL ⊢
  exact helix_tickCritSpeed hr (mul_ne_zero hm hv) hmω hab hN hL

/-! ### N1g (d): where it fails -/

/-- **N1g (d).** A planar circle (`v = 0`, the Moon trap) or an aliased tick (`sin ω = 0`: the
tick is a multiple of half a turn) has no unit of change: the steps do not span ℝ³ (N1c′). -/
theorem helix_not_isUnit {r ω v : ℝ} (h : v = 0 ∨ sin ω = 0) (a b : ℤ) :
    ¬ IsUnit (secondMoment (windowSteps (helix r ω v) a b)).det := by
  rw [isUnit_det_secondMoment_iff_covers]
  intro hc
  rcases h with hv | hω
  · -- every step misses e₃
    have := hc ![0, 0, 1] fun k => by simp [windowSteps_helix, dotProduct, Fin.sum_univ_succ, hv]
    simpa using congrFun this 2
  · -- every sin ωk vanishes, so every step misses e₂
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 hω
    have hs : ∀ k : ℤ, sin (ω * k) = 0 := fun k => by
      rw [← hn, show (n : ℝ) * π * k = ((n * k : ℤ) : ℝ) * π by push_cast; ring]
      exact sin_int_mul_pi _
    have hS : ∀ k : ℤ, helixS r ω k = 0 := fun k => by
      simp only [helixS]
      rw [show (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) by push_cast; ring, hs, hs, sub_self, mul_zero]
    have := hc ![0, 1, 0] fun k => by simp [windowSteps_helix, dotProduct, Fin.sum_univ_succ, hS]
    simpa using congrFun this 1

/-! ### D-014 examples -/

theorem sin_pi_div_two_ne : sin (π / 2) ≠ 0 := by rw [sin_pi_div_two]; exact one_ne_zero

/-- D-014 for N1g (a)–(b): the quarter-turn helix `r = 1, ω = π/2, v = 1` over one turn `[0, 4)`
has a unit of change in which `c° = √3` (`c̃ = 1`). -/
example : ∃ L : Matrix (Fin 3) (Fin 3) ℝ,
    Lᵀ * L = (secondMoment (windowSteps (helix 1 (π / 2) 1) 0 4))⁻¹ ∧
      (tickCritSpeed L (helix 1 (π / 2) 1) 0 4 : ℝ) = √3 :=
  helix_exists_unit one_ne_zero one_ne_zero sin_pi_div_two_ne (by norm_num) ⟨1, by push_cast; ring⟩

/-- D-014 for N1g (c): the same helix seen every 3 ticks (`3ω = 3π/2`, not aliased) over three turns
`[0, 4)`: again `c° = √3`. -/
example {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : Lᵀ * L = (secondMoment (windowSteps (fun k => helix 1 (π / 2) 1 (3 * k)) 0 4))⁻¹) :
    (tickCritSpeed L (fun k => helix 1 (π / 2) 1 (3 * k)) 0 4 : ℝ) = √3 := by
  refine helix_decimate_tickCritSpeed one_ne_zero one_ne_zero ?_ (by norm_num) ⟨3, by push_cast; ring⟩ hL
  rw [show ((3 : ℤ) : ℝ) * (π / 2) = π / 2 + π by push_cast; ring, sin_add_pi, sin_pi_div_two]
  norm_num

/-- D-014 for N1g (d): the same helix seen every 2 ticks (`2ω = π`) is aliased: no unit of change. -/
example : ¬ IsUnit (secondMoment (windowSteps (fun k => helix 1 (π / 2) 1 (2 * k)) 0 4)).det := by
  rw [helix_decimate]
  exact helix_not_isUnit (Or.inr (by push_cast; rw [show (2 : ℝ) * (π / 2) = π by ring, sin_pi])) 0 4

/-- D-014 for N1g (d): the planar circle (`v = 0`) has no unit of change. -/
example : ¬ IsUnit (secondMoment (windowSteps (helix 1 (π / 2) 0) 0 4)).det :=
  helix_not_isUnit (Or.inl rfl) 0 4

end GeneralizedC
