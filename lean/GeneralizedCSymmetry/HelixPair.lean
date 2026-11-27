/-
GeneralizedCSymmetry/HelixPair.lean: helix pairs as exact β1 witnesses (P2-1a: Y4, Y5, the helix
part of Y6).

  Y4  helixRot, helix_sharesCone_rot      the helix and its rotation by φ about the axis share the
                                          cone, for every φ (whole-turn windows)
  Y5  helix_isCrossSpeed_speed, helix_crossSpeed_split
                                          U-split: equal r and ω, v′² > v²: s_{B|A}² = (2 + v′²/v²)/3 > 1
                                          and s_{A|B}² = (2 + v²/v′²)/3 < 1 (nested cones)
      helixSwap, helix_crossSpeed_cross   U-cross: the helix with its axis turned from z to x
                                          (anisotropic, ρ² ≠ 2v²): both cross-speeds > 1
  Y6  helix_decimate_crossSpeed           trap A7 per count: the m-tick observer has s² ≥ m²/3,
                                          so s > 1 for |m| ≥ 2

Uses the core's helix results (N1g, `Helix.lean`) and `isLorentzC_helix` (K6). The core is not
edited (D-053 C4, D-054 A7). Every theorem is followed by its D-014 example.
-/
import GeneralizedCSymmetry.CrossSpeed

open Matrix WithLp NNReal Real GeneralizedC

namespace GeneralizedCSymmetry

/-! ### The helix unit -/

/-- The step of a helix at any tick `k`. -/
theorem helix_step (r ω v : ℝ) (k : ℤ) :
    ofLp (helix r ω v (k + 1) - helix r ω v k) = ![helixC r ω k, helixS r ω k, v] := by
  ext i
  fin_cases i <;> simp [helix, helixC, helixS] <;> ring

/-- The helix window's unit of change, as a formula: `‖w‖²_{M⁻¹} = (2/ρ²)(w₀² + w₁²) + w₂²/v²`. -/
theorem mahal_helix_unit {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0) {a b : ℤ}
    (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) (w : Fin 3 → ℝ) :
    mahal (secondMoment (windowSteps (helix r ω v) a b)) w
      = 2 / helixRho2 r ω * (w 0 ^ 2 + w 1 ^ 2) + w 2 ^ 2 / v ^ 2 := by
  rw [mahal, helix_inv_secondMoment hr hv hω hab hN]
  simp [dotProduct, Fin.sum_univ_succ, mulVec_diagonal]
  ring

/-! ### Y4: the rotated helix shares the cone -/

/-- Rotation by `φ` about the third (helix) axis. -/
noncomputable def rotZ (φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos φ, -sin φ, 0; sin φ, cos φ, 0; 0, 0, 1]

theorem det_rotZ (φ : ℝ) : (rotZ φ).det = 1 := by
  simp [rotZ, det_fin_three]
  linear_combination sin_sq_add_cos_sq φ

theorem isUnit_det_rotZ (φ : ℝ) : IsUnit (rotZ φ).det := by
  rw [det_rotZ]; exact isUnit_one

/-- `rotZ φ` fixes `diag(d, d, e)` under conjugation: `R D Rᵀ = D`. -/
theorem rotZ_conj_diagonal (φ d e : ℝ) :
    rotZ φ * diagonal ![d, d, e] * (rotZ φ)ᵀ = diagonal ![d, d, e] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, vecMul_diagonal, Fin.sum_univ_succ, transpose_apply] <;>
    first
    | linear_combination d * sin_sq_add_cos_sq φ
    | ring

/-- The helix rotated by `φ` about its axis (a rotation, not a time-shifted copy, which would look
like trap A8; D-054 A3). -/
noncomputable def helixRot (r ω v φ : ℝ) : ℤ → State :=
  fun k => matState (rotZ φ) (helix r ω v k)

theorem helixRot_secondMoment {r ω v : ℝ} (hω : sin ω ≠ 0) {a b : ℤ} (hab : a < b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) (φ : ℝ) :
    secondMoment (windowSteps (helixRot r ω v φ) a b)
      = diagonal ![helixRho2 r ω / 2, helixRho2 r ω / 2, v ^ 2] := by
  unfold helixRot
  rw [windowSteps_map, secondMoment_map, helix_secondMoment hω hab hN, rotZ_conj_diagonal]

theorem isLorentzC_helixRot {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0) {a b : ℤ}
    (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) (φ : ℝ) :
    IsLorentzC (helixRot r ω v φ) a b √3 :=
  (isLorentzC_map (isUnit_det_rotZ φ)).2 (isLorentzC_helix hr hv hω hab hN)

/-- **Y4 (helix pass, A3).** For `r, v ≠ 0`, `sin ω ≠ 0`, and windows `[a, b)`, `[a′, b′)` that
each cover whole turns: the helix and the helix rotated by any `φ` about its axis share the cone.
Their window unit `diag(ρ²/2, ρ²/2, v²)` commutes with the rotation (N1a, Y9). -/
theorem helix_sharesCone_rot {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0)
    {a b a' b' : ℤ} (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j)
    (hab' : a' < b') (hN' : ∃ j : ℤ, ((b' - a' : ℤ) : ℝ) * ω = 2 * π * j) (φ : ℝ) :
    SharesCone ![helix r ω v, helixRot r ω v φ] ![(a, b), (a', b')] := by
  have hM0 := helix_secondMoment (r := r) (v := v) hω hab hN
  have hM1 := helixRot_secondMoment (r := r) (v := v) hω hab' hN' φ
  refine (sharesCone_iff_secondMoment_eq _ _ fun i => ?_).2 fun i j => ?_
  · fin_cases i
    · exact isLorentzC_helix hr hv hω hab hN
    · exact isLorentzC_helixRot hr hv hω hab' hN' φ
  · fin_cases i <;> fin_cases j
    exacts [rfl, hM0.trans hM1.symm, hM1.trans hM0.symm, rfl]

/-- The quarter-turn helix over one turn `[0, 4)`. -/
theorem quarterTurn_hN : ∃ j : ℤ, (((4 : ℤ) - 0 : ℤ) : ℝ) * (π / 2) = 2 * π * j :=
  ⟨1, by push_cast; ring⟩

/-- D-014 for Y4: the quarter-turn helix and its rotation by `π/3` share the cone over `[0, 4)`. -/
example : SharesCone ![helix 1 (π / 2) 1, helixRot 1 (π / 2) 1 (π / 3)] ![(0, 4), (0, 4)] :=
  helix_sharesCone_rot one_ne_zero one_ne_zero sin_pi_div_two_ne (by norm_num) quarterTurn_hN
    (by norm_num) quarterTurn_hN (π / 3)

/-! ### Y5: U-split (different axial speeds) and U-cross (permuted axis) -/

/-- **Y5 (exact cross-speed).** Equal `r` and `ω`, axial speeds `v` (A) and `v′` (B): every step of
`B` has the same length in `A`'s unit, so `s_{B|A}² = (2 + v′²/v²)/3`. `B`'s window needs no
whole turns. -/
theorem helix_isCrossSpeed_speed {r ω v v' : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0)
    {a b a' b' : ℤ} (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j)
    (hab' : a' < b') :
    IsCrossSpeed (helix r ω v) a b √3 (helix r ω v') a' b' √((2 + v' ^ 2 / v ^ 2) / 3) := by
  have hρ := (helixRho2_pos hr hω).ne'
  have hcm : ∀ k, crossMahal (helix r ω v) a b (helix r ω v') k = 2 + v' ^ 2 / v ^ 2 := by
    intro k
    unfold crossMahal
    rw [helix_step, mahal_helix_unit hr hv hω hab hN]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [helixC_sq_add_helixS_sq]
    field_simp
  have hsq : √(2 + v' ^ 2 / v ^ 2) = √((2 + v' ^ 2 / v ^ 2) / 3) * √3 := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  refine ⟨isLorentzC_helix hr hv hω hab hN, fun k _ => by rw [hcm, hsq],
    a', Finset.mem_Ico.2 ⟨le_rfl, hab'⟩, by rw [hcm, hsq]⟩

/-- **Y5, U-split (A4).** Equal `r`, `ω`, whole turns on both windows, and `v² < v′²`: the faster
helix exceeds the slower one's cone (`s_{B|A} > 1`) while the slower one stays inside the faster
one's (`s_{A|B} < 1`): nested cones. The "satellites at different altitudes" control. -/
theorem helix_crossSpeed_split {r ω v v' : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hv' : v' ≠ 0)
    (hω : sin ω ≠ 0) {a b a' b' : ℤ} (hab : a < b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) (hab' : a' < b')
    (hN' : ∃ j : ℤ, ((b' - a' : ℤ) : ℝ) * ω = 2 * π * j) (hlt : v ^ 2 < v' ^ 2) :
    IsCrossSpeed (helix r ω v) a b √3 (helix r ω v') a' b' √((2 + v' ^ 2 / v ^ 2) / 3) ∧
      IsCrossSpeed (helix r ω v') a' b' √3 (helix r ω v) a b √((2 + v ^ 2 / v' ^ 2) / 3) ∧
      1 < √((2 + v' ^ 2 / v ^ 2) / 3) ∧ √((2 + v ^ 2 / v' ^ 2) / 3) < 1 := by
  have hv2 : 0 < v ^ 2 := by positivity
  have hv2' : 0 < v' ^ 2 := by positivity
  refine ⟨helix_isCrossSpeed_speed hr hv hω hab hN hab',
    helix_isCrossSpeed_speed hr hv' hω hab' hN' hab, ?_, ?_⟩
  · rw [Real.lt_sqrt zero_le_one]
    have : 1 < v' ^ 2 / v ^ 2 := (one_lt_div hv2).2 hlt
    linarith
  · rw [Real.sqrt_lt' one_pos]
    have : v ^ 2 / v' ^ 2 < 1 := (div_lt_one hv2').2 hlt
    linarith

/-- D-014 for Y5 (U-split): helices with `v = 1` and `v′ = 2` over `[0, 4)`: cross-speeds `√2 > 1`
and `√(3/4) < 1`. -/
example : 1 < √((2 + (2 : ℝ) ^ 2 / 1 ^ 2) / 3) ∧ √((2 + (1 : ℝ) ^ 2 / 2 ^ 2) / 3) < 1 :=
  (helix_crossSpeed_split (r := 1) (ω := π / 2) one_ne_zero one_ne_zero two_ne_zero
    sin_pi_div_two_ne (by norm_num : (0 : ℤ) < 4) quarterTurn_hN (by norm_num : (0 : ℤ) < 4)
    quarterTurn_hN (by norm_num)).2.2

/-- Exchange of the first and third axes (the helix axis turned from z to x). -/
def swapXZ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem isUnit_det_swapXZ : IsUnit swapXZ.det := by
  rw [isUnit_iff_ne_zero]
  simp [swapXZ, det_fin_three]

/-- The helix with its axis permuted. -/
noncomputable def helixSwap (r ω v : ℝ) : ℤ → State :=
  fun k => matState swapXZ (helix r ω v k)

theorem helixSwap_secondMoment {r ω v : ℝ} (hω : sin ω ≠ 0) {a b : ℤ} (hab : a < b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    secondMoment (windowSteps (helixSwap r ω v) a b)
      = diagonal ![v ^ 2, helixRho2 r ω / 2, helixRho2 r ω / 2] := by
  unfold helixSwap
  rw [windowSteps_map, secondMoment_map, helix_secondMoment hω hab hN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapXZ, Matrix.mul_apply, vecMul_diagonal, Fin.sum_univ_succ, transpose_apply]

theorem helixSwap_inv_secondMoment {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0)
    {a b : ℤ} (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) :
    (secondMoment (windowSteps (helixSwap r ω v) a b))⁻¹
      = diagonal ![1 / v ^ 2, 2 / helixRho2 r ω, 2 / helixRho2 r ω] := by
  have hρ := (helixRho2_pos hr hω).ne'
  rw [helixSwap_secondMoment hω hab hN]
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]
  all_goals first | exact hρ | exact inv_mul_cancel₀ (pow_ne_zero 2 hv)

/-- `q/p + p/q > 2` for distinct positive `p, q`. -/
theorem div_add_div_gt_two {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) :
    2 < q / p + p / q := by
  have h : q / p + p / q - 2 = (p - q) ^ 2 / (p * q) := by field_simp; ring
  have : 0 < (p - q) ^ 2 / (p * q) := div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hpq))))
    (by positivity)
  linarith

/-- **Y5, U-cross (A4).** For an anisotropic helix (`ρ² ≠ 2v²`), the helix and its axis-permuted
copy each exceed the other's cone: both cross-speeds exist and are `> 1` (crossing cones, not even
a speed ordering). Via the means `tr(M_A⁻¹M_B) = tr(M_B⁻¹M_A) = 2v²/ρ² + 1 + ρ²/(2v²) > 3`. -/
theorem helix_crossSpeed_cross {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0)
    {a b a' b' : ℤ} (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j)
    (hab' : a' < b') (hN' : ∃ j : ℤ, ((b' - a' : ℤ) : ℝ) * ω = 2 * π * j)
    (hani : helixRho2 r ω ≠ 2 * v ^ 2) :
    (∃ s, IsCrossSpeed (helix r ω v) a b √3 (helixSwap r ω v) a' b' s) ∧
      (∃ s, IsCrossSpeed (helixSwap r ω v) a' b' √3 (helix r ω v) a b s) ∧
      (∀ s, IsCrossSpeed (helix r ω v) a b √3 (helixSwap r ω v) a' b' s → 1 < s) ∧
      (∀ s, IsCrossSpeed (helixSwap r ω v) a' b' √3 (helix r ω v) a b s → 1 < s) := by
  have hρp := helixRho2_pos hr hω
  have hq : 0 < 2 * v ^ 2 := by positivity
  have hA := isLorentzC_helix hr hv hω hab hN
  have hB : IsLorentzC (helixSwap r ω v) a' b' √3 :=
    (isLorentzC_map isUnit_det_swapXZ).2 (isLorentzC_helix hr hv hω hab' hN')
  have hgt : 3 < 2 * v ^ 2 / helixRho2 r ω + 1 + helixRho2 r ω / (2 * v ^ 2) := by
    have := div_add_div_gt_two hρp hq hani
    linarith
  have tAB : trace ((secondMoment (windowSteps (helix r ω v) a b))⁻¹ *
      secondMoment (windowSteps (helixSwap r ω v) a' b'))
        = 2 * v ^ 2 / helixRho2 r ω + 1 + helixRho2 r ω / (2 * v ^ 2) := by
    rw [helix_inv_secondMoment hr hv hω hab hN, helixSwap_secondMoment hω hab' hN',
      diagonal_mul_diagonal, trace_diagonal]
    simp [Fin.sum_univ_succ]
    field_simp
    ring
  have tBA : trace ((secondMoment (windowSteps (helixSwap r ω v) a' b'))⁻¹ *
      secondMoment (windowSteps (helix r ω v) a b))
        = 2 * v ^ 2 / helixRho2 r ω + 1 + helixRho2 r ω / (2 * v ^ 2) := by
    rw [helixSwap_inv_secondMoment hr hv hω hab' hN', helix_secondMoment hω hab hN,
      diagonal_mul_diagonal, trace_diagonal]
    simp [Fin.sum_univ_succ]
    field_simp
    ring
  have key : ∀ {s t : ℝ}, 0 ≤ s → t ≤ (s * √3) ^ 2 → 3 < t → 1 < s := by
    intro s t hs ht h3
    rw [mul_pow, Real.sq_sqrt (by norm_num)] at ht
    nlinarith
  refine ⟨exists_isCrossSpeed hA hab', exists_isCrossSpeed hB hab, fun s h => ?_, fun s h => ?_⟩
  · exact key h.nonneg (tAB ▸ trace_le_of_isCrossSpeed h) hgt
  · exact key h.nonneg (tBA ▸ trace_le_of_isCrossSpeed h) hgt

theorem helixRho2_quarterTurn : helixRho2 1 (π / 2) = 2 := by
  simp [helixRho2, cos_pi_div_two]

/-- D-014 for Y5 (U-cross): the quarter-turn helix with `v = 2` (`ρ² = 2 ≠ 8 = 2v²`) and its
axis-permuted copy, over `[0, 4)`: both cross-speeds exceed 1. -/
example : (∀ s, IsCrossSpeed (helix 1 (π / 2) 2) 0 4 √3 (helixSwap 1 (π / 2) 2) 0 4 s → 1 < s) ∧
    (∀ s, IsCrossSpeed (helixSwap 1 (π / 2) 2) 0 4 √3 (helix 1 (π / 2) 2) 0 4 s → 1 < s) :=
  (helix_crossSpeed_cross one_ne_zero two_ne_zero sin_pi_div_two_ne (by norm_num) quarterTurn_hN
    (by norm_num) quarterTurn_hN (by rw [helixRho2_quarterTurn]; norm_num)).2.2

/-! ### Y6 (helix part): trap A7 per count -/

/-- **Y6 (helix part, trap A7).** Measured per **count** in the helix's own unit, its `m`-tick
observer has cross-speed `s² ≥ m²/3`: each of its steps carries the axial drift of `m` ticks.
So it "exceeds" automatically for `|m| ≥ 2`, a decimation artefact, not a different cone. -/
theorem helix_decimate_crossSpeed {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0)
    {a b : ℤ} (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) {m aB bB : ℤ}
    {s : ℝ} (h : IsCrossSpeed (helix r ω v) a b √3 (fun k => helix r ω v (m * k)) aB bB s) :
    (m : ℝ) ^ 2 / 3 ≤ s ^ 2 := by
  rw [helix_decimate] at h
  obtain ⟨k, -, hkc⟩ := h.2.2
  have hcm : crossMahal (helix r ω v) a b (helix r (m * ω) (m * v)) k
      = 2 / helixRho2 r ω * (helixC r (m * ω) k ^ 2 + helixS r (m * ω) k ^ 2) + (m : ℝ) ^ 2 := by
    unfold crossMahal
    rw [helix_step, mahal_helix_unit hr hv hω hab hN]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    field_simp
  have hρ := helixRho2_pos hr hω
  have hge : (m : ℝ) ^ 2 ≤ crossMahal (helix r ω v) a b (helix r (m * ω) (m * v)) k := by
    rw [hcm]
    have : 0 ≤ 2 / helixRho2 r ω * (helixC r (m * ω) k ^ 2 + helixS r (m * ω) k ^ 2) := by
      positivity
    linarith
  have h0 : 0 ≤ crossMahal (helix r ω v) a b (helix r (m * ω) (m * v)) k :=
    (sq_nonneg _).trans hge
  have h3 : crossMahal (helix r ω v) a b (helix r (m * ω) (m * v)) k = 3 * s ^ 2 := by
    rw [← Real.sq_sqrt h0, hkc, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  linarith

/-- **Y6 (helix part), the exceedance.** For `|m| ≥ 2` the per-count cross-speed exceeds 1. -/
theorem helix_decimate_crossSpeed_gt {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0)
    {a b : ℤ} (hab : a < b) (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) {m aB bB : ℤ}
    (hm : 2 ≤ |m|) {s : ℝ}
    (h : IsCrossSpeed (helix r ω v) a b √3 (fun k => helix r ω v (m * k)) aB bB s) : 1 < s := by
  have h1 := helix_decimate_crossSpeed hr hv hω hab hN h
  have hm2 : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hm
    nlinarith [sq_abs (m : ℝ), abs_nonneg (m : ℝ)]
  nlinarith [h.nonneg]

/-- D-014 for Y6 (helix part): the quarter-turn helix read every 2 ticks over `[0, 2)`, measured per
count in its own unit, exceeds its cone. -/
example {s : ℝ} (h : IsCrossSpeed (helix 1 (π / 2) 1) 0 4 √3 (fun k => helix 1 (π / 2) 1 (2 * k)) 0 2 s) :
    1 < s :=
  helix_decimate_crossSpeed_gt one_ne_zero one_ne_zero sin_pi_div_two_ne (by norm_num)
    quarterTurn_hN (by norm_num) h

/-- D-014 for Y8, non-trivial (D-058): the helices with axial speeds `v = 1` and `v′ = 2` over
`[0, 4)` have `s_{B|A}² + s_{A|B}² = 2 + 3/4 ≥ 2` (nested cones, never both inside). -/
example : 2 ≤ √((2 + (2 : ℝ) ^ 2 / 1 ^ 2) / 3) ^ 2 + √((2 + (1 : ℝ) ^ 2 / 2 ^ 2) / 3) ^ 2 :=
  crossSpeed_sq_add_ge
    (helix_isCrossSpeed_speed (r := 1) (ω := π / 2) (v := 1) (v' := 2) one_ne_zero one_ne_zero
      sin_pi_div_two_ne (by norm_num : (0 : ℤ) < 4) quarterTurn_hN (by norm_num : (0 : ℤ) < 4))
    (helix_isCrossSpeed_speed (r := 1) (ω := π / 2) (v := 2) (v' := 1) one_ne_zero two_ne_zero
      sin_pi_div_two_ne (by norm_num : (0 : ℤ) < 4) quarterTurn_hN (by norm_num : (0 : ℤ) < 4))

end GeneralizedCSymmetry
