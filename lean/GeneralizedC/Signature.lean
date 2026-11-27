/-
GeneralizedC/Signature.lean: Q_c has signature (1,3) for c ≠ 0 (T8).

  minkowskiBilin, minkowskiQF          (Q_c bundled as a Mathlib `QuadraticForm`)
  minkowskiQF_apply                    (agrees with the plain function `minkowskiQ` of T1–T5)
  T8   minkowskiQF_equivalent          (c ≠ 0: Q_c ≅ diag(1, −1, −1, −1), explicit isometry)
       sigPos_minkowskiQF, sigNeg_minkowskiQF   (sigPos = 1, sigNeg = 3, Sylvester uniqueness)
       radical_minkowskiQF             (c ≠ 0: nondegenerate, radical = 0)
  T8'  mem_radical_minkowskiQF_zero    (c = 0: degenerate, the time axis lies in the radical)

Design (PROGRESS D-017, cp3_breakdown T8 C1(a), C2(a)).
-/
import GeneralizedC.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

open scoped InnerProductSpace
open QuadraticMap QuadraticForm

namespace GeneralizedC

/-- The Minkowski bilinear form `B_c((t, x), (s, y)) = c² t s − ⟨x, y⟩`. -/
noncomputable def minkowskiBilin (c : ℝ) : LinearMap.BilinForm ℝ (ℝ × State) :=
  LinearMap.mk₂ ℝ (fun p q => c ^ 2 * p.1 * q.1 - ⟪p.2, q.2⟫_ℝ)
    (fun p p' q => by simp only [Prod.fst_add, Prod.snd_add, inner_add_left]; ring)
    (fun a p q => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_left]; ring)
    (fun p q q' => by simp only [Prod.fst_add, Prod.snd_add, inner_add_right]; ring)
    (fun a p q => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right]; ring)

/-- `Q_c` as a Mathlib quadratic form: `Q_c(p) = B_c(p, p)`. -/
noncomputable def minkowskiQF (c : ℝ) : QuadraticForm ℝ (ℝ × State) :=
  (minkowskiBilin c).toQuadraticMap

/-- The bundled form agrees with `minkowskiQ`, so T1–T5 are statements about it. -/
theorem minkowskiQF_apply (c : ℝ) (p : ℝ × State) : minkowskiQF c p = minkowskiQ c p := by
  simp only [minkowskiQF, LinearMap.BilinMap.toQuadraticMap_apply, minkowskiBilin,
    LinearMap.mk₂_apply, real_inner_self_eq_norm_sq, minkowskiQ]
  ring

/-- `‖x‖² = x₀² + x₁² + x₂²` on the state space. -/
theorem norm_sq_state (x : State) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity),
    Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The coordinate change `(Δt, Δx) ↦ (cΔt, Δx₀, Δx₁, Δx₂)`; invertible exactly when `c ≠ 0`. -/
noncomputable def minkowskiCoords {c : ℝ} (hc : c ≠ 0) : (ℝ × State) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun p := ![c * p.1, p.2 0, p.2 1, p.2 2]
  invFun f := (f 0 / c, WithLp.toLp 2 ![f 1, f 2, f 3])
  map_add' p q := by
    ext i; fin_cases i <;> simp [mul_add]
  map_smul' a p := by
    ext i; fin_cases i <;> simp [mul_left_comm]
  left_inv p := by
    ext i
    · simp [hc]
    · fin_cases i <;> simp
  right_inv f := by
    ext i; fin_cases i <;> simp
    field_simp

/-- The diagonal weights of `diag(1, −1, −1, −1)`. -/
def minkowskiWeights : Fin 4 → ℝ := ![1, -1, -1, -1]

/-- **T8 (explicit form).** For `c ≠ 0`, `Q_c` is isometric to the weighted sum of squares
`u₀² − u₁² − u₂² − u₃²` via `minkowskiCoords`. -/
noncomputable def minkowskiIsometry {c : ℝ} (hc : c ≠ 0) :
    (minkowskiQF c).IsometryEquiv (weightedSumSquares ℝ minkowskiWeights) where
  toLinearEquiv := minkowskiCoords hc
  map_app' p := by
    rw [minkowskiQF_apply, weightedSumSquares_apply, Fin.sum_univ_four]
    simp only [minkowskiQ, norm_sq_state, minkowskiWeights, minkowskiCoords]
    simp
    ring

theorem minkowskiQF_equivalent {c : ℝ} (hc : c ≠ 0) :
    (minkowskiQF c).Equivalent (weightedSumSquares ℝ minkowskiWeights) :=
  ⟨minkowskiIsometry hc⟩

/-- **T8.** For `c ≠ 0`, `Q_c` has exactly one positive direction ... -/
theorem sigPos_minkowskiQF {c : ℝ} (hc : c ≠ 0) : sigPos (minkowskiQF c) = 1 := by
  rw [sigPos_of_equiv_weightedSumSquares (minkowskiQF_equivalent hc)]
  have : {i | 0 < minkowskiWeights i} = {0} := by
    ext i; fin_cases i <;> simp [minkowskiWeights]
  rw [this, Set.ncard_singleton]

/-- ... and exactly three negative directions: signature (1, 3). -/
theorem sigNeg_minkowskiQF {c : ℝ} (hc : c ≠ 0) : sigNeg (minkowskiQF c) = 3 := by
  rw [sigNeg_of_equiv_weightedSumSquares (minkowskiQF_equivalent hc)]
  have : {i | minkowskiWeights i < 0} = ((({1, 2, 3} : Finset (Fin 4))) : Set (Fin 4)) := by
    ext i; fin_cases i <;> simp [minkowskiWeights]
  rw [this, Set.ncard_coe_finset]
  rfl

/-- **T8 (nondegenerate).** For `c ≠ 0` the radical of `Q_c` is zero: 1 + 3 + rank = 4. -/
theorem radical_minkowskiQF {c : ℝ} (hc : c ≠ 0) : (minkowskiQF c).radical = ⊥ := by
  have h := sigPos_add_sigNeg_add_radical (Q := minkowskiQF c)
  rw [sigPos_minkowskiQF hc, sigNeg_minkowskiQF hc, Module.finrank_prod, Module.finrank_self,
    finrank_euclideanSpace, Fintype.card_fin] at h
  exact Submodule.finrank_eq_zero.mp (by omega)

/-- D-014 for T8: `c = 1`. -/
example : sigPos (minkowskiQF 1) = 1 ∧ sigNeg (minkowskiQF 1) = 3 ∧
    (minkowskiQF 1).radical = ⊥ :=
  ⟨sigPos_minkowskiQF one_ne_zero, sigNeg_minkowskiQF one_ne_zero,
    radical_minkowskiQF one_ne_zero⟩

/-- D-014 for T8 with a large, physical value: `c = 299 792 458`. -/
example : sigPos (minkowskiQF 299792458) = 1 ∧ sigNeg (minkowskiQF 299792458) = 3 :=
  ⟨sigPos_minkowskiQF (by norm_num), sigNeg_minkowskiQF (by norm_num)⟩

/-- **T8′ (c = 0 is degenerate).** `Q_0 = −‖Δx‖²` ignores time: the pure time displacement
`(1, 0)` lies in the radical (it is "orthogonal to everything", including itself). -/
theorem mem_radical_minkowskiQF_zero : ((1 : ℝ), (0 : State)) ∈ (minkowskiQF 0).radical := by
  rw [mem_radical_iff']
  refine ⟨?_, fun n => ?_⟩ <;> simp [minkowskiQF_apply, minkowskiQ]

/-- So for `c = 0` the radical is not zero, in contrast with `radical_minkowskiQF`. -/
theorem radical_minkowskiQF_zero_ne_bot : (minkowskiQF 0).radical ≠ ⊥ := by
  intro h
  have := mem_radical_minkowskiQF_zero
  rw [h, Submodule.mem_bot] at this
  simp at this

end GeneralizedC
