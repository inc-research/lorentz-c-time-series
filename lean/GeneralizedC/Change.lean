/-
GeneralizedC/Change.lean: the unit of change, as matrix algebra (CP5: N1a, N1c).

  secondMoment u                  M(u) = (1/N) Σₖ uₖ uₖᵀ, uncentered (D-031 R2, D-034 C2)
  mahal M v                       ‖v‖²_{M⁻¹} = vᵀ M⁻¹ v, squared Mahalanobis length
  N1a  secondMoment_map            M(Du) = D M(u) Dᵀ
       mahal_conj                  mahal (D M Dᵀ) (D v) = mahal M v      (det D a unit; nothing on M)
       mahal_secondMoment_map      every step keeps its length under any invertible change of units
  N1c  mean_mahal_secondMoment     (1/N) Σₖ mahal M (uₖ) = n           (det M a unit)
       exists_le_mahal             some step has mahal ≥ n               (so c̃ ≥ 1)
       mahal_eq_of_le              all ≤ n ⇒ all = n                     (c̃ = 1 iff equal lengths)
  N1c′ secondMoment_posSemidef     M is positive semidefinite                         (CP5b)
       secondMoment_posDef_iff_span, isUnit_det_secondMoment_iff_span
                                   M PD ⇔ det M a unit ⇔ the steps span ℝⁿ (coverage, U6c)
  N1d  mahal_secondMoment_le_card  det M a unit ⇒ mahal M (uₖ) ≤ N      (c̃ ≤ √(N/n))
  N1f  relMat_conj, charpoly_relMat_conj
                                   relative eigenvalues of two second moments are unit-free (U6a)

Design (PROGRESS D-034, cp5_breakdown): vectors `Fin n → ℝ` with Mathlib's `Matrix` (C1); squared
lengths, no square roots (C4); weakest invertibility hypotheses, `IsUnit _.det` (C3). Mathlib's
`M⁻¹` is the nonsingular inverse: the true inverse when `det M` is a unit, `0` otherwise.
Every theorem with hypotheses is followed by `example`s that satisfy them (D-014).
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

open Matrix

namespace GeneralizedC

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Uncentered second moment of a finite family of steps: `M = (1/N) Σₖ uₖ uₖᵀ` (D-031 R2). -/
noncomputable def secondMoment (u : ι → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ k, vecMulVec (u k) (u k)

/-- Squared length of a change `v` in the unit of change `M⁻¹`: `vᵀ M⁻¹ v` (Mahalanobis). -/
noncomputable def mahal (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  v ⬝ᵥ (M⁻¹ *ᵥ v)

/-! ### N1a: unit equivariance -/

/-- `(Da)(Da)ᵀ = D (a aᵀ) Dᵀ`. -/
theorem vecMulVec_mulVec_self (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    vecMulVec (D *ᵥ a) (D *ᵥ a) = D * vecMulVec a a * Dᵀ := by
  rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

/-- **N1a (i).** Changing the units of the axes by any matrix `D` changes the second moment to
`D M Dᵀ`. -/
theorem secondMoment_map (D : Matrix (Fin n) (Fin n) ℝ) (u : ι → Fin n → ℝ) :
    secondMoment (fun k => D *ᵥ u k) = D * secondMoment u * Dᵀ := by
  simp only [secondMoment, vecMulVec_mulVec_self, Matrix.mul_smul, Matrix.smul_mul,
    Finset.mul_sum, Finset.sum_mul]

/-- **N1a (ii).** For `det D` a unit: `mahal (D M Dᵀ) (D v) = mahal M v`. No hypothesis on `M`
(if `det M = 0`, both nonsingular inverses are `0`; breakdown N1a A1). -/
theorem mahal_conj {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsUnit D.det)
    (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    mahal (D * M * Dᵀ) (D *ᵥ v) = mahal M v := by
  have hDt : IsUnit Dᵀ.det := by rwa [det_transpose]
  have h1 : D⁻¹ *ᵥ (D *ᵥ v) = v := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hD, one_mulVec]
  have h2 : ∀ w, (D *ᵥ v) ⬝ᵥ (Dᵀ⁻¹ *ᵥ w) = v ⬝ᵥ w := by
    intro w
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, mul_nonsing_inv _ hDt, vecMul_one]
  unfold mahal
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec, h1, h2]

/-- **N1a (iii).** Every step has the same Mahalanobis length before and after an invertible
change of units `D`. So `c̃`, built from these lengths, does not depend on the units. -/
theorem mahal_secondMoment_map {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsUnit D.det)
    (u : ι → Fin n → ℝ) (k : ι) :
    mahal (secondMoment fun k => D *ᵥ u k) (D *ᵥ u k) = mahal (secondMoment u) (u k) := by
  rw [secondMoment_map]
  exact mahal_conj hD _ _

/-- D-014 for N1a: a per-axis change of units on two axes (×9/5 for °C → °F, ×1 for the
other), for any family of steps. -/
example (u : ι → Fin 2 → ℝ) (k : ι) :
    mahal (secondMoment fun k => diagonal ![9 / 5, 1] *ᵥ u k) (diagonal ![9 / 5, 1] *ᵥ u k)
      = mahal (secondMoment u) (u k) :=
  mahal_secondMoment_map (by simp [det_diagonal]) u k

/-- D-014 for N1a: a change of units that mixes the axes (a shear), `det = 1`. -/
example (u : ι → Fin 2 → ℝ) (k : ι) :
    mahal (secondMoment fun k => !![1, 1; 0, 1] *ᵥ u k) (!![1, 1; 0, 1] *ᵥ u k)
      = mahal (secondMoment u) (u k) :=
  mahal_secondMoment_map (by simp [det_fin_two]) u k

/-! ### N1c: the trace identity -/

/-- `tr(A M(u)) = (1/N) Σₖ uₖᵀ A uₖ`: a quadratic form summed over the steps is a trace. -/
theorem trace_mul_secondMoment (A : Matrix (Fin n) (Fin n) ℝ) (u : ι → Fin n → ℝ) :
    trace (A * secondMoment u) = (Fintype.card ι : ℝ)⁻¹ * ∑ k, u k ⬝ᵥ (A *ᵥ u k) := by
  simp only [secondMoment, Matrix.mul_smul, Finset.mul_sum, trace_smul, trace_sum, mul_vecMulVec,
    trace_vecMulVec, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [dotProduct_comm]

/-- **N1c (i).** For `det M(u)` a unit, the mean squared Mahalanobis length of the steps is
exactly `n`: `(1/N) Σₖ mahal M (uₖ) = tr(M⁻¹ M) = tr Iₙ = n`. The RMS step has length `√n`. -/
theorem mean_mahal_secondMoment (u : ι → Fin n → ℝ) (hM : IsUnit (secondMoment u).det) :
    (Fintype.card ι : ℝ)⁻¹ * ∑ k, mahal (secondMoment u) (u k) = n := by
  show (Fintype.card ι : ℝ)⁻¹ * ∑ k, u k ⬝ᵥ ((secondMoment u)⁻¹ *ᵥ u k) = n
  rw [← trace_mul_secondMoment, nonsing_inv_mul _ hM, trace_one, Fintype.card_fin]

/-- The sum form of N1c (i): `Σₖ mahal M (uₖ) = N · n`. -/
theorem sum_mahal_secondMoment [Nonempty ι] (u : ι → Fin n → ℝ)
    (hM : IsUnit (secondMoment u).det) :
    ∑ k, mahal (secondMoment u) (u k) = Fintype.card ι * n := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← mean_mahal_secondMoment u hM, mul_inv_cancel_left₀ hc]

/-- **N1c (ii).** Some step has squared length `≥ n`: the longest step is at least `√n` long,
so `c̃ = max‖Δxₖ‖_{M⁻¹} / √n ≥ 1`. -/
theorem exists_le_mahal [Nonempty ι] (u : ι → Fin n → ℝ) (hM : IsUnit (secondMoment u).det) :
    ∃ k, (n : ℝ) ≤ mahal (secondMoment u) (u k) := by
  by_contra h
  push Not at h
  have hlt : ∑ k, mahal (secondMoment u) (u k) < ∑ _k : ι, (n : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ => h k
  rw [sum_mahal_secondMoment u hM, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  exact lt_irrefl _ hlt

/-- **N1c (iii).** If no step is longer than `√n`, every step has length exactly `√n`
(`c̃ = 1` iff all steps are equally long; equal length, not equal direction). -/
theorem mahal_eq_of_le [Nonempty ι] (u : ι → Fin n → ℝ) (hM : IsUnit (secondMoment u).det)
    (h : ∀ k, mahal (secondMoment u) (u k) ≤ n) : ∀ k, mahal (secondMoment u) (u k) = n := by
  by_contra hne
  push Not at hne
  obtain ⟨k, hk⟩ := hne
  have hlt : ∑ k, mahal (secondMoment u) (u k) < ∑ _k : ι, (n : ℝ) :=
    Finset.sum_lt_sum (fun k _ => h k) ⟨k, Finset.mem_univ k, lt_of_le_of_ne (h k) hk⟩
  rw [sum_mahal_secondMoment u hM, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  exact lt_irrefl _ hlt

/-- The two steps `+1` and `−1` on one axis: the light-ray case. -/
def pmSteps : Fin 2 → Fin 1 → ℝ := ![![1], ![-1]]

theorem secondMoment_pmSteps : secondMoment pmSteps = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [secondMoment, pmSteps, Fin.sum_univ_two]
  norm_num

/-- D-014 for N1c: `M(±1) = 1` is invertible, and both steps have squared length `1 = n`
(so `c̃ = 1`): (i) holds with mean `1`, and (iii) applies. -/
example : (2 : ℝ)⁻¹ * ∑ k, mahal (secondMoment pmSteps) (pmSteps k) = 1 := by
  have := mean_mahal_secondMoment pmSteps (by rw [secondMoment_pmSteps, det_one]; exact isUnit_one)
  simpa using this

example : ∀ k, mahal (secondMoment pmSteps) (pmSteps k) = 1 := by
  have hM : IsUnit (secondMoment pmSteps).det := by
    rw [secondMoment_pmSteps, det_one]; exact isUnit_one
  have := mahal_eq_of_le pmSteps hM fun k => by
    rw [secondMoment_pmSteps]
    fin_cases k <;> simp [mahal, pmSteps]
  simpa using this

/-- D-014 for N1c (ii): some step of `±1` has squared length `≥ 1`. -/
example : ∃ k, (1 : ℝ) ≤ mahal (secondMoment pmSteps) (pmSteps k) := by
  simpa using exists_le_mahal pmSteps (by rw [secondMoment_pmSteps, det_one]; exact isUnit_one)

/-! ### N1c′: coverage (CP5b) -/

/-- `M(u) v = (1/N) Σₖ (uₖ · v) uₖ`. -/
theorem mulVec_secondMoment (u : ι → Fin n → ℝ) (v : Fin n → ℝ) :
    secondMoment u *ᵥ v = (Fintype.card ι : ℝ)⁻¹ • ∑ k, (u k ⬝ᵥ v) • u k := by
  rw [secondMoment, smul_mulVec, sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form of the second moment: `vᵀ M v = (1/N) Σₖ (uₖ · v)²`. -/
theorem dotProduct_mulVec_secondMoment (u : ι → Fin n → ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (secondMoment u *ᵥ v) = (Fintype.card ι : ℝ)⁻¹ * ∑ k, (u k ⬝ᵥ v) ^ 2 := by
  rw [mulVec_secondMoment, dotProduct_smul, dotProduct_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm v, sq]

theorem secondMoment_isHermitian (u : ι → Fin n → ℝ) : (secondMoment u).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]
  simp only [secondMoment, transpose_smul, transpose_sum, transpose_vecMulVec]

/-- **N1c′ (i).** The second moment is positive semidefinite. -/
theorem secondMoment_posSemidef (u : ι → Fin n → ℝ) : (secondMoment u).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨secondMoment_isHermitian u, fun x => ?_⟩
  rw [star_trivial, dotProduct_mulVec_secondMoment]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => sq_nonneg _)

/-- `M(u) v = 0` exactly when `v` is orthogonal to every step. -/
theorem mulVec_secondMoment_eq_zero_iff (u : ι → Fin n → ℝ) (v : Fin n → ℝ) :
    secondMoment u *ᵥ v = 0 ↔ ∀ k, u k ⬝ᵥ v = 0 := by
  constructor
  · intro h k
    have : Nonempty ι := ⟨k⟩
    have hc : (Fintype.card ι : ℝ)⁻¹ ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    have hq : (Fintype.card ι : ℝ)⁻¹ * ∑ j, (u j ⬝ᵥ v) ^ 2 = 0 := by
      rw [← dotProduct_mulVec_secondMoment, h, dotProduct_zero]
    have hs := (mul_eq_zero.1 hq).resolve_left hc
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (u j ⬝ᵥ v)).1 hs k
      (Finset.mem_univ k)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  · intro h
    rw [mulVec_secondMoment]
    simp [h]

/-- The steps **cover** `ℝⁿ`: no non-zero direction is orthogonal to every step. -/
def Covers (u : ι → Fin n → ℝ) : Prop :=
  ∀ v : Fin n → ℝ, (∀ k, u k ⬝ᵥ v = 0) → v = 0

omit [Fintype ι] in
/-- Covering is spanning: `Covers u ⇔ span{uₖ} = ℝⁿ` (via the dual space: every linear
functional on `ℝⁿ` is a dot product). -/
theorem covers_iff_span_eq_top (u : ι → Fin n → ℝ) :
    Covers u ↔ Submodule.span ℝ (Set.range u) = ⊤ := by
  rw [← Submodule.dualAnnihilator_eq_bot_iff, Submodule.eq_bot_iff]
  constructor
  · intro h φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    obtain ⟨v, rfl⟩ := (dotProductEquiv ℝ (Fin n)).surjective φ
    have hv : v = 0 := h v fun k => by
      have := hφ (u k) (Submodule.subset_span ⟨k, rfl⟩)
      simpa [dotProduct_comm] using this
    simp [hv]
  · intro h v hv
    have hann : dotProductEquiv ℝ (Fin n) v ∈ (Submodule.span ℝ (Set.range u)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        simp only [dotProductEquiv_apply_apply]
        rw [dotProduct_comm]
        exact hv k
      | zero => simp
      | add x y _ _ hx hy => simp_all [dotProduct_add]
      | smul a x _ hx => simp_all
    exact (dotProductEquiv ℝ (Fin n)).map_eq_zero_iff.1 (h _ hann)

/-- **N1c′ (iii).** `det M(u)` is a unit ⇔ the steps cover `ℝⁿ`. -/
theorem isUnit_det_secondMoment_iff_covers (u : ι → Fin n → ℝ) :
    IsUnit (secondMoment u).det ↔ Covers u := by
  rw [isUnit_iff_ne_zero, Ne, ← exists_mulVec_eq_zero_iff]
  constructor
  · intro h v hv
    by_contra hne
    exact h ⟨v, hne, (mulVec_secondMoment_eq_zero_iff u v).2 hv⟩
  · rintro h ⟨v, hne, hv⟩
    exact hne (h v ((mulVec_secondMoment_eq_zero_iff u v).1 hv))

/-- **N1c′ (iii), span form.** The unit of change exists exactly when the steps span `ℝⁿ`. -/
theorem isUnit_det_secondMoment_iff_span (u : ι → Fin n → ℝ) :
    IsUnit (secondMoment u).det ↔ Submodule.span ℝ (Set.range u) = ⊤ := by
  rw [isUnit_det_secondMoment_iff_covers, covers_iff_span_eq_top]

/-- **N1c′ (ii).** `M(u)` is positive definite ⇔ the steps span `ℝⁿ`. -/
theorem secondMoment_posDef_iff_span (u : ι → Fin n → ℝ) :
    (secondMoment u).PosDef ↔ Submodule.span ℝ (Set.range u) = ⊤ := by
  rw [← covers_iff_span_eq_top, posDef_iff_dotProduct_mulVec]
  simp only [secondMoment_isHermitian u, true_and, star_trivial, dotProduct_mulVec_secondMoment]
  constructor
  · intro h v hv
    by_contra hne
    have := h hne
    simp [hv] at this
  · intro h x hx
    have : ∃ k, u k ⬝ᵥ x ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (h x hall)
    obtain ⟨k, hk⟩ := this
    have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨k⟩)
    refine mul_pos (inv_pos.2 hcard) ?_
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨k, Finset.mem_univ k, by positivity⟩

/-! ### N1d: the block cap (CP5b) -/

/-- **N1d.** If `det M(u)` is a unit, every step has squared length at most `N` in the unit of
change: `mahal M (uₖ) ≤ N`. So `c° ≤ √N` and `c̃ ≤ √(N/n)`. (The leverage of a step is at
most 1.) -/
theorem mahal_secondMoment_le_card (u : ι → Fin n → ℝ) (hM : IsUnit (secondMoment u).det)
    (k : ι) : mahal (secondMoment u) (u k) ≤ Fintype.card ι := by
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨k⟩)
  set w := (secondMoment u)⁻¹ *ᵥ u k with hw
  have hMw : secondMoment u *ᵥ w = u k := by
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hM, one_mulVec]
  -- h = uₖ · w is the step's squared length; also h = wᵀ M w = (1/N) Σⱼ (uⱼ · w)²
  have hh : mahal (secondMoment u) (u k) = u k ⬝ᵥ w := rfl
  have hq : u k ⬝ᵥ w = (Fintype.card ι : ℝ)⁻¹ * ∑ j, (u j ⬝ᵥ w) ^ 2 := by
    rw [← dotProduct_mulVec_secondMoment, hMw, dotProduct_comm]
  have hk : (u k ⬝ᵥ w) ^ 2 ≤ ∑ j, (u j ⬝ᵥ w) ^ 2 :=
    Finset.single_le_sum (f := fun j => (u j ⬝ᵥ w) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ k)
  have h0 : 0 ≤ u k ⬝ᵥ w := by
    rw [hq]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have h1 : (Fintype.card ι : ℝ)⁻¹ * (u k ⬝ᵥ w) ^ 2 ≤ u k ⬝ᵥ w := by
    calc (Fintype.card ι : ℝ)⁻¹ * (u k ⬝ᵥ w) ^ 2
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ j, (u j ⬝ᵥ w) ^ 2 :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = u k ⬝ᵥ w := hq.symm
  rw [hh]
  rcases h0.eq_or_lt with h0 | h0
  · rw [← h0]; exact hcard.le
  · -- divide h1 by h > 0: h / N ≤ 1
    have h2 : (Fintype.card ι : ℝ)⁻¹ * (u k ⬝ᵥ w) ≤ 1 := by
      have := h1
      rw [sq, ← mul_assoc] at this
      exact (mul_le_iff_le_one_left h0).1 (by linarith)
    rwa [inv_mul_le_iff₀ hcard, mul_one] at h2

/-! ### N1f: relative eigenvalues are unit-free (CP5b) -/

/-- **N1f.** For `det D` a unit, the relative matrix `M_P⁻¹ M_I` of two second moments changes
by a similarity under a change of units `D`: `(D M_P Dᵀ)⁻¹ (D M_I Dᵀ) = D⁻ᵀ (M_P⁻¹ M_I) Dᵀ`.
No hypothesis on `M_P` (both nonsingular inverses are `0` together). -/
theorem relMat_conj {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsUnit D.det)
    (MP MI : Matrix (Fin n) (Fin n) ℝ) :
    (D * MP * Dᵀ)⁻¹ * (D * MI * Dᵀ) = Dᵀ⁻¹ * (MP⁻¹ * MI) * Dᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc D⁻¹ D, nonsing_inv_mul _ hD, Matrix.one_mul]

/-- **N1f (eigenvalues).** The relative matrix has the same characteristic polynomial, hence the
same relative eigenvalues, in every system of units. U6a's unit-stability statistic is unit-free. -/
theorem charpoly_relMat_conj {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsUnit D.det)
    (MP MI : Matrix (Fin n) (Fin n) ℝ) :
    ((D * MP * Dᵀ)⁻¹ * (D * MI * Dᵀ)).charpoly = (MP⁻¹ * MI).charpoly := by
  have hDt : IsUnit Dᵀ.det := by rwa [det_transpose]
  rw [relMat_conj hD]
  exact charpoly_units_conj' (nonsingInvUnit Dᵀ hDt) (MP⁻¹ * MI)

/-- The trace (sum of the relative eigenvalues) is unit-free too. -/
theorem trace_relMat_conj {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsUnit D.det)
    (MP MI : Matrix (Fin n) (Fin n) ℝ) :
    trace ((D * MP * Dᵀ)⁻¹ * (D * MI * Dᵀ)) = trace (MP⁻¹ * MI) := by
  have hDt : IsUnit Dᵀ.det := by rwa [det_transpose]
  rw [relMat_conj hD, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc (MP⁻¹ * MI),
    mul_nonsing_inv _ hDt, Matrix.mul_one]

/-! ### D-014 examples for CP5b (cp5b_breakdown, three families) -/

/-- Family 1: `±e₁, ±e₂, ±e₃` (N = 6): `M = I/3`, every step has squared length 3. -/
def pmBasis : Fin 6 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1]]

theorem secondMoment_pmBasis : secondMoment pmBasis = (3 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondMoment, pmBasis, Fin.sum_univ_succ] <;> norm_num

theorem inv_secondMoment_pmBasis : (secondMoment pmBasis)⁻¹ = (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [secondMoment_pmBasis]
  refine inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, Matrix.one_mul]
  norm_num

/-- D-014 for N1c′: `±eᵢ` covers `ℝ³`, so its unit of change exists. -/
theorem isUnit_det_pmBasis : IsUnit (secondMoment pmBasis).det := by
  rw [isUnit_det_secondMoment_iff_covers]
  intro v hv
  have h0 := hv 0; have h2 := hv 2; have h4 := hv 4
  simp [pmBasis, dotProduct, Fin.sum_univ_succ] at h0 h2 h4
  ext i; fin_cases i <;> simp [h0, h2, h4]

/-- D-014 for N1c: every step of `±eᵢ` has squared length `3 = n` (the light-ray case in three
dimensions, `c̃ = 1`). -/
theorem mahal_pmBasis (k : Fin 6) : mahal (secondMoment pmBasis) (pmBasis k) = 3 := by
  rw [mahal, inv_secondMoment_pmBasis]
  fin_cases k <;> simp [pmBasis, dotProduct, Fin.sum_univ_succ, smul_mulVec, one_mulVec]

/-- Reindexing a family does not change its second moment. -/
theorem secondMoment_comp_equiv {ι' : Type*} [Fintype ι'] (u : ι → Fin n → ℝ) (e : ι' ≃ ι) :
    secondMoment (u ∘ e) = secondMoment u := by
  simp only [secondMoment, Function.comp, Fintype.card_congr e]
  congr 1
  exact e.sum_comp fun k => vecMulVec (u k) (u k)

/-- Family 2: `e₁, e₂, e₃, 2e₁` (N = 4): `M = diag(5, 1, 1)/4`. -/
def leverageSteps : Fin 4 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![2, 0, 0]]

theorem secondMoment_leverageSteps :
    secondMoment leverageSteps = diagonal ![5 / 4, 1 / 4, 1 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondMoment, leverageSteps, Fin.sum_univ_succ]

theorem inv_secondMoment_leverageSteps :
    (secondMoment leverageSteps)⁻¹ = diagonal ![4 / 5, 4, 4] := by
  rw [secondMoment_leverageSteps]
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

/-- D-014 for N1d: the cap `mahal ≤ N = 4` is reached by `e₂` (orthogonal to every other step:
leverage 1), while the long step `2e₁` has only `16/5`. -/
example : mahal (secondMoment leverageSteps) (leverageSteps 1) = 4 ∧
    mahal (secondMoment leverageSteps) (leverageSteps 3) = 16 / 5 ∧
    mahal (secondMoment leverageSteps) (leverageSteps 1) ≤ Fintype.card (Fin 4) := by
  refine ⟨?_, ?_, mahal_secondMoment_le_card leverageSteps ?_ 1⟩
  · rw [mahal, inv_secondMoment_leverageSteps]
    simp [leverageSteps, dotProduct, Fin.sum_univ_succ, mulVec_diagonal]
  · rw [mahal, inv_secondMoment_leverageSteps]
    simp [leverageSteps, dotProduct, Fin.sum_univ_succ, mulVec_diagonal]
    norm_num
  · rw [secondMoment_leverageSteps, det_diagonal]
    simp [Fin.prod_univ_succ]

/-- Family 3: `e₁, −e₁, e₂` (N = 3): planar steps. -/
def planarSteps : Fin 3 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![-1, 0, 0], ![0, 1, 0]]

/-- D-014 for N1c′ (the trap): the planar steps miss `e₃`, so no unit of change exists. -/
example : ¬ IsUnit (secondMoment planarSteps).det := by
  rw [isUnit_det_secondMoment_iff_covers]
  intro h
  have := h ![0, 0, 1] fun k => by fin_cases k <;> simp [planarSteps, dotProduct, Fin.sum_univ_succ]
  have h2 := congrFun this 2
  simp at h2

/-- D-014 for N1f: a change of units on two axes (×9/5, ×1) leaves the relative characteristic
polynomial of any two second moments unchanged. -/
example (MP MI : Matrix (Fin 2) (Fin 2) ℝ) :
    ((diagonal ![9 / 5, 1] * MP * (diagonal ![9 / 5, 1])ᵀ)⁻¹ *
      (diagonal ![9 / 5, 1] * MI * (diagonal ![9 / 5, 1])ᵀ)).charpoly = (MP⁻¹ * MI).charpoly :=
  charpoly_relMat_conj (by simp [det_diagonal]) MP MI

end GeneralizedC
