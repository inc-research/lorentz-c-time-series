/-
GeneralizedC/Window.lean: the window bridge √n ≤ c° ≤ √N (CP5b: N1e).

  windowSteps x a b              the steps Δxₖ, k ∈ [a, b), indexed by the subtype of `Finset.Ico a b`
  N1e (i)   sqrt_three_le_tickCritSpeed      √3 ≤ c°                   (c̃ ≥ 1)
  N1e (ii)  mahal_eq_three_of_tickCritSpeed_eq   c° = √3 ⇒ every step has mahal = 3 (light-ray case)
  N1e (iii) tickCritSpeed_le_sqrt_card       c° ≤ √(b − a)            (c̃ ≤ √(N/3))

Here M is the window's own second moment (D-031 R2), `det M` a unit, and L any factor with
`Lᵀ L = M⁻¹` (N1b). Joins N1c, N1d (Change.lean) to the c° bridge N1b-iv (GaugeM.lean).

Design (PROGRESS D-039 C1): the window's steps are indexed by the subtype of `Finset.Ico a b`
(no index shifting); new file. Every theorem is followed by its D-014 example.
-/
import GeneralizedC.GaugeM

open Matrix WithLp NNReal

namespace GeneralizedC

/-- The steps of the window `[a, b)` of a sampled series, as vectors of `ℝ³`. -/
def windowSteps (x : ℤ → State) (a b : ℤ) : {k // k ∈ Finset.Ico a b} → Fin 3 → ℝ :=
  fun k => ofLp (x (k.1 + 1) - x k.1)

/-- The window `[a, b)` has `(b − a).toNat` steps. -/
theorem card_windowSteps (a b : ℤ) : Fintype.card {k // k ∈ Finset.Ico a b} = (b - a).toNat := by
  simp [Fintype.card_coe, Int.card_Ico]

theorem nonempty_window {a b : ℤ} (hab : a < b) : Nonempty {k // k ∈ Finset.Ico a b} :=
  ⟨⟨a, Finset.mem_Ico.2 ⟨le_rfl, hab⟩⟩⟩

/-- **N1e (i).** With the window's own unit of change, `c° ≥ √3`, i.e. `c̃ ≥ 1`. -/
theorem sqrt_three_le_tickCritSpeed {L : Matrix (Fin 3) (Fin 3) ℝ} {x : ℤ → State} {a b : ℤ}
    (hab : a < b) (hM : IsUnit (secondMoment (windowSteps x a b)).det)
    (hL : Lᵀ * L = (secondMoment (windowSteps x a b))⁻¹) :
    √3 ≤ (tickCritSpeed L x a b : ℝ) := by
  have := nonempty_window hab
  obtain ⟨k, hk⟩ := exists_le_mahal (windowSteps x a b) hM
  have hk' := Finset.mem_Ico.1 k.2
  calc √3 ≤ √(mahal (secondMoment (windowSteps x a b)) (windowSteps x a b k)) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hk)
    _ ≤ _ := mahal_le_tickCritSpeed hL x hk'.1 hk'.2

/-- **N1e (ii).** If `c° = √3` (so `c̃ = 1`), every step of the window has squared length exactly
3: the light-ray case, every step on the cone. -/
theorem mahal_eq_three_of_tickCritSpeed_eq {L : Matrix (Fin 3) (Fin 3) ℝ} {x : ℤ → State}
    {a b : ℤ} (hab : a < b) (hM : IsUnit (secondMoment (windowSteps x a b)).det)
    (hL : Lᵀ * L = (secondMoment (windowSteps x a b))⁻¹)
    (h : (tickCritSpeed L x a b : ℝ) = √3) :
    ∀ k ∈ Finset.Ico a b, mahal (secondMoment (windowSteps x a b)) (ofLp (x (k + 1) - x k)) = 3 := by
  have := nonempty_window hab
  have hle : ∀ k, mahal (secondMoment (windowSteps x a b)) (windowSteps x a b k) ≤ (3 : ℕ) := by
    intro k
    have hk' := Finset.mem_Ico.1 k.2
    have := mahal_le_tickCritSpeed hL x hk'.1 hk'.2
    rw [h] at this
    have := (Real.sqrt_le_sqrt_iff (by norm_num)).1 this
    exact_mod_cast this
  intro k hk
  have := mahal_eq_of_le (windowSteps x a b) hM hle ⟨k, hk⟩
  exact_mod_cast this

/-- **N1e (iii).** `c° ≤ √N` with `N = b − a` steps, i.e. `c̃ ≤ √(N/3)` (N1d on the window). -/
theorem tickCritSpeed_le_sqrt_card {L : Matrix (Fin 3) (Fin 3) ℝ} {x : ℤ → State} {a b : ℤ}
    (hab : a < b) (hM : IsUnit (secondMoment (windowSteps x a b)).det)
    (hL : Lᵀ * L = (secondMoment (windowSteps x a b))⁻¹) :
    (tickCritSpeed L x a b : ℝ) ≤ √((b - a : ℤ) : ℝ) := by
  obtain ⟨k, hak, hkb, hk⟩ := exists_mahal_eq_tickCritSpeed hL x hab
  rw [← hk]
  apply Real.sqrt_le_sqrt
  have h := mahal_secondMoment_le_card (windowSteps x a b) hM ⟨k, Finset.mem_Ico.2 ⟨hak, hkb⟩⟩
  rw [card_windowSteps] at h
  have e : (((b - a).toNat : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  calc _ ≤ ((b - a).toNat : ℝ) := h
    _ = ((b - a : ℤ) : ℝ) := by rw [← e]; norm_cast

/-! ### D-014: a concrete window in the light-ray case -/

/-- The walk `0 → e₁ → 0 → e₂ → 0 → e₃ → 0` (positions at `k = 0, …, 6`): its six steps are
`e₁, −e₁, e₂, −e₂, e₃, −e₃`. -/
noncomputable def pmWalk : ℤ → State :=
  fun k => toLp 2 fun i : Fin 3 => if k = 2 * (i : ℤ) + 1 then (1 : ℝ) else 0

/-- The window `[0, 6)` indexed by `Fin 6`. -/
def icoFin6 : {k // k ∈ Finset.Ico (0 : ℤ) 6} ≃ Fin 6 where
  toFun k := ⟨k.1.toNat, by have := Finset.mem_Ico.1 k.2; omega⟩
  invFun j := ⟨(j.1 : ℤ), Finset.mem_Ico.2 ⟨by omega, by have := j.2; omega⟩⟩
  left_inv k := by
    have := Finset.mem_Ico.1 k.2
    ext
    simp only
    omega
  right_inv j := by ext; simp

theorem windowSteps_pmWalk : windowSteps pmWalk 0 6 = pmBasis ∘ icoFin6 := by
  funext ⟨k, hk⟩
  have hk' := Finset.mem_Ico.1 hk
  obtain ⟨h0, h6⟩ := hk'
  interval_cases k <;> ext i <;> fin_cases i <;>
    simp [windowSteps, pmWalk, pmBasis, icoFin6]

theorem secondMoment_pmWalk : secondMoment (windowSteps pmWalk 0 6) = secondMoment pmBasis := by
  rw [windowSteps_pmWalk, secondMoment_comp_equiv]

/-- `L = √3 · I` factors the walk's `M⁻¹ = 3 I`. -/
theorem sqrt_three_factor :
    (√3 • (1 : Matrix (Fin 3) (Fin 3) ℝ))ᵀ * (√3 • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      = (secondMoment (windowSteps pmWalk 0 6))⁻¹ := by
  rw [secondMoment_pmWalk, inv_secondMoment_pmBasis, transpose_smul, transpose_one,
    smul_mul_smul_comm, Matrix.one_mul, Real.mul_self_sqrt (by norm_num)]

theorem isUnit_det_pmWalk : IsUnit (secondMoment (windowSteps pmWalk 0 6)).det := by
  rw [secondMoment_pmWalk]; exact isUnit_det_pmBasis

/-- D-014 for N1e (i) and (iii): the walk's window has `√3 ≤ c° ≤ √6`. -/
example : √3 ≤ (tickCritSpeed (√3 • 1) pmWalk 0 6 : ℝ) ∧
    (tickCritSpeed (√3 • 1) pmWalk 0 6 : ℝ) ≤ √((6 - 0 : ℤ) : ℝ) :=
  ⟨sqrt_three_le_tickCritSpeed (by norm_num) isUnit_det_pmWalk sqrt_three_factor,
    tickCritSpeed_le_sqrt_card (by norm_num) isUnit_det_pmWalk sqrt_three_factor⟩

/-- D-014 for N1e (ii): the walk attains the lower edge, `c° = √3` (`c̃ = 1`): every step is
equally long in the window's own unit of change. -/
theorem tickCritSpeed_pmWalk : (tickCritSpeed (√3 • 1) pmWalk 0 6 : ℝ) = √3 := by
  obtain ⟨k, hak, hkb, hk⟩ := exists_mahal_eq_tickCritSpeed sqrt_three_factor pmWalk
    (by norm_num : (0 : ℤ) < 6)
  rw [← hk]
  have : ofLp (pmWalk (k + 1) - pmWalk k)
      = windowSteps pmWalk 0 6 ⟨k, Finset.mem_Ico.2 ⟨hak, hkb⟩⟩ := rfl
  rw [this, windowSteps_pmWalk, Function.comp_apply, secondMoment_comp_equiv, mahal_pmBasis]

example : ∀ k ∈ Finset.Ico (0 : ℤ) 6,
    mahal (secondMoment (windowSteps pmWalk 0 6)) (ofLp (pmWalk (k + 1) - pmWalk k)) = 3 :=
  mahal_eq_three_of_tickCritSpeed_eq (by norm_num) isUnit_det_pmWalk sqrt_three_factor
    tickCritSpeed_pmWalk

end GeneralizedC
