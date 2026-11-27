/-
GeneralizedC/GaugeM.lean: general positive-definite G, and the bridge from c° to E1 (CP5: N1b).

  minkowskiQM c G                  Q_{c,G}(Δt, Δx) = c²Δt² − Δxᵀ G Δx   (any 3×3 matrix G)
  N1b-i   minkowskiQM_eq           Lᵀ L = G ⇒ Q_{c,G}(Δt, Δx) = Q_c(Δt, LΔx)
          minkowskiQM_diagonal     G = diag g gives T9's minkowskiQG
          allChordsCausalM_iff, allChordsTimelikeM_iff, minkowskiQM_tableChord
                                   (c,G) chords of x ⇔ c chords of Lx  (T9d, general G)
  N1b-ii  mem_formGroupM_iff       Λ ∈ O_G(1,3; c) ⇔ (1 ⊕ L) Λ (1 ⊕ L)⁻¹ ∈ O(1,3; c)   (T9c, general)
  N1b-iii exists_factor_of_posDef  G positive definite ⇒ some L with Lᵀ L = G, det L ≠ 0  (L = √G)
  N1b-iv  slope_tick_eq_mahal      Lᵀ L = M⁻¹ ⇒ slope of step k of the table (j, L xⱼ) = ‖Δxₖ‖_{M⁻¹}
          tickCritSpeed            c° of one window = critSpeedOn over lagPairs 1 a b (D-034 C6)

Design (PROGRESS D-034 C5, C6; cp5_breakdown N1b): hypothesis form (any L with Lᵀ L = G) for
i, ii, iv; existence of L separately (iii). Matrices act on `State` through
`Matrix.toEuclideanLin`. Every theorem is followed by its D-014 example.
-/
import GeneralizedC.Invariance
import GeneralizedC.Change
import Mathlib.Analysis.Matrix.Order

open Matrix WithLp NNReal

namespace GeneralizedC

/-! ### Matrices acting on `State` -/

/-- A 3×3 matrix as a linear map of the state space. -/
noncomputable abbrev matState (L : Matrix (Fin 3) (Fin 3) ℝ) : State →ₗ[ℝ] State :=
  Matrix.toEuclideanLin L

theorem ofLp_matState (L : Matrix (Fin 3) (Fin 3) ℝ) (v : State) :
    ofLp (matState L v) = L *ᵥ ofLp v :=
  rfl

/-- `‖w‖² = w ⬝ w` on the state space. -/
theorem norm_sq_eq_dotProduct (w : State) : ‖w‖ ^ 2 = ofLp w ⬝ᵥ ofLp w := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- `‖Lv‖² = vᵀ (Lᵀ L) v`. The only bridge needed between matrices and `State`. -/
theorem norm_sq_matState (L : Matrix (Fin 3) (Fin 3) ℝ) (v : State) :
    ‖matState L v‖ ^ 2 = ofLp v ⬝ᵥ ((Lᵀ * L) *ᵥ ofLp v) := by
  rw [norm_sq_eq_dotProduct, ofLp_matState, ← mulVec_mulVec, dotProduct_mulVec (ofLp v) Lᵀ,
    vecMul_transpose]

/-! ### N1b-i: transport -/

/-- `Q_{c,G}(Δt, Δx) = c²Δt² − Δxᵀ G Δx` for any 3×3 matrix `G`. -/
noncomputable def minkowskiQM (c : ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × State) : ℝ :=
  c ^ 2 * p.1 ^ 2 - ofLp p.2 ⬝ᵥ (G *ᵥ ofLp p.2)

/-- **N1b-i.** If `Lᵀ L = G`, then `Q_{c,G}(Δt, Δx) = Q_c(Δt, LΔx)`. -/
theorem minkowskiQM_eq {L G : Matrix (Fin 3) (Fin 3) ℝ} (hLG : Lᵀ * L = G) (c : ℝ)
    (p : ℝ × State) : minkowskiQM c G p = minkowskiQ c (p.1, matState L p.2) := by
  simp only [minkowskiQM, minkowskiQ, norm_sq_matState, hLG]

/-- The diagonal case is T9's form: `Q_{c, diag g} = minkowskiQG c g`. -/
theorem minkowskiQM_diagonal (c : ℝ) (g : Fin 3 → ℝ) (p : ℝ × State) :
    minkowskiQM c (diagonal g) p = minkowskiQG c g p := by
  simp only [minkowskiQM, minkowskiQG, mulVec_diagonal, dotProduct, Fin.sum_univ_three]
  ring

/-- D-014 for N1b-i: `L = 1`, `G = 1` gives back `Q_c`. -/
example (c : ℝ) (p : ℝ × State) : minkowskiQM c 1 p = minkowskiQ c (p.1, matState 1 p.2) :=
  minkowskiQM_eq (by simp) c p

/-- `(c, G)`-causal displacement, general `G`. -/
def IsCausalM (c : ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × State) : Prop :=
  0 ≤ minkowskiQM c G p

/-- `(c, G)`-timelike displacement, general `G`. -/
def IsTimelikeM (c : ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ × State) : Prop :=
  0 < minkowskiQM c G p

def AllChordsCausalM (c : ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ → State) : Prop :=
  ∀ s t, s ≠ t → IsCausalM c G (chord x s t)

def AllChordsTimelikeM (c : ℝ) (G : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ → State) : Prop :=
  ∀ s t, s ≠ t → IsTimelikeM c G (chord x s t)

/-- A chord of `x` measured with `G` is the chord of `Lx` measured with `I`. -/
theorem minkowskiQM_chord {L G : Matrix (Fin 3) (Fin 3) ℝ} (hLG : Lᵀ * L = G) (c : ℝ)
    (x : ℝ → State) (s t : ℝ) :
    minkowskiQM c G (chord x s t) = minkowskiQ c (chord (fun t => matState L (x t)) s t) := by
  rw [minkowskiQM_eq hLG]
  simp only [chord, map_sub]

/-- The same for a chord of a table. -/
theorem minkowskiQM_tableChord {ι : Type*} {L G : Matrix (Fin 3) (Fin 3) ℝ} (hLG : Lᵀ * L = G)
    (c : ℝ) (t : ι → ℝ) (x : ι → State) (i j : ι) :
    minkowskiQM c G (tableChord t x i j)
      = minkowskiQ c (tableChord t (fun k => matState L (x k)) i j) := by
  rw [minkowskiQM_eq hLG]
  simp only [tableChord, map_sub]

/-- **N1b-i (causal).** Every chord of `x` is `(c, G)`-causal ⇔ every chord of `Lx` is
`c`-causal (T9d for any `G = Lᵀ L`). -/
theorem allChordsCausalM_iff {L G : Matrix (Fin 3) (Fin 3) ℝ} (hLG : Lᵀ * L = G) (c : ℝ)
    (x : ℝ → State) :
    AllChordsCausalM c G x ↔ AllChordsCausal c (fun t => matState L (x t)) := by
  simp only [AllChordsCausalM, IsCausalM, AllChordsCausal, IsCausal, minkowskiQM_chord hLG]

/-- **N1b-i (timelike).** -/
theorem allChordsTimelikeM_iff {L G : Matrix (Fin 3) (Fin 3) ℝ} (hLG : Lᵀ * L = G) (c : ℝ)
    (x : ℝ → State) :
    AllChordsTimelikeM c G x ↔ AllChordsTimelike c (fun t => matState L (x t)) := by
  simp only [AllChordsTimelikeM, IsTimelikeM, AllChordsTimelike, IsTimelike,
    minkowskiQM_chord hLG]

/-- D-014 for N1b-i: with `G = 1` (`L = 1`), uniform motion is `(‖v‖, 1)`-causal. -/
example (v : State) : AllChordsCausalM ‖v‖ 1 (uniformMotion v) := by
  rw [allChordsCausalM_iff (L := 1) (by simp)]
  simpa using allChordsCausal_uniformMotion v

/-! ### N1b-ii: the group -/

/-- `L` as a linear equivalence of the state space, for `det L` a unit. -/
noncomputable def matStateEquiv {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) :
    State ≃ₗ[ℝ] State :=
  LinearEquiv.ofLinearMap (matState L) (matState L⁻¹)
    (LinearMap.ext fun v => by
      simp [matState, Matrix.toLpLin_apply, mulVec_mulVec, mul_nonsing_inv _ hL])
    (LinearMap.ext fun v => by
      simp [matState, Matrix.toLpLin_apply, mulVec_mulVec, nonsing_inv_mul _ hL])

/-- The gauge map `1 ⊕ L` on events. -/
noncomputable def gaugeL {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) :
    (ℝ × State) ≃ₗ[ℝ] (ℝ × State) :=
  (LinearEquiv.refl ℝ ℝ).prodCongr (matStateEquiv hL)

/-- **N1b-ii.** If `Lᵀ L = G` and `det L` is a unit: `Λ ∈ O_G(1,3; c)` ⇔
`(1 ⊕ L) Λ (1 ⊕ L)⁻¹ ∈ O(1,3; c)`. No new group appears for a non-diagonal `G` either. -/
theorem mem_formGroupM_iff {L G : Matrix (Fin 3) (Fin 3) ℝ} (hLG : Lᵀ * L = G)
    (hL : IsUnit L.det) (c : ℝ) (Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)) :
    Λ ∈ formGroup (minkowskiQM c G) ↔
      gaugeL hL * Λ * (gaugeL hL)⁻¹ ∈ formGroup (minkowskiQ c) := by
  set E := gaugeL hL
  have hE : ∀ p, minkowskiQ c (E p) = minkowskiQM c G p := fun p =>
    (minkowskiQM_eq hLG c p).symm
  constructor
  · intro h q
    show minkowskiQ c (E (Λ (E.symm q))) = minkowskiQ c q
    rw [hE, formGroup_apply h, ← hE, LinearEquiv.apply_symm_apply]
  · intro h p
    have := h (E p)
    change minkowskiQ c (E (Λ (E.symm (E p)))) = minkowskiQ c (E p) at this
    rwa [LinearEquiv.symm_apply_apply, hE, hE] at this

/-- D-014 for N1b-ii: `Λ = −I` preserves every `Q_{c,G}`, so it lands in `O(1,3; c)` after the
gauge map, here with `L = 1`. -/
example (c : ℝ) :
    gaugeL (L := 1) (by simp) * LinearEquiv.neg ℝ * (gaugeL (L := 1) (by simp))⁻¹
      ∈ formGroup (minkowskiQ c) :=
  (mem_formGroupM_iff (G := 1) (by simp) _ c _).1 fun p => by simp [minkowskiQM]

/-! ### N1b-iii: existence of `L` -/

open scoped MatrixOrder in
/-- **N1b-iii.** Every positive-definite `G` factors as `Lᵀ L` with `det L ≠ 0`: take the
positive square root `L = √G` (continuous functional calculus). -/
theorem exists_factor_of_posDef {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.PosDef) :
    ∃ L : Matrix (Fin 3) (Fin 3) ℝ, Lᵀ * L = G ∧ IsUnit L.det := by
  have h0 : 0 ≤ G := hG.posSemidef.nonneg
  refine ⟨CFC.sqrt G, ?_, ?_⟩
  · have hs : star (CFC.sqrt G) = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hs
    rw [hs, CFC.sqrt_mul_sqrt_self G h0]
  · rw [hG.posSemidef.det_sqrt, RCLike.sqrt_real, isUnit_iff_ne_zero]
    exact (Real.sqrt_pos.2 hG.det_pos).ne'

/-- D-014 for N1b-iii: the identity is positive definite. -/
example : ∃ L : Matrix (Fin 3) (Fin 3) ℝ, Lᵀ * L = 1 ∧ IsUnit L.det :=
  exists_factor_of_posDef PosDef.one

/-! ### N1b-iv: the bridge to E1 -/

/-- **N1b-iv.** With tick time `τⱼ = j` and `Lᵀ L = M⁻¹`, the slope of step `k` of the
transported table `(j, L xⱼ)` is the Mahalanobis length `‖Δxₖ‖_{M⁻¹}` of the step. -/
theorem slope_tick_eq_mahal {L M : Matrix (Fin 3) (Fin 3) ℝ} (hL : Lᵀ * L = M⁻¹)
    (x : ℤ → State) (k : ℤ) :
    (slope (fun j : ℤ => (j : ℝ)) (fun j => matState L (x j)) k (k + 1) : ℝ)
      = √(mahal M (ofLp (x (k + 1) - x k))) := by
  rw [coe_slope, ← map_sub]
  have h1 : ((k + 1 : ℤ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
  rw [h1, abs_one, div_one, ← Real.sqrt_sq (norm_nonneg _), norm_sq_matState, hL]
  rfl

/-- The observer's `c°` for one window `[a, b]` of tick time: the critical speed of the
transported table `(j, L xⱼ)` over its steps (D-034 C6). With `Lᵀ L = M⁻¹` it is
`maxₖ ‖Δxₖ‖_{M⁻¹}` (below), and `c̃ = c° / √n`. -/
noncomputable def tickCritSpeed (L : Matrix (Fin 3) (Fin 3) ℝ) (x : ℤ → State) (a b : ℤ) : ℝ≥0 :=
  critSpeedOn (fun j : ℤ => (j : ℝ)) (fun j => matState L (x j)) (lagPairs 1 a b)

/-- Every step of the window has Mahalanobis length `≤ c°` (E1a). -/
theorem mahal_le_tickCritSpeed {L M : Matrix (Fin 3) (Fin 3) ℝ} (hL : Lᵀ * L = M⁻¹)
    (x : ℤ → State) {a b k : ℤ} (hak : a ≤ k) (hkb : k < b) :
    √(mahal M (ofLp (x (k + 1) - x k))) ≤ tickCritSpeed L x a b := by
  rw [← slope_tick_eq_mahal hL]
  exact NNReal.coe_le_coe.2
    (slope_le_critSpeedOn _ _ (p := (k, k + 1)) (mem_lagPairs.2 ⟨hak, by omega, rfl⟩))

/-- Some step of a non-empty window has Mahalanobis length exactly `c°` (E1c): `c°` is the
maximum `maxₖ ‖Δxₖ‖_{M⁻¹}`, attained, and that step is lightlike. -/
theorem exists_mahal_eq_tickCritSpeed {L M : Matrix (Fin 3) (Fin 3) ℝ} (hL : Lᵀ * L = M⁻¹)
    (x : ℤ → State) {a b : ℤ} (hab : a < b) :
    ∃ k, a ≤ k ∧ k < b ∧ √(mahal M (ofLp (x (k + 1) - x k))) = tickCritSpeed L x a b := by
  have hne : (lagPairs 1 a b).Nonempty := ⟨(a, a + 1), mem_lagPairs.2 ⟨le_rfl, by omega, rfl⟩⟩
  obtain ⟨⟨k, l⟩, hp, hsl, -⟩ :=
    exists_isLightlike_critSpeedOn (Int.cast_injective (α := ℝ)) (fun j => matState L (x j)) hne
  obtain ⟨h1, h2, h3⟩ := mem_lagPairs.1 hp
  simp only at h1 h2 h3
  subst h3
  refine ⟨k, h1, by omega, ?_⟩
  rw [← slope_tick_eq_mahal hL]
  exact congrArg NNReal.toReal hsl

/-- T10 applies to `c°`: over the window, the largest step equals the largest chord. -/
theorem tickCritSpeed_eq_windowPairs (L : Matrix (Fin 3) (Fin 3) ℝ) (x : ℤ → State) (a b : ℤ) :
    tickCritSpeed L x a b
      = critSpeedOn (fun j : ℤ => (j : ℝ)) (fun j => matState L (x j)) (windowPairs a b) :=
  (critSpeedOn_windowPairs Int.cast_strictMono _ a b).symm

/-- D-014 for N1b-iv: `M = 1`, `L = 1` (unit change = the original units): every step's slope
is its length, and the window `[0, 1]` attains `c°`. -/
example (x : ℤ → State) (k : ℤ) :
    (slope (fun j : ℤ => (j : ℝ)) (fun j => matState 1 (x j)) k (k + 1) : ℝ)
      = √(mahal 1 (ofLp (x (k + 1) - x k))) :=
  slope_tick_eq_mahal (by simp) x k

example (x : ℤ → State) :
    ∃ k, 0 ≤ k ∧ k < 1 ∧ √(mahal 1 (ofLp (x (k + 1) - x k))) = tickCritSpeed 1 x 0 1 :=
  exists_mahal_eq_tickCritSpeed (by simp) x zero_lt_one

end GeneralizedC
