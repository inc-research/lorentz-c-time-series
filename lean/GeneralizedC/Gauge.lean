/-
GeneralizedC/Gauge.lean: the (c, G) gauge and the reduction to G = I (T9, T9d), diagonal G.

  minkowskiQG                          Q_{c,G}(Δt, Δx) = c²Δt² − Σᵢ gᵢ Δxᵢ²,  G = diag(g₀, g₁, g₂)
  T9a  minkowskiQG_gauge               Q_{c, λ²G} = λ² · Q_{c/λ, G}
  T9b  minkowskiQ_one_gaugeD           Q_{c,G} = Q_{1,I} ∘ D,  D(Δt, Δx) = (cΔt, G^{1/2}Δx)
  T9c  mem_lorentzGroupG_iff           Λ preserves Q_{c,G} ⇔ DΛD⁻¹ preserves Q_{1,I}
                                       (O_G(1,3; c) = D⁻¹ O(1,3) D)
  T9d  allChordsTimelikeG_iff, allChordsCausalG_iff
                                       (c,G)-timelike/causal chords of x ⇔ c-timelike/causal
                                       chords of G^{1/2} x   (what D-003 needs)

Design (PROGRESS D-017, cp3_breakdown T9): diagonal G with positive entries; groups as
form-preserving linear equivalences (a `Subgroup` of the automorphism group), not matrices.
-/
import GeneralizedC.SpeedBounds
import GeneralizedC.Signature

namespace GeneralizedC

/-- `Q_{c,G}` for a diagonal state metric `G = diag(g₀, g₁, g₂)`. -/
noncomputable def minkowskiQG (c : ℝ) (g : Fin 3 → ℝ) (p : ℝ × State) : ℝ :=
  c ^ 2 * p.1 ^ 2 - ∑ i, g i * p.2 i ^ 2

/-- With `G = I` this is the form of T1–T8. -/
theorem minkowskiQG_one (c : ℝ) (p : ℝ × State) :
    minkowskiQG c (fun _ => 1) p = minkowskiQ c p := by
  simp only [minkowskiQG, minkowskiQ, norm_sq_state, Fin.sum_univ_three, one_mul]

/-- **T9a (gauge).** Scaling the state metric by `λ²` is the same as dividing `c` by `λ`
(and multiplying the form by `λ² > 0`, which keeps every cone): `Q_{c, λ²G} = λ² Q_{c/λ, G}`. -/
theorem minkowskiQG_gauge {lam : ℝ} (hlam : lam ≠ 0) (c : ℝ) (g : Fin 3 → ℝ) (p : ℝ × State) :
    minkowskiQG c (fun i => lam ^ 2 * g i) p = lam ^ 2 * minkowskiQG (c / lam) g p := by
  simp only [minkowskiQG, mul_sub, Finset.mul_sum]
  congr 1
  · field_simp
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- D-014 for T9a: `λ = 2`, `c = 1`, `G = I`. -/
example (p : ℝ × State) :
    minkowskiQG 1 (fun _ => 2 ^ 2 * 1) p = 2 ^ 2 * minkowskiQG (1 / 2) (fun _ => 1) p :=
  minkowskiQG_gauge two_ne_zero 1 _ p

/-- Coordinatewise scaling of the state space by non-zero factors `aᵢ`, as a linear
equivalence (a change of unit for each component). -/
noncomputable def stateScale (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) : State ≃ₗ[ℝ] State where
  toFun x := WithLp.toLp 2 (fun i => a i * x i)
  invFun x := WithLp.toLp 2 (fun i => x i / a i)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' r x := by ext i; simp [mul_left_comm]
  left_inv x := by ext i; exact mul_div_cancel_left₀ _ (ha i)
  right_inv x := by ext i; have := ha i; simp; field_simp

@[simp] theorem stateScale_apply (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) (x : State) (i : Fin 3) :
    stateScale a ha x i = a i * x i :=
  rfl

/-- `G^{1/2} = diag(√g₀, √g₁, √g₂)` for positive weights. -/
noncomputable def sqrtG (g : Fin 3 → ℝ) (hg : ∀ i, 0 < g i) : State ≃ₗ[ℝ] State :=
  stateScale (fun i => √(g i)) fun i => (Real.sqrt_pos.mpr (hg i)).ne'

/-- The core identity: `Q_{c,G}(Δt, Δx) = Q_c(Δt, G^{1/2}Δx)`. -/
theorem minkowskiQG_eq (c : ℝ) {g : Fin 3 → ℝ} (hg : ∀ i, 0 < g i) (p : ℝ × State) :
    minkowskiQG c g p = minkowskiQ c (p.1, sqrtG g hg p.2) := by
  simp only [minkowskiQG, minkowskiQ, norm_sq_state, sqrtG, stateScale_apply, mul_pow,
    Real.sq_sqrt (hg _).le, Fin.sum_univ_three]

/-- The gauge map `D(Δt, Δx) = (cΔt, G^{1/2}Δx)`, invertible for `c ≠ 0`, `G ≻ 0`. -/
noncomputable def gaugeD {c : ℝ} (hc : c ≠ 0) (g : Fin 3 → ℝ) (hg : ∀ i, 0 < g i) :
    (ℝ × State) ≃ₗ[ℝ] (ℝ × State) :=
  (LinearEquiv.smulOfNeZero ℝ ℝ c hc).prodCongr (sqrtG g hg)

/-- **T9b (factorization).** `Q_{1,I}(D p) = Q_{c,G}(p)`. -/
theorem minkowskiQ_one_gaugeD {c : ℝ} (hc : c ≠ 0) {g : Fin 3 → ℝ} (hg : ∀ i, 0 < g i)
    (p : ℝ × State) : minkowskiQ 1 (gaugeD hc g hg p) = minkowskiQG c g p := by
  rw [minkowskiQG_eq c hg]
  simp only [gaugeD, LinearEquiv.prodCongr_apply, LinearEquiv.smulOfNeZero_apply, smul_eq_mul,
    minkowskiQ]
  ring

/-- D-014 for T9b: `c = 1`, `G = diag(4, 4, 4)`. -/
example (p : ℝ × State) :
    minkowskiQ 1 (gaugeD one_ne_zero (fun _ => 4) (fun _ => by norm_num) p)
      = minkowskiQG 1 (fun _ => 4) p :=
  minkowskiQ_one_gaugeD one_ne_zero _ p

/-- The group of linear equivalences of `ℝ × State` preserving a form `Q`. -/
def formGroup (Q : ℝ × State → ℝ) : Subgroup ((ℝ × State) ≃ₗ[ℝ] (ℝ × State)) where
  carrier := {Λ | ∀ p, Q (Λ p) = Q p}
  one_mem' _ := rfl
  mul_mem' {Λ M} hΛ hM p := by
    show Q (Λ (M p)) = Q p
    rw [hΛ, hM]
  inv_mem' {Λ} hΛ p := by
    show Q (Λ.symm p) = Q p
    rw [← hΛ (Λ.symm p), LinearEquiv.apply_symm_apply]

/-- The Lorentz group `O(1,3)`, in units `c = 1`, `G = I`. -/
noncomputable def lorentzGroup : Subgroup ((ℝ × State) ≃ₗ[ℝ] (ℝ × State)) := formGroup (minkowskiQ 1)

/-- The generalized Lorentz group `O_G(1,3; c)`. -/
noncomputable def lorentzGroupG (c : ℝ) (g : Fin 3 → ℝ) : Subgroup ((ℝ × State) ≃ₗ[ℝ] (ℝ × State)) :=
  formGroup (minkowskiQG c g)

/-- **T9c (groups).** For `c ≠ 0`, `G ≻ 0`: `Λ ∈ O_G(1,3; c) ⇔ DΛD⁻¹ ∈ O(1,3)`.
No new group appears: the generalized group is the Lorentz group seen through the units `D`. -/
theorem mem_lorentzGroupG_iff {c : ℝ} (hc : c ≠ 0) {g : Fin 3 → ℝ} (hg : ∀ i, 0 < g i)
    (Λ : (ℝ × State) ≃ₗ[ℝ] (ℝ × State)) :
    Λ ∈ lorentzGroupG c g ↔ gaugeD hc g hg * Λ * (gaugeD hc g hg)⁻¹ ∈ lorentzGroup := by
  set D := gaugeD hc g hg
  constructor
  · intro h q
    show minkowskiQ 1 (D (Λ (D.symm q))) = minkowskiQ 1 q
    rw [minkowskiQ_one_gaugeD, h, ← minkowskiQ_one_gaugeD hc hg, LinearEquiv.apply_symm_apply]
  · intro h p
    have := h (D p)
    change minkowskiQ 1 (D (Λ (D.symm (D p)))) = minkowskiQ 1 (D p) at this
    rwa [LinearEquiv.symm_apply_apply, minkowskiQ_one_gaugeD, minkowskiQ_one_gaugeD] at this

/-- Point reflection `p ↦ −p` preserves every `Q_{c,G}`. -/
theorem neg_mem_lorentzGroupG (c : ℝ) (g : Fin 3 → ℝ) :
    LinearEquiv.neg ℝ ∈ lorentzGroupG c g := by
  intro p
  simp [minkowskiQG]

/-- D-014 for T9c: with `c = 1`, `G = diag(4, 4, 4)`, the reflection `−1` is in
`O_G(1,3; 1)`, so T9c puts `D(−1)D⁻¹` in `O(1,3)`. -/
example : gaugeD one_ne_zero (fun _ => (4 : ℝ)) (fun _ => by norm_num) * LinearEquiv.neg ℝ *
    (gaugeD one_ne_zero (fun _ => (4 : ℝ)) (fun _ => by norm_num))⁻¹ ∈ lorentzGroup :=
  (mem_lorentzGroupG_iff one_ne_zero _ _).1 (neg_mem_lorentzGroupG 1 _)

/-! ### T9d: transport of chord conditions -/

/-- `(c, G)`-timelike displacement. -/
def IsTimelikeG (c : ℝ) (g : Fin 3 → ℝ) (p : ℝ × State) : Prop := 0 < minkowskiQG c g p

/-- `(c, G)`-causal displacement. -/
def IsCausalG (c : ℝ) (g : Fin 3 → ℝ) (p : ℝ × State) : Prop := 0 ≤ minkowskiQG c g p

def AllChordsTimelikeG (c : ℝ) (g : Fin 3 → ℝ) (x : ℝ → State) : Prop :=
  ∀ s t, s ≠ t → IsTimelikeG c g (chord x s t)

def AllChordsCausalG (c : ℝ) (g : Fin 3 → ℝ) (x : ℝ → State) : Prop :=
  ∀ s t, s ≠ t → IsCausalG c g (chord x s t)

/-- A chord of `x` measured with `G` is the chord of `G^{1/2} x` measured with `I`. -/
theorem minkowskiQG_chord (c : ℝ) {g : Fin 3 → ℝ} (hg : ∀ i, 0 < g i) (x : ℝ → State)
    (s t : ℝ) :
    minkowskiQG c g (chord x s t) = minkowskiQ c (chord (fun t => sqrtG g hg (x t)) s t) := by
  rw [minkowskiQG_eq c hg]
  simp only [chord, map_sub]

/-- **T9d (timelike).** Every chord of `x` is `(c, G)`-timelike ⇔ every chord of `G^{1/2} x`
is `c`-timelike. So every theorem proved for `G = I` applies to `G`-data via `G^{1/2} x`. -/
theorem allChordsTimelikeG_iff (c : ℝ) {g : Fin 3 → ℝ} (hg : ∀ i, 0 < g i) (x : ℝ → State) :
    AllChordsTimelikeG c g x ↔ AllChordsTimelike c (fun t => sqrtG g hg (x t)) := by
  simp only [AllChordsTimelikeG, IsTimelikeG, AllChordsTimelike, IsTimelike,
    minkowskiQG_chord c hg]

/-- **T9d (causal).** The same for causal chords (D-015). -/
theorem allChordsCausalG_iff (c : ℝ) {g : Fin 3 → ℝ} (hg : ∀ i, 0 < g i) (x : ℝ → State) :
    AllChordsCausalG c g x ↔ AllChordsCausal c (fun t => sqrtG g hg (x t)) := by
  simp only [AllChordsCausalG, IsCausalG, AllChordsCausal, IsCausal, minkowskiQG_chord c hg]

/-- D-014 for T9d: in units `G = diag(4, 4, 4)`, uniform motion with velocity `v` is causal
at `c = ‖G^{1/2} v‖` (= 2‖v‖), transported from the `G = I` fact for velocity `G^{1/2} v`. -/
example (v : State) :
    AllChordsCausalG ‖sqrtG (fun _ => 4) (fun _ => by norm_num) v‖ (fun _ => 4)
      (uniformMotion v) := by
  rw [allChordsCausalG_iff _ (fun _ => by norm_num)]
  have : (fun t => sqrtG (fun _ => (4 : ℝ)) (fun _ => by norm_num) (uniformMotion v t))
      = uniformMotion (sqrtG (fun _ => 4) (fun _ => by norm_num) v) := by
    funext t
    simp only [uniformMotion, map_smul]
  rw [this]
  exact allChordsCausal_uniformMotion _

/-- D-014 for T9d (timelike): a constant path, `c = 1`, `G = diag(4, 4, 4)`. -/
example (p : State) : AllChordsTimelikeG 1 (fun _ => 4) (fun _ => p) :=
  (allChordsTimelikeG_iff 1 (fun _ => by norm_num) _).2
    (allChordsTimelike_of_lipschitzWith (L := 0) zero_lt_one (LipschitzWith.const _))

end GeneralizedC
