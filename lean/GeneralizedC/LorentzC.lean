/-
GeneralizedC/LorentzC.lean: the kinematic result as one Lean object (P1, D-049, D-050).

  stepMahal x a b k          squared length of step k in the window's own unit of change
  IsLorentzC x a b c         (i) the window's steps cover ℝ³; (ii) every step has √mahal ≤ c;
                             (iii) some step has √mahal = c                    (D-050 C2, no L inside)
  K1  isLorentzC_iff, existsUnique_isLorentzC
                             a < b and cover ⇒ exactly one c; it is c° = tickCritSpeed L x a b
                             for every L with Lᵀ L = M⁻¹
  K2  IsLorentzC.isCausalM_chord, IsLorentzC.exists_lightlike_step
                             every chord of the window is c-causal in the own unit; one step is lightlike
  K3  IsLorentzC.bounds      √3 ≤ c ≤ √N
  K4  isLorentzC_map         any invertible change of axis units leaves c unchanged
  K5  IsLorentzC.natural     after x ↦ Lx / c the window has c* = 1, and every Λ ∈ O(1,3) keeps it
  IsSystemLorentzC           decimations m ∈ S of one series, each with its window, one common c
                             (exact agreement only, D-050 C3)
  K6  helix_isSystemLorentzC the helix: c = √3 at every m with sin mω ≠ 0, over whole turns
  K7  helix_not_isLorentzC, not_isSystemLorentzC_of_aliased
                             planar (v = 0) or aliased (sin mω = 0): no Lorentz c at all

Spec: q016_breakdown.html §8 (P1). In words: any window of a tick-time record whose steps span ℝ³
has exactly one Lorentz c, its largest step measured in the record's own unit of change.
Every theorem is followed by its D-014 example.
-/
import GeneralizedC.Helix
import GeneralizedC.Normalize

open Matrix WithLp NNReal Real

namespace GeneralizedC

/-! ### The definition -/

/-- The squared length of step `k` of the window `[a, b)`, in the window's own unit of change
`M⁻¹`, with `M = secondMoment (windowSteps x a b)` (D-031 R2). -/
noncomputable def stepMahal (x : ℤ → State) (a b k : ℤ) : ℝ :=
  mahal (secondMoment (windowSteps x a b)) (ofLp (x (k + 1) - x k))

/-- **IsLorentzC.** `c` is a Lorentz c of the window `[a, b)` of the tick-time record `x`:
(i) the steps cover ℝ³ (the unit of change exists, N1c′); (ii) every step is at most `c` long in
that unit (c-causal); (iii) some step is exactly `c` long (lightlike). No factor `L` appears. -/
def IsLorentzC (x : ℤ → State) (a b : ℤ) (c : ℝ) : Prop :=
  Covers (windowSteps x a b) ∧
    (∀ k ∈ Finset.Ico a b, √(stepMahal x a b k) ≤ c) ∧
    ∃ k ∈ Finset.Ico a b, √(stepMahal x a b k) = c

variable {x : ℤ → State} {a b : ℤ} {c : ℝ}

theorem IsLorentzC.lt (h : IsLorentzC x a b c) : a < b := by
  obtain ⟨k, hk, -⟩ := h.2.2
  have := Finset.mem_Ico.1 hk
  omega

theorem IsLorentzC.nonneg (h : IsLorentzC x a b c) : 0 ≤ c := by
  obtain ⟨k, -, hk⟩ := h.2.2
  rw [← hk]
  exact Real.sqrt_nonneg _

/-- A Lorentz c is unique: it is the largest step. -/
theorem IsLorentzC.unique {c' : ℝ} (h : IsLorentzC x a b c) (h' : IsLorentzC x a b c') :
    c = c' := by
  obtain ⟨k, hk, hkc⟩ := h.2.2
  obtain ⟨k', hk', hkc'⟩ := h'.2.2
  exact le_antisymm (hkc ▸ h'.2.1 k hk) (hkc' ▸ h.2.1 k' hk')

theorem isUnit_det_of_covers (hcov : Covers (windowSteps x a b)) :
    IsUnit (secondMoment (windowSteps x a b)).det :=
  (isUnit_det_secondMoment_iff_covers _).2 hcov

/-- If the steps cover ℝ³, the window's `M⁻¹` has a factor `L` (N1c′, N1b-iii). -/
theorem exists_factor_window (hcov : Covers (windowSteps x a b)) :
    ∃ L : Matrix (Fin 3) (Fin 3) ℝ, Lᵀ * L = (secondMoment (windowSteps x a b))⁻¹ := by
  have hPD := ((secondMoment_posDef_iff_span _).2 ((covers_iff_span_eq_top _).1 hcov)).inv
  obtain ⟨L, hL, -⟩ := exists_factor_of_posDef hPD
  exact ⟨L, hL⟩

/-! ### K1: existence and uniqueness -/

/-- `c° = tickCritSpeed L x a b` is a Lorentz c whenever the window is non-empty and covers. -/
theorem isLorentzC_tickCritSpeed {L : Matrix (Fin 3) (Fin 3) ℝ} (hab : a < b)
    (hcov : Covers (windowSteps x a b)) (hL : Lᵀ * L = (secondMoment (windowSteps x a b))⁻¹) :
    IsLorentzC x a b (tickCritSpeed L x a b) := by
  refine ⟨hcov, fun k hk => ?_, ?_⟩
  · have hk' := Finset.mem_Ico.1 hk
    exact mahal_le_tickCritSpeed hL x hk'.1 hk'.2
  · obtain ⟨k, h1, h2, h3⟩ := exists_mahal_eq_tickCritSpeed hL x hab
    exact ⟨k, Finset.mem_Ico.2 ⟨h1, h2⟩, h3⟩

/-- **K1 (characterization).** For any `L` with `Lᵀ L = M⁻¹`: `c` is a Lorentz c of the window
⇔ the steps cover, the window is non-empty, and `c = c° = tickCritSpeed L x a b`. So `c°` does
not depend on the choice of `L`. -/
theorem isLorentzC_iff {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : Lᵀ * L = (secondMoment (windowSteps x a b))⁻¹) :
    IsLorentzC x a b c ↔
      Covers (windowSteps x a b) ∧ a < b ∧ c = tickCritSpeed L x a b := by
  constructor
  · intro h
    exact ⟨h.1, h.lt, h.unique (isLorentzC_tickCritSpeed h.lt h.1 hL)⟩
  · rintro ⟨hcov, hab, rfl⟩
    exact isLorentzC_tickCritSpeed hab hcov hL

/-- **K1 (existence and uniqueness).** A non-empty window whose steps cover ℝ³ has exactly one
Lorentz c. -/
theorem existsUnique_isLorentzC (hab : a < b) (hcov : Covers (windowSteps x a b)) :
    ∃! c, IsLorentzC x a b c := by
  obtain ⟨L, hL⟩ := exists_factor_window hcov
  exact ⟨_, isLorentzC_tickCritSpeed hab hcov hL, fun c' h' => h'.unique
    (isLorentzC_tickCritSpeed hab hcov hL)⟩

/-- The covering window of the walk `0 → e₁ → 0 → e₂ → 0 → e₃ → 0`. -/
theorem covers_pmWalk : Covers (windowSteps pmWalk 0 6) :=
  (isUnit_det_secondMoment_iff_covers _).1 isUnit_det_pmWalk

/-- D-014 for `IsLorentzC` and K1: the walk's Lorentz c is `√3`. -/
theorem isLorentzC_pmWalk : IsLorentzC pmWalk 0 6 √3 :=
  (isLorentzC_iff sqrt_three_factor).2 ⟨covers_pmWalk, by norm_num, tickCritSpeed_pmWalk.symm⟩

/-- D-014 for K1: the walk has exactly one Lorentz c. -/
example : ∃! c, IsLorentzC pmWalk 0 6 c :=
  existsUnique_isLorentzC (by norm_num) covers_pmWalk

/-! ### K2: every chord of the window is c-causal; one step is lightlike -/

/-- **K2.** If `c` is a Lorentz c of the window, every chord `(i, j)` of the window (any two
samples in `[a, b]`, not only steps) is `c`-causal in the window's own unit, measured with the
form `Q_{c, M⁻¹}(Δτ, Δx) = c²Δτ² − Δxᵀ M⁻¹ Δx` in tick time (T10). -/
theorem IsLorentzC.isCausalM_chord (h : IsLorentzC x a b c) {i j : ℤ} (hai : a ≤ i) (hib : i ≤ b)
    (haj : a ≤ j) (hjb : j ≤ b) :
    IsCausalM c (secondMoment (windowSteps x a b))⁻¹ (tableChord (fun k : ℤ => (k : ℝ)) x i j) := by
  obtain ⟨L, hL⟩ := exists_factor_window h.1
  have hc : c = tickCritSpeed L x a b := ((isLorentzC_iff hL).1 h).2.2
  unfold IsCausalM
  rw [minkowskiQM_tableChord hL]
  have hle : (critSpeedOn (fun k : ℤ => (k : ℝ)) (fun k => matState L (x k)) (windowPairs a b) : ℝ)
      ≤ c := by
    rw [← tickCritSpeed_eq_windowPairs, hc]
  have := (allCausalOn_iff h.nonneg (Int.cast_injective (α := ℝ)) _ (windowPairs a b)).2 hle (i, j)
    (by simp only [windowPairs, Finset.mem_product, Finset.mem_Icc]; exact ⟨⟨hai, hib⟩, haj, hjb⟩)
  exact this

/-- **K2 (lightlike step).** Some step of the window lies on the cone: `Q_{c, M⁻¹} = 0`. -/
theorem IsLorentzC.exists_lightlike_step (h : IsLorentzC x a b c) :
    ∃ k ∈ Finset.Ico a b,
      minkowskiQM c (secondMoment (windowSteps x a b))⁻¹
        (tableChord (fun k : ℤ => (k : ℝ)) x k (k + 1)) = 0 := by
  obtain ⟨L, hL⟩ := exists_factor_window h.1
  obtain ⟨k, hk, hkc⟩ := h.2.2
  refine ⟨k, hk, ?_⟩
  rw [minkowskiQM_tableChord hL]
  have hn : ‖matState L (x (k + 1)) - matState L (x k)‖ = c := by
    have := slope_tick_eq_mahal hL x k
    rw [coe_slope] at this
    have h1 : |((k + 1 : ℤ) : ℝ) - (k : ℝ)| = 1 := by push_cast; simp
    rw [h1, div_one] at this
    rw [this]
    exact hkc
  simp only [minkowskiQ, tableChord, hn]
  push_cast
  ring

/-- D-014 for K2: the walk's chord from `0` to `6` is `√3`-causal, and some step is lightlike. -/
example : IsCausalM √3 (secondMoment (windowSteps pmWalk 0 6))⁻¹
    (tableChord (fun k : ℤ => (k : ℝ)) pmWalk 0 6) :=
  isLorentzC_pmWalk.isCausalM_chord le_rfl (by norm_num) (by norm_num) le_rfl

example : ∃ k ∈ Finset.Ico (0 : ℤ) 6, minkowskiQM √3 (secondMoment (windowSteps pmWalk 0 6))⁻¹
    (tableChord (fun k : ℤ => (k : ℝ)) pmWalk k (k + 1)) = 0 :=
  isLorentzC_pmWalk.exists_lightlike_step

/-! ### K3: bounds -/

/-- **K3.** A Lorentz c lies between `√3` and `√N`, `N = b − a` (N1e). So `1 ≤ c̃ ≤ √(N/3)`. -/
theorem IsLorentzC.bounds (h : IsLorentzC x a b c) : √3 ≤ c ∧ c ≤ √((b - a : ℤ) : ℝ) := by
  obtain ⟨L, hL⟩ := exists_factor_window h.1
  have hc : c = tickCritSpeed L x a b := ((isLorentzC_iff hL).1 h).2.2
  have hM := isUnit_det_of_covers h.1
  rw [hc]
  exact ⟨sqrt_three_le_tickCritSpeed h.lt hM hL, tickCritSpeed_le_sqrt_card h.lt hM hL⟩

/-- D-014 for K3: the walk's `c = √3` sits at the lower edge, below `√6`. -/
example : √3 ≤ √3 ∧ √3 ≤ √((6 - 0 : ℤ) : ℝ) := isLorentzC_pmWalk.bounds

/-! ### K4: unit-free -/

/-- The steps of the re-unitized record `D x` are `D` times the steps of `x`. -/
theorem windowSteps_map (D : Matrix (Fin 3) (Fin 3) ℝ) (x : ℤ → State) (a b : ℤ) :
    windowSteps (fun k => matState D (x k)) a b = fun k => D *ᵥ windowSteps x a b k := by
  funext k
  simp only [windowSteps]
  rw [← map_sub, ofLp_matState]

theorem covers_map {D : Matrix (Fin 3) (Fin 3) ℝ} (hD : IsUnit D.det) {ι : Type*} [Fintype ι]
    (u : ι → Fin 3 → ℝ) : Covers (fun k => D *ᵥ u k) ↔ Covers u := by
  rw [← isUnit_det_secondMoment_iff_covers, ← isUnit_det_secondMoment_iff_covers,
    secondMoment_map, det_mul, det_mul, det_transpose]
  have hD0 : D.det ≠ 0 := hD.ne_zero
  simp only [isUnit_iff_ne_zero, ne_eq, mul_eq_zero, hD0, false_or, or_false]

theorem stepMahal_map {D : Matrix (Fin 3) (Fin 3) ℝ} (hD : IsUnit D.det) {k : ℤ}
    (hk : k ∈ Finset.Ico a b) :
    stepMahal (fun k => matState D (x k)) a b k = stepMahal x a b k := by
  have e1 : stepMahal (fun k => matState D (x k)) a b k
      = mahal (secondMoment (windowSteps (fun k => matState D (x k)) a b))
          (windowSteps (fun k => matState D (x k)) a b ⟨k, hk⟩) := rfl
  have e2 : stepMahal x a b k = mahal (secondMoment (windowSteps x a b)) (windowSteps x a b ⟨k, hk⟩) :=
    rfl
  rw [e1, e2, windowSteps_map]
  exact mahal_secondMoment_map hD (windowSteps x a b) ⟨k, hk⟩

/-- **K4.** Any invertible change of the axes' units `D` (including ones that mix axes) leaves
the Lorentz c unchanged: `IsLorentzC (D x) a b c ⇔ IsLorentzC x a b c` (N1a). -/
theorem isLorentzC_map {D : Matrix (Fin 3) (Fin 3) ℝ} (hD : IsUnit D.det) :
    IsLorentzC (fun k => matState D (x k)) a b c ↔ IsLorentzC x a b c := by
  unfold IsLorentzC
  rw [windowSteps_map, covers_map hD]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · exact forall₂_congr fun k hk => by rw [stepMahal_map hD hk]
  · exact exists_congr fun k => and_congr_right fun hk => by rw [stepMahal_map hD hk]

/-- D-014 for K4: the walk recorded in other units (×9/5 on the first axis) has the same `√3`. -/
example : IsLorentzC (fun k => matState (diagonal ![9 / 5, 1, 1]) (pmWalk k)) 0 6 √3 :=
  (isLorentzC_map (by simp [det_diagonal, Fin.prod_univ_succ])).2 isLorentzC_pmWalk

/-! ### K5: natural units -/

/-- The window `[a, b]` as a finite table indexed by its samples, in tick time. -/
def windowTime (a b : ℤ) : {k // k ∈ Finset.Icc a b} → ℝ := fun k => (k.1 : ℝ)

theorem windowTime_injective (a b : ℤ) : Function.Injective (windowTime a b) :=
  fun _ _ h => Subtype.ext (Int.cast_injective h)

/-- Slopes of the window table are slopes of the series. -/
theorem coe_slope_window (y : ℤ → State) (a b : ℤ) (p q : {k // k ∈ Finset.Icc a b}) :
    (slope (windowTime a b) (fun k => y k.1) p q : ℝ) = (slope (fun j : ℤ => (j : ℝ)) y p.1 q.1 : ℝ) := by
  simp only [coe_slope, windowTime]

/-- `critSpeed` as the least bound of the slopes (E1 for a whole finite table). -/
theorem critSpeed_le_iff {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 ≤ c) (t : ι → ℝ) (y : ι → State) :
    (critSpeed t y : ℝ) ≤ c ↔ ∀ p q : ι, (slope t y p q : ℝ) ≤ c := by
  rw [critSpeed, critSpeedOn_le_iff hc]
  exact ⟨fun h p q => h (p, q) (Finset.mem_univ _), fun h p _ => h p.1 p.2⟩

theorem slope_le_critSpeed {ι : Type*} [Fintype ι] (t : ι → ℝ) (y : ι → State) (p q : ι) :
    slope t y p q ≤ critSpeed t y :=
  slope_le_critSpeedOn t y (p := (p, q)) (Finset.mem_univ _)

/-- The critical speed of the finite window table is the `c*` over the window's pairs. -/
theorem critSpeed_window (y : ℤ → State) (a b : ℤ) :
    (critSpeed (windowTime a b) (fun k => y k.1) : ℝ)
      = critSpeedOn (fun j : ℤ => (j : ℝ)) y (windowPairs a b) := by
  apply le_antisymm
  · refine (critSpeed_le_iff (coe_nonneg _) _ _).2 fun p q => ?_
    have hp : (p.1, q.1) ∈ windowPairs a b := by
      simp only [windowPairs, Finset.mem_product]
      exact ⟨p.2, q.2⟩
    rw [coe_slope_window]
    have h := NNReal.coe_le_coe.2 (slope_le_critSpeedOn (fun j : ℤ => (j : ℝ)) y hp)
    simp only at h  -- reduce `(↑p, ↑q).1` first; otherwise `exact` unfolds the interval finsets
    exact h
  · refine (critSpeedOn_le_iff (coe_nonneg _) _ _ _).2 fun p hp => ?_
    simp only [windowPairs, Finset.mem_product] at hp
    have h' := NNReal.coe_le_coe.2 (slope_le_critSpeed (windowTime a b) (fun k => y k.1)
      ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩)
    rw [coe_slope_window] at h'
    exact h'

/-- **K5 (natural units).** For a Lorentz c and any `L` with `Lᵀ L = M⁻¹`: the window table of
`Lx / c` has critical speed `1`, and every `Λ` in the textbook Lorentz group `O(1,3)` keeps it
at `1` (T15, T14). -/
theorem IsLorentzC.natural (h : IsLorentzC x a b c) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : Lᵀ * L = (secondMoment (windowSteps x a b))⁻¹) :
    critSpeed (windowTime a b) (fun k => c⁻¹ • matState L (x k.1)) = 1 ∧
      ∀ Λ ∈ lorentzGroup,
        critSpeed (frameTime Λ (windowTime a b) fun k => c⁻¹ • matState L (x k.1))
          (frameState Λ (windowTime a b) fun k => c⁻¹ • matState L (x k.1)) = 1 := by
  set Y : {k // k ∈ Finset.Icc a b} → State := fun k => matState L (x k.1) with hY
  have hc : c = tickCritSpeed L x a b := ((isLorentzC_iff hL).1 h).2.2
  have hcs : (critSpeed (windowTime a b) Y : ℝ) = c := by
    rw [hY, critSpeed_window (fun j => matState L (x j)) a b, ← tickCritSpeed_eq_windowPairs, hc]
  have hpos : 0 < c := lt_of_lt_of_le (by positivity) h.bounds.1
  have hpos' : 0 < (critSpeed (windowTime a b) Y : ℝ) := by rw [hcs]; exact hpos
  constructor
  · have h1 : critSpeed (windowTime a b) (fun k => (critSpeed (windowTime a b) Y : ℝ)⁻¹ • Y k) = 1 :=
      critSpeedOn_normalize (windowTime a b) Y Finset.univ hpos'
    rw [hcs] at h1
    exact h1
  · intro Λ hΛ
    have h2 := critSpeed_frame_normalized (windowTime_injective a b) hpos' hΛ
    rw [hcs] at h2
    exact h2

/-- D-014 for K5: the walk in natural units (`L = √3 I`, `c = √3`) has `c* = 1`, and the
rapidity boost of `O(1,3)` keeps it at `1`. -/
example (η : ℝ) :
    critSpeed (frameTime (rapidityBoost one_ne_zero η) (windowTime 0 6)
        fun k => (√3)⁻¹ • matState (√3 • 1) (pmWalk k.1))
      (frameState (rapidityBoost one_ne_zero η) (windowTime 0 6)
        fun k => (√3)⁻¹ • matState (√3 • 1) (pmWalk k.1)) = 1 :=
  (isLorentzC_pmWalk.natural sqrt_three_factor).2 _ (rapidityBoost_mem one_ne_zero η)

/-! ### The system level -/

/-- **IsSystemLorentzC.** The observers of one series `x` that see every `m`-th sample, `m ∈ S`,
each over its own window `win m = (aₘ, bₘ)`, all have the same Lorentz c. Exact agreement only
(D-050 C3); tolerance versions stay empirical. -/
def IsSystemLorentzC (x : ℤ → State) (S : Set ℤ) (win : ℤ → ℤ × ℤ) (c : ℝ) : Prop :=
  ∀ m ∈ S, IsLorentzC (fun k => x (m * k)) (win m).1 (win m).2 c

/-- A system Lorentz c is unique (for a non-empty set of observers). -/
theorem IsSystemLorentzC.unique {S : Set ℤ} {win : ℤ → ℤ × ℤ} {c' : ℝ} (hS : S.Nonempty)
    (h : IsSystemLorentzC x S win c) (h' : IsSystemLorentzC x S win c') : c = c' := by
  obtain ⟨m, hm⟩ := hS
  exact (h m hm).unique (h' m hm)

/-! ### K6: the helix is a witness -/

/-- The helix window over whole turns has Lorentz c `√3` (N1g). -/
theorem isLorentzC_helix {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) (hω : sin ω ≠ 0) (hab : a < b)
    (hN : ∃ j : ℤ, ((b - a : ℤ) : ℝ) * ω = 2 * π * j) : IsLorentzC (helix r ω v) a b √3 := by
  have hstep : ∀ k ∈ Finset.Ico a b, stepMahal (helix r ω v) a b k = 3 := fun k hk =>
    helix_mahal_eq_three hr hv hω hab hN ⟨k, hk⟩
  refine ⟨(isUnit_det_secondMoment_iff_covers _).1 (isUnit_det_helix hr hv hω hab hN),
    fun k hk => by rw [hstep k hk], ⟨a, Finset.mem_Ico.2 ⟨le_rfl, hab⟩, by
      rw [hstep a (Finset.mem_Ico.2 ⟨le_rfl, hab⟩)]⟩⟩

/-- **K6.** The helix (`r, v ≠ 0`) is a system with Lorentz c `√3`: every observer `m ∈ S` with
`sin mω ≠ 0` whose window covers whole turns of `mω` has `c = √3`. -/
theorem helix_isSystemLorentzC {r ω v : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) {S : Set ℤ}
    {win : ℤ → ℤ × ℤ}
    (hS : ∀ m ∈ S, sin (m * ω) ≠ 0 ∧ (win m).1 < (win m).2 ∧
      ∃ j : ℤ, (((win m).2 - (win m).1 : ℤ) : ℝ) * (m * ω) = 2 * π * j) :
    IsSystemLorentzC (helix r ω v) S win √3 := by
  intro m hm
  obtain ⟨hmω, hab, hN⟩ := hS m hm
  have hm0 : (m : ℝ) ≠ 0 := by
    rintro h0
    rw [h0, zero_mul, sin_zero] at hmω
    exact hmω rfl
  rw [helix_decimate]
  exact isLorentzC_helix hr (mul_ne_zero hm0 hv) hmω hab hN

/-- D-014 for K6: the quarter-turn helix seen every tick and every 3 ticks, over `[0, 4)`, is a
system with Lorentz c `√3`. -/
example : IsSystemLorentzC (helix 1 (π / 2) 1) {1, 3} (fun _ => (0, 4)) √3 := by
  refine helix_isSystemLorentzC one_ne_zero one_ne_zero fun m hm => ?_
  rcases hm with rfl | rfl
  · refine ⟨by push_cast; rw [one_mul]; exact sin_pi_div_two_ne, by norm_num, 1, by push_cast; ring⟩
  · refine ⟨?_, by norm_num, 3, by push_cast; ring⟩
    rw [show ((3 : ℤ) : ℝ) * (π / 2) = π / 2 + π by push_cast; ring, sin_add_pi, sin_pi_div_two]
    norm_num

/-! ### K7: the non-witnesses -/

/-- **K7.** A planar circle (`v = 0`) or an aliased tick (`sin ω = 0`) has no Lorentz c at all,
for any window: there is no unit of change (N1g (d), N1c′). -/
theorem helix_not_isLorentzC {r ω v : ℝ} (h : v = 0 ∨ sin ω = 0) (a b : ℤ) (c : ℝ) :
    ¬ IsLorentzC (helix r ω v) a b c := fun hc =>
  helix_not_isUnit h a b ((isUnit_det_secondMoment_iff_covers _).2 hc.1)

/-- **K7 (observers).** The `m`-tick observer of a helix has no Lorentz c if `v = 0` or
`sin mω = 0`; so a system containing such an observer has no system Lorentz c. -/
theorem not_isSystemLorentzC_of_aliased {r ω v : ℝ} {S : Set ℤ} {win : ℤ → ℤ × ℤ} {m : ℤ}
    (hm : m ∈ S) (h : v = 0 ∨ sin (m * ω) = 0) (c : ℝ) :
    ¬ IsSystemLorentzC (helix r ω v) S win c := by
  intro hsys
  have := hsys m hm
  rw [helix_decimate] at this
  exact helix_not_isLorentzC (h.imp (fun hv => by simp [hv]) id) _ _ c this

/-- D-014 for K7: the planar circle has no Lorentz c. -/
example (c : ℝ) : ¬ IsLorentzC (helix 1 (π / 2) 0) 0 4 c :=
  helix_not_isLorentzC (Or.inl rfl) 0 4 c

/-- D-014 for K7: adding the aliased 2-tick observer (`2ω = π`) destroys the system. -/
example (c : ℝ) : ¬ IsSystemLorentzC (helix 1 (π / 2) 1) {1, 2} (fun _ => (0, 4)) c :=
  not_isSystemLorentzC_of_aliased (m := 2) (by simp)
    (Or.inr (by push_cast; rw [show (2 : ℝ) * (π / 2) = π by ring, sin_pi])) c

end GeneralizedC
