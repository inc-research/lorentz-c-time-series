/-
GeneralizedCSymmetry/CrossSpeed.lean: the β1 cross-speed between two state-spacetime systems
(P2-1a: Y1, Y2, Y3, the general part of Y6, Y8, Y9).

  crossMahal xA aA bA xB k       squared length of B's step k in A's frozen window unit M_A⁻¹
  Y1  IsCrossSpeed xA aA bA cA xB aB bB s
                                 A's window is IsLorentzC at cA; every step of B's window has
                                 √mahal(M_A, ΔxB) ≤ s·cA; some step reaches it (no L, no sup)
      SharesCone x win           IsCrossSpeed … 1 for every ordered pair (symmetric reference, exact)
      exists_isCrossSpeed, IsCrossSpeed.unique
  Y2  isCrossSpeed_self          A against itself gives 1
  Y3  isCrossSpeed_map           one D (det a unit) applied to both SSTS leaves the cross-speed
  Y6  crossSpeed_decimate_le     per A-tick, any m-decimation of A has cross-speed ≤ m (s/m ≤ 1)
  Y8  crossSpeed_sq_add_ge       both all-light in their own units ⇒ s_{B|A}² + s_{A|B}² ≥ 2
  Y9  sharesCone_iff_secondMoment_eq
                                 all-light family: SharesCone ⇔ all window second moments equal

Design (PROGRESS D-053 C4, D-054 A1–A7, D-055 B-v; p2_breakdown.html §1c, §7): a new library that
imports the closed core `GeneralizedC` (tag kinematic-v1) as a dependency and never edits it.
Every theorem is followed by its D-014 example.
-/
import GeneralizedC

open Matrix WithLp NNReal Real GeneralizedC

namespace GeneralizedCSymmetry

/-! ### Y1: definitions -/

/-- The squared length of step `k` of `xB`, measured in `A`'s frozen unit of change: `A`'s window
second moment `M_A = secondMoment (windowSteps xA aA bA)` (U4: the full `G_A` is carried over). -/
noncomputable def crossMahal (xA : ℤ → State) (aA bA : ℤ) (xB : ℤ → State) (k : ℤ) : ℝ :=
  mahal (secondMoment (windowSteps xA aA bA)) (ofLp (xB (k + 1) - xB k))

/-- **Y1 (A1).** `s` is the cross-speed of `B` (window `[aB, bB)`) in `A`'s frame (window
`[aA, bA)`, Lorentz c `cA`): `A`'s window is `IsLorentzC` at `cA`; every step of `B` is at most
`s·cA` long in `A`'s unit; and some step is exactly that long. Shaped like `IsLorentzC`: no factor
`L`, no supremum. `s = 1` means `B` saturates `A`'s cone. -/
def IsCrossSpeed (xA : ℤ → State) (aA bA : ℤ) (cA : ℝ) (xB : ℤ → State) (aB bB : ℤ) (s : ℝ) :
    Prop :=
  IsLorentzC xA aA bA cA ∧
    (∀ k ∈ Finset.Ico aB bB, √(crossMahal xA aA bA xB k) ≤ s * cA) ∧
    ∃ k ∈ Finset.Ico aB bB, √(crossMahal xA aA bA xB k) = s * cA

/-- **Y1 (A2).** A family of SSTS (records `x i` with windows `win i`) **shares the cone**: for
every ordered pair `(i, j)`, `j`'s cross-speed in `i`'s frozen unit is exactly 1 (the symmetric
reference, U3). Exact only; the tolerance stays on the run card (D-055 B-ii). -/
def SharesCone {J : Type*} (x : J → ℤ → State) (win : J → ℤ × ℤ) : Prop :=
  ∀ i j, ∃ c, IsCrossSpeed (x i) (win i).1 (win i).2 c (x j) (win j).1 (win j).2 1

variable {xA xB : ℤ → State} {aA bA aB bB : ℤ} {cA s : ℝ}

theorem IsCrossSpeed.cA_pos (h : IsCrossSpeed xA aA bA cA xB aB bB s) : 0 < cA :=
  lt_of_lt_of_le (by positivity) h.1.bounds.1

theorem IsCrossSpeed.nonneg (h : IsCrossSpeed xA aA bA cA xB aB bB s) : 0 ≤ s := by
  obtain ⟨k, -, hk⟩ := h.2.2
  have h0 : 0 ≤ s * cA := hk ▸ Real.sqrt_nonneg _
  exact nonneg_of_mul_nonneg_left h0 h.cA_pos

theorem IsCrossSpeed.lt (h : IsCrossSpeed xA aA bA cA xB aB bB s) : aB < bB := by
  obtain ⟨k, hk, -⟩ := h.2.2
  have := Finset.mem_Ico.1 hk
  omega

/-- The cross-speed is unique: it is `B`'s largest step in `A`'s unit, divided by `cA`. -/
theorem IsCrossSpeed.unique {s' : ℝ} (h : IsCrossSpeed xA aA bA cA xB aB bB s)
    (h' : IsCrossSpeed xA aA bA cA xB aB bB s') : s = s' := by
  obtain ⟨k, hk, hkc⟩ := h.2.2
  obtain ⟨k', hk', hkc'⟩ := h'.2.2
  have h1 : s * cA ≤ s' * cA := hkc ▸ h'.2.1 k hk
  have h2 : s' * cA ≤ s * cA := hkc' ▸ h.2.1 k' hk'
  exact mul_right_cancel₀ h.cA_pos.ne' (le_antisymm h1 h2)

/-- A cross-speed exists whenever `A`'s window has a Lorentz c and `B`'s window is non-empty. -/
theorem exists_isCrossSpeed (hA : IsLorentzC xA aA bA cA) (hab : aB < bB) :
    ∃ s, IsCrossSpeed xA aA bA cA xB aB bB s := by
  have hc : 0 < cA := lt_of_lt_of_le (by positivity) hA.bounds.1
  obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image (Finset.Ico aB bB)
    (fun k => √(crossMahal xA aA bA xB k)) ⟨aB, Finset.mem_Ico.2 ⟨le_rfl, hab⟩⟩
  refine ⟨√(crossMahal xA aA bA xB k0) / cA, hA, fun k hk => ?_, k0, hk0, ?_⟩
  · rw [div_mul_cancel₀ _ hc.ne']
    exact hmax k hk
  · rw [div_mul_cancel₀ _ hc.ne']

/-! ### Y2: self-reference -/

/-- **Y2.** An SSTS against itself: if `A`'s window has Lorentz c `cA`, its cross-speed in its own
unit is 1. -/
theorem isCrossSpeed_self {x : ℤ → State} {a b : ℤ} {c : ℝ} (h : IsLorentzC x a b c) :
    IsCrossSpeed x a b c x a b 1 := by
  refine ⟨h, fun k hk => ?_, ?_⟩
  · rw [one_mul]
    exact h.2.1 k hk
  · obtain ⟨k, hk, e⟩ := h.2.2
    exact ⟨k, hk, by rw [one_mul]; exact e⟩

/-- D-014 for Y1 and Y2: the walk `0 → e₁ → 0 → e₂ → 0 → e₃ → 0` against itself. -/
example : IsCrossSpeed pmWalk 0 6 √3 pmWalk 0 6 1 := isCrossSpeed_self isLorentzC_pmWalk

/-- D-014 for Y1 (existence): the quarter-turn helix measured in the walk's unit has a cross-speed. -/
example : ∃ s, IsCrossSpeed pmWalk 0 6 √3 (helix 1 (π / 2) 1) 0 4 s :=
  exists_isCrossSpeed isLorentzC_pmWalk (by norm_num)

/-! ### Y3: unit-free -/

theorem crossMahal_map {D : Matrix (Fin 3) (Fin 3) ℝ} (hD : IsUnit D.det) (k : ℤ) :
    crossMahal (fun k => matState D (xA k)) aA bA (fun k => matState D (xB k)) k
      = crossMahal xA aA bA xB k := by
  unfold crossMahal
  rw [windowSteps_map, secondMoment_map, ← map_sub, ofLp_matState, mahal_conj hD]

/-- **Y3.** One change of units `D` (det a unit), applied to **both** SSTS, leaves the cross-speed
unchanged (Duff: only the unit-free relation is physical). Separate `D`s for `A` and `B` are
deliberately not covered (that is the F1 point). -/
theorem isCrossSpeed_map {D : Matrix (Fin 3) (Fin 3) ℝ} (hD : IsUnit D.det) :
    IsCrossSpeed (fun k => matState D (xA k)) aA bA cA (fun k => matState D (xB k)) aB bB s ↔
      IsCrossSpeed xA aA bA cA xB aB bB s := by
  unfold IsCrossSpeed
  rw [isLorentzC_map hD]
  simp only [crossMahal_map hD]

/-- **Y3 (families).** The same for `SharesCone`. -/
theorem sharesCone_map {J : Type*} {x : J → ℤ → State} {win : J → ℤ × ℤ}
    {D : Matrix (Fin 3) (Fin 3) ℝ} (hD : IsUnit D.det) :
    SharesCone (fun i k => matState D (x i k)) win ↔ SharesCone x win := by
  unfold SharesCone
  exact forall₂_congr fun i j => exists_congr fun c => isCrossSpeed_map hD

/-- D-014 for Y3: the walk against itself, recorded in other units (×9/5 on the first axis). -/
example : IsCrossSpeed (fun k => matState (diagonal ![9 / 5, 1, 1]) (pmWalk k)) 0 6 √3
    (fun k => matState (diagonal ![9 / 5, 1, 1]) (pmWalk k)) 0 6 1 :=
  (isCrossSpeed_map (by simp [det_diagonal, Fin.prod_univ_succ])).2
    (isCrossSpeed_self isLorentzC_pmWalk)

/-! ### Y6 (general part): decimations per A-tick -/

/-- An `m`-chord of `A`'s window is at most `m·c` long in `A`'s unit (from K2, every chord is
c-causal in the own unit). -/
theorem sqrt_crossMahal_decimate_le {x : ℤ → State} {a b : ℤ} {c : ℝ} (hA : IsLorentzC x a b c)
    {m k : ℤ} (hm : 0 ≤ m) (h1 : a ≤ m * k) (h2 : m * (k + 1) ≤ b) :
    √(crossMahal x a b (fun j => x (m * j)) k) ≤ m * c := by
  have hmk : m * k ≤ m * (k + 1) := by nlinarith
  have hK2 := hA.isCausalM_chord (i := m * k) (j := m * (k + 1)) h1 (hmk.trans h2)
    (h1.trans hmk) h2
  unfold IsCausalM minkowskiQM tableChord at hK2
  simp only at hK2
  have hd : ((m * (k + 1) : ℤ) : ℝ) - ((m * k : ℤ) : ℝ) = m := by push_cast; ring
  rw [hd] at hK2
  have hle : crossMahal x a b (fun j => x (m * j)) k ≤ (m * c) ^ 2 := by
    show mahal (secondMoment (windowSteps x a b)) (ofLp (x (m * (k + 1)) - x (m * k))) ≤ _
    unfold mahal
    nlinarith
  have hmc : 0 ≤ (m : ℝ) * c := mul_nonneg (by exact_mod_cast hm) hA.nonneg
  calc √(crossMahal x a b (fun j => x (m * j)) k) ≤ √((m * c) ^ 2) := Real.sqrt_le_sqrt hle
    _ = m * c := Real.sqrt_sq hmc

/-- **Y6 (general part, trap A7).** Measured per **A-tick**, any `m`-decimation of `A` stays
inside `A`'s cone: if the decimated record's window `[aB, bB)` sits inside `A`'s window
(`a ≤ m·aB`, `m·bB ≤ b`), its cross-speed per count is at most `m`, i.e. `s / m ≤ 1` per A-tick.
So "never exceeds" passes for free on decimations (D-053 C2). -/
theorem crossSpeed_decimate_le {x : ℤ → State} {a b : ℤ} {c : ℝ} {m : ℤ} (hm : 0 < m)
    (h1 : a ≤ m * aB) (h2 : m * bB ≤ b)
    (h : IsCrossSpeed x a b c (fun j => x (m * j)) aB bB s) : s ≤ m := by
  obtain ⟨k, hk, hkc⟩ := h.2.2
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.1 hk
  have hle := sqrt_crossMahal_decimate_le h.1 hm.le (k := k) (by nlinarith) (by nlinarith)
  rw [hkc] at hle
  exact le_of_mul_le_mul_right hle h.cA_pos

/-- D-014 for Y6 (general part): the walk read every 2 ticks over `[0, 3)` stays within twice the
walk's c per count, i.e. within its cone per walk-tick. -/
example {s : ℝ} (h : IsCrossSpeed pmWalk 0 6 √3 (fun j => pmWalk (2 * j)) 0 3 s) : s ≤ 2 := by
  have := crossSpeed_decimate_le (m := 2) (by norm_num) (by norm_num) (by norm_num) h
  exact_mod_cast this

/-! ### The trace inequality behind Y8 and Y9 -/

/-- The mean of `B`'s steps in `A`'s unit is `tr(M_A⁻¹ M_B)`; a cross-speed bounds it:
`tr(M_A⁻¹ M_B) ≤ (s·cA)²` (the mean is at most the max; generalizes N1c (i)). -/
theorem trace_le_of_isCrossSpeed (h : IsCrossSpeed xA aA bA cA xB aB bB s) :
    trace ((secondMoment (windowSteps xA aA bA))⁻¹ * secondMoment (windowSteps xB aB bB))
      ≤ (s * cA) ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card {k // k ∈ Finset.Ico aB bB} :=
    Nat.cast_pos.2 (Fintype.card_pos_iff.2 (nonempty_window h.lt))
  rw [trace_mul_secondMoment]
  have hterm : ∀ k : {k // k ∈ Finset.Ico aB bB},
      windowSteps xB aB bB k ⬝ᵥ ((secondMoment (windowSteps xA aA bA))⁻¹ *ᵥ windowSteps xB aB bB k)
        ≤ (s * cA) ^ 2 := by
    intro k
    have hk := h.2.1 k.1 k.2
    change √(crossMahal xA aA bA xB k.1) ≤ s * cA at hk
    change crossMahal xA aA bA xB k.1 ≤ _
    rcases le_or_gt (crossMahal xA aA bA xB k.1) 0 with h0 | h0
    · exact h0.trans (sq_nonneg _)
    · have := Real.sq_sqrt h0.le
      nlinarith [Real.sqrt_nonneg (crossMahal xA aA bA xB k.1)]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm k
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc (Fintype.card {k // k ∈ Finset.Ico aB bB} : ℝ)⁻¹ * ∑ k, _
      ≤ (Fintype.card {k // k ∈ Finset.Ico aB bB} : ℝ)⁻¹ *
          ((Fintype.card {k // k ∈ Finset.Ico aB bB} : ℝ) * (s * cA) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (s * cA) ^ 2 := by field_simp

open scoped MatrixOrder in
/-- For `Y` positive semidefinite with `det Y` a unit: `tr Y + tr Y⁻¹ ≥ 2n`, with equality only
for `Y = 1`. Proof: `Y = Z²` with `Z = √Y` symmetric, and `tr((Z − Z⁻¹)ᵀ(Z − Z⁻¹)) ≥ 0`. -/
theorem trace_add_trace_inv {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℝ} (hY : Y.PosSemidef)
    (hdet : IsUnit Y.det) :
    2 * (n : ℝ) ≤ trace Y + trace Y⁻¹ ∧ (trace Y + trace Y⁻¹ = 2 * n → Y = 1) := by
  set Z := CFC.sqrt Y with hZdef
  have hZZ : Z * Z = Y := CFC.sqrt_mul_sqrt_self Y hY.nonneg
  have hZs : Zᵀ = Z := by
    have := (CFC.sqrt_nonneg Y).isSelfAdjoint.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hZdet : IsUnit Z.det := by
    have h0 := hdet.ne_zero
    rw [← hZZ, det_mul] at h0
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul h0)
  have hYinv : Y⁻¹ = Z⁻¹ * Z⁻¹ := by rw [← hZZ, Matrix.mul_inv_rev]
  set W := Z - Z⁻¹ with hW
  have hWs : Wᴴ = W := by
    rw [conjTranspose_eq_transpose_of_trivial, hW, transpose_sub, transpose_nonsing_inv, hZs]
  have hkey : trace (Wᴴ * W) = trace Y + trace Y⁻¹ - 2 * n := by
    rw [hWs, hW, sub_mul, mul_sub, mul_sub, mul_nonsing_inv _ hZdet, nonsing_inv_mul _ hZdet,
      hZZ, ← hYinv]
    simp only [trace_sub, trace_one, Fintype.card_fin]
    ring
  have hnn : 0 ≤ trace (Wᴴ * W) := (posSemidef_conjTranspose_mul_self W).trace_nonneg
  refine ⟨by linarith, fun heq => ?_⟩
  have h0 : trace (Wᴴ * W) = 0 := by rw [hkey, heq]; ring
  have hW0 : W = 0 := trace_conjTranspose_mul_self_eq_zero_iff.1 h0
  have hZ : Z = Z⁻¹ := sub_eq_zero.1 hW0
  rw [← hZZ]
  nth_rewrite 2 [hZ]
  exact mul_nonsing_inv _ hZdet

/-- For `P, Q` positive definite (3×3): `tr(P⁻¹Q) + tr(Q⁻¹P) ≥ 6`, with equality only if `P = Q`.
Via a factor `Lᵀ L = P⁻¹` (N1b-iii) and `Y = L Q Lᵀ`. -/
theorem trace_relMat_add {P Q : Matrix (Fin 3) (Fin 3) ℝ} (hP : P.PosDef) (hQ : Q.PosDef) :
    6 ≤ trace (P⁻¹ * Q) + trace (Q⁻¹ * P) ∧
      (trace (P⁻¹ * Q) + trace (Q⁻¹ * P) = 6 → P = Q) := by
  obtain ⟨L, hL, hLdet⟩ := exists_factor_of_posDef hP.inv
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP.det_pos.ne'
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ.det_pos.ne'
  have hLtu : IsUnit Lᵀ.det := by rwa [det_transpose]
  set Y := L * Q * Lᵀ with hYdef
  have hYpsd : Y.PosSemidef := by
    have := hQ.posSemidef.mul_mul_conjTranspose_same L
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hYdet : IsUnit Y.det := by
    rw [hYdef, det_mul, det_mul, det_transpose]
    exact (hLdet.mul hQu).mul hLdet
  have hPeq : P = L⁻¹ * Lᵀ⁻¹ := by
    rw [← nonsing_inv_nonsing_inv P hPu, ← hL, Matrix.mul_inv_rev]
  have h1 : trace (P⁻¹ * Q) = trace Y := by
    rw [← hL, Matrix.mul_assoc, trace_mul_comm, hYdef]
  have h2 : trace (Q⁻¹ * P) = trace Y⁻¹ := by
    rw [hYdef, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hPeq, trace_mul_comm, Matrix.mul_assoc,
      trace_mul_comm L⁻¹, Matrix.mul_assoc]
  obtain ⟨hge, heq⟩ := trace_add_trace_inv hYpsd hYdet
  refine ⟨by rw [h1, h2]; norm_num at hge; linarith, fun h6 => ?_⟩
  have hY1 : Y = 1 := heq (by rw [← h1, ← h2, h6]; norm_num)
  -- Q = L⁻¹ Y Lᵀ⁻¹ = L⁻¹ Lᵀ⁻¹ = P
  have hQ' : Q = L⁻¹ * Y * Lᵀ⁻¹ := by
    rw [hYdef, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hLtu, Matrix.mul_one,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hLdet, Matrix.one_mul]
  rw [hQ', hY1, Matrix.mul_one, ← hPeq]

/-- The window second moment of a covering window is positive definite (N1c′). -/
theorem posDef_of_covers {x : ℤ → State} {a b : ℤ} (hcov : Covers (windowSteps x a b)) :
    (secondMoment (windowSteps x a b)).PosDef :=
  (secondMoment_posDef_iff_span _).2 ((covers_iff_span_eq_top _).1 hcov)

/-! ### Y8: no mutual containment -/

/-- **Y8 (A5).** If both SSTS are all-light in their own units (Lorentz c `√3`, i.e. every step
of length `√3`, K3), their two cross-speeds satisfy `s_{B|A}² + s_{A|B}² ≥ 2`. So "both inside"
never happens: a β1 non-pass is nested (U-split) or crossing (U-cross), and the outcome list is
complete. -/
theorem crossSpeed_sq_add_ge {sBA sAB : ℝ} (hBA : IsCrossSpeed xA aA bA √3 xB aB bB sBA)
    (hAB : IsCrossSpeed xB aB bB √3 xA aA bA sAB) : 2 ≤ sBA ^ 2 + sAB ^ 2 := by
  have t1 := trace_le_of_isCrossSpeed hBA
  have t2 := trace_le_of_isCrossSpeed hAB
  have h := (trace_relMat_add (posDef_of_covers hBA.1.1) (posDef_of_covers hAB.1.1)).1
  rw [mul_pow, Real.sq_sqrt (by norm_num)] at t1 t2
  linarith

/-! ### Y9: pass ⇔ equal second moments -/

/-- If two windows have the same second moment and the same Lorentz c, `B`'s cross-speed in `A`'s
unit is 1 (A's unit is then B's unit). -/
theorem isCrossSpeed_one_of_secondMoment_eq {c : ℝ} (hA : IsLorentzC xA aA bA c)
    (hB : IsLorentzC xB aB bB c)
    (hM : secondMoment (windowSteps xA aA bA) = secondMoment (windowSteps xB aB bB)) :
    IsCrossSpeed xA aA bA c xB aB bB 1 := by
  have he : ∀ k, crossMahal xA aA bA xB k = stepMahal xB aB bB k := fun k => by
    unfold crossMahal stepMahal
    rw [hM]
  refine ⟨hA, fun k hk => ?_, ?_⟩
  · rw [he, one_mul]
    exact hB.2.1 k hk
  · obtain ⟨k, hk, e⟩ := hB.2.2
    exact ⟨k, hk, by rw [he, one_mul, e]⟩

/-- **Y9 (pair form).** For two SSTS all-light in their own units: they share the cone (cross-speed
1 both ways) ⇔ their window second moments are equal. The equality case of Y8. -/
theorem sharesCone_pair_iff (hA : IsLorentzC xA aA bA √3) (hB : IsLorentzC xB aB bB √3) :
    (IsCrossSpeed xA aA bA √3 xB aB bB 1 ∧ IsCrossSpeed xB aB bB √3 xA aA bA 1) ↔
      secondMoment (windowSteps xA aA bA) = secondMoment (windowSteps xB aB bB) := by
  constructor
  · rintro ⟨hBA, hAB⟩
    have t1 := trace_le_of_isCrossSpeed hBA
    have t2 := trace_le_of_isCrossSpeed hAB
    rw [one_mul, Real.sq_sqrt (by norm_num)] at t1 t2
    obtain ⟨hge, heq⟩ := trace_relMat_add (posDef_of_covers hA.1) (posDef_of_covers hB.1)
    exact heq (by linarith)
  · intro hM
    exact ⟨isCrossSpeed_one_of_secondMoment_eq hA hB hM,
      isCrossSpeed_one_of_secondMoment_eq hB hA hM.symm⟩

/-- **Y9.** A family of SSTS, each all-light in its own unit (Lorentz c `√3`), shares the cone
exactly when all their window second moments are equal (D-055 B-v). -/
theorem sharesCone_iff_secondMoment_eq {J : Type*} (x : J → ℤ → State) (win : J → ℤ × ℤ)
    (h : ∀ i, IsLorentzC (x i) (win i).1 (win i).2 √3) :
    SharesCone x win ↔ ∀ i j, secondMoment (windowSteps (x i) (win i).1 (win i).2)
      = secondMoment (windowSteps (x j) (win j).1 (win j).2) := by
  constructor
  · intro hs i j
    obtain ⟨c, hij⟩ := hs i j
    obtain ⟨c', hji⟩ := hs j i
    have hc : c = √3 := hij.1.unique (h i)
    have hc' : c' = √3 := hji.1.unique (h j)
    subst hc hc'
    exact (sharesCone_pair_iff (h i) (h j)).1 ⟨hij, hji⟩
  · intro hM i j
    exact ⟨√3, isCrossSpeed_one_of_secondMoment_eq (h i) (h j) (hM i j)⟩

/-- D-014 for Y9: the walk with itself (a one-element family) shares the cone. -/
example : SharesCone (fun _ : Unit => pmWalk) (fun _ => (0, 6)) :=
  (sharesCone_iff_secondMoment_eq _ _ fun _ => isLorentzC_pmWalk).2 fun _ _ => rfl

/-- D-014 for Y8: the walk against itself, `1² + 1² ≥ 2` (the equality case). -/
example : 2 ≤ (1 : ℝ) ^ 2 + 1 ^ 2 :=
  crossSpeed_sq_add_ge (isCrossSpeed_self isLorentzC_pmWalk) (isCrossSpeed_self isLorentzC_pmWalk)

end GeneralizedCSymmetry
