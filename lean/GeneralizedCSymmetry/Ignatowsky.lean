/-
GeneralizedCSymmetry/Ignatowsky.lean: Ignatowsky's theorem in 1+1 (P2-1b: Y7a, Y7b, Y7c).

  Setting: events (t, x) ∈ ℝ²; the change to a frame moving at velocity v is a real 2×2 matrix
  Λ(v), for v in a velocity set V. Hypotheses (`IsIgnatowskyFamily V Λ`):
    I0  V contains some v ≠ 0                                  (non-triviality)
    I1  Λ(v) is linear; the new origin is the worldline x = vt (A2, A6; linearity assumed, Y7-1)
    I2  v ∈ V ⇒ −v ∈ V and Λ(−v) Λ(v) = 1                     (A1, reciprocity)
    I3  P Λ(v) P = Λ(−v), P = diag(1, −1)                     (A3, parity)
    I4  Λ(u) Λ(v) = Λ(w) for some w ∈ V                        (A1, group)
    I5  Λ(v)₀₀ > 0                                             (A5, time order)
  No continuity hypothesis (A4): I5 with reciprocity and parity fixes the positive root (Y7-3).

  Y7a IsIgnatowskyFamily.exists_K
                    one K ≥ 0 with Kv² < 1 and Λ(v) = T_{K,v} = γ [[1, −Kv], [−v, 1]] for v ∈ V
  Y7b ignatowskyT_family, ignatowskyT_mul
                    converse: T_K on {Kv² < 1} satisfies I0–I5; w = (u + v)/(1 + Kuv)
  Y7c invariant_speed_iff, invariant_speed_iff_of_pos, not_invariant_speed_of_zero,
      IsIgnatowskyFamily.invariant_speed_iff
                    the speeds kept by every T_{K,v} are those with Ku² = 1: ±1/√K for K > 0,
                    none for K = 0 (one K, one invariant speed: the β1 link)
  Y7d IsIgnatowskyFamily.existsUnique_K                                       (P2-1c, D-062)
                    exactly one K ≥ 0 fits an I0–I5 family (fixed by the (0,1) entry at any v ≠ 0)
  Y7e IsIgnatowskyFamily.invariant_speed_iff'                                 (P2-1c, D-062)
                    for that unique K: Λ(v) = T_{K,v} and the invariant speeds are those with
                    Ku² = 1 (one group, one invariant speed, for *the* K of the family)

Spec: p2_breakdown.html §7 "P2-1b", THOUGHTS Q-040, PROGRESS D-059; P2-1c: PROGRESS D-060, D-062. Self-contained in 1+1; the core
`GeneralizedC` is not edited. Every theorem is followed by its D-014 example.
-/
import GeneralizedC

open Matrix Real

namespace GeneralizedCSymmetry

/-- Real 2×2 matrices acting on events `(t, x)` (index 0 = t, 1 = x). -/
abbrev Frame2 := Matrix (Fin 2) (Fin 2) ℝ

/-- Parity `P = diag(1, −1)` (x ↦ −x). -/
def parity2 : Frame2 := !![1, 0; 0, -1]

/-- The Ignatowsky family `T_{K,v} = γ [[1, −Kv], [−v, 1]]`, `γ = 1/√(1 − Kv²)`. `K = 0` is
Galilean (`γ = 1`), `K = 1/c²` is Lorentz. -/
noncomputable def ignatowskyT (K v : ℝ) : Frame2 :=
  (1 / √(1 - K * v ^ 2)) • !![1, -(K * v); -v, 1]

/-- **The hypotheses I0–I5** on a family `Λ` of frame changes indexed by a velocity set `V`. -/
structure IsIgnatowskyFamily (V : Set ℝ) (Λ : ℝ → Frame2) : Prop where
  /-- I0: some non-zero velocity. -/
  nontrivial : ∃ v ∈ V, v ≠ 0
  /-- I1: the new frame's origin is the worldline `x = vt`. -/
  origin : ∀ v ∈ V, ∀ t : ℝ, (Λ v *ᵥ ![t, v * t]) 1 = 0
  /-- I2: `V` is closed under `v ↦ −v`. -/
  neg_mem : ∀ v ∈ V, -v ∈ V
  /-- I2: reciprocity. -/
  reciprocal : ∀ v ∈ V, Λ (-v) * Λ v = 1
  /-- I3: parity. -/
  parity : ∀ v ∈ V, parity2 * Λ v * parity2 = Λ (-v)
  /-- I4: group closure. -/
  closed : ∀ u ∈ V, ∀ v ∈ V, ∃ w ∈ V, Λ u * Λ v = Λ w
  /-- I5: time order. -/
  timeOrder : ∀ v ∈ V, 0 < Λ v 0 0

namespace IsIgnatowskyFamily

variable {V : Set ℝ} {Λ : ℝ → Frame2} (h : IsIgnatowskyFamily V Λ)
include h

/-! ### Entry relations -/

/-- I1 in entries: `C + D v = 0`. -/
theorem origin_entry {v : ℝ} (hv : v ∈ V) : Λ v 1 0 + Λ v 1 1 * v = 0 := by
  have := h.origin v hv 1
  simpa [mulVec, dotProduct, Fin.sum_univ_two] using this

/-- I3 in entries: `Λ(−v) = [[A, −B], [−C, D]]`. -/
theorem neg_entries {v : ℝ} (hv : v ∈ V) :
    Λ (-v) 0 0 = Λ v 0 0 ∧ Λ (-v) 0 1 = -Λ v 0 1 ∧ Λ (-v) 1 0 = -Λ v 1 0 ∧
      Λ (-v) 1 1 = Λ v 1 1 := by
  have hp := h.parity v hv
  have e00 := congrFun (congrFun hp 0) 0
  have e01 := congrFun (congrFun hp 0) 1
  have e10 := congrFun (congrFun hp 1) 0
  have e11 := congrFun (congrFun hp 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, parity2, vecMul, dotProduct] at e00 e01 e10 e11
  refine ⟨e00.symm, ?_, ?_, e11.symm⟩ <;> linarith

/-- I2 with I3 in entries: `A² − BC = 1`, `B(A − D) = 0`, `C(D − A) = 0`, `D² − BC = 1`. -/
theorem recip_entries {v : ℝ} (hv : v ∈ V) :
    Λ v 0 0 * Λ v 0 0 - Λ v 0 1 * Λ v 1 0 = 1 ∧ Λ v 0 1 * (Λ v 0 0 - Λ v 1 1) = 0 ∧
      Λ v 1 0 * (Λ v 1 1 - Λ v 0 0) = 0 ∧ Λ v 1 1 * Λ v 1 1 - Λ v 0 1 * Λ v 1 0 = 1 := by
  obtain ⟨n00, n01, n10, n11⟩ := h.neg_entries hv
  have hr := h.reciprocal v hv
  have e00 := congrFun (congrFun hr 0) 0
  have e01 := congrFun (congrFun hr 0) 1
  have e10 := congrFun (congrFun hr 1) 0
  have e11 := congrFun (congrFun hr 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, n00, n01, n10, n11, one_apply_eq] at e00 e11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, n00, n01, n10, n11] at e01 e10
  rw [one_apply_ne (by decide)] at e01 e10
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- For `v ≠ 0`: equal diagonal entries, `A = D`. -/
theorem diag_eq_of_ne {v : ℝ} (hv : v ∈ V) (hv0 : v ≠ 0) : Λ v 0 0 = Λ v 1 1 := by
  obtain ⟨r00, r01, r10, r11⟩ := h.recip_entries hv
  have ho := h.origin_entry hv
  by_contra hne
  have hB : Λ v 0 1 = 0 := (mul_eq_zero.1 r01).resolve_right (sub_ne_zero.2 hne)
  have hC : Λ v 1 0 = 0 := (mul_eq_zero.1 r10).resolve_right (sub_ne_zero.2 (Ne.symm hne))
  rw [hC, zero_add] at ho
  have hD : Λ v 1 1 = 0 := (mul_eq_zero.1 ho).resolve_right hv0
  rw [hB, hD] at r11
  simp at r11

/-- `Λ(0) = 1` (when `0 ∈ V`): I1 and I3 make `Λ(0)` diagonal, I2 and I5 give `A = 1`, and I0
with I4 give `D = 1` (otherwise `Λ(0) = P` would turn some `Λ(v)` upside down). -/
theorem zero_eq_one (h0 : (0 : ℝ) ∈ V) : Λ 0 = 1 := by
  have ho := h.origin_entry h0
  simp only [mul_zero, add_zero] at ho
  obtain ⟨-, n01, -, -⟩ := h.neg_entries h0
  rw [neg_zero] at n01
  have hB : Λ 0 0 1 = 0 := by linarith
  obtain ⟨r00, -, -, r11⟩ := h.recip_entries h0
  rw [hB, zero_mul, sub_zero] at r00 r11
  have hA0 := h.timeOrder 0 h0
  have hA : Λ 0 0 0 = 1 := by nlinarith
  -- D = 1, via a non-zero velocity and closure
  obtain ⟨v0, hv0, hv00⟩ := h.nontrivial
  have hd0 := h.diag_eq_of_ne hv0 hv00
  have hA' := h.timeOrder v0 hv0
  obtain ⟨w, hw, hcl⟩ := h.closed 0 h0 v0 hv0
  have p00 := congrFun (congrFun hcl 0) 0
  have p11 := congrFun (congrFun hcl 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hA, hB, ho, one_mul, zero_mul, add_zero,
    zero_add] at p00 p11
  have hD : Λ 0 1 1 = 1 := by
    rcases eq_or_ne w 0 with rfl | hw0
    · -- Λ(0) Λ(v0) = Λ(0) forces Λ(v0) = Λ(0)⁻¹ Λ(0) = 1, against C₀ = −A₀ v₀ ≠ 0
      have hsq : Λ 0 * Λ 0 = 1 := by simpa using h.reciprocal 0 h0
      have hv1 : Λ v0 = 1 := by
        calc Λ v0 = Λ 0 * Λ 0 * Λ v0 := by rw [hsq, Matrix.one_mul]
          _ = Λ 0 * Λ 0 := by rw [Matrix.mul_assoc, hcl]
          _ = 1 := hsq
      have hov := h.origin_entry hv0
      rw [hv1] at hov hA'
      simp at hov
      exact absurd hov hv00
    · have hdw := h.diag_eq_of_ne hw hw0
      rw [← p00, ← p11, hd0] at hdw
      have : Λ v0 1 1 * (1 - Λ 0 1 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · rw [← hd0] at h1; linarith
      · linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hA, hB, ho, hD]

/-- Equal diagonal entries for every `v ∈ V`. -/
theorem diag_eq {v : ℝ} (hv : v ∈ V) : Λ v 0 0 = Λ v 1 1 := by
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [h.zero_eq_one hv]; simp
  · exact h.diag_eq_of_ne hv hv0

/-- The `x′`-row: `C = −A v`. -/
theorem entry_10 {v : ℝ} (hv : v ∈ V) : Λ v 1 0 = -(Λ v 0 0 * v) := by
  have := h.origin_entry hv
  rw [← h.diag_eq hv] at this
  linarith

/-- Closure makes `B/(A v)` the same for all velocities: `B_v A₀ v₀ = A_v v B₀`. -/
theorem ratio_eq {v v0 : ℝ} (hv : v ∈ V) (hv0 : v0 ∈ V) :
    Λ v 0 1 * (Λ v0 0 0 * v0) = Λ v 0 0 * v * Λ v0 0 1 := by
  obtain ⟨w, hw, hcl⟩ := h.closed v hv v0 hv0
  have p00 := congrFun (congrFun hcl 0) 0
  have p11 := congrFun (congrFun hcl 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at p00 p11
  have hdw := h.diag_eq hw
  rw [← p00, ← p11, h.entry_10 hv, h.entry_10 hv0, ← h.diag_eq hv, ← h.diag_eq hv0] at hdw
  linarith

/-! ### Y7a -/

/-- The family has the shape `Λ(v) = A_v [[1, −Kv], [−v, 1]]` with
`K = −B₀/(A₀ v₀)` from any non-zero `v₀ ∈ V`, and `A_v² (1 − Kv²) = 1`. -/
theorem shape {v0 : ℝ} (hv0 : v0 ∈ V) (hv00 : v0 ≠ 0) {v : ℝ} (hv : v ∈ V) :
    Λ v 0 1 = -(-Λ v0 0 1 / (Λ v0 0 0 * v0) * v) * Λ v 0 0 ∧
      Λ v 0 0 ^ 2 * (1 - -Λ v0 0 1 / (Λ v0 0 0 * v0) * v ^ 2) = 1 := by
  have hA0 := (h.timeOrder v0 hv0).ne'
  have hr := h.ratio_eq hv hv0
  have hB : Λ v 0 1 = -(-Λ v0 0 1 / (Λ v0 0 0 * v0) * v) * Λ v 0 0 := by
    field_simp
    linarith
  refine ⟨hB, ?_⟩
  obtain ⟨r00, -, -, -⟩ := h.recip_entries hv
  rw [hB, h.entry_10 hv] at r00
  linear_combination r00

/-- **K ≥ 0 (A5 by iteration).** If every `Λ(v)` has the shape `A_v [[1, −Kv], [−v, 1]]` with
`A_v > 0`, then `K ≥ 0`: for `K < 0`, composing a positive velocity with itself grows at least
linearly, until the t-coefficient `A_u A_v (1 + Kuv)` of the product turns non-positive. -/
theorem K_nonneg {K : ℝ}
    (hsh : ∀ v ∈ V, Λ v 0 1 = -(K * v) * Λ v 0 0) : 0 ≤ K := by
  -- composition: 0 < 1 + Kuv and w (1 + Kuv) = u + v
  have hcomp : ∀ u ∈ V, ∀ v ∈ V, ∃ w ∈ V, 0 < 1 + K * u * v ∧ w * (1 + K * u * v) = u + v := by
    intro u hu v hv
    obtain ⟨w, hw, hcl⟩ := h.closed u hu v hv
    have p00 := congrFun (congrFun hcl 0) 0
    have p10 := congrFun (congrFun hcl 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at p00 p10
    rw [hsh u hu, h.entry_10 hv] at p00
    rw [h.entry_10 hu, ← h.diag_eq hu, h.entry_10 hv, h.entry_10 hw] at p10
    have hAu := h.timeOrder u hu
    have hAv := h.timeOrder v hv
    have hAw := h.timeOrder w hw
    have hpos : 0 < Λ u 0 0 * Λ v 0 0 := mul_pos hAu hAv
    refine ⟨w, hw, ?_, ?_⟩
    · have e : Λ w 0 0 = Λ u 0 0 * Λ v 0 0 * (1 + K * u * v) := by rw [← p00]; ring
      rw [e] at hAw
      exact pos_of_mul_pos_right hAw hpos.le
    · have e1 : Λ w 0 0 = Λ u 0 0 * Λ v 0 0 * (1 + K * u * v) := by rw [← p00]; ring
      have e2 : Λ w 0 0 * w = Λ u 0 0 * Λ v 0 0 * (u + v) := by linarith
      rw [e1] at e2
      have := mul_left_cancel₀ hpos.ne' (by linarith : Λ u 0 0 * Λ v 0 0 * ((1 + K * u * v) * w)
        = Λ u 0 0 * Λ v 0 0 * (u + v))
      linarith
  by_contra hK
  push Not at hK
  obtain ⟨v0, hv0, hv00⟩ := h.nontrivial
  -- a positive velocity p ∈ V
  obtain ⟨p, hp, hp0⟩ : ∃ p ∈ V, 0 < p := by
    rcases lt_or_gt_of_ne hv00 with hlt | hgt
    · exact ⟨-v0, h.neg_mem v0 hv0, by linarith⟩
    · exact ⟨v0, hv0, hgt⟩
  -- iteration: velocities in V at least (n + 1) p
  have hiter : ∀ n : ℕ, ∃ w ∈ V, ((n : ℝ) + 1) * p ≤ w := by
    intro n
    induction n with
    | zero => exact ⟨p, hp, by simp⟩
    | succ n ih =>
      obtain ⟨w, hw, hwn⟩ := ih
      obtain ⟨w', hw', hden, hw'eq⟩ := hcomp w hw p hp
      have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hwn
      have hden1 : 1 + K * w * p ≤ 1 := by
        nlinarith [mul_neg_of_neg_of_pos hK (mul_pos hwpos hp0)]
      refine ⟨w', hw', ?_⟩
      have : w + p ≤ w' := by
        by_contra hlt
        push Not at hlt
        nlinarith [mul_pos (sub_pos.2 hlt) hden,
          mul_nonneg (le_of_lt (add_pos hwpos hp0)) (sub_nonneg.2 hden1)]
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (-K * p * p))
  obtain ⟨w, hw, hwn⟩ := hiter n
  obtain ⟨-, -, hden, -⟩ := hcomp w hw p hp
  have hKpp : 0 < -K * p * p := mul_pos (mul_pos (neg_pos.2 hK) hp0) hp0
  have h1 : 1 < ((n : ℝ) + 1) * (-K * p * p) := by
    have := (div_lt_iff₀ hKpp).1 hn
    nlinarith
  nlinarith

/-- **Y7a (Ignatowsky in 1+1).** A family satisfying I0–I5 is the Ignatowsky family for one
`K ≥ 0`: for every `v ∈ V`, `Kv² < 1` and `Λ(v) = T_{K,v}`. -/
theorem exists_K : ∃ K, 0 ≤ K ∧ ∀ v ∈ V, K * v ^ 2 < 1 ∧ Λ v = ignatowskyT K v := by
  obtain ⟨v0, hv0, hv00⟩ := h.nontrivial
  set K := -Λ v0 0 1 / (Λ v0 0 0 * v0) with hKdef
  have hsh : ∀ v ∈ V, Λ v 0 1 = -(K * v) * Λ v 0 0 := fun v hv => (h.shape hv0 hv00 hv).1
  refine ⟨K, h.K_nonneg hsh, fun v hv => ?_⟩
  have hA := h.timeOrder v hv
  have hg : Λ v 0 0 ^ 2 * (1 - K * v ^ 2) = 1 := (h.shape hv0 hv00 hv).2
  have hX : 0 < 1 - K * v ^ 2 := by
    by_contra hle
    push Not at hle
    nlinarith [sq_nonneg (Λ v 0 0)]
  refine ⟨by linarith, ?_⟩
  -- √(1 − Kv²) = A⁻¹
  have hsq : √(1 - K * v ^ 2) = (Λ v 0 0)⁻¹ := by
    rw [show 1 - K * v ^ 2 = ((Λ v 0 0)⁻¹) ^ 2 by field_simp; linarith]
    exact Real.sqrt_sq (inv_nonneg.2 hA.le)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ignatowskyT, hsq, hsh v hv, h.entry_10 hv, ← h.diag_eq hv]
  ring

end IsIgnatowskyFamily

/-! ### Y7b: the converse -/

/-- `γ² (1 − Kv²) = 1` and `γ > 0` on `Kv² < 1`. -/
theorem ignatowsky_gamma {K v : ℝ} (hv : K * v ^ 2 < 1) :
    0 < 1 / √(1 - K * v ^ 2) ∧ (1 / √(1 - K * v ^ 2)) ^ 2 * (1 - K * v ^ 2) = 1 := by
  have hX : 0 < 1 - K * v ^ 2 := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_pow, Real.sq_sqrt hX.le]
  field_simp

theorem ignatowskyT_apply_00 {K v : ℝ} : ignatowskyT K v 0 0 = 1 / √(1 - K * v ^ 2) := by
  simp [ignatowskyT]

/-- `1 + Kuv > 0` on `Ku² < 1`, `Kv² < 1`, `K ≥ 0`. -/
theorem one_add_pos {K u v : ℝ} (hK : 0 ≤ K) (hu : K * u ^ 2 < 1) (hv : K * v ^ 2 < 1) :
    0 < 1 + K * u * v := by
  have h0u : 0 ≤ K * u ^ 2 := by positivity
  have h0v : 0 ≤ K * v ^ 2 := by positivity
  have : (K * u * v) ^ 2 < 1 := by
    have e : (K * u * v) ^ 2 = (K * u ^ 2) * (K * v ^ 2) := by ring
    rw [e]
    calc K * u ^ 2 * (K * v ^ 2) ≤ K * u ^ 2 * 1 := mul_le_mul_of_nonneg_left hv.le h0u
      _ < 1 := by linarith
  by_contra hle
  push Not at hle
  nlinarith [mul_nonneg (neg_nonneg.2 hle) (by linarith : (0 : ℝ) ≤ 1 - K * u * v)]

/-- **Y7b (composition law).** For `K ≥ 0` and `Ku², Kv² < 1`:
`T_{K,u} T_{K,v} = T_{K,w}` with `w = (u + v)/(1 + Kuv)`, and `Kw² < 1`. -/
theorem ignatowskyT_mul {K u v : ℝ} (hK : 0 ≤ K) (hu : K * u ^ 2 < 1) (hv : K * v ^ 2 < 1) :
    K * ((u + v) / (1 + K * u * v)) ^ 2 < 1 ∧
      ignatowskyT K u * ignatowskyT K v = ignatowskyT K ((u + v) / (1 + K * u * v)) := by
  have hd := one_add_pos hK hu hv
  have hXu : 0 < 1 - K * u ^ 2 := by linarith
  have hXv : 0 < 1 - K * v ^ 2 := by linarith
  have hid : 1 - K * ((u + v) / (1 + K * u * v)) ^ 2
      = (1 - K * u ^ 2) * (1 - K * v ^ 2) / (1 + K * u * v) ^ 2 := by
    field_simp
    ring
  have hXw : 0 < 1 - K * ((u + v) / (1 + K * u * v)) ^ 2 := by rw [hid]; positivity
  refine ⟨by linarith, ?_⟩
  have hsw : √(1 - K * ((u + v) / (1 + K * u * v)) ^ 2)
      = √(1 - K * u ^ 2) * √(1 - K * v ^ 2) / (1 + K * u * v) := by
    rw [hid, Real.sqrt_div' _ (by positivity), Real.sqrt_mul hXu.le, Real.sqrt_sq hd.le]
  have hsu := Real.sqrt_pos.2 hXu
  have hsv := Real.sqrt_pos.2 hXv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ignatowskyT, Matrix.mul_apply, Fin.sum_univ_two, hsw] <;> field_simp <;> ring

/-- **Y7b (converse).** For `K ≥ 0`, the Ignatowsky family `T_K` on `V = {v : Kv² < 1}` satisfies
I0–I5. -/
theorem ignatowskyT_family {K : ℝ} (hK : 0 ≤ K) :
    IsIgnatowskyFamily {v | K * v ^ 2 < 1} (ignatowskyT K) where
  nontrivial := by
    refine ⟨1 / (K + 2), ?_, by positivity⟩
    show K * (1 / (K + 2)) ^ 2 < 1
    rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
    nlinarith
  origin := by
    intro v _ t
    simp [ignatowskyT, mulVec, dotProduct, Fin.sum_univ_two]
    ring
  neg_mem := by
    intro v hv
    simpa [neg_sq] using hv
  reciprocal := by
    intro v hv
    obtain ⟨-, hg⟩ := ignatowsky_gamma hv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ignatowskyT, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
      | linear_combination hg
      | ring
  parity := by
    intro v _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ignatowskyT, parity2, Matrix.mul_apply, Fin.sum_univ_two]
  closed := by
    intro u hu v hv
    exact ⟨_, (ignatowskyT_mul hK hu hv).1, (ignatowskyT_mul hK hu hv).2⟩
  timeOrder := by
    intro v hv
    rw [ignatowskyT_apply_00]
    exact (ignatowsky_gamma hv).1

/-- D-014 for Y7b: the Galilean family (`K = 0`, all of ℝ) and the Lorentz family at `c = 1`
(`K = 1`, `|v| < 1`) satisfy I0–I5. -/
example : IsIgnatowskyFamily {v | 0 * v ^ 2 < 1} (ignatowskyT 0) := ignatowskyT_family le_rfl

example : IsIgnatowskyFamily {v | 1 * v ^ 2 < 1} (ignatowskyT 1) := ignatowskyT_family zero_le_one

/-- D-014 for Y7b (composition): at `K = 1`, `1/2 ⊕ 1/2 = 4/5`. -/
example : ignatowskyT 1 (1 / 2) * ignatowskyT 1 (1 / 2) = ignatowskyT 1 (4 / 5) := by
  have := (ignatowskyT_mul (K := 1) (u := 1 / 2) (v := 1 / 2) zero_le_one (by norm_num)
    (by norm_num)).2
  rw [this]
  norm_num

/-- D-014 for Y7a: the Lorentz family at `c = 1` gives back `K ≥ 0` (here the theorem recovers it). -/
example : ∃ K, 0 ≤ K ∧ ∀ v ∈ {v : ℝ | 1 * v ^ 2 < 1},
    K * v ^ 2 < 1 ∧ ignatowskyT 1 v = ignatowskyT K v :=
  (ignatowskyT_family zero_le_one).exists_K

/-- D-014 for Y7a, the non-example: the rotation family `T_{−1}` (`K = −1`, all of ℝ) satisfies
I1–I3 and I5, but it is not a family in Ignatowsky's sense: closure (I4) fails, as Y7a shows. -/
example : ¬ IsIgnatowskyFamily Set.univ (ignatowskyT (-1)) := by
  intro h
  obtain ⟨K, hK0, hK⟩ := h.exists_K
  obtain ⟨hK1, heq⟩ := hK 1 trivial
  have e := congrFun (congrFun heq 0) 1
  simp [ignatowskyT] at e
  have hpos : 0 < 1 / √(1 - K) := by
    have : 0 < 1 - K := by linarith
    positivity
  have h2 : (0 : ℝ) < 1 / √2 := by positivity
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at e
  nlinarith [inv_pos.2 (Real.sqrt_pos.2 (show (0 : ℝ) < 1 - K by linarith)),
    inv_pos.2 (Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num))]

/-! ### Y7c: one K, one invariant speed -/

/-- `T_{K,v}` keeps the speed `u` (maps the worldline `x = ut` to itself) exactly when `v = 0` or
`Ku² = 1`: `x′ − u t′ = γ v (Ku² − 1)`. -/
theorem ignatowskyT_fixes_speed_iff {K u v : ℝ} (hv : K * v ^ 2 < 1) :
    (ignatowskyT K v *ᵥ ![1, u]) 1 = u * (ignatowskyT K v *ᵥ ![1, u]) 0 ↔
      v = 0 ∨ K * u ^ 2 = 1 := by
  have hg := (ignatowsky_gamma hv).1
  simp only [ignatowskyT, mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  simp
  constructor
  · intro heq
    have : 1 / √(1 - K * v ^ 2) * v * (K * u ^ 2 - 1) = 0 := by linear_combination heq
    rcases mul_eq_zero.1 this with h1 | h1
    · exact Or.inl ((mul_eq_zero.1 h1).resolve_left hg.ne')
    · exact Or.inr (by linarith)
  · rintro (rfl | h1)
    · ring
    · linear_combination (1 / √(1 - K * v ^ 2)) * v * h1

/-- **Y7c.** For a velocity set `V` with a non-zero element, inside `Kv² < 1`: the speeds kept by
every `T_{K,v}`, `v ∈ V`, are exactly those with `Ku² = 1`. -/
theorem invariant_speed_iff {K u : ℝ} {V : Set ℝ} (hV : ∃ v ∈ V, v ≠ 0)
    (hVK : ∀ v ∈ V, K * v ^ 2 < 1) :
    (∀ v ∈ V, (ignatowskyT K v *ᵥ ![1, u]) 1 = u * (ignatowskyT K v *ᵥ ![1, u]) 0) ↔
      K * u ^ 2 = 1 := by
  constructor
  · intro hall
    obtain ⟨v, hv, hv0⟩ := hV
    exact ((ignatowskyT_fixes_speed_iff (hVK v hv)).1 (hall v hv)).resolve_left hv0
  · intro h1 v hv
    exact (ignatowskyT_fixes_speed_iff (hVK v hv)).2 (Or.inr h1)

/-- **Y7c (K > 0).** The invariant speeds are exactly `±1/√K`. -/
theorem invariant_speed_iff_of_pos {K u : ℝ} (hK : 0 < K) {V : Set ℝ} (hV : ∃ v ∈ V, v ≠ 0)
    (hVK : ∀ v ∈ V, K * v ^ 2 < 1) :
    (∀ v ∈ V, (ignatowskyT K v *ᵥ ![1, u]) 1 = u * (ignatowskyT K v *ᵥ ![1, u]) 0) ↔
      u = 1 / √K ∨ u = -(1 / √K) := by
  rw [invariant_speed_iff hV hVK]
  have hs : (1 / √K) ^ 2 = 1 / K := by rw [div_pow, Real.sq_sqrt hK.le, one_pow]
  rw [← sq_eq_sq_iff_eq_or_eq_neg, hs]
  constructor
  · intro h1; field_simp; linarith
  · intro h1; field_simp at h1; linarith

/-- **Y7c (K = 0).** The Galilean family keeps no finite speed. -/
theorem not_invariant_speed_of_zero {u : ℝ} {V : Set ℝ} (hV : ∃ v ∈ V, v ≠ 0) :
    ¬ ∀ v ∈ V, (ignatowskyT 0 v *ᵥ ![1, u]) 1 = u * (ignatowskyT 0 v *ᵥ ![1, u]) 0 := by
  rw [invariant_speed_iff hV (fun v _ => by simp)]
  simp

/-- **Y7c for a family (the β1 link).** For a family satisfying I0–I5, with its `K` from Y7a: the
speeds kept by every frame change of the family are exactly those with `Ku² = 1`. One group, one
invariant speed for every law that shares it. -/
theorem IsIgnatowskyFamily.invariant_speed_iff {V : Set ℝ} {Λ : ℝ → Frame2}
    (h : IsIgnatowskyFamily V Λ) :
    ∃ K, 0 ≤ K ∧ ∀ u : ℝ,
      (∀ v ∈ V, (Λ v *ᵥ ![1, u]) 1 = u * (Λ v *ᵥ ![1, u]) 0) ↔ K * u ^ 2 = 1 := by
  obtain ⟨K, hK0, hK⟩ := h.exists_K
  refine ⟨K, hK0, fun u => ?_⟩
  have e : (∀ v ∈ V, (Λ v *ᵥ ![1, u]) 1 = u * (Λ v *ᵥ ![1, u]) 0) ↔
      ∀ v ∈ V, (ignatowskyT K v *ᵥ ![1, u]) 1 = u * (ignatowskyT K v *ᵥ ![1, u]) 0 :=
    forall₂_congr fun v hv => by rw [(hK v hv).2]
  rw [e]
  exact GeneralizedCSymmetry.invariant_speed_iff h.nontrivial fun v hv => (hK v hv).1

/-- D-014 for Y7c: at `K = 1` (Lorentz, `c = 1`), the invariant speeds are `±1`. -/
example (u : ℝ) :
    (∀ v ∈ {v : ℝ | 1 * v ^ 2 < 1},
      (ignatowskyT 1 v *ᵥ ![1, u]) 1 = u * (ignatowskyT 1 v *ᵥ ![1, u]) 0) ↔
      u = 1 ∨ u = -1 := by
  rw [invariant_speed_iff_of_pos one_pos (ignatowskyT_family zero_le_one).nontrivial
    (fun v hv => hv)]
  simp

/-- D-014 for Y7c (K = 0): the Galilean family keeps no speed, e.g. not `u = 1`. -/
example : ¬ ∀ v ∈ {v : ℝ | 0 * v ^ 2 < 1},
    (ignatowskyT 0 v *ᵥ ![1, 1]) 1 = 1 * (ignatowskyT 0 v *ᵥ ![1, 1]) 0 :=
  not_invariant_speed_of_zero (ignatowskyT_family le_rfl).nontrivial

/-! ### P2-1c: the K of a family is unique (Y7d, Y7e) -/

/-- `T_{K,v}` determines `K` at any `v ≠ 0` where its t-coefficient is positive: the (0,1) entry
over the (0,0) entry is `−Kv`. -/
theorem ignatowskyT_K_eq {K K' v : ℝ} (hv : v ≠ 0) (h00 : 0 < ignatowskyT K v 0 0)
    (heq : ignatowskyT K v = ignatowskyT K' v) : K = K' := by
  have e00 := congrFun (congrFun heq 0) 0
  have e01 := congrFun (congrFun heq 0) 1
  rw [ignatowskyT_apply_00] at h00
  simp only [ignatowskyT, Matrix.smul_apply, smul_eq_mul, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, mul_one] at e00 e01
  rw [← e00] at e01
  have hKv : K * v = K' * v := by
    have := mul_left_cancel₀ h00.ne' e01
    linarith
  exact mul_right_cancel₀ hv hKv

/-- **Y7d (uniqueness of K).** Exactly one `K ≥ 0` fits a family satisfying I0–I5: existence is
Y7a, and any two fitting values agree at a non-zero velocity of `V` (I0). -/
theorem IsIgnatowskyFamily.existsUnique_K {V : Set ℝ} {Λ : ℝ → Frame2}
    (h : IsIgnatowskyFamily V Λ) :
    ∃! K, 0 ≤ K ∧ ∀ v ∈ V, K * v ^ 2 < 1 ∧ Λ v = ignatowskyT K v := by
  obtain ⟨K, hK0, hK⟩ := h.exists_K
  refine ⟨K, ⟨hK0, hK⟩, fun K' ⟨_, hK'⟩ => ?_⟩
  obtain ⟨v0, hv0, hv00⟩ := h.nontrivial
  have h00 : 0 < ignatowskyT K' v0 0 0 := by
    rw [← (hK' v0 hv0).2]
    exact h.timeOrder v0 hv0
  exact ignatowskyT_K_eq hv00 h00 (((hK' v0 hv0).2).symm.trans (hK v0 hv0).2)

/-- D-014 for Y7d: the Lorentz family at `c = 1` has `K = 1` as its unique `K`. -/
example {K : ℝ} (hK : 0 ≤ K ∧ ∀ v ∈ {v : ℝ | 1 * v ^ 2 < 1},
    K * v ^ 2 < 1 ∧ ignatowskyT 1 v = ignatowskyT K v) : K = 1 :=
  (ignatowskyT_family zero_le_one).existsUnique_K.unique hK
    ⟨zero_le_one, fun _ hv => ⟨hv, rfl⟩⟩

/-- **Y7e (Y7c with the family's own K).** For a family satisfying I0–I5 there is exactly one
`K ≥ 0` such that `Λ(v) = T_{K,v}` for every `v ∈ V`, and for that `K` the speeds kept by every
frame change of the family are exactly those with `Ku² = 1`. One group, one invariant speed, for
*the* `K` of the family. -/
theorem IsIgnatowskyFamily.invariant_speed_iff' {V : Set ℝ} {Λ : ℝ → Frame2}
    (h : IsIgnatowskyFamily V Λ) :
    ∃! K, 0 ≤ K ∧ (∀ v ∈ V, Λ v = ignatowskyT K v) ∧ ∀ u : ℝ,
      ((∀ v ∈ V, (Λ v *ᵥ ![1, u]) 1 = u * (Λ v *ᵥ ![1, u]) 0) ↔ K * u ^ 2 = 1) := by
  obtain ⟨K, hK0, hK⟩ := h.exists_K
  refine ⟨K, ⟨hK0, fun v hv => (hK v hv).2, fun u => ?_⟩, fun K' ⟨_, hK', _⟩ => ?_⟩
  · have e : (∀ v ∈ V, (Λ v *ᵥ ![1, u]) 1 = u * (Λ v *ᵥ ![1, u]) 0) ↔
        ∀ v ∈ V, (ignatowskyT K v *ᵥ ![1, u]) 1 = u * (ignatowskyT K v *ᵥ ![1, u]) 0 :=
      forall₂_congr fun v hv => by rw [(hK v hv).2]
    rw [e]
    exact GeneralizedCSymmetry.invariant_speed_iff h.nontrivial fun v hv => (hK v hv).1
  · obtain ⟨v0, hv0, hv00⟩ := h.nontrivial
    have h00 : 0 < ignatowskyT K' v0 0 0 := by
      rw [← hK' v0 hv0]
      exact h.timeOrder v0 hv0
    exact ignatowskyT_K_eq hv00 h00 ((hK' v0 hv0).symm.trans (hK v0 hv0).2)

/-- D-014 for Y7e: the Lorentz family at `c = 1`; its unique `K` is `1`, and its invariant speeds
are those with `u² = 1`. -/
example {K : ℝ} (hK : 0 ≤ K ∧ (∀ v ∈ {v : ℝ | 1 * v ^ 2 < 1}, ignatowskyT 1 v = ignatowskyT K v) ∧
    ∀ u : ℝ, ((∀ v ∈ {v : ℝ | 1 * v ^ 2 < 1},
      (ignatowskyT 1 v *ᵥ ![1, u]) 1 = u * (ignatowskyT 1 v *ᵥ ![1, u]) 0) ↔ K * u ^ 2 = 1)) :
    K = 1 := by
  obtain ⟨K1, -, huniq⟩ := (ignatowskyT_family zero_le_one).invariant_speed_iff'
  have h1 := huniq K hK
  have h2 := huniq 1 ⟨zero_le_one, fun v _ => rfl, fun u =>
    invariant_speed_iff (ignatowskyT_family zero_le_one).nontrivial fun v hv => hv⟩
  rw [h1, h2]

end GeneralizedCSymmetry
