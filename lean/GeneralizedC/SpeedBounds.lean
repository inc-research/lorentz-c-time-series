/-
GeneralizedC/SpeedBounds.lean: speed bounds versus timelike and causal chords.

  T1a  isTimelike_iff                       (bridge: Q_c > 0 ⇔ ‖Δx‖ < c|Δt|, for 0 ≤ c; D-005)
  T1   allChordsTimelike_of_lipschitzWith   (L-Lipschitz with L < c ⇒ every chord timelike)
  T1b  isCausal_iff                         (bridge: Q_c ≥ 0 ⇔ ‖Δx‖ ≤ c|Δt|, for 0 ≤ c; D-015)
  T2c  lipschitzWith_iff_allChordsCausal    (c-Lipschitz ⇔ every chord causal, for 0 ≤ c)
  T2   lipschitzWith_of_allChordsTimelike   (every chord timelike ⇒ c-Lipschitz)
  T2a  AllChordsTimelike.mono, AllChordsCausal.mono   (admissible at c, c ≤ c′ ⇒ admissible at c′)
  T2b  allChordsTimelike_rescale_iff, allChordsCausal_rescale_iff   (units lemma)
  T4   not_allChordsCausal_of_unbounded     (unbounded chord slopes ⇒ no c works)
  T5   exists_timelike_of_finite            (finite strictly-timed series ⇒ some c works)

Every theorem with hypotheses is followed by `example`s that satisfy them (D-014).
-/
import GeneralizedC.Basic

open NNReal

namespace GeneralizedC

/-! ### Helpers about the definitions -/

/-- Timelike implies causal (open cone ⊂ closed cone). -/
theorem IsTimelike.isCausal {c : ℝ} {p : ℝ × State} (h : IsTimelike c p) : IsCausal c p :=
  le_of_lt h

/-- `Q_c` depends on `c` only through `c²`, so `c` and `|c|` give the same form. -/
theorem minkowskiQ_abs (c : ℝ) (p : ℝ × State) : minkowskiQ |c| p = minkowskiQ c p := by
  simp only [minkowskiQ, sq_abs]

/-- The spatial part of a chord of uniform motion: `‖(t − s) • v‖ = ‖v‖ |t − s|`. -/
theorem norm_chord_uniformMotion (v : State) (s t : ℝ) :
    ‖(chord (uniformMotion v) s t).2‖ = ‖v‖ * |t - s| := by
  simp only [chord, uniformMotion, ← sub_smul, norm_smul, Real.norm_eq_abs, mul_comm]

/-- Uniform motion with velocity `v` is `‖v‖`-Lipschitz. -/
theorem lipschitzWith_uniformMotion (v : State) :
    LipschitzWith ⟨‖v‖, norm_nonneg v⟩ (uniformMotion v) := by
  refine LipschitzWith.of_dist_le_mul fun t s => le_of_eq ?_
  have h := norm_chord_uniformMotion v s t
  simp only [chord] at h
  rw [dist_eq_norm, h, Real.dist_eq]
  rfl

/-! ### T1a and T1 (CP1) -/

/-- **T1a (bridge).** For `0 ≤ c`, a displacement is strictly timelike exactly when it is
slower than `c`: `Q_c(Δt, Δx) > 0 ↔ ‖Δx‖ < c|Δt|`. -/
theorem isTimelike_iff {c : ℝ} (hc : 0 ≤ c) (p : ℝ × State) :
    IsTimelike c p ↔ ‖p.2‖ < c * |p.1| := by
  -- ⊢ IsTimelike c p ↔ ‖p.2‖ < c * |p.1|
  unfold IsTimelike minkowskiQ
  -- ⊢ 0 < c ^ 2 * p.1 ^ 2 - ‖p.2‖ ^ 2 ↔ ‖p.2‖ < c * |p.1|
  rw [sub_pos, ← sq_abs p.1, ← mul_pow]
  -- ⊢ ‖p.2‖ ^ 2 < (c * |p.1|) ^ 2 ↔ ‖p.2‖ < c * |p.1|
  exact pow_lt_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (abs_nonneg _)) two_ne_zero

/-- **T1.** If the state path `x` is `L`-Lipschitz with `L < c`, every chord is strictly
timelike. -/
theorem allChordsTimelike_of_lipschitzWith {c : ℝ} {L : ℝ≥0} {x : ℝ → State}
    (hL : (L : ℝ) < c) (hx : LipschitzWith L x) : AllChordsTimelike c x := by
  have hc : 0 ≤ c := (NNReal.coe_nonneg L).trans hL.le
  intro s t hst
  rw [isTimelike_iff hc]
  show ‖x t - x s‖ < c * |t - s|
  have hpos : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hst))
  calc ‖x t - x s‖ = dist (x t) (x s) := (dist_eq_norm _ _).symm
    _ ≤ L * dist t s        := hx.dist_le_mul t s
    _ = L * |t - s|         := by rw [Real.dist_eq]
    _ < c * |t - s|         := mul_lt_mul_of_pos_right hL hpos

/-- D-014 for T1, trivial case: a constant path, `L = 0`, `c = 1`. -/
example (p : State) : AllChordsTimelike 1 (fun _ => p) :=
  allChordsTimelike_of_lipschitzWith (L := 0) zero_lt_one (LipschitzWith.const p)

/-- D-014 for T1, non-trivial case: uniform motion with velocity `v` is timelike for any
`c > ‖v‖`, here `c = ‖v‖ + 1`. -/
example (v : State) : AllChordsTimelike (‖v‖ + 1) (uniformMotion v) :=
  allChordsTimelike_of_lipschitzWith (by exact lt_add_one _) (lipschitzWith_uniformMotion v)

/-! ### T1b: the causal bridge (D-015) -/

/-- **T1b (causal bridge).** For `0 ≤ c`, a displacement is causal exactly when it is not
faster than `c`: `Q_c(Δt, Δx) ≥ 0 ↔ ‖Δx‖ ≤ c|Δt|`. Same proof as T1a, with `≤` for `<`. -/
theorem isCausal_iff {c : ℝ} (hc : 0 ≤ c) (p : ℝ × State) :
    IsCausal c p ↔ ‖p.2‖ ≤ c * |p.1| := by
  unfold IsCausal minkowskiQ
  -- ⊢ 0 ≤ c ^ 2 * p.1 ^ 2 - ‖p.2‖ ^ 2 ↔ ‖p.2‖ ≤ c * |p.1|
  rw [sub_nonneg, ← sq_abs p.1, ← mul_pow]
  -- ⊢ ‖p.2‖ ^ 2 ≤ (c * |p.1|) ^ 2 ↔ ‖p.2‖ ≤ c * |p.1|
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (abs_nonneg _)) two_ne_zero

/-- D-014 for T1b, and the reason D-015 exists: uniform motion is causal at its own speed
`c = ‖v‖`... -/
theorem allChordsCausal_uniformMotion (v : State) : AllChordsCausal ‖v‖ (uniformMotion v) := by
  intro s t _
  rw [isCausal_iff (norm_nonneg v), norm_chord_uniformMotion]
  rfl

/-- ...but not timelike at that speed: every chord is lightlike (`Q = 0`). No `v ≠ 0` is
needed: for `v = 0` the speed is `c = 0`, and at `c = 0` nothing is timelike. -/
theorem not_allChordsTimelike_uniformMotion (v : State) :
    ¬ AllChordsTimelike ‖v‖ (uniformMotion v) := by
  intro h
  have h01 := h 0 1 zero_ne_one
  rw [isTimelike_iff (norm_nonneg v), norm_chord_uniformMotion] at h01
  exact lt_irrefl _ h01

/-! ### T2c and T2: Lipschitz ⇔ causal, and timelike ⇒ Lipschitz -/

/-- **T2c.** For `0 ≤ c`: the path `x` is `c`-Lipschitz exactly when every chord is
`c`-causal. Both sides use `≤`, so the equivalence is exact (D-015). -/
theorem lipschitzWith_iff_allChordsCausal {c : ℝ} (hc : 0 ≤ c) {x : ℝ → State} :
    LipschitzWith ⟨c, hc⟩ x ↔ AllChordsCausal c x := by
  constructor
  · -- (⇒) the Lipschitz bound, read through T1b
    intro hx s t _
    rw [isCausal_iff hc]
    show ‖x t - x s‖ ≤ c * |t - s|
    rw [← dist_eq_norm, ← Real.dist_eq]
    exact hx.dist_le_mul t s
  · -- (⇐) T1b turns each causal chord into the Lipschitz bound; `s = t` is trivial
    intro h
    refine LipschitzWith.of_dist_le_mul fun t s => ?_
    show dist (x t) (x s) ≤ c * dist t s
    rcases eq_or_ne s t with rfl | hst
    · simp
    · have hst' := (isCausal_iff hc _).1 (h s t hst)
      simp only [chord] at hst'
      rw [dist_eq_norm, Real.dist_eq]
      exact hst'

/-- D-014 for T2c (⇐): uniform motion is `‖v‖`-Lipschitz, recovered from its causal chords. -/
example (v : State) : LipschitzWith ⟨‖v‖, norm_nonneg v⟩ (uniformMotion v) :=
  (lipschitzWith_iff_allChordsCausal (norm_nonneg v)).2 (allChordsCausal_uniformMotion v)

/-- D-014 for T2c (⇒): a constant path is `0`-Lipschitz, hence causal even at `c = 0`. -/
example (p : State) : AllChordsCausal 0 (fun _ => p) :=
  (lipschitzWith_iff_allChordsCausal le_rfl).1 (LipschitzWith.const p)

/-- **T2.** If every chord is strictly `c`-timelike (with `0 ≤ c`), the path is `c`-Lipschitz.
One line from T2c, since a timelike chord is causal. Only `≤ c` can be concluded, not `< c`:
see T3 (hyperbolic motion). -/
theorem lipschitzWith_of_allChordsTimelike {c : ℝ} (hc : 0 ≤ c) {x : ℝ → State}
    (h : AllChordsTimelike c x) : LipschitzWith ⟨c, hc⟩ x :=
  (lipschitzWith_iff_allChordsCausal hc).2 fun s t hst => (h s t hst).isCausal

/-- D-014 for T2: uniform motion is timelike at `c = ‖v‖ + 1` (T1), so T2 makes it
`(‖v‖ + 1)`-Lipschitz. -/
example (v : State) : LipschitzWith ⟨‖v‖ + 1, by positivity⟩ (uniformMotion v) :=
  lipschitzWith_of_allChordsTimelike _
    (allChordsTimelike_of_lipschitzWith (by exact lt_add_one _) (lipschitzWith_uniformMotion v))

/-! ### T2a: monotonicity in `c` -/

/-- `Q_c(p)` is monotone in `c` on `c ≥ 0`: raising `c` adds `(c′² − c²)Δt² ≥ 0`. -/
theorem minkowskiQ_mono {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') (p : ℝ × State) :
    minkowskiQ c p ≤ minkowskiQ c' p := by
  unfold minkowskiQ
  gcongr

/-- **T2a (timelike).** Admissible at `c` and `0 ≤ c ≤ c′` ⇒ admissible at `c′`. -/
theorem AllChordsTimelike.mono {c c' : ℝ} {x : ℝ → State} (h : AllChordsTimelike c x)
    (hc : 0 ≤ c) (hcc : c ≤ c') : AllChordsTimelike c' x :=
  fun s t hst => lt_of_lt_of_le (h s t hst) (minkowskiQ_mono hc hcc _)

/-- **T2a (causal).** Admissible at `c` and `0 ≤ c ≤ c′` ⇒ admissible at `c′`. -/
theorem AllChordsCausal.mono {c c' : ℝ} {x : ℝ → State} (h : AllChordsCausal c x)
    (hc : 0 ≤ c) (hcc : c ≤ c') : AllChordsCausal c' x :=
  fun s t hst => le_trans (h s t hst) (minkowskiQ_mono hc hcc _)

/-- D-014 for T2a (causal): uniform motion, causal at `‖v‖`, is causal at `‖v‖ + 1`. -/
example (v : State) : AllChordsCausal (‖v‖ + 1) (uniformMotion v) :=
  (allChordsCausal_uniformMotion v).mono (norm_nonneg v) (lt_add_one _).le

/-- D-014 for T2a (timelike): a constant path, timelike at `1`, is timelike at `2`. -/
example (p : State) : AllChordsTimelike 2 (fun _ => p) :=
  (allChordsTimelike_of_lipschitzWith (L := 0) zero_lt_one (LipschitzWith.const p)).mono
    zero_le_one one_le_two

/-! ### T2b: the units lemma -/

/-- Change of units: time unit scaled by `α`, state unit by `β`. A sample at old time `s`
appears at new time `α s` with value `β • x s`; so `y t′ = β • x (t′ / α)`. -/
noncomputable def rescale (α β : ℝ) (x : ℝ → State) : ℝ → State :=
  fun t => β • x (t / α)

/-- The form scales by `β²`: `Q_{(β/α)c}(αΔt, βΔx) = β² Q_c(Δt, Δx)`. -/
theorem minkowskiQ_rescale {α : ℝ} (hα : α ≠ 0) (β c Δt : ℝ) (Δx : State) :
    minkowskiQ (β / α * c) (α * Δt, β • Δx) = β ^ 2 * minkowskiQ c (Δt, Δx) := by
  simp only [minkowskiQ, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

/-- A chord of the rescaled path is the rescaled chord of `x` between times `s/α` and `t/α`. -/
theorem chord_rescale {α : ℝ} (hα : α ≠ 0) (β : ℝ) (x : ℝ → State) (s t : ℝ) :
    chord (rescale α β x) s t = (α * (t / α - s / α), β • (x (t / α) - x (s / α))) := by
  simp only [chord, rescale, smul_sub, Prod.mk.injEq, and_true]
  field_simp

/-- The form on a chord of the rescaled path is `β²` times the form on the original chord. -/
theorem minkowskiQ_chord_rescale {α : ℝ} (hα : α ≠ 0) (β c : ℝ) (x : ℝ → State) (s t : ℝ) :
    minkowskiQ (β / α * c) (chord (rescale α β x) s t)
      = β ^ 2 * minkowskiQ c (chord x (s / α) (t / α)) := by
  rw [chord_rescale hα, minkowskiQ_rescale hα]
  rfl

/-- `s ↦ s / α` is injective for `α ≠ 0`. -/
theorem div_ne_div_of_ne {α s t : ℝ} (hα : α ≠ 0) (hst : s ≠ t) : s / α ≠ t / α :=
  fun h => hst (by simpa [hα] using congrArg (· * α) h)

/-- **T2b (units lemma, timelike).** For `α, β ≠ 0`: every chord of `x` is `c`-timelike ⇔
every chord of `y t′ = β • x (t′/α)` is `(β/α)c`-timelike. Units (`α, β > 0`) are the main
case; `α < 0` (time reversal) and `β < 0` (reflection) are included for free. -/
theorem allChordsTimelike_rescale_iff {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (c : ℝ)
    (x : ℝ → State) :
    AllChordsTimelike c x ↔ AllChordsTimelike (β / α * c) (rescale α β x) := by
  have hβ2 : 0 < β ^ 2 := by positivity
  constructor
  · intro h s t hst
    unfold IsTimelike
    rw [minkowskiQ_chord_rescale hα]
    exact mul_pos hβ2 (h _ _ (div_ne_div_of_ne hα hst))
  · intro h s t hst
    have h' := h (α * s) (α * t) (fun e => hst (mul_left_cancel₀ hα e))
    unfold IsTimelike at h'
    rw [minkowskiQ_chord_rescale hα, mul_div_cancel_left₀ _ hα,
      mul_div_cancel_left₀ _ hα] at h'
    exact pos_of_mul_pos_right h' hβ2.le

/-- **T2b (units lemma, causal).** Same statement for the causal notion (D-015). -/
theorem allChordsCausal_rescale_iff {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (c : ℝ)
    (x : ℝ → State) :
    AllChordsCausal c x ↔ AllChordsCausal (β / α * c) (rescale α β x) := by
  have hβ2 : 0 < β ^ 2 := by positivity
  constructor
  · intro h s t hst
    unfold IsCausal
    rw [minkowskiQ_chord_rescale hα]
    exact mul_nonneg hβ2.le (h _ _ (div_ne_div_of_ne hα hst))
  · intro h s t hst
    have h' := h (α * s) (α * t) (fun e => hst (mul_left_cancel₀ hα e))
    unfold IsCausal at h'
    rw [minkowskiQ_chord_rescale hα, mul_div_cancel_left₀ _ hα,
      mul_div_cancel_left₀ _ hα] at h'
    exact nonneg_of_mul_nonneg_right h' hβ2

/-- D-014 for T2b: uniform motion, timelike at `‖v‖ + 1`, measured with time unit ×2 and
state unit ×3, is timelike at `(3/2)(‖v‖ + 1)`. -/
example (v : State) : AllChordsTimelike (3 / 2 * (‖v‖ + 1)) (rescale 2 3 (uniformMotion v)) :=
  (allChordsTimelike_rescale_iff two_ne_zero three_ne_zero _ _).1
    (allChordsTimelike_of_lipschitzWith (by exact lt_add_one _) (lipschitzWith_uniformMotion v))

/-- D-014 for T2b (causal): uniform motion at its own speed, same change of units. -/
example (v : State) : AllChordsCausal (3 / 2 * ‖v‖) (rescale 2 3 (uniformMotion v)) :=
  (allChordsCausal_rescale_iff two_ne_zero three_ne_zero _ _).1 (allChordsCausal_uniformMotion v)

/-! ### T4: unbounded chord slopes -/

/-- **T4.** If chord slopes are unbounded (for every `M` some chord has
`‖Δx‖ > M|Δt|`), then no `c` works, not even in the causal sense, and for any real `c`
(negative `c` gives the same cone as `|c|`). -/
theorem not_allChordsCausal_of_unbounded {x : ℝ → State}
    (hx : ∀ M : ℝ, ∃ s t, s ≠ t ∧ M * |t - s| < ‖x t - x s‖) (c : ℝ) :
    ¬ AllChordsCausal c x := by
  intro h
  obtain ⟨s, t, hst, hlt⟩ := hx |c|
  have hc : IsCausal |c| (chord x s t) := by
    unfold IsCausal
    rw [minkowskiQ_abs]
    exact h s t hst
  rw [isCausal_iff (abs_nonneg c)] at hc
  exact absurd hc (not_le.mpr hlt)

/-- T4 for the timelike notion, via timelike ⇒ causal. -/
theorem not_allChordsTimelike_of_unbounded {x : ℝ → State}
    (hx : ∀ M : ℝ, ∃ s t, s ≠ t ∧ M * |t - s| < ‖x t - x s‖) (c : ℝ) :
    ¬ AllChordsTimelike c x :=
  fun h => not_allChordsCausal_of_unbounded hx c fun s t hst => (h s t hst).isCausal

/-- D-014 for T4: `x t = t² • v` with `‖v‖ = 1` has unbounded chord slopes
(the chord from `0` to `t = |M| + 1` has slope `t > M`). -/
example (v : State) (hv : ‖v‖ = 1) (c : ℝ) : ¬ AllChordsCausal c (fun t => t ^ 2 • v) := by
  refine not_allChordsCausal_of_unbounded (fun M => ⟨0, |M| + 1, ?_, ?_⟩) c
  · positivity
  · have h1 : 0 < |M| + 1 := by positivity
    simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul,
      norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_pos h1, abs_pow]
    nlinarith [le_abs_self M]

/-! ### T5: finite data always admit some `c` -/

/-- **T5.** A finite series with distinct sample times (`t` injective, e.g. strictly
increasing) admits a `c > 0` for which every chord between distinct samples is strictly
timelike. Witness: `c = 1 + Σᵢ Σⱼ ‖xⱼ − xᵢ‖ / |tⱼ − tᵢ|`, which exceeds every chord slope.
(The `i = j` terms are `0 / 0 = 0` in Lean.) -/
theorem exists_timelike_of_finite {ι : Type*} [Fintype ι] (t : ι → ℝ) (x : ι → State)
    (ht : Function.Injective t) :
    ∃ c : ℝ, 0 < c ∧ ∀ i j, i ≠ j → IsTimelike c (t j - t i, x j - x i) := by
  set S := ∑ i, ∑ j, ‖x j - x i‖ / |t j - t i| with hS
  have hterm : ∀ i j, 0 ≤ ‖x j - x i‖ / |t j - t i| := fun _ _ => by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j
  refine ⟨1 + S, by linarith, fun i j hij => ?_⟩
  rw [isTimelike_iff (by linarith)]
  show ‖x j - x i‖ < (1 + S) * |t j - t i|
  have hpos : 0 < |t j - t i| := abs_pos.mpr (sub_ne_zero.mpr (ht.ne hij.symm))
  -- the (i, j) slope is one non-negative term of the double sum
  have hle : ‖x j - x i‖ / |t j - t i| ≤ S :=
    calc ‖x j - x i‖ / |t j - t i| ≤ ∑ j', ‖x j' - x i‖ / |t j' - t i| :=
          Finset.single_le_sum (fun j' _ => hterm i j') (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', ‖x j' - x i'‖ / |t j' - t i'|)
          (fun i' _ => Finset.sum_nonneg fun j' _ => hterm i' j') (Finset.mem_univ i)
  rw [← div_lt_iff₀ hpos]
  linarith

/-- D-014 for T5: five samples at integer times `0, …, 4`, with values `k² • v`. -/
example (v : State) :
    ∃ c : ℝ, 0 < c ∧ ∀ i j : Fin 5, i ≠ j →
      IsTimelike c ((j : ℝ) - i, ((j : ℝ) ^ 2) • v - ((i : ℝ) ^ 2) • v) :=
  exists_timelike_of_finite (fun k : Fin 5 => (k : ℝ)) (fun k => ((k : ℝ) ^ 2) • v)
    (Nat.cast_injective.comp Fin.val_injective)

end GeneralizedC
