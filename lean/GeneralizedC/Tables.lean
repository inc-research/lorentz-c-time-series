/-
GeneralizedC/Tables.lean: the critical speed c* of a finite table, as a Lean object (CP4).

  E1   critSpeedOn, critSpeed            c* over a finite set S of sample pairs (D-024, D-029 C1)
  E1a  slope_le_critSpeedOn               every slope in S is ≤ c*_S
  E1b  allCausalOn_iff                    every chord in S is c-causal ⇔ c*_S ≤ c   (A = [c*, ∞))
  E1c  exists_isLightlike_critSpeedOn     S ≠ ∅ ⇒ some chord in S has slope c*_S and is lightlike
  E1d  allTimelikeOn_iff                  every chord in S is c-timelike ⇔ c*_S < c (A° = (c*, ∞))
  T10  allCausal_window_of_steps          causal steps in a window ⇒ causal chords in the window
       critSpeedOn_windowPairs            c* of a window's pairs = c* of its consecutive steps
  T10b critSpeedOn_lagPairs_le            c* at lag m ≤ c* at lag 1 (complete data)
  T13  abs_slope_sub_le                   pairwise: two rules δ apart move a slope ≤ 2δ/|Δt|
       abs_critSpeedOn_sub_le             gaps ≥ h ⇒ |c*_S(x′) − c*_S(x)| ≤ 2δ/h

Design (PROGRESS D-029, cp4_breakdown): c* lives in ℝ≥0 and is a `Finset.sup` (the empty
maximum is 0, no side conditions, C2). One definition covers the whole table, one lag Δt and one
window (C1). T10 uses ℤ-indexed sequences with a window [a, b], as T7 does (C3).
Every theorem with hypotheses is followed by `example`s that satisfy them (D-014).
-/
import GeneralizedC.SpeedBounds
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

open NNReal

namespace GeneralizedC

variable {ι : Type*}

/-! ### E1: definitions -/

/-- The chord of a table from sample `i` to sample `j`: `(t j − t i, x j − x i)`. -/
def tableChord (t : ι → ℝ) (x : ι → State) (i j : ι) : ℝ × State :=
  (t j - t i, x j - x i)

/-- A displacement is lightlike when `Q_c` vanishes: on the cone itself. -/
def IsLightlike (c : ℝ) (p : ℝ × State) : Prop :=
  minkowskiQ c p = 0

/-- The chord slope `‖x j − x i‖ / |t j − t i|` of a pair of samples, in `ℝ≥0`.
For `i = j` it is `0 / 0 = 0` (Lean's convention). -/
noncomputable def slope (t : ι → ℝ) (x : ι → State) (i j : ι) : ℝ≥0 :=
  ⟨‖x j - x i‖ / |t j - t i|, by positivity⟩

@[simp] theorem coe_slope (t : ι → ℝ) (x : ι → State) (i j : ι) :
    (slope t x i j : ℝ) = ‖x j - x i‖ / |t j - t i| :=
  rfl

/-- **E1.** The critical speed over a finite set `S` of sample pairs: the largest chord slope
in `S` (D-024: c* = max), and `0` if `S` is empty. -/
noncomputable def critSpeedOn (t : ι → ℝ) (x : ι → State) (S : Finset (ι × ι)) : ℝ≥0 :=
  S.sup fun p => slope t x p.1 p.2

/-- **E1.** The critical speed of a whole finite table: `critSpeedOn` over all pairs. -/
noncomputable def critSpeed [Fintype ι] (t : ι → ℝ) (x : ι → State) : ℝ≥0 :=
  critSpeedOn t x Finset.univ

/-! ### Bridges between slopes and the form -/

/-- The equality twin of T1a/T1b: for `0 ≤ c`, `Q_c(Δt, Δx) = 0 ⇔ ‖Δx‖ = c|Δt|`. -/
theorem isLightlike_iff {c : ℝ} (hc : 0 ≤ c) (p : ℝ × State) :
    IsLightlike c p ↔ ‖p.2‖ = c * |p.1| := by
  unfold IsLightlike minkowskiQ
  rw [sub_eq_zero, ← sq_abs p.1, ← mul_pow, eq_comm]
  exact pow_left_inj₀ (norm_nonneg _) (mul_nonneg hc (abs_nonneg _)) two_ne_zero

/-- With distinct times, the spatial part of a chord is its slope times its duration. -/
theorem norm_eq_slope_mul {t : ι → ℝ} (ht : Function.Injective t) (x : ι → State) (i j : ι) :
    ‖x j - x i‖ = slope t x i j * |t j - t i| := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have hpos : 0 < |t j - t i| := abs_pos.mpr (sub_ne_zero.mpr (ht.ne hij.symm))
    rw [coe_slope, div_mul_cancel₀ _ hpos.ne']

/-- For `0 ≤ c` and distinct times: a chord is `c`-causal ⇔ its slope is `≤ c` (T1b, per pair). -/
theorem isCausal_tableChord_iff {c : ℝ} (hc : 0 ≤ c) {t : ι → ℝ} (ht : Function.Injective t)
    (x : ι → State) (i j : ι) :
    IsCausal c (tableChord t x i j) ↔ (slope t x i j : ℝ) ≤ c := by
  rw [isCausal_iff hc]
  show ‖x j - x i‖ ≤ c * |t j - t i| ↔ _
  rcases eq_or_ne i j with rfl | hij
  · simpa using hc
  · have hpos : 0 < |t j - t i| := abs_pos.mpr (sub_ne_zero.mpr (ht.ne hij.symm))
    rw [coe_slope, div_le_iff₀ hpos]

/-- A lightlike chord between distinct samples has slope exactly `c`. -/
theorem slope_eq_of_isLightlike {c : ℝ} (hc : 0 ≤ c) {t : ι → ℝ} (ht : Function.Injective t)
    (x : ι → State) {i j : ι} (hij : i ≠ j) (h : IsLightlike c (tableChord t x i j)) :
    (slope t x i j : ℝ) = c := by
  have hpos : 0 < |t j - t i| := abs_pos.mpr (sub_ne_zero.mpr (ht.ne hij.symm))
  rw [isLightlike_iff hc] at h
  change ‖x j - x i‖ = c * |t j - t i| at h
  rw [coe_slope, h, mul_div_cancel_right₀ _ hpos.ne']

/-! ### E1a–E1d -/

/-- **E1a.** Every slope in `S` is at most `c*_S`. -/
theorem slope_le_critSpeedOn (t : ι → ℝ) (x : ι → State) {S : Finset (ι × ι)} {p : ι × ι}
    (hp : p ∈ S) : slope t x p.1 p.2 ≤ critSpeedOn t x S :=
  Finset.le_sup (f := fun p : ι × ι => slope t x p.1 p.2) hp

/-- `c*_S ≤ c` (in ℝ, `0 ≤ c`) ⇔ every slope in `S` is `≤ c`. The maximum is the least bound. -/
theorem critSpeedOn_le_iff {c : ℝ} (hc : 0 ≤ c) (t : ι → ℝ) (x : ι → State)
    (S : Finset (ι × ι)) :
    (critSpeedOn t x S : ℝ) ≤ c ↔ ∀ p ∈ S, (slope t x p.1 p.2 : ℝ) ≤ c := by
  constructor
  · intro h p hp
    exact (NNReal.coe_le_coe.2 (slope_le_critSpeedOn t x hp)).trans h
  · intro h
    have : critSpeedOn t x S ≤ ⟨c, hc⟩ :=
      Finset.sup_le fun p hp => (NNReal.coe_le_coe (r₂ := ⟨c, hc⟩)).1 (h p hp)
    exact NNReal.coe_le_coe.2 this

/-- **E1b (admissible set).** For `0 ≤ c` and distinct times: every chord in `S` is `c`-causal
⇔ `c*_S ≤ c`. So the admissible set of a table is `A = [c*, ∞)`. -/
theorem allCausalOn_iff {c : ℝ} (hc : 0 ≤ c) {t : ι → ℝ} (ht : Function.Injective t)
    (x : ι → State) (S : Finset (ι × ι)) :
    (∀ p ∈ S, IsCausal c (tableChord t x p.1 p.2)) ↔ (critSpeedOn t x S : ℝ) ≤ c := by
  rw [critSpeedOn_le_iff hc]
  exact forall₂_congr fun p _ => isCausal_tableChord_iff hc ht x p.1 p.2

/-- E1b at `c = c*_S` itself: every chord in `S` is causal for the table's own cone (D-015). -/
theorem allCausalOn_critSpeedOn {t : ι → ℝ} (ht : Function.Injective t) (x : ι → State)
    (S : Finset (ι × ι)) : ∀ p ∈ S, IsCausal (critSpeedOn t x S) (tableChord t x p.1 p.2) :=
  (allCausalOn_iff (critSpeedOn t x S).coe_nonneg ht x S).2 le_rfl

/-- **E1c (attained, lightlike).** If `S` is non-empty, some pair in `S` has slope exactly
`c*_S`, and its chord is lightlike for `c*_S`: the steepest pair lies on the table's cone. -/
theorem exists_isLightlike_critSpeedOn {t : ι → ℝ} (ht : Function.Injective t) (x : ι → State)
    {S : Finset (ι × ι)} (hS : S.Nonempty) :
    ∃ p ∈ S, slope t x p.1 p.2 = critSpeedOn t x S ∧
      IsLightlike (critSpeedOn t x S) (tableChord t x p.1 p.2) := by
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup S hS fun p : ι × ι => slope t x p.1 p.2
  refine ⟨p, hp, hmax.symm, ?_⟩
  rw [isLightlike_iff (critSpeedOn t x S).coe_nonneg]
  show ‖x p.2 - x p.1‖ = _ * |t p.2 - t p.1|
  rw [norm_eq_slope_mul ht, critSpeedOn, hmax]

/-- **E1d (timelike set).** For `0 ≤ c`, distinct times, `S` non-empty and without diagonal
pairs `(i, i)`: every chord in `S` is `c`-timelike ⇔ `c*_S < c`. So `A° = (c*, ∞)` for data. -/
theorem allTimelikeOn_iff {c : ℝ} (hc : 0 ≤ c) {t : ι → ℝ} (ht : Function.Injective t)
    (x : ι → State) {S : Finset (ι × ι)} (hS : S.Nonempty) (hdiag : ∀ p ∈ S, p.1 ≠ p.2) :
    (∀ p ∈ S, IsTimelike c (tableChord t x p.1 p.2)) ↔ (critSpeedOn t x S : ℝ) < c := by
  have hpos : ∀ p ∈ S, 0 < |t p.2 - t p.1| := fun p hp =>
    abs_pos.mpr (sub_ne_zero.mpr (ht.ne (hdiag p hp).symm))
  constructor
  · intro h
    obtain ⟨p, hp, hsl, hlight⟩ := exists_isLightlike_critSpeedOn ht x hS
    have h1 := (isTimelike_iff hc _).1 (h p hp)
    rw [isLightlike_iff (critSpeedOn t x S).coe_nonneg] at hlight
    rw [hlight] at h1
    exact lt_of_mul_lt_mul_right h1 (abs_nonneg _)
  · intro h p hp
    rw [isTimelike_iff hc]
    show ‖x p.2 - x p.1‖ < c * |t p.2 - t p.1|
    rw [norm_eq_slope_mul ht]
    exact mul_lt_mul_of_pos_right
      (lt_of_le_of_lt (NNReal.coe_le_coe.2 (slope_le_critSpeedOn t x hp)) h) (hpos p hp)

/-- Uniform motion sampled at distinct times: every chord slope is `‖v‖` (or `0` on the
diagonal), so every chord is causal at `‖v‖`. -/
theorem isCausal_tableChord_smul (t : ι → ℝ) (v : State) (i j : ι) :
    IsCausal ‖v‖ (tableChord t (fun k => t k • v) i j) := by
  rw [isCausal_iff (norm_nonneg v)]
  simp only [tableChord, ← sub_smul, norm_smul, Real.norm_eq_abs, mul_comm, le_refl]

/-- D-014 for E1b: three samples of uniform motion at times `0, 1, 2` have `c* ≤ ‖v‖`. -/
example (v : State) :
    (critSpeed (fun k : Fin 3 => (k : ℝ)) (fun k => (k : ℝ) • v) : ℝ) ≤ ‖v‖ :=
  (allCausalOn_iff (norm_nonneg v) (Nat.cast_injective.comp Fin.val_injective) _ _).1
    fun p _ => isCausal_tableChord_smul (fun k : Fin 3 => (k : ℝ)) v p.1 p.2

/-- D-014 for E1c: the same table is non-empty, so its steepest chord is lightlike. -/
example (v : State) :
    ∃ p ∈ (Finset.univ : Finset (Fin 3 × Fin 3)),
      IsLightlike (critSpeed (fun k : Fin 3 => (k : ℝ)) (fun k => (k : ℝ) • v))
        (tableChord (fun k : Fin 3 => (k : ℝ)) (fun k => (k : ℝ) • v) p.1 p.2) := by
  obtain ⟨p, hp, -, h⟩ := exists_isLightlike_critSpeedOn
    (Nat.cast_injective.comp Fin.val_injective) (fun k : Fin 3 => (k : ℝ) • v)
    Finset.univ_nonempty
  exact ⟨p, hp, h⟩

/-- D-014 for E1d: the single pair `(0, 1)` of that table is timelike at `‖v‖ + 1`. -/
example (v : State) :
    ∀ p ∈ ({((0 : Fin 3), (1 : Fin 3))} : Finset (Fin 3 × Fin 3)),
      IsTimelike (‖v‖ + 1) (tableChord (fun k : Fin 3 => (k : ℝ)) (fun k => (k : ℝ) • v) p.1 p.2) := by
  refine (allTimelikeOn_iff (by positivity) (Nat.cast_injective.comp Fin.val_injective) _
    (Finset.singleton_nonempty _) (by simp)).2 ?_
  have := (allCausalOn_iff (norm_nonneg v) (Nat.cast_injective.comp Fin.val_injective)
    (fun k : Fin 3 => (k : ℝ) • v) {((0 : Fin 3), (1 : Fin 3))}).1
    fun p _ => isCausal_tableChord_smul (fun k : Fin 3 => (k : ℝ)) v p.1 p.2
  linarith

/-! ### T10: largest step = largest chord -/

/-- Steps of a table satisfy the speed bound, so chords from `i` forward do (the induction of
T10, in norm form). Increasing times make every `|Δt|` a plain `Δt`, and durations add. -/
theorem norm_sub_le_of_steps {c : ℝ} {t : ℤ → ℝ} {x : ℤ → State} {i b : ℤ}
    (hsteps : ∀ k, i ≤ k → k < b → ‖x (k + 1) - x k‖ ≤ c * (t (k + 1) - t k)) :
    ∀ j, i ≤ j → j ≤ b → ‖x j - x i‖ ≤ c * (t j - t i) := by
  -- induction on the number of steps n, with j = i + n
  have hn : ∀ n : ℕ, i + n ≤ b → ‖x (i + n) - x i‖ ≤ c * (t (i + n) - t i) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hnb
      have h1 := ih (by omega)
      have h2 := hsteps (i + n) (by omega) (by omega)
      push_cast
      rw [← add_assoc]
      calc ‖x (i + n + 1) - x i‖ ≤ ‖x (i + n + 1) - x (i + n)‖ + ‖x (i + n) - x i‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ c * (t (i + n + 1) - t (i + n)) + c * (t (i + n) - t i) := add_le_add h2 h1
        _ = c * (t (i + n + 1) - t i) := by ring
  intro j hij hjb
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = i + n := ⟨(j - i).toNat, by omega⟩
  exact hn n hjb

/-- `Q_c` of a chord does not depend on its direction: the reversed chord is `−p`. -/
theorem minkowskiQ_tableChord_symm (c : ℝ) (t : ι → ℝ) (x : ι → State) (i j : ι) :
    minkowskiQ c (tableChord t x j i) = minkowskiQ c (tableChord t x i j) := by
  simp only [minkowskiQ, tableChord]
  rw [← neg_sub (t j), ← neg_sub (x j), norm_neg, neg_sq]

/-- **T10 (causal form).** For `0 ≤ c` and strictly increasing times: if every consecutive step
`(k, k + 1)` in the window `[a, b]` is `c`-causal, then every chord `(i, j)` in the window is
`c`-causal. A chain of causal steps is causal. (The converse is trivial: steps are chords.) -/
theorem allCausal_window_of_steps {c : ℝ} (hc : 0 ≤ c) {t : ℤ → ℝ} (ht : StrictMono t)
    (x : ℤ → State) {a b : ℤ}
    (hsteps : ∀ k, a ≤ k → k < b → IsCausal c (tableChord t x k (k + 1))) :
    ∀ i j, a ≤ i → i ≤ b → a ≤ j → j ≤ b → IsCausal c (tableChord t x i j) := by
  -- forward chords first
  have fwd : ∀ i j, a ≤ i → i ≤ j → j ≤ b → IsCausal c (tableChord t x i j) := by
    intro i j hai hij hjb
    rw [isCausal_iff hc]
    show ‖x j - x i‖ ≤ c * |t j - t i|
    rw [abs_of_nonneg (sub_nonneg.2 (ht.monotone hij))]
    refine norm_sub_le_of_steps (fun k hik hkb => ?_) j hij hjb
    have h := (isCausal_iff hc _).1 (hsteps k (hai.trans hik) hkb)
    change ‖x (k + 1) - x k‖ ≤ c * |t (k + 1) - t k| at h
    rwa [abs_of_pos (sub_pos.2 (ht (lt_add_one k)))] at h
  intro i j hai hib haj hjb
  rcases le_total i j with hij | hji
  · exact fwd i j hai hij hjb
  · unfold IsCausal
    rw [← minkowskiQ_tableChord_symm]
    exact fwd j i haj hji hib

/-- All ordered pairs of indices in the window `[a, b]`. -/
def windowPairs (a b : ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc a b ×ˢ Finset.Icc a b

/-- The pairs exactly `m` indices apart inside the window `[a, b]`: `(k, k + m)`, `a ≤ k ≤ b − m`.
On a regular grid `tₙ = nΔt` these are the pairs at lag `mΔt`; `m = 1` gives the steps. -/
def lagPairs (m a b : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc a (b - m)).image fun k => (k, k + m)

theorem mem_lagPairs {m a b : ℤ} {p : ℤ × ℤ} :
    p ∈ lagPairs m a b ↔ a ≤ p.1 ∧ p.1 ≤ b - m ∧ p.2 = p.1 + m := by
  constructor
  · rintro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
    simpa using Finset.mem_Icc.1 hk
  · rintro ⟨h1, h2, h3⟩
    exact Finset.mem_image.2 ⟨p.1, Finset.mem_Icc.2 ⟨h1, h2⟩, Prod.ext rfl h3.symm⟩

/-- For `0 ≤ m`, the lag-`m` pairs of a window are pairs of that window. -/
theorem lagPairs_subset_windowPairs {m : ℤ} (hm : 0 ≤ m) (a b : ℤ) :
    lagPairs m a b ⊆ windowPairs a b := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := mem_lagPairs.1 hp
  simp only [windowPairs, Finset.mem_product, Finset.mem_Icc]
  omega

/-- **T10 (c* form).** Over a window, the c* of all pairs equals the c* of the consecutive
steps. One pass over the steps computes the largest chord slope exactly (d1_results P2). -/
theorem critSpeedOn_windowPairs {t : ℤ → ℝ} (ht : StrictMono t) (x : ℤ → State) (a b : ℤ) :
    critSpeedOn t x (windowPairs a b) = critSpeedOn t x (lagPairs 1 a b) := by
  refine le_antisymm ?_ (Finset.sup_mono (lagPairs_subset_windowPairs zero_le_one a b))
  set c := critSpeedOn t x (lagPairs 1 a b)
  have hsteps := allCausalOn_critSpeedOn ht.injective x (lagPairs 1 a b)
  rw [← NNReal.coe_le_coe, ← allCausalOn_iff c.coe_nonneg ht.injective]
  rintro ⟨i, j⟩ hp
  simp only [windowPairs, Finset.mem_product, Finset.mem_Icc] at hp
  refine allCausal_window_of_steps c.coe_nonneg ht x (fun k hak hkb => ?_) i j
    hp.1.1 hp.1.2 hp.2.1 hp.2.2
  exact hsteps (k, k + 1) (mem_lagPairs.2 ⟨hak, by omega, rfl⟩)

/-- **T10b (lag multiples).** On complete data (every index present) with strictly increasing
times, the largest slope over pairs `m ≥ 0` indices apart is at most the largest step slope.
On a regular grid `tₙ = nΔt`: `c*_{mΔt} ≤ c*_{Δt}`. (Data with gaps are not covered: there a
pair `mΔt` apart may exist without the steps between its samples.) -/
theorem critSpeedOn_lagPairs_le {t : ℤ → ℝ} (ht : StrictMono t) (x : ℤ → State) {m : ℤ}
    (hm : 0 ≤ m) (a b : ℤ) :
    critSpeedOn t x (lagPairs m a b) ≤ critSpeedOn t x (lagPairs 1 a b) := by
  rw [← critSpeedOn_windowPairs ht]
  exact Finset.sup_mono (lagPairs_subset_windowPairs hm a b)

/-- A regular grid `tₙ = nΔt` with `Δt > 0` is strictly increasing. -/
theorem strictMono_grid {Δt : ℝ} (hΔt : 0 < Δt) : StrictMono fun n : ℤ => (n : ℝ) * Δt :=
  fun _ _ h => mul_lt_mul_of_pos_right (Int.cast_lt.2 h) hΔt

/-- D-014 for T10 (causal form): uniform motion on a regular grid has causal steps at `‖v‖`,
so all chords of any window are causal at `‖v‖`. -/
example (v : State) {Δt : ℝ} (hΔt : 0 < Δt) (a b : ℤ) :
    ∀ i j, a ≤ i → i ≤ b → a ≤ j → j ≤ b →
      IsCausal ‖v‖ (tableChord (fun n : ℤ => (n : ℝ) * Δt) (fun n => ((n : ℝ) * Δt) • v) i j) :=
  allCausal_window_of_steps (norm_nonneg v) (strictMono_grid hΔt) _
    fun k _ _ => isCausal_tableChord_smul _ v k (k + 1)

/-- D-014 for T10b: on the one-minute grid, any record has `c*` at lag 60 at most its `c*` at
lag 1 (here the window `[0, 1440]`, one day of minutes). -/
example (x : ℤ → State) :
    critSpeedOn (fun n : ℤ => (n : ℝ) * 1) x (lagPairs 60 0 1440)
      ≤ critSpeedOn (fun n : ℤ => (n : ℝ) * 1) x (lagPairs 1 0 1440) :=
  critSpeedOn_lagPairs_le (strictMono_grid one_pos) x (by norm_num) 0 1440

/-! ### T13: comparing two rules -/

/-- **T13 (pairwise core).** Two tables on the same time stamps, with `‖x′ᵢ − xᵢ‖ ≤ δ` for
every sample: the slopes of a pair differ by at most `2δ / |t j − t i|`. -/
theorem abs_slope_sub_le (t : ι → ℝ) {x x' : ι → State} {δ : ℝ}
    (hδ : ∀ i, ‖x' i - x i‖ ≤ δ) (i j : ι) :
    |(slope t x' i j : ℝ) - slope t x i j| ≤ 2 * δ / |t j - t i| := by
  have e : ‖x' j - x' i‖ / |t j - t i| - ‖x j - x i‖ / |t j - t i|
      = (‖x' j - x' i‖ - ‖x j - x i‖) / |t j - t i| := by ring
  simp only [coe_slope]
  rw [e, abs_div, abs_abs]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  calc |‖x' j - x' i‖ - ‖x j - x i‖| ≤ ‖(x' j - x' i) - (x j - x i)‖ := abs_norm_sub_norm_le _ _
    _ = ‖(x' j - x j) - (x' i - x i)‖ := by congr 1; abel
    _ ≤ ‖x' j - x j‖ + ‖x' i - x i‖ := norm_sub_le _ _
    _ ≤ δ + δ := add_le_add (hδ j) (hδ i)
    _ = 2 * δ := by ring

/-- **T13.** Two tables on the same time stamps, `‖x′ᵢ − xᵢ‖ ≤ δ` for every sample, and a set
`S` of pairs whose time gaps are all `≥ h > 0`: `|c*_S(x′) − c*_S(x)| ≤ 2δ/h`. A maximum moves
by at most the largest change of its terms. (`0 ≤ δ` is needed only for an empty table, where
the other hypothesis says nothing about `δ`.) -/
theorem abs_critSpeedOn_sub_le (t : ι → ℝ) {x x' : ι → State} {δ h : ℝ} (hh : 0 < h)
    (hδ0 : 0 ≤ δ) (hδ : ∀ i, ‖x' i - x i‖ ≤ δ) {S : Finset (ι × ι)} (hS : ∀ p ∈ S, h ≤ |t p.2 - t p.1|) :
    |(critSpeedOn t x' S : ℝ) - critSpeedOn t x S| ≤ 2 * δ / h := by
  have hε : 0 ≤ 2 * δ / h := by positivity
  rcases S.eq_empty_or_nonempty with rfl | -
  · simpa [critSpeedOn] using hε
  · -- non-empty S
    -- each slope moves by at most 2δ/h
    have hpair : ∀ p ∈ S, |(slope t x' p.1 p.2 : ℝ) - slope t x p.1 p.2| ≤ 2 * δ / h :=
      fun p hp => (abs_slope_sub_le t hδ p.1 p.2).trans
        (div_le_div_of_nonneg_left (by positivity) hh (hS p hp))
    -- one direction for each pair of tables
    have key : ∀ y y' : ι → State,
        (∀ p ∈ S, |(slope t y' p.1 p.2 : ℝ) - slope t y p.1 p.2| ≤ 2 * δ / h) →
        (critSpeedOn t y' S : ℝ) ≤ critSpeedOn t y S + 2 * δ / h := by
      intro y y' hyy
      rw [critSpeedOn_le_iff (by positivity)]
      intro p hp
      have h1 := (abs_le.1 (hyy p hp)).2
      have h2 := NNReal.coe_le_coe.2 (slope_le_critSpeedOn t y hp)
      linarith
    rw [abs_le]
    constructor
    · have := key x' x fun p hp => by rw [abs_sub_comm]; exact hpair p hp
      linarith
    · have := key x x' hpair
      linarith

/-- D-014 for T13: shifting every sample of a table by a fixed vector `w` with `‖w‖ ≤ δ`
(a rule that differs by a constant offset) moves c* at lag `h = 1` by at most `2δ`. -/
example (x : ℤ → State) (w : State) {δ : ℝ} (hw : ‖w‖ ≤ δ) (a b : ℤ) :
    |(critSpeedOn (fun n : ℤ => (n : ℝ)) (fun n => x n + w) (lagPairs 1 a b) : ℝ)
      - critSpeedOn (fun n : ℤ => (n : ℝ)) x (lagPairs 1 a b)| ≤ 2 * δ / 1 := by
  refine abs_critSpeedOn_sub_le _ one_pos ((norm_nonneg w).trans hw) (fun i => by simpa using hw) fun p hp => ?_
  obtain ⟨-, -, h3⟩ := mem_lagPairs.1 hp
  simp [h3]

end GeneralizedC
