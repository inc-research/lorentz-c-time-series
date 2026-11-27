/-
GeneralizedC/Basic.lean: core definitions for the (1+3) time-series project.

Design decisions (see PROGRESS.md § Decisions):
  D-001  "timelike" is defined through the Minkowski form Q_c, not through speeds.
  D-002  worldlines are defined on all of ℝ.
  D-003  the state metric G is the identity (EuclideanSpace) until T9 proves the reduction.
  D-015  the primary admissibility notion is *causal* (closed cone, Q_c ≥ 0); *timelike*
         (open cone, Q_c > 0) is kept as the "massive" sub-notion.
-/
-- Targeted imports, not `import Mathlib` (D-009): Mathlib's full closure is ~1.9 GB of .olean
-- files, and Lean's load time is dominated by memory and disk I/O (PROGRESS F-002, F-003).
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.EMetricSpace.Lipschitz

open NNReal

namespace GeneralizedC

/-- State space ℝ³ with the Euclidean (L²) norm. (G = I, D-003.)
Note: the plain type `Fin 3 → ℝ` would carry the *sup* norm in Mathlib; see t1a_breakdown A6. -/
abbrev State := EuclideanSpace ℝ (Fin 3)

/-- The generalized Minkowski form on event displacements (Δt, Δx):
`Q_c(Δt, Δx) = c²Δt² − ‖Δx‖²`. A plain function for now; T8 upgrades it to a `QuadraticForm`.
`noncomputable`: real numbers (and hence the Euclidean norm) cannot be evaluated by running code,
so Lean asks us to mark definitions that use them. This changes nothing about what we can prove. -/
noncomputable def minkowskiQ (c : ℝ) (p : ℝ × State) : ℝ :=
  c ^ 2 * p.1 ^ 2 - ‖p.2‖ ^ 2

/-- A displacement is strictly timelike when `Q_c` is positive (D-001). -/
def IsTimelike (c : ℝ) (p : ℝ × State) : Prop :=
  0 < minkowskiQ c p

/-- The chord of the worldline `x` from time `s` to time `t`: the event displacement
`(t − s, x t − x s)`. -/
def chord (x : ℝ → State) (s t : ℝ) : ℝ × State :=
  (t - s, x t - x s)

/-- Every chord between distinct times is strictly timelike (domain ℝ, D-002). -/
def AllChordsTimelike (c : ℝ) (x : ℝ → State) : Prop :=
  ∀ s t, s ≠ t → IsTimelike c (chord x s t)

/-- A displacement is causal when `Q_c` is non-negative: timelike or lightlike (D-015). -/
def IsCausal (c : ℝ) (p : ℝ × State) : Prop :=
  0 ≤ minkowskiQ c p

/-- Every chord between distinct times is causal (D-015). The case `s = t` is excluded only to
match `AllChordsTimelike`; that chord is `(0, 0)`, which is causal anyway. -/
def AllChordsCausal (c : ℝ) (x : ℝ → State) : Prop :=
  ∀ s t, s ≠ t → IsCausal c (chord x s t)

/-- Uniform motion with constant velocity `v`: `x t = t • v`. Used in the non-vacuity
examples (D-014). -/
def uniformMotion (v : State) : ℝ → State :=
  fun t => t • v

end GeneralizedC
