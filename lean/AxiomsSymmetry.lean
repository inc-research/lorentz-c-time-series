/- Axiom audit for the P2 library `GeneralizedCSymmetry` (D-054 A7): run
   `lake env lean AxiomsSymmetry.lean`. Every proved theorem should list only
   propext, Classical.choice, Quot.sound (no `sorryAx`). The core audit is `Axioms.lean` (unchanged). -/
import GeneralizedCSymmetry

open GeneralizedC GeneralizedCSymmetry

-- P2-1a (β1)
#print axioms IsCrossSpeed.unique                   -- Y1 (uniqueness)
#print axioms exists_isCrossSpeed                   -- Y1 (existence)
#print axioms isCrossSpeed_self                     -- Y2
#print axioms isCrossSpeed_map                      -- Y3
#print axioms sharesCone_map                        -- Y3 (families)
#print axioms helix_sharesCone_rot                  -- Y4
#print axioms helix_isCrossSpeed_speed              -- Y5 (exact cross-speed)
#print axioms helix_crossSpeed_split                -- Y5 (U-split)
#print axioms helix_crossSpeed_cross                -- Y5 (U-cross)
#print axioms crossSpeed_decimate_le                -- Y6 (per A-tick: s ≤ m)
#print axioms helix_decimate_crossSpeed             -- Y6 (per count: s² ≥ m²/3)
#print axioms helix_decimate_crossSpeed_gt          -- Y6 (per count: s > 1 for |m| ≥ 2)
#print axioms trace_le_of_isCrossSpeed              -- mean ≤ max (Y8, Y9)
#print axioms trace_add_trace_inv                   -- tr Y + tr Y⁻¹ ≥ 2n (Y8, Y9)
#print axioms trace_relMat_add                      -- tr(P⁻¹Q) + tr(Q⁻¹P) ≥ 6 (Y8, Y9)
#print axioms crossSpeed_sq_add_ge                  -- Y8
#print axioms sharesCone_pair_iff                   -- Y9 (pair)
#print axioms sharesCone_iff_secondMoment_eq        -- Y9
-- P2-1b (Y7, Ignatowsky in 1+1)
#print axioms IsIgnatowskyFamily.zero_eq_one        -- Λ(0) = 1 (from I0, I4)
#print axioms IsIgnatowskyFamily.diag_eq            -- equal diagonal entries
#print axioms IsIgnatowskyFamily.K_nonneg           -- K ≥ 0 by iterating I4 (A5)
#print axioms IsIgnatowskyFamily.exists_K           -- Y7a
#print axioms ignatowskyT_mul                       -- Y7b (composition law)
#print axioms ignatowskyT_family                    -- Y7b (converse)
#print axioms ignatowskyT_fixes_speed_iff           -- Y7c (one frame)
#print axioms invariant_speed_iff                   -- Y7c
#print axioms invariant_speed_iff_of_pos            -- Y7c (K > 0: ±1/√K)
#print axioms not_invariant_speed_of_zero           -- Y7c (K = 0: none)
#print axioms IsIgnatowskyFamily.invariant_speed_iff -- Y7c for a family (β1 link)
-- P2-1c (D-060 follow-up, D-062)
#print axioms IsIgnatowskyFamily.existsUnique_K     -- Y7d
#print axioms IsIgnatowskyFamily.invariant_speed_iff' -- Y7e
