/- Axiom audit: run `lake env lean Axioms.lean`. Every proved theorem should list only
   propext, Classical.choice, Quot.sound (no `sorryAx`). -/
import GeneralizedC

open GeneralizedC

-- CP1
#print axioms isTimelike_iff                        -- T1a
#print axioms allChordsTimelike_of_lipschitzWith    -- T1
-- CP2
#print axioms isCausal_iff                          -- T1b
#print axioms lipschitzWith_iff_allChordsCausal     -- T2c
#print axioms lipschitzWith_of_allChordsTimelike    -- T2
#print axioms AllChordsTimelike.mono                -- T2a
#print axioms AllChordsCausal.mono                  -- T2a
#print axioms allChordsTimelike_rescale_iff         -- T2b
#print axioms allChordsCausal_rescale_iff           -- T2b
#print axioms hyperbolic_gap                        -- T3
#print axioms not_allChordsCausal_of_unbounded      -- T4
#print axioms not_allChordsTimelike_of_unbounded    -- T4
#print axioms exists_timelike_of_finite             -- T5
-- CP3
#print axioms boostTime_strictMono_surjective       -- T6
#print axioms boostTime_of_allChordsCausal          -- T6
#print axioms boostTime_of_allChordsTimelike        -- T6
#print axioms boostTime_uniformMotion_self          -- T6 (A2)
#print axioms boostedStamps_uniform_iff             -- T7
#print axioms minkowskiQF_apply                     -- T8
#print axioms minkowskiQF_equivalent                -- T8
#print axioms sigPos_minkowskiQF                    -- T8
#print axioms sigNeg_minkowskiQF                    -- T8
#print axioms radical_minkowskiQF                   -- T8
#print axioms radical_minkowskiQF_zero_ne_bot       -- T8 (c = 0)
#print axioms minkowskiQG_gauge                     -- T9a
#print axioms minkowskiQ_one_gaugeD                 -- T9b
#print axioms mem_lorentzGroupG_iff                 -- T9c
#print axioms allChordsTimelikeG_iff                -- T9d
#print axioms allChordsCausalG_iff                  -- T9d
-- CP4
#print axioms slope_le_critSpeedOn                  -- E1a
#print axioms allCausalOn_iff                       -- E1b
#print axioms exists_isLightlike_critSpeedOn        -- E1c
#print axioms allTimelikeOn_iff                     -- E1d
#print axioms isLightlike_iff                       -- E1 (bridge A3)
#print axioms allCausal_window_of_steps             -- T10
#print axioms critSpeedOn_windowPairs               -- T10 (c* form)
#print axioms critSpeedOn_lagPairs_le               -- T10b
#print axioms abs_slope_sub_le                      -- T13 (pairwise)
#print axioms abs_critSpeedOn_sub_le                -- T13
#print axioms isCausal_frame_iff                    -- T14a
#print axioms isTimelike_frame_iff                  -- T14a
#print axioms isLightlike_frame_iff                 -- T14a
#print axioms frameTime_injective                   -- T14b
#print axioms critSpeed_frame                       -- T14
#print axioms critSpeed_frame_G                     -- T14 (diagonal G)
#print axioms rapidityBoost_mem                     -- T14 (C7 boost)
-- CP5
#print axioms secondMoment_map                      -- N1a (i)
#print axioms mahal_conj                            -- N1a (ii)
#print axioms mahal_secondMoment_map                -- N1a (iii)
#print axioms mean_mahal_secondMoment               -- N1c (i)
#print axioms exists_le_mahal                       -- N1c (ii)
#print axioms mahal_eq_of_le                        -- N1c (iii)
#print axioms minkowskiQM_eq                        -- N1b-i
#print axioms minkowskiQM_diagonal                  -- N1b-i (diagonal = T9)
#print axioms allChordsCausalM_iff                  -- N1b-i
#print axioms allChordsTimelikeM_iff                -- N1b-i
#print axioms mem_formGroupM_iff                    -- N1b-ii
#print axioms exists_factor_of_posDef               -- N1b-iii
#print axioms slope_tick_eq_mahal                   -- N1b-iv
#print axioms mahal_le_tickCritSpeed                -- N1b-iv
#print axioms exists_mahal_eq_tickCritSpeed         -- N1b-iv
#print axioms tickCritSpeed_eq_windowPairs          -- N1b-iv (T10)
#print axioms critSpeedOn_smul                      -- T15a
#print axioms critSpeedOn_normalize                 -- T15a
#print axioms isCausal_normalize_iff                -- T15b
#print axioms isTimelike_normalize_iff              -- T15b
#print axioms isLightlike_normalize_iff             -- T15b
#print axioms mem_formGroup_iff_normalized          -- T15c
#print axioms critSpeed_frame_normalized            -- T15d
-- CP5b
#print axioms secondMoment_posSemidef               -- N1c′ (i)
#print axioms secondMoment_posDef_iff_span          -- N1c′ (ii)
#print axioms isUnit_det_secondMoment_iff_span      -- N1c′ (iii)
#print axioms isUnit_det_secondMoment_iff_covers    -- N1c′ (iii, orthogonal form)
#print axioms covers_iff_span_eq_top                -- N1c′ (covers ⇔ span)
#print axioms mahal_secondMoment_le_card            -- N1d
#print axioms sqrt_three_le_tickCritSpeed           -- N1e (i)
#print axioms mahal_eq_three_of_tickCritSpeed_eq    -- N1e (ii)
#print axioms tickCritSpeed_le_sqrt_card            -- N1e (iii)
#print axioms tickCritSpeed_pmWalk                  -- N1e (example: c° = √3)
#print axioms relMat_conj                           -- N1f
#print axioms charpoly_relMat_conj                  -- N1f
#print axioms trace_relMat_conj                     -- N1f
-- CP5b, N1g (helix)
#print axioms helix_secondMoment                    -- N1g (a)
#print axioms helix_mahal_eq_three                  -- N1g (b)
#print axioms helix_tickCritSpeed                   -- N1g (b)
#print axioms helix_exists_unit                     -- N1g (b)
#print axioms helix_decimate                        -- N1g (c)
#print axioms helix_decimate_tickCritSpeed          -- N1g (c)
#print axioms helix_not_isUnit                      -- N1g (d)
-- P1 (kinematic result, LorentzC.lean)
#print axioms IsLorentzC.unique                     -- IsLorentzC: uniqueness
#print axioms isLorentzC_iff                        -- K1 (c = c° for every L)
#print axioms existsUnique_isLorentzC               -- K1 (∃!)
#print axioms IsLorentzC.isCausalM_chord            -- K2 (all chords c-causal)
#print axioms IsLorentzC.exists_lightlike_step      -- K2 (one step lightlike)
#print axioms IsLorentzC.bounds                     -- K3
#print axioms isLorentzC_map                        -- K4
#print axioms IsLorentzC.natural                    -- K5
#print axioms IsSystemLorentzC.unique               -- IsSystemLorentzC: uniqueness
#print axioms isLorentzC_helix                      -- K6 (one window)
#print axioms helix_isSystemLorentzC                -- K6
#print axioms helix_not_isLorentzC                  -- K7
#print axioms not_isSystemLorentzC_of_aliased       -- K7 (system)
#print axioms isLorentzC_pmWalk                     -- example: walk, c = √3
