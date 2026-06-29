# Designing Optimal Binary Rating Systems

## Source Version

- Paper: *Designing Optimal Binary Rating Systems*
- Authors: Nikhil Garg, Ramesh Johari
- Version formalized: AISTATS 2019 / PMLR 89 version, 2019
- Official URL: https://proceedings.mlr.press/v89/garg19a.html
- Public PDF: https://proceedings.mlr.press/v89/garg19a/garg19a.pdf
- Supplement used for intake: https://proceedings.mlr.press/v89/garg19a/garg19a-supp.pdf
- ArXiv TeX checked for source audit: https://arxiv.org/e-print/1806.06908

The source PDF, supplement, and extracted text caches are local/ignored
artifacts. Do not commit them unless redistribution rights are checked
separately.
Use the local cache first when checking paper text during proof work:
`source/garg19a.pdf`, `source/garg19a.txt`, `source/garg19a-supp.pdf`, and
`source/garg19a-supp.txt`. The arXiv TeX cache, when present, lives under
`source_tex/arxiv_1806.06908` and is also ignored by Git.

## Current Status

Status: formalized.

The binary-rating theory from the AISTATS/PMLR paper and supplement is
Lean-checked. The formalization covers the finite Bernoulli large-deviation
rate formulas, Lemma 3.1 finite optimizer, Theorem 3.1 value/rate
decomposition, Lemma C.3 aggregation, Lemma C.4 rate characterization, Lemmas
C.5-C.12, Theorem 3.2 finite algorithmic certificates, Appendix B.1
subsequence convergence, Appendix B.2/B.3 learning wrappers, and the
Kendall/Spearman example branches.

Current stopping point: `lake build GJ19OptimalBinaryRatingSystems` passes.
Technical closeout notes in `POST_FORMALIZATION_AUDIT.md` and
`ADDITIONAL_ASSUMPTIONS_NEEDED.md` record proof-interface reducers used during
the final push; they are audit notes, not public status notes.

## Paper-Facing Ledger

- Implementation theorem file: `GJ19OptimalBinaryRatingSystems/MainTheorems.lean`
- Human-facing theorem file: `GJ19OptimalBinaryRatingSystems/PaperInterface.lean`
- Named assumption surface: `GJ19OptimalBinaryRatingSystems/Assumptions.lean`
- Machine-readable status source: `GJ19OptimalBinaryRatingSystems/status.json`
- Outside-Lean proof plan: `GJ19OptimalBinaryRatingSystems/FORMALIZATION_PLAN.md`
- Final validation report: `GJ19OptimalBinaryRatingSystems/FINAL_VALIDATION_REPORT.md`
- Detailed post-formalization audit: `GJ19OptimalBinaryRatingSystems/POST_FORMALIZATION_AUDIT.md`
- Dependency DAG: `GJ19OptimalBinaryRatingSystems/DependencyDAG.tex`

## Theorem Status

| Paper item | Lean declaration | Status | Remaining assumptions |
|---|---|---|---|
| Bernoulli KL and support-safe KL formulas | `definition_bernoulli_kl_formula`, `definition_bernoulli_kl_top_formula` | formalized | None |
| Theorem 3.1 adjacent binary-rate formula | `theorem31_adjacent_binary_rate_formula`, `theorem31_adjacent_binary_rate_top_formula` | formalized | None |
| Lemma 3.1 closed adjacent-rate expression | `lemma31_closed_adjacent_rate_formula`, `lemma31_closed_adjacent_rate_value_at_weighted_threshold` | formalized | None |
| Lemma 3.1 finite equalized-rate optimizer | `lemma31_forward_clipped_equalized_rates_exist_unique`, `lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn`, `lemma31_endpoint_aware_maximizer_iff_pairwise_equalized` | formalized | None |
| Finite adjacent objective exact-rate theorem | `finite_binary_adjacent_uniform_objective_exact_rate_from_endpoint_weighted_common_threshold`, `finite_binary_adjacent_uniform_objective_exact_rate_from_equalized_endpoint_levels`, `finite_binary_adjacent_uniform_objective_exact_rate_from_forward_clipped_levels`, `finite_binary_adjacent_weighted_objective_exact_rate_from_forward_clipped_levels` | formalized | None |
| Theorem 3.1 asymptotic-value bridge | `paper_theorem31_asymptotic_value_integral_tendsto_of_success_prob_tendsto_one` | formalized | None |
| Theorem 3.1 two-stage optimality logic | `paper_theorem31_two_stage_lexicographic_optimality` | formalized | None |
| Lemma C.5 doubled-chain construction | `lemmaC5_uniform_doubled_endpoint_levels_isEndpointLevelVector`, `lemmaC5_uniform_doubled_endpoint_levels_equalizes` | formalized | None |
| Corollary C.2 and Lemmas C.6-C.9 finite support bounds | `paper_corollaryC2_uniform_equalized_last_rate_tendsto_zero`, `paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero`, `lemmaC6_uniform_penultimate_level_ge_one_sub_inv_of_equalized_rates`, `lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objective`, `lemmaC8_uniform_first_level_ge_half_of_equalized_objective_rate_lower`, `lemmaC9_nested_bisection_operation_count_le_stepBound` | formalized | None |
| Theorem C.1 weighted Laplace skeleton | `paper_theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_weightedEssentialInf`, `paper_theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_nearRate_sets`, `paper_theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_pointwiseExponentialRateCertificate_nearRate_sets`, `paper_theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_weightedNearInf` | formalized | None |
| Lemma C.3 finite decomposition algebra | `paper_lemmaC3_finite_component_weighted_error_sum_hasExponentialRate_of_min_component`, `paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_certificates` | formalized | None |
| Lemma C.3 adjacent-dominance algebra | `paper_lemmaC3_selected_ordered_pair_weighted_error_sum_hasExponentialRate_of_adjacent_min`, `paper_lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos` | formalized | None |
| Lemma C.4 forward direction | `paper_lemmaC4_forward_clipped_endpoint_piecewise_constant_has_positive_exponential_rate`, `paper_lemmaC4_forward_clipped_endpoint_piecewiseConstKernel_has_positive_exponential_rate` | formalized | None |
| Lemma C.4 rate characterization | `paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_sourcePbar_selected_realization`, `paper_lemmaC4_appropriate_finite_levels_weighted_sourcePbarWbar_rate_certificate_of_selected_realization` | formalized | None |
| Lemma C.4 positive-support reverse branch | `paper_lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError`, `paper_lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError` | formalized | None |
| Theorem 3.1 fixed-discretization rate-optimal bridge | `paper_theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate_of_cell_midpoints`, `paper_theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints` | formalized | None |
| Theorem 3.2 finite certificate | `theorem32_exists_grid_depth_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos` | formalized | None |
| Lemma C.10 Spearman source reduction | `paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective` | formalized | None |
| Lemma C.11 Kendall objective | `paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced` | formalized | None |
| Lemma C.12 Spearman objective | `paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced` | formalized | None |
| Theorem B.1 Cauchy-completeness bridge | `paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh`, `paper_theoremB1_uniform_subsequence_principle_canonical_uniform_optimal_equispaced_floor_selector` | formalized | None |
| Corollary C.4 equispaced convergence bridge | `paper_corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity`, `paper_corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_optimal_equispaced_floor_selector` | formalized | None |
| Full Theorem 3.1 | `paper_theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints`, `paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_sourcePbar_selected_realization`, `paper_theorem31_exists_cell_integral_volume_weighted_uniform_endpoint_two_stage_lexicographic_optimality_of_integrableOn_Icc` | formalized | None |
| Appendix B convergence and learning lemmas | `paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh`, `paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking`, `paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking` | formalized | None |
| Spearman/Kendall example branch | `paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective`, `paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced`, `paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced`, `paper_corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_optimal_equispaced_floor_selector` | formalized | None |

## Validation

Last targeted check:

```bash
lake build GJ19OptimalBinaryRatingSystems
```

Result on 2026-06-28: passed.
