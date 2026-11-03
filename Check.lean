import Tournament

set_option pp.universes true

-- thm:intro-char
#check Tournament.Correspondence.MainLower.introductory_characterization
#print axioms Tournament.Correspondence.MainLower.introductory_characterization

-- def:revealing
#check Tournament.StronglyRevealing
#print axioms Tournament.StronglyRevealing

-- lem:structure
#check Tournament.Correspondence.MainLower.graph_structure
#print axioms Tournament.Correspondence.MainLower.graph_structure

-- prop:graph
#check Tournament.Correspondence.MainLower.reduction_to_observable_comparisons
#print axioms Tournament.Correspondence.MainLower.reduction_to_observable_comparisons
#check Tournament.Computation.GraphPreparation.specification
#print axioms Tournament.Computation.GraphPreparation.specification

-- thm:characterization
#check Tournament.Characterization.characterization
#print axioms Tournament.Characterization.characterization

-- lem:ew
#check Tournament.Upper.ExponentialWeights.second_order_pairings
#print axioms Tournament.Upper.ExponentialWeights.second_order_pairings

-- def:holding-family
#check Tournament.HoldingFamily
#print axioms Tournament.HoldingFamily
#check Tournament.HoldingFamily.ratio
#print axioms Tournament.HoldingFamily.ratio
#check Tournament.HoldingFamily.refreshRate
#print axioms Tournament.HoldingFamily.refreshRate
#check Tournament.HoldingFamily.kernel
#print axioms Tournament.HoldingFamily.kernel

-- lem:holding-chains
#check Tournament.Correspondence.holding_chains
#print axioms Tournament.Correspondence.holding_chains

-- def:assignment
#check Tournament.Upper.ComparisonAssignment
#print axioms Tournament.Upper.ComparisonAssignment
#check Tournament.Upper.ComparisonAssignment.totalWeight
#print axioms Tournament.Upper.ComparisonAssignment.totalWeight
#check Tournament.Upper.ComparisonAssignment.sourceLaw
#print axioms Tournament.Upper.ComparisonAssignment.sourceLaw

-- thm:main
#check Tournament.Upper.tournamentPrivateStrategy_bound
#print axioms Tournament.Upper.tournamentPrivateStrategy_bound
#check Tournament.Correspondence.effective_tournament_upper_finite
#print axioms Tournament.Correspondence.effective_tournament_upper_finite
#check Tournament.Computation.FiniteTournamentProgram.tournamentProgram_bound_finite
#print axioms Tournament.Computation.FiniteTournamentProgram.tournamentProgram_bound_finite
#check Tournament.Computation.FiniteProgramHorizon.tournamentProgram_observes
#print axioms Tournament.Computation.FiniteProgramHorizon.tournamentProgram_observes

-- prop:self-financing
#check Tournament.Upper.ExponentialWeights.self_financing_regret_extended
#print axioms Tournament.Upper.ExponentialWeights.self_financing_regret_extended

-- prop:block
#check Tournament.Upper.prepared_block_guarantee
#print axioms Tournament.Upper.prepared_block_guarantee

-- cor:fixed-rate
#check Tournament.Upper.SteeringParameters.feedback_fixed_rate
#print axioms Tournament.Upper.SteeringParameters.feedback_fixed_rate

-- lem:spectral
#check Tournament.Correspondence.spectral_structure
#print axioms Tournament.Correspondence.spectral_structure

-- def:score-rule
#check Tournament.Upper.ScoreRule
#print axioms Tournament.Upper.ScoreRule
#check Tournament.Upper.ScoreRule.decoder_realization
#print axioms Tournament.Upper.ScoreRule.decoder_realization

-- lem:tournament-scores
#check Tournament.Upper.tournament_scores_form_scoreRule
#print axioms Tournament.Upper.tournament_scores_form_scoreRule

-- def:balanced
#check Tournament.Upper.BalancedEstimator
#print axioms Tournament.Upper.BalancedEstimator

-- lem:rooted-assignment
#check Tournament.Upper.rooted_assignment_optimum
#print axioms Tournament.Upper.rooted_assignment_optimum

-- lem:balanced-estimator
#check Tournament.Upper.ComparisonAssignment.balanced_estimator_from_assignment
#print axioms Tournament.Upper.ComparisonAssignment.balanced_estimator_from_assignment

-- lem:probing
#check Tournament.Upper.ScoreRule.steering_and_estimation_on_chunk
#print axioms Tournament.Upper.ScoreRule.steering_and_estimation_on_chunk

-- cor:probing-block
#check Tournament.Upper.probing_block
#print axioms Tournament.Upper.probing_block

-- lem:energy
#check Tournament.Upper.estimation_paid_by_steering
#print axioms Tournament.Upper.estimation_paid_by_steering

-- lem:tails
#check Tournament.Correspondence.score_and_estimate_tails
#print axioms Tournament.Correspondence.score_and_estimate_tails

-- lem:sdb
#check Tournament.Upper.ShrinkingDartboard.shrinking_dartboard_before
#print axioms Tournament.Upper.ShrinkingDartboard.shrinking_dartboard_before
#check Tournament.Upper.ShrinkingDartboard.shrinking_dartboard_general
#print axioms Tournament.Upper.ShrinkingDartboard.shrinking_dartboard_general

-- thm:explore
#check Tournament.Upper.Exploration.observable_graph_lazy_exploration
#print axioms Tournament.Upper.Exploration.observable_graph_lazy_exploration
#check Tournament.Upper.Exploration.observable_graph_large_rate_finite
#print axioms Tournament.Upper.Exploration.observable_graph_large_rate_finite

-- thm:lower
#check Tournament.Lower.lower_bound
#print axioms Tournament.Lower.lower_bound

-- lem:few-observers
#check Tournament.few_observers
#print axioms Tournament.few_observers

-- cor:domination
#check Tournament.Lower.Domination.minimax_lower_bound_explicit
#print axioms Tournament.Lower.Domination.minimax_lower_bound_explicit

-- lem:missed-advantage
#check Tournament.Upper.GeometricProbing.expected_missed_advantage
#print axioms Tournament.Upper.GeometricProbing.expected_missed_advantage

-- thm:breakeven
#check Tournament.Upper.GeometricProbing.geometric_probing
#print axioms Tournament.Upper.GeometricProbing.geometric_probing
#check Tournament.Upper.GeometricProbing.tuned_geometric_probing
#print axioms Tournament.Upper.GeometricProbing.tuned_geometric_probing

-- lem:occupation
#check Tournament.FilteredMoments.accumulated_quantities_finite_horizon
#print axioms Tournament.FilteredMoments.accumulated_quantities_finite_horizon

-- lem:occupation-potentials
#check Tournament.Correspondence.occupation_potentials
#print axioms Tournament.Correspondence.occupation_potentials
#check Tournament.Upper.ScoreRule.untruncated_chunk_absoluteScores_lintegral_le
#print axioms Tournament.Upper.ScoreRule.untruncated_chunk_absoluteScores_lintegral_le
#check Tournament.Upper.ScoreRule.untruncated_chunk_absoluteScores_integrable
#print axioms Tournament.Upper.ScoreRule.untruncated_chunk_absoluteScores_integrable

-- lem:partition
#check Tournament.Correspondence.geometric_partition
#print axioms Tournament.Correspondence.geometric_partition

-- lem:reference-bound
#check Tournament.Upper.reference_errors_paid_by_energy
#print axioms Tournament.Upper.reference_errors_paid_by_energy

-- lem:rate-comparison
#check Tournament.Upper.dyadic_rate_comparison_integer
#print axioms Tournament.Upper.dyadic_rate_comparison_integer

-- lem:band-errors
#check Tournament.Upper.errors_caused_by_one_band
#print axioms Tournament.Upper.errors_caused_by_one_band

-- lem:dyadic
#check Tournament.Correspondence.MainLower.depth_and_congestion
#print axioms Tournament.Correspondence.MainLower.depth_and_congestion

-- lem:clip
#check Tournament.Correspondence.MainLower.clipping_error
#print axioms Tournament.Correspondence.MainLower.clipping_error

-- lem:lower-regret
#check Tournament.Correspondence.MainLower.regret
#print axioms Tournament.Correspondence.MainLower.regret

-- lem:reconstruct
#check Tournament.Correspondence.MainLower.reconstruction
#print axioms Tournament.Correspondence.MainLower.reconstruction

-- lem:lower-kl
#check Tournament.Lower.lower_kl_real
#print axioms Tournament.Lower.lower_kl_real
#check Tournament.Lower.lower_kl_toReal_real
#print axioms Tournament.Lower.lower_kl_toReal_real

-- prop:bayes
#check Tournament.Lower.bayes_regret_real
#print axioms Tournament.Lower.bayes_regret_real
