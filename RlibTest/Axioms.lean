module

import Rlib

#print axioms Rlib.probability_sum
#print axioms Rlib.integral_toMeasure_eq_expect
#print axioms Rlib.expect_const
#print axioms Rlib.expect_zero
#print axioms Rlib.expect_add
#print axioms Rlib.expect_mul
#print axioms Rlib.expect_mono
#print axioms Rlib.expect_pure
#print axioms Rlib.expect_bind
#print axioms Rlib.expect_map
#print axioms Rlib.norm_expect_sub_expect_le
#print axioms Rlib.sampleMean_const
#print axioms Rlib.sampleMean_add
#print axioms Rlib.sampleMean_mul
#print axioms Rlib.expect_empiricalPMF
#print axioms Rlib.empiricalPMF_apply_toReal
#print axioms Rlib.MDP.oneStepActionValue_ofSamples
#print axioms Rlib.MDP.oneStepActionValue_zero
#print axioms Rlib.MDP.isProbabilityMeasure_pathMeasure
#print axioms Rlib.MDP.map_prefix_pathMeasure
#print axioms Rlib.MDP.expectedReturn_zero
#print axioms Rlib.MDP.expectedReturn_succ
#print axioms Rlib.MDP.expectedReturn_eq_iterate
#print axioms Rlib.MDP.discountedReturn_prefix_eq_sum
#print axioms Rlib.MDP.summable_norm_discountedReward
#print axioms Rlib.MDP.tendsto_discountedReturn
#print axioms Rlib.MDP.norm_discountedReturn_le
#print axioms Rlib.MDP.norm_infiniteReturn_le
#print axioms Rlib.MDP.tendsto_expectedReturn
#print axioms Rlib.MDP.integrable_infiniteReturn
#print axioms Rlib.MDP.integral_infiniteReturn_eq_policyValue
#print axioms Rlib.MDP.oneStepActionValue_mono
#print axioms Rlib.MDP.oneStepValue_mono
#print axioms Rlib.MDP.norm_oneStepActionValue_sub_le
#print axioms Rlib.MDP.norm_oneStepValue_sub_le
#print axioms Rlib.MDP.oneStepValue_contractingWith
#print axioms Rlib.MDP.existsUnique_oneStepValue_fixedPoint
#print axioms Rlib.MDP.oneStepValue_policyValue
#print axioms Rlib.MDP.eq_policyValue_of_fixedPoint
#print axioms Rlib.MDP.optimalityOperator_mono
#print axioms Rlib.MDP.norm_optimalityOperator_sub_le
#print axioms Rlib.MDP.optimalityOperator_contractingWith
#print axioms Rlib.MDP.existsUnique_optimalityOperator_fixedPoint
#print axioms Rlib.MDP.valueIteration_zero
#print axioms Rlib.MDP.valueIteration_succ
#print axioms Rlib.MDP.norm_valueIteration_sub_le
#print axioms Rlib.MDP.tendsto_valueIteration
#print axioms Rlib.MDP.existsUnique_valueIteration_limit
#print axioms Rlib.MDP.oneStepValue_le_optimalityOperator
#print axioms Rlib.MDP.exists_deterministic_greedy_policy
#print axioms Rlib.MDP.oneStepValue_greedyPolicy
#print axioms Rlib.MDP.policy_improvement
#print axioms Rlib.MDP.exists_policy_improvement
#print axioms Rlib.MDP.policyIteration_zero
#print axioms Rlib.MDP.policyIteration_succ
#print axioms Rlib.MDP.oneStepValue_policyIteration_succ
#print axioms Rlib.MDP.policyValue_policyIteration_mono
#print axioms Rlib.MDP.policyIteration_stable_of_value_eq
#print axioms Rlib.MDP.optimalityOperator_policyValue_of_policyIteration_stable
#print axioms Rlib.MDP.exists_policyIteration_stable_optimal
#print axioms Rlib.Examples.oneState_value

#print axioms Rlib.measure_abs_sampleMean_sub_le
#print axioms Rlib.measure_abs_sampleMean_sub_le_of_abs_le
#print axioms Rlib.MDP.measure_abs_ofSamples_reward_sub_le
#print axioms Rlib.MDP.measure_abs_ofSamples_transition_sub_le
#print axioms Rlib.ae_tendsto_sum_mul_of_condExp_eq_zero

#print axioms Rlib.qLearningUpdate_apply_same
#print axioms Rlib.qLearningUpdate_apply_ne
#print axioms Rlib.norm_qMax_sub_le
#print axioms Rlib.MDP.expect_qLearningTarget
#print axioms Rlib.MDP.qBellmanOperator_ofSamples
#print axioms Rlib.MDP.qMax_qBellmanOperator
#print axioms Rlib.MDP.norm_qBellmanOperator_sub_le
#print axioms Rlib.MDP.qBellmanOperator_contractingWith
#print axioms Rlib.MDP.existsUnique_qBellmanOperator_fixedPoint

#print axioms Rlib.MDP.norm_qBellmanSweep_sub_le
#print axioms Rlib.MDP.norm_qBellmanSweepIteration_sub_le
#print axioms Rlib.MDP.tendsto_qBellmanSweepIteration

#print axioms Rlib.MDP.qLearningUpdate_sub_qBellmanUpdate
#print axioms Rlib.MDP.norm_qLearningUpdate_sub_qBellmanUpdate
#print axioms Rlib.MDP.expect_qLearningUpdate_apply_same

#print axioms Rlib.MDP.qLearningUpdate_eq_qPerturbedUpdate
#print axioms Rlib.MDP.norm_qPerturbedSweep_sub_le
#print axioms Rlib.MDP.norm_qPerturbedSweepIteration_sub_le

#print axioms Rlib.eventually_le_of_le_one_sub_mul_add
#print axioms Rlib.tendsto_zero_of_le_one_sub_mul_add
#print axioms Rlib.tendsto_zero_of_eq_one_sub_mul_add_of_tendsto_sum

#print axioms Rlib.norm_qMax_le
#print axioms Rlib.norm_qLearningSync_le
#print axioms Rlib.MDP.qLearningSync_eq_qSyncIteration
#print axioms Rlib.MDP.norm_qSyncIteration_succ_sub_le
#print axioms Rlib.MDP.tendsto_qSyncIteration
#print axioms Rlib.MDP.tendsto_qLearningSync
#print axioms Rlib.MDP.tendsto_qSyncIteration_of_tendsto_sum

#print axioms Rlib.MDP.abs_qLearningSyncError_le
#print axioms Rlib.MDP.ae_tendsto_qLearningSync

#print axioms Rlib.MDP.measurable_qLearningSync_apply
#print axioms Rlib.MDP.condExp_qLearningSyncError_eq_zero
#print axioms Rlib.MDP.ae_tendsto_qLearningSync_of_indep

#print axioms Rlib.MDP.norm_qAsyncIteration_sub_le
#print axioms Rlib.MDP.tendsto_qAsyncIteration

#print axioms Rlib.visitStep_nonneg
#print axioms Rlib.visitStep_le_one
#print axioms Rlib.norm_qLearningAsync_le
#print axioms Rlib.MDP.qLearningAsync_eq_qAsyncIteration
#print axioms Rlib.MDP.tendsto_qLearningAsync

#print axioms Rlib.MDP.abs_qLearningTarget_sub_le
#print axioms Rlib.MDP.condExp_qLearningTarget_sub_eq_zero
#print axioms Rlib.MDP.measurable_qLearningAsync_apply
#print axioms Rlib.MDP.ae_tendsto_qLearningAsync_of_indep

#print axioms Rlib.MDP.norm_sub_le_of_qBellmanOperator_fixed

#print axioms Rlib.MDP.measure_abs_ofSamples_qBellmanOperator_sub_le
#print axioms Rlib.MDP.measure_norm_ofSamples_qBellmanOperator_sub_le

#print axioms Rlib.MDP.norm_le_of_qBellmanOperator_fixed
#print axioms Rlib.MDP.measure_norm_ofSamples_fixed_sub_le
#print axioms Rlib.MDP.measure_norm_ofSamples_fixed_sub_le_of_le

#print axioms Rlib.MDP.expect_policyActionValue
#print axioms Rlib.MDP.expect_advantage
#print axioms Rlib.MDP.policyActionValue_eq
