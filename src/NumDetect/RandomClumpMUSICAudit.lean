import NumDetect.RandomClumpMUSIC
import General.Fourier.QuantitativePolynomialBounds
import General.Fourier.QuantitativePolynomialGridBounds
import General.Fourier.QuantitativePolynomialL2Derivative
import General.Fourier.QuantitativePolynomialVariationCrossCorrelation
import General.Fourier.WeightedClumpCrossBounds
import General.Fourier.QuantitativeCompanionBounds
import General.Fourier.QuantitativePolynomialCrossCorrelation
import General.Fourier.QuantitativeClumpSectionBounds
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-! Strict trust-boundary audit of the manuscript-model random-clump MUSIC
correlation theorem and its geometry, sampling, normalization and noise chain. -/

open Lean Elab Command

#print axioms LeanNumDetect.NumDetect.positiveCubeClumpVandermonde_lower_highProbability
#print axioms LeanNumDetect.NumDetect.positiveCubeClumpMUSIC_correlation_stability_highProbability
#print axioms LeanNumDetect.NumDetect.positiveCubeClumpGHM_numberDetection_highProbability
#print axioms LeanNumDetect.NumDetect.positiveCubeGHM_numberDetection_highProbability
#print axioms LeanNumDetect.NumDetect.angularClumpPartition_structure
#print axioms LeanNumDetect.NumDetect.positiveCubeMUSIC_correlation_stability_of_singularValues

run_cmd do
  let roots : Array Name := #[`External, `General, `RandSamp, `SegmentedVDM, `NumDetect]
  let ordinary : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if roots.any (fun root => root.isPrefixOf origin) then
      if let .axiomInfo _ := info then
        throwError "Unexpected project axiom in {origin}: {name}"
      if info.type.hasSorry then
        throwError "Admission in declaration type in {origin}: {name}"
      if (info.value? true).any Expr.hasSorry then
        throwError "Admission in {origin}: {name}"
  for name in #[
      ``LeanNumDetect.NumDetect.periodicCoordinateDistance_eq_angularTorusDistance,
      ``LeanNumDetect.NumDetect.periodicL1Distance_eq_multidimensionalAngularTorusL1Distance,
      ``LeanNumDetect.NumDetect.periodicLInfDistance_eq_multidimensionalAngularTorusDistance,
      ``LeanNumDetect.NumDetect.AtomicMeasure.distinctMultidimensionalAngularNodes,
      ``LeanNumDetect.NumDetect.angularClumpPartition_structure,
      ``LeanNumDetect.NumDetect.angularClumpPartition_geometry,
      ``LeanNumDetect.NumDetect.angularClumpPartition_l1SpacingLowerBound,
      ``LeanNumDetect.NumDetect.angularClumpPartition_sizePowerSum,
      ``LeanNumDetect.PolynomialEvaluationBounds.polynomial_unit_abs_le_one_of_legendreEquation,
      ``LeanNumDetect.PolynomialEvaluationBounds.jetPolynomial_unit_row_bound_sharp,
      ``LeanNumDetect.PolynomialEvaluationBounds.jetCoefficientEnergySq_eq_binomial_max,
      ``LeanNumDetect.PolynomialEvaluationBounds.jetPolynomial_coefficient_norm_le_energy_explicit,
      ``LeanNumDetect.PolynomialEvaluationBounds.jetPolynomial_energy_mul_gridSize_sub_loss_le,
      ``LeanNumDetect.PolynomialEvaluationBounds.jetPolynomial_derivative_energy_sqrt_le_explicit,
      ``LeanNumDetect.QuantitativeCompanionBounds.companion_signal_error_bound,
      ``LeanNumDetect.PolynomialCrossCorrelation.inner_modulatedPolynomial_norm_le_of_sup,
      ``LeanNumDetect.PolynomialCrossCorrelation.inner_modulatedPolynomial_norm_le_of_energy,
      ``LeanNumDetect.PolynomialCrossCorrelation.inner_modulatedPolynomial_norm_le_of_size_energy,
      ``LeanNumDetect.WeightedClumpCrossBounds.nonnegative_cross_quadratic_bound,
      ``LeanNumDetect.WeightedClumpCrossBounds.sizeWeighted_clump_sum_energy_lower,
      ``LeanNumDetect.QuantitativeClumpSectionBounds.section_signal_error,
      ``LeanNumDetect.RandSamp.hasMaxClumpSize_clumpCount_sub_one_le,
      ``LeanNumDetect.RandSamp.ClumpPartition.real_globalMomentCoefficient_le,
      ``LeanNumDetect.RandSamp.cubeClump_quantitative_leverage_energy,
      ``LeanNumDetect.RandSamp.multidimensionalMultiClump_lowerGram_sampling_explicit,
      ``LeanNumDetect.RandSamp.multidimensionalMultiClump_lower_sampling_explicit,
      ``LeanNumDetect.RandSamp.cube_multiclump_singular_lower_quantitative_originalConstant,
      ``LeanNumDetect.RandSamp.multidimensionalMultiClump_lower_sampling,
      ``LeanNumDetect.RandSamp.cube_multiclump_singular_lower_optimized,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_lowerGram_of_leverage,
      ``LeanNumDetect.NumDetect.positiveCubeClumpVandermonde_lower_highProbability,
      ``LeanNumDetect.NumDetect.unnormalizedCubeVandermonde_singular_lower,
      ``LeanNumDetect.NumDetect.positiveCubeGHM_numberDetection_of_singularValues,
      ``LeanNumDetect.NumDetect.positiveCubeGHM_numberDetection_highProbability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpGHM_numberDetection_highProbability,
      ``LeanNumDetect.FiniteMatrixSampling.probability_product_lower_bound,
      ``LeanNumDetect.NumDetect.positiveCubeGHM_noise_spectralNorm_lt,
      ``LeanNumDetect.NumDetect.positiveCubeMUSIC_correlation_stability_of_singularValues,
      ``LeanNumDetect.NumDetect.ghmMUSIC_correlation_stability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpMUSIC_correlation_stability_highProbability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpMUSIC_and_numberDetection_highProbability] do
    for ax in ← collectAxioms name do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in random-clump MUSIC result {name}"
  logInfo "Random-clump MUSIC audit passed: the manuscript model bridge, lower-only sampling, unnormalized Vandermonde bound, number detection, normalization, noise and correlation theorems have no admissions or project axioms and use only standard logical axioms."
