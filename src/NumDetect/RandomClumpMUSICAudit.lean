import NumDetect.RandomClumpMUSIC
import RandSamp.CubeThicknessLowerSampling
import General.Fourier.CubeFrameThickness
import General.MatrixAnalysis.CappedWeightSequence
import General.Probability.ThickFrameSampling
import General.Probability.SmoothWeightThickness
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-! Strict trust-boundary audit of the unconditional manuscript-model random
VDM, GHM, MUSIC correlation, and number-detection chain under Li's geometry
with sample counts proportional to the total node count n. The retained
standalone thickness and capped-weight alternatives are audited in the same
environment; the public theorem keeps its direct logarithmic route. -/

open Lean Elab Command

#print axioms LeanNumDetect.CubeFrameLogDet.cubeFrameRow_entropyMean_spectral_six_fifths
#print axioms LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_inverse_quadratic_lower_of_entropy
#print axioms LeanNumDetect.RandSamp.cubeFixedSupport_weak_minSingularValue_probability
#print axioms LeanNumDetect.NumDetect.liCubeClumpVandermonde_normalized_uniform_lower
#print axioms LeanNumDetect.NumDetect.positiveCubeClumpVandermonde_lower_highProbability
#print axioms LeanNumDetect.NumDetect.positiveCubeClumpMUSIC_correlation_stability_highProbability
#print axioms LeanNumDetect.NumDetect.positiveCubeClumpGHM_signalSingularValue_lower_highProbability
#print axioms LeanNumDetect.NumDetect.positiveCubeClumpGHM_numberDetection_highProbability

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
      ``LeanNumDetect.CappedWeightIteration.exists_capped_weights_of_determinant_floor,
      ``LeanNumDetect.FiniteMatrixSampling.framePotential_realDet_lower_slack_of_card,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_thick_frame_lower_bound_probability,
      ``LeanNumDetect.FiniteMatrixSampling.exists_smoothFramePotential_minimizer,
      ``LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_realDet_inverse_lower_slack_of_card,
      ``LeanNumDetect.CubeFrameThickness.cubeFrameRow_thickCard,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_lowerGram_of_whitened_thickness,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_thickness_lowerGram_probability,
      ``LeanNumDetect.CubeFrameBasis.cubeFrameRow_connectedBasis,
      ``LeanNumDetect.CubeFrameLogDet.cubeFrameRow_logDetMean_lower,
      ``LeanNumDetect.CubeFrameLogDet.cubeFrameRow_entropyMean_spectral_six_fifths,
      ``LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_inverse_quadratic_lower_of_entropy,
      ``LeanNumDetect.hasDerivAt_log_realDet_affine,
      ``LeanNumDetect.FiniteMatrixSampling.exists_smoothFramePotential_minimizer_of_entropy,
      ``LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_minimizer_stationary,
      ``LeanNumDetect.FiniteMatrixSampling.smooth_normalized_row_bound,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_logarithmic_frame_lower_bound_probability,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_weak_minSingularValue_probability,
      ``LeanNumDetect.NumDetect.liCubeClumpVandermonde_normalized_lower,
      ``LeanNumDetect.NumDetect.liCubeClumpVandermonde_normalized_uniform_lower,
      ``LeanNumDetect.NumDetect.positiveCubeClumpVandermonde_normalized_lower_probability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpVandermonde_lower_highProbability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpFactorPair_lower_probability,
      ``LeanNumDetect.NumDetect.unnormalizedCubeVandermonde_singular_lower,
      ``LeanNumDetect.NumDetect.positiveCubeGHM_noise_spectralNorm_lt,
      ``LeanNumDetect.NumDetect.positiveCubeMUSIC_correlation_stability_of_singularValues,
      ``LeanNumDetect.NumDetect.positiveCubeGHM_numberDetection_of_singularValues,
      ``LeanNumDetect.NumDetect.positiveCubeClumpMUSIC_correlation_stability_highProbability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpGHM_signalSingularValue_lower_highProbability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpGHM_numberDetection_highProbability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpMUSIC_and_numberDetection_highProbability] do
    for ax in ← collectAxioms name do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in random-clump result {name}"
  -- Audit the actual public cube and number-detection proofs. The new route
  -- must use the direct Hadamard average, the smooth minimum, its first-order
  -- condition, and direct eigenvalue and normalized rank-one bounds.
  -- Retained standalone alternatives must remain outside the public proof route.
  let forbidden : Array Name := #[
    `LeanNumDetect.RandSamp.cubeFixedSupport_lowerGram_of_whitened_thickness,
    `LeanNumDetect.RandSamp.cubeFixedSupport_thickness_lowerGram_probability,
    `LeanNumDetect.FiniteMatrixSampling.exists_thick_frame_weights,
    `LeanNumDetect.FiniteMatrixSampling.sampleMean_thick_frame_lower_bound_probability,
    `LeanNumDetect.FiniteMatrixSampling.exists_smoothFramePotential_minimizer,
    `LeanNumDetect.ConnectedBasisBounds.CubeBasisPrefix.thick_card,
    `LeanNumDetect.CappedWeightIteration.exists_nondescending_step,
    `LeanNumDetect.CappedWeightIteration.realDet_drop_of_not_relative_lower,
    `LeanNumDetect.CubeFrameThickness.cubeFrameRow_thickCard,
    `LeanNumDetect.TranslatedBasisThickness.thick_card_of_translated_l1LowerBound,
    `LeanNumDetect.TranslatedBasisThickness.cube_thick_card,
    `LeanNumDetect.FiniteMatrixSampling.sum_smoothEntropy_spectral_lower_radius,
    `LeanNumDetect.FiniteMatrixSampling.matrix_sum_smoothEntropy_spectral_lower_radius,
    `LeanNumDetect.FiniteMatrixSampling.smooth_entropyMean_spectral_six_fifths,
    `LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_realDet_inverse_lower_slack_of_card]
  let alternativeModules : Array Name := #[
    `General.MatrixAnalysis.CappedRowLeverage,
    `General.MatrixAnalysis.CappedWeightIteration,
    `General.MatrixAnalysis.CappedWeightMap,
    `General.MatrixAnalysis.CappedWeightSequence,
    `General.Probability.CappedWeightEntropy,
    `General.Probability.CappedWeightSpectralCoercivity,
    `General.Probability.ThickFrameSampling,
    `General.Probability.SmoothWeightThickness,
    `General.Fourier.TranslatedBasisThickness,
    `General.Fourier.ConnectedCubeBasisThickness,
    `General.Fourier.CubeFrameThickness,
    `RandSamp.CubeThicknessLowerSampling]
  let mut pending : Array Name := #[
    ``LeanNumDetect.RandSamp.cubeFixedSupport_weak_lowerGram_probability,
    ``LeanNumDetect.RandSamp.cubeFixedSupport_weak_minSingularValue_probability,
    ``LeanNumDetect.NumDetect.positiveCubeClumpVandermonde_normalized_lower_probability,
    ``LeanNumDetect.NumDetect.positiveCubeClumpVandermonde_lower_highProbability,
    ``LeanNumDetect.NumDetect.positiveCubeClumpFactorPair_lower_probability,
    ``LeanNumDetect.NumDetect.positiveCubeClumpMUSIC_correlation_stability_highProbability,
    ``LeanNumDetect.NumDetect.positiveCubeClumpGHM_signalSingularValue_lower_highProbability,
    ``LeanNumDetect.NumDetect.positiveCubeClumpGHM_numberDetection_highProbability,
    ``LeanNumDetect.NumDetect.positiveCubeClumpMUSIC_and_numberDetection_highProbability]
  let mut seen : NameSet := {}
  while let some name := pending.back? do
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if let some info := env.find? name then
        let origin := match env.getModuleIdxFor? name with
          | some idx => env.header.moduleNames[idx]!
          | none => env.mainModule
        if alternativeModules.contains origin || forbidden.contains name then
          throwError "Standalone alternative appears in direct cube sampling proof: {name}"
        if roots.any (fun root => root.isPrefixOf origin) then
          pending := pending ++ info.type.getUsedConstants
          if let some value := info.value? true then
            pending := pending ++ value.getUsedConstants
  for required in #[
      ``LeanNumDetect.FrameLogDetMean.log_det_le_sum_log_diag,
      ``LeanNumDetect.FrameLogDetMean.log_det_mono,
      ``LeanNumDetect.CubeFrameLogDet.cubeFrameRow_logDetMean_lower,
      ``LeanNumDetect.CubeFrameLogDet.cubeFrameRow_entropyMean_spectral_six_fifths,
      ``LeanNumDetect.FiniteMatrixSampling.exists_smoothFramePotential_minimizer_of_entropy,
      ``LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_minimizer_stationary,
      ``LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_inverse_quadratic_lower_of_entropy,
      ``LeanNumDetect.FiniteMatrixSampling.smooth_normalized_row_bound,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_logarithmic_frame_lower_bound_probability] do
    unless seen.contains required do
      throwError "Missing direct construction in public cube sampling proof: {required}"
  -- The metric Cauchy--Schwarz helper remains legitimate for proving that
  -- small affine perturbations stay positive definite in the stationarity
  -- argument. It must not reappear in the normalized row-cap argument.
  let mut capPending : Array Name := #[``LeanNumDetect.FiniteMatrixSampling.smooth_normalized_row_bound]
  let mut capSeen : NameSet := {}
  while let some name := capPending.back? do
    capPending := capPending.pop
    unless capSeen.contains name do
      capSeen := capSeen.insert name
      if name == `LeanNumDetect.FrameMatrixBounds.row_energy_le_inverse_metric ||
          name == `LeanNumDetect.CappedWeightIteration.row_energy_le_inverse_metric then
        throwError "Metric Cauchy--Schwarz detour appears in normalized rank-one bound: {name}"
      if let some info := env.find? name then
        let origin := match env.getModuleIdxFor? name with
          | some idx => env.header.moduleNames[idx]!
          | none => env.mainModule
        if roots.any (fun root => root.isPrefixOf origin) then
          capPending := capPending ++ info.type.getUsedConstants
          if let some value := info.value? true then
            capPending := capPending ++ value.getUsedConstants
  logInfo "Random-clump audit passed: Li geometry, direct Fourier logarithmic determinant average, smooth potential minimum and stationary weights, direct eigenvalue and rank-one bounds, unchanged n-based sample counts and uniform sampling, unnormalized VDM, GHM noise, MUSIC correlation and number detection, together with retained standalone capped-weight and thickness alternatives, use no admissions or project axioms."
