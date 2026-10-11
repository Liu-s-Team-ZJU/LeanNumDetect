import NumDetect.RandomClumpMUSIC
import RandSamp.CubeWeakLowerSampling
import RandSamp.CubeThicknessLowerSampling
import General.MatrixAnalysis.CappedWeightSequence
import General.Probability.ThickFrameSampling
import General.Probability.SmoothWeightThickness
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-! Strict trust-boundary audit of the manuscript's greedy random VDM, GHM,
MUSIC correlation, and number-detection chain. Legacy logarithmic-potential
and capped-weight results retain independent trust checks; the public proof
must use the actual greedy frame process and without-replacement comparison. -/

open Lean Elab Command

#print axioms LeanNumDetect.FiniteMatrixSampling.sampleMean_greedy_thick_frame_lower_tail
#print axioms LeanNumDetect.RandSamp.cubeFixedSupport_greedy_minSingularValue_probability
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
  -- Legacy reusable constructions are checked separately from the current route.
  for name in #[
      ``LeanNumDetect.CappedWeightIteration.exists_capped_weights_of_determinant_floor,
      ``LeanNumDetect.FiniteMatrixSampling.framePotential_realDet_lower_slack_of_card,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_thick_frame_lower_bound_probability,
      ``LeanNumDetect.FiniteMatrixSampling.exists_smoothFramePotential_minimizer,
      ``LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_realDet_inverse_lower_slack_of_card,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_lowerGram_of_whitened_thickness,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_thickness_lowerGram_probability,
      ``LeanNumDetect.CubeFrameLogDet.cubeFrameRow_logDetMean_lower,
      ``LeanNumDetect.CubeFrameLogDet.cubeFrameRow_entropyMean_spectral_six_fifths,
      ``LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_inverse_quadratic_lower_of_entropy,
      ``LeanNumDetect.hasDerivAt_log_realDet_affine,
      ``LeanNumDetect.FiniteMatrixSampling.exists_smoothFramePotential_minimizer_of_entropy,
      ``LeanNumDetect.FiniteMatrixSampling.smoothFramePotential_minimizer_stationary,
      ``LeanNumDetect.FiniteMatrixSampling.smooth_normalized_row_bound,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_logarithmic_frame_lower_bound_probability,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_weak_minSingularValue_probability,
      ``LeanNumDetect.CubeFrameThickness.cubeFrameRow_thickCard,
      ``LeanNumDetect.CubeFrameBasis.cubeFrameRow_connectedBasis,
      ``LeanNumDetect.GreedyBasisBounds.det_gram_lower_of_greedySeparated,
      ``LeanNumDetect.GreedyBasisBounds.greedy_full_energy_lower,
      ``LeanNumDetect.GreedyBasisBounds.greedy_on_span_energy_lower,
      ``LeanNumDetect.GreedyFrameProcess.quadratic_storedGram_run_le,
      ``LeanNumDetect.FiniteMatrixSampling.greedyCyclePotential_contraction,
      ``LeanNumDetect.FiniteMatrixSampling.sampling_withoutReplacement_convex_le,
      ``LeanNumDetect.FiniteMatrixSampling.greedy_thick_frame_iid_trace_moment,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_greedy_thick_frame_lower_tail,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_greedy_thick_frame_probability,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_greedy_lowerGram_probability,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_greedy_minSingularValue_probability,
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
  let legacyModules : Array Name := #[
    `General.MatrixAnalysis.FrameLogDetMean,
    `General.Fourier.CubeFrameLogDet,
    `General.MatrixAnalysis.LogDetDirectionalDerivative,
    `General.MatrixAnalysis.ShiftedLogDetSpectrum,
    `General.MatrixAnalysis.SmoothFrameStationarity,
    `General.Probability.SmoothFramePotential,
    `General.Probability.SmoothWeightExistence,
    `General.Probability.LogarithmicFrameSampling,
    `General.Probability.SmoothWeightThickness,
    `General.MatrixAnalysis.CappedRowLeverage,
    `General.MatrixAnalysis.CappedWeightIteration,
    `General.MatrixAnalysis.CappedWeightMap,
    `General.MatrixAnalysis.CappedWeightSequence,
    `General.Probability.CappedWeightEntropy,
    `General.Probability.CappedWeightSpectralCoercivity,
    `General.Probability.ThickFrameSampling,
    `RandSamp.CubeWeakLowerSampling,
    `RandSamp.CubeThicknessLowerSampling]
  let requiredModules : Array Name := #[
    `General.Probability.GreedyFrameProcess,
    `General.MatrixAnalysis.GreedyBasisBounds,
    `General.Probability.GreedyCyclePotential,
    `General.Probability.SamplingConvexOrder,
    `General.Probability.GreedyFrameSampling,
    `General.Probability.GreedyThickFrameSampling,
    `General.Fourier.CubeFrameThickness,
    `RandSamp.CubeGreedyLowerSampling]
  -- Inspect each public theorem independently, including its declaration body.
  for theoremName in #[
      ``LeanNumDetect.RandSamp.cubeFixedSupport_greedy_minSingularValue_probability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpVandermonde_lower_highProbability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpMUSIC_correlation_stability_highProbability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpGHM_signalSingularValue_lower_highProbability,
      ``LeanNumDetect.NumDetect.positiveCubeClumpGHM_numberDetection_highProbability] do
    let mut pending : Array Name := #[theoremName]
    let mut seen : NameSet := {}
    let mut usedModules : NameSet := {}
    while let some name := pending.back? do
      pending := pending.pop
      unless seen.contains name do
        seen := seen.insert name
        if let some info := env.find? name then
          let origin := match env.getModuleIdxFor? name with
            | some idx => env.header.moduleNames[idx]!
            | none => env.mainModule
          if legacyModules.contains origin ||
              name == `LeanNumDetect.FiniteMatrixSampling.matrixChernoff_withoutReplacement_lower then
            throwError "Legacy route appears in greedy theorem {theoremName}: {name}"
          if roots.any (fun root => root.isPrefixOf origin) then
            usedModules := usedModules.insert origin
            pending := pending ++ info.type.getUsedConstants
            if let some value := info.value? true then
              pending := pending ++ value.getUsedConstants
    for required in requiredModules do
      unless usedModules.contains required do
        throwError "Missing greedy proof module {required} in {theoremName}"
    for required in #[
        ``LeanNumDetect.GreedyBasisBounds.greedy_full_energy_lower,
        ``LeanNumDetect.GreedyFrameProcess.quadratic_storedGram_run_le,
        ``LeanNumDetect.FiniteMatrixSampling.greedyCyclePotential_contraction,
        ``LeanNumDetect.FiniteMatrixSampling.sampling_withoutReplacement_convex_le] do
      unless seen.contains required do
        throwError "Missing concrete greedy construction {required} in {theoremName}"
  logInfo "Random-clump audit passed: every public theorem uses the concrete greedy frame process, determinant basis bounds, scalar cycle potential, trace Laplace bound and without-replacement convex comparison, and excludes logarithmic-potential and capped-weight routes. The public and retained legacy results have no admissions or project axioms."
