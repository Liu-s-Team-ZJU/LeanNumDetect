import NumDetect.RandomClumpMUSIC
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-! Strict trust-boundary audit of the unconditional manuscript-model random
VDM, GHM, MUSIC correlation, and number-detection chain under Li's geometry
with sample counts proportional to the total node count n. -/

open Lean Elab Command

#print axioms LeanNumDetect.CubeFrameThickness.cubeFrameRow_thickCard
#print axioms LeanNumDetect.FiniteMatrixSampling.framePotential_realDet_lower_slack_of_card
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
      ``LeanNumDetect.CubeFrameThickness.cubeFrameRow_connectedBasis,
      ``LeanNumDetect.CubeFrameThickness.cubeFrameRow_thickCard,
      ``LeanNumDetect.FiniteMatrixSampling.framePotential_realDet_lower_slack_of_card,
      ``LeanNumDetect.CappedWeightIteration.exists_capped_weights_of_determinant_floor,
      ``LeanNumDetect.FiniteMatrixSampling.exists_thick_frame_weights,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_thick_frame_lower_bound_probability,
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
  logInfo "Random-clump audit passed: Li geometry, actual Fourier frame thickness, capped weights, n-based sample counts, unchanged uniform sampling, unnormalized VDM, GHM noise, MUSIC correlation and number detection use no admissions or project axioms."
