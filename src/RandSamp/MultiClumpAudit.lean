import RandSamp.MultiClumpTheorem
import General.Fourier.ExponentialCompanion
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-!
# Trust-boundary audit for multiclump sampling in every dimension

Every imported project declaration, including private declarations and
types, must be free of admissions and project axioms. The final theorem
and its full analytic and probabilistic chain may depend only on Lean's
standard logical axioms.
-/

open Lean Elab Command

#print axioms LeanNumDetect.RandSamp.multiClump_random_row_sampling
#print axioms LeanNumDetect.RandSamp.multiClump_sampling_statement
#print axioms LeanNumDetect.RandSamp.multidimensionalMultiClump_random_row_sampling
#print axioms LeanNumDetect.RandSamp.multidimensionalMultiClump_sampling_with_sharp_lower
#print axioms LeanNumDetect.RandSamp.cubeClump_leverage_thresholds
#print axioms LeanNumDetect.RandSamp.cube_multiclump_singular_lower
#print axioms LeanNumDetect.RandSamp.cube_multiclump_singular_upper
#print axioms LeanNumDetect.RandSamp.arithmeticClump_lower_real_exponent_sharp

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
      ``LeanNumDetect.RandSamp.angularTorusDistance_eq_winding,
      ``LeanNumDetect.RandSamp.angular_short_clump_lift,
      ``LeanNumDetect.RandSamp.hasMaxClumpSize_squareSum_le,
      ``LeanNumDetect.RandSamp.fullVandermonde_energy,
      ``LeanNumDetect.RandSamp.angularDistinct_fullGram_posDef,
      ``LeanNumDetect.AlmostOrthogonalEnergy.clump_sum_half_energy,
      ``LeanNumDetect.RandSamp.cube_multiclump_singular_lower,
      ``LeanNumDetect.RandSamp.cube_fullGram_posDef_of_distinct,
      ``LeanNumDetect.ExponentialCompanion.exists_uniform_jet_radius,
      ``LeanNumDetect.AlmostOrthogonalEnergy.row_bound_of_clump_bounds,
      ``LeanNumDetect.RandSamp.cube_multiclump_singular_upper,
      ``LeanNumDetect.RandSamp.arithmeticClump_sampled_minimumSingularValue_upper,
      ``LeanNumDetect.RandSamp.arithmeticClump_structure,
      ``LeanNumDetect.RandSamp.arithmeticClump_lower_real_exponent_sharp,
      ``LeanNumDetect.RandSamp.allSingularValueEvent_of_relativeGramEvent,
      ``LeanNumDetect.RandSamp.multiClumpSuccess_iff_relativeGram,
      ``LeanNumDetect.RandSamp.multiClump_sampling_of_deterministicControl,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_relativeGram_allSingularValues_of_leverage,
      ``LeanNumDetect.RandSamp.multiClumpSamplingConclusion_of_multidimensional_one,
      ``LeanNumDetect.RandSamp.multidimensionalMultiClumpSuccess_one,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_relative_bounds_probability,
      ``LeanNumDetect.singularValues_relative_bounds] do
    for ax in ← collectAxioms name do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in admission-free conversion {name}"
  for name in #[
      ``LeanNumDetect.RandSamp.multiClump_deterministic_control,
      ``LeanNumDetect.RandSamp.cubeClump_leverage_thresholds,
      ``LeanNumDetect.RandSamp.multidimensionalMultiClump_deterministic_control,
      ``LeanNumDetect.RandSamp.multidimensionalMultiClump_random_row_sampling,
      ``LeanNumDetect.RandSamp.multidimensionalMultiClump_sampling_with_sharp_lower,
      ``LeanNumDetect.RandSamp.multiClump_random_row_sampling,
      ``LeanNumDetect.RandSamp.multiClump_sampling_statement] do
    for ax in ← collectAxioms name do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in multiclump theorem {name}"
  logInfo "Multidimensional multiclump audit passed: no admissions or project axioms; the cube theorem, exact dimension-one corollary, sharp lower bound, and real-exponent sharpness use only the standard logical axioms."
