import RandSamp.FixedSeparated
import RandSamp.FixedSeparatedCube
import RandSamp.FixedSupport
import RandSamp.DFTGridOne
import RandSamp.UniformSeparated
import RandSamp.NonuniformVandermonde
import General.Probability.UniformCounting
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-!
Audit the complete manuscript development and its imported project dependencies.
Every imported project declaration must be free of admissions and project axioms;
all listed probabilistic and deterministic results use only Lean's standard axioms.
-/

open Lean Elab Command

#print axioms LeanNumDetect.RandSamp.separated_full_energy_bounds
#print axioms LeanNumDetect.RandSamp.separated_full_gram_bounds
#print axioms LeanNumDetect.RandSamp.sampledVandermonde_energy
#print axioms LeanNumDetect.RandSamp.matrixSingularValue_bounds_of_norm_sq_bounds
#print axioms LeanNumDetect.RandSamp.chernoff_failure_bound_of_sample_size
#print axioms LeanNumDetect.FiniteMatrixSampling.sample_probability_eq_uniform_toOuterMeasure
#print axioms LeanNumDetect.RandSamp.nonuniformVandermonde_minimumSingularValue
#print axioms LeanNumDetect.RandSamp.fixedSupport_singularValues
#print axioms LeanNumDetect.RandSamp.fixedSeparated_singularValues
#print axioms LeanNumDetect.RandSamp.cubeSampledVandermonde_one_singularValue
#print axioms LeanNumDetect.RandSamp.cube_separated_full_energy_bounds
#print axioms LeanNumDetect.RandSamp.cube_separated_full_gram_bounds
#print axioms LeanNumDetect.RandSamp.cubeSeparated_lower_bound_pos
#print axioms LeanNumDetect.FiniteMatrixSampling.finiteSample_probability_eq_uniform_toOuterMeasure
#print axioms LeanNumDetect.RandSamp.cubeFixedSupport_singularValues
#print axioms LeanNumDetect.RandSamp.fixedSeparatedCube_singularValues
#print axioms LeanNumDetect.FiniteMatrixSampling.finiteSample_complex_norm_probability_le
#print axioms LeanNumDetect.RandSamp.dftGrid_singularValues
#print axioms LeanNumDetect.RandSamp.dftGrid_restrictedIsometry
#print axioms LeanNumDetect.RandSamp.dftGridOne_singularValues
#print axioms LeanNumDetect.RandSamp.dftGridOne_restrictedIsometry

run_cmd do
  let roots : Array Name := #[`External, `General, `RandSamp, `SegmentedVDM, `NumDetect]
  let ordinary : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  -- Inspect declaration types and bodies, including private proofs, in every
  -- imported project module. There is no exception for the External directory.
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if roots.any (fun root => root.isPrefixOf origin) then
      if let .axiomInfo _ := info then
        throwError "Unexpected project axiom in {origin}: {name}"
      if info.type.hasSorry || (info.value? true).any Expr.hasSorry then
        throwError "Unexpected admission in {origin}: {name}"
  -- These supporting results are fully formalized, independently of Chernoff.
  for name in #[
      ``LeanNumDetect.RandSamp.separated_full_energy_bounds,
      ``LeanNumDetect.RandSamp.separated_full_gram_bounds,
      ``LeanNumDetect.RandSamp.sampledVandermonde_energy,
      ``LeanNumDetect.RandSamp.fourierRowGram_posSemidef,
      ``LeanNumDetect.RandSamp.fourierPopulation_bound,
      ``LeanNumDetect.RandSamp.quadratic_fourier_mean,
      ``LeanNumDetect.RandSamp.quadratic_fourier_sampleMean,
      ``LeanNumDetect.RandSamp.matrixSingularValue_bounds_of_norm_sq_bounds,
      ``LeanNumDetect.RandSamp.singularValueEvent_of_sampleMean_bounds,
      ``LeanNumDetect.RandSamp.chernoff_failure_bound_of_sample_size,
      ``LeanNumDetect.RandSamp.fourier_chernoff_failure_bound_of_sample_size,
      ``LeanNumDetect.FiniteMatrixSampling.probability_eq_uniform_toOuterMeasure,
      ``LeanNumDetect.FiniteMatrixSampling.sample_probability_eq_uniform_toOuterMeasure,
      ``LeanNumDetect.FiniteMatrixSampling.exists_rayleigh_extrema,
      ``LeanNumDetect.FiniteMatrixSampling.lower_chernoff_factor_le,
      ``LeanNumDetect.FiniteMatrixSampling.upper_chernoff_factor_le,
      ``LeanNumDetect.RandSamp.nonuniformVandermonde_minimumSingularValue,
      ``LeanNumDetect.RandSamp.cube_separated_full_energy_bounds,
      ``LeanNumDetect.RandSamp.cubeLower_le_bartonMass,
      ``LeanNumDetect.RandSamp.cube_separated_full_gram_bounds,
      ``LeanNumDetect.RandSamp.cubeSeparatedLower_pos,
      ``LeanNumDetect.RandSamp.cubeSeparated_lower_bound_pos,
      ``LeanNumDetect.RandSamp.cubeSeparatedLower_one,
      ``LeanNumDetect.RandSamp.cubeSeparatedUpper_one,
      ``LeanNumDetect.RandSamp.fixedSeparated_lower_bound_pos,
      ``LeanNumDetect.singularValues_eq_of_norm_eq,
      ``LeanNumDetect.RandSamp.cubeFourierRow_one,
      ``LeanNumDetect.RandSamp.cubeSampledVandermonde_one_singularValue,
      ``LeanNumDetect.matrixSingularValue_sq_sub_one_le_of_coherence,
      ``LeanNumDetect.matrixSingularValue_bounds_of_coherence,
      ``LeanNumDetect.matrix_norm_sq_bounds_of_coherence,
      ``LeanNumDetect.matrixSingularValue_interval_iff_norm_sq_bounds,
      ``LeanNumDetect.matrixSingularValue_submatrix_equiv,
      ``LeanNumDetect.FiniteMatrixSampling.probability_exists_finset_le,
      ``LeanNumDetect.FiniteMatrixSampling.probability_forall_finset_ge,
      ``LeanNumDetect.FiniteMatrixSampling.finiteSample_complex_norm_probability_le,
      ``LeanNumDetect.FiniteMatrixSampling.finiteSample_complex_centered_norm_probability_le,
      ``LeanNumDetect.FiniteMatrixSampling.finiteSample_uniform_complex_probability_ge,
      ``LeanNumDetect.FiniteMatrixSampling.finite_net_failure_bound_of_sample_size,
      ``LeanNumDetect.exists_torusGridPoint_near,
      ``LeanNumDetect.torusGrid_card_le,
      ``LeanNumDetect.matrixSingularValue_bounds_of_gram_perturbation,
      ``LeanNumDetect.LatticeSelbergMinorant.intervalMinorant_le_openIndicator,
      ``LeanNumDetect.RandSamp.uniform_cube_full_energy_bounds,
      ``LeanNumDetect.RandSamp.uniform_cube_full_gram_bounds,
      ``LeanNumDetect.RandSamp.uniformCubeLower_one,
      ``LeanNumDetect.RandSamp.uniformCube_lower_bound_pos,
      ``LeanNumDetect.RandSamp.uniformSeparated_lower_bound_pos,
      ``LeanNumDetect.RandSamp.norm_cubeKernelError_sub_le,
      ``LeanNumDetect.RandSamp.cubeGram_difference_entry,
      ``LeanNumDetect.RandSamp.cube_singularValues_of_uniform_kernel,
      ``LeanNumDetect.RandSamp.dftCharacter_exp,
      ``LeanNumDetect.RandSamp.sum_dftCharacter_eq_zero,
      ``LeanNumDetect.RandSamp.dftSampledMatrix_gram,
      ``LeanNumDetect.RandSamp.dftSampledMatrix_eq_cubeSampledVandermonde,
      ``LeanNumDetect.RandSamp.card_nonzero_dftIndex,
      ``LeanNumDetect.RandSamp.dft_failure_bound_of_sample_size,
      ``LeanNumDetect.RandSamp.dftGrid_coherence_probability,
      ``LeanNumDetect.RandSamp.dftGridSingularValueEvent_iff_energy,
      ``LeanNumDetect.RandSamp.dftSupportMatrixOne_singularValue,
      ``LeanNumDetect.RandSamp.dftGridOneSingularValueEvent_iff,
      ``LeanNumDetect.RandSamp.dftGridOne_singularValueEvent_iff_energyEvent,
      ``LeanNumDetect.RandSamp.card_cubeFrequency,
      ``LeanNumDetect.RandSamp.cubeSampledVandermonde_energy,
      ``LeanNumDetect.RandSamp.cubeFourierRowGram_posSemidef,
      ``LeanNumDetect.RandSamp.cubeFourierPopulation_bound,
      ``LeanNumDetect.RandSamp.quadratic_cubeFourierRowGram,
      ``LeanNumDetect.RandSamp.quadratic_cubeFourier_mean,
      ``LeanNumDetect.RandSamp.quadratic_cubeFourier_sampleMean,
      ``LeanNumDetect.RandSamp.cubeSingularValueEvent_of_sampleMean_bounds,
      ``LeanNumDetect.FiniteMatrixSampling.probability_comp_equiv,
      ``LeanNumDetect.FiniteMatrixSampling.finiteMean_comp_equiv,
      ``LeanNumDetect.FiniteMatrixSampling.finiteSampleSum_comp_equiv,
      ``LeanNumDetect.FiniteMatrixSampling.finiteSampleMean_comp_equiv,
      ``LeanNumDetect.FiniteMatrixSampling.finiteSample_probability_eq_uniform_toOuterMeasure] do
    for ax in ← collectAxioms name do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in fully proved supporting result {name}"
  for theoremName in #[
      ``LeanNumDetect.tendsto_exp_mul_exp_pow,
      ``LeanNumDetect.GoldenThompson.trace_exp_add_le,
      ``LeanNumDetect.TraceExponential.convexOn_traceExp,
      ``LeanNumDetect.FiniteMatrixSampling.sampling_withoutReplacement_convex_le,
      ``LeanNumDetect.FiniteMatrixSampling.matrixChernoff_withoutReplacement_lower,
      ``LeanNumDetect.FiniteMatrixSampling.matrixChernoff_withoutReplacement_upper,
      ``LeanNumDetect.FiniteMatrixSampling.sampleMean_bounds_probability,
      ``LeanNumDetect.RandSamp.fixedSupport_singularValues,
      ``LeanNumDetect.RandSamp.fixedSeparated_singularValues,
      ``LeanNumDetect.RandSamp.uniformCubeKernel_probability,
      ``LeanNumDetect.RandSamp.uniformSeparatedCube_singularValues,
      ``LeanNumDetect.RandSamp.uniformSeparated_singularValues,
      ``LeanNumDetect.RandSamp.dftGrid_singularValues,
      ``LeanNumDetect.RandSamp.dftGrid_restrictedIsometry,
      ``LeanNumDetect.RandSamp.dftGridOne_singularValues,
      ``LeanNumDetect.RandSamp.dftGridOne_restrictedIsometry,
      ``LeanNumDetect.FiniteMatrixSampling.finiteSampleMean_bounds_probability,
      ``LeanNumDetect.RandSamp.cubeFixedSupport_singularValues,
      ``LeanNumDetect.RandSamp.fixedSeparatedCube_singularValues] do
    for ax in ← collectAxioms theoremName do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in fully proved result {theoremName}"
  logInfo "RandSamp audit passed: all deterministic and probabilistic results use only standard Lean axioms; no admissions or project axioms."
