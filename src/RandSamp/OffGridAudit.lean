import RandSamp.UniformOffGridRelativeGram
import RandSamp.SeparatedOffGridRelativeGram
import RandSamp.OffGridBiasOperator
import RandSamp.OffGridAtomicRepresentation
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-!
# Admission-free audit for the near-linear off-grid theorem

Every imported project declaration, including private declarations, must have
an admission-free type and proof and must not be a project axiom. All listed
supporting results and final concentration theorems use only the standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. There are no
External or named-theorem exceptions.
-/

open Lean Elab Command

#print axioms LeanNumDetect.BoundedRieszConcentration.boundedRows_concentration
#print axioms LeanNumDetect.RandSamp.exists_fullFourierSignal_atomic_expansion_of_fullGram_lower
#print axioms LeanNumDetect.FiniteMatrixSampling.boundedAtomicIid_concentration
#print axioms LeanNumDetect.FiniteMatrixSampling.boundedAtomicSample_concentration
#print axioms LeanNumDetect.RandSamp.uniformOffGrid_relativeGram
#print axioms LeanNumDetect.RandSamp.uniformSeparated_relativeGram_singularValues
#print axioms LeanNumDetect.RandSamp.uniformOffGrid_and_uniformSeparated_sameConstant
#print axioms LeanNumDetect.RandSamp.relativeGramEvent_operator_bias_bound
#print axioms LeanNumDetect.RandSamp.uniformSeparatedLower_rayleigh_scale_bound

run_cmd do
  let roots : Array Name := #[`External, `General, `RandSamp, `SegmentedVDM, `NumDetect]
  let ordinary : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let original := ``LeanNumDetect.BoundedRieszConcentration.boundedRows_concentration
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if roots.any (fun root => root.isPrefixOf origin) then
      if let .axiomInfo _ := info then
        throwError "Unexpected project axiom in {origin}: {name}"
      if info.type.hasSorry then
        throwError "Unexpected admission in declaration type in {origin}: {name}"
      if (info.value? true).any Expr.hasSorry then
        throwError "Unexpected admission in declaration proof in {origin}: {name}"
  for name in #[
      ``LeanNumDetect.exists_fourierAtom_grid_expansion,
      ``LeanNumDetect.fourierAtomicGridSize_le,
      ``LeanNumDetect.RandSamp.exists_fullFourierSignal_atomic_expansion,
      ``LeanNumDetect.RandSamp.exists_fullFourierSignal_atomic_expansion_of_fullGram_lower,
      ``LeanNumDetect.RandSamp.norm_fullFourierSignal_sq,
      ``LeanNumDetect.RandSamp.sampled_fullFourierSignal_energy,
      ``LeanNumDetect.RandSamp.normalized_expansion_mem_atomicCoefficientClass,
      ``LeanNumDetect.RandSamp.relativeGramEvent_of_atomicGridDeviation,
      ``LeanNumDetect.RandSamp.uniformSeparated_fullGram_bounds,
      ``LeanNumDetect.RandSamp.singularValueEvent_of_relativeGramEvent,
      ``LeanNumDetect.RandSamp.uniformSeparatedLower_pos_of_separation,
      ``LeanNumDetect.RandSamp.relativeGramEvent_bias_bound,
      ``LeanNumDetect.RandSamp.separatedRelativeGramSamplingConstant_of_uniform,
      ``LeanNumDetect.RandSamp.relativeGramEvent_operator_bias_bound,
      ``LeanNumDetect.RandSamp.uniformSeparatedLower_rayleigh_scale_bound,
      ``LeanNumDetect.FiniteMatrixSampling.hermitian_operatorNorm_le_iff_quadratic_abs_le,
      ``LeanNumDetect.FiniteMatrixSampling.hermitian_operatorBias_le_iff_quadratic_bias_le,
      ``LeanNumDetect.FiniteMatrixSampling.sampling_withoutReplacement_convex_le,
      ``LeanNumDetect.FiniteMatrixSampling.integral_finiteUniformMeasure,
      ``LeanNumDetect.FiniteMatrixSampling.iIndepFun_finiteUniform_coordinates,
      ``LeanNumDetect.FiniteMatrixSampling.identDistrib_finiteUniform_coordinate,
      ``LeanNumDetect.FiniteMatrixSampling.sourceRestrictedDeviation_eq_atomicIidDeviation] do
    for ax in ← collectAxioms name do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in fully proved off-grid supporting result {name}"
  for name in #[
      original,
      ``LeanNumDetect.FiniteMatrixSampling.boundedAtomicIid_concentration,
      ``LeanNumDetect.FiniteMatrixSampling.boundedAtomicSample_concentration,
      ``LeanNumDetect.RandSamp.uniformOffGrid_relativeGram,
      ``LeanNumDetect.RandSamp.uniformSeparated_relativeGram_singularValues,
      ``LeanNumDetect.RandSamp.uniformOffGrid_and_uniformSeparated_sameConstant] do
    for ax in ← collectAxioms name do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in off-grid result {name}"
  logInfo "Off-grid audit passed: zero project admissions and axioms; all checked supporting results and final theorems use only standard Lean axioms."
