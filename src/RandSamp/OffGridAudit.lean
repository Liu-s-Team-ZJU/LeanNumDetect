import RandSamp.UniformOffGridRelativeGram
import RandSamp.SeparatedOffGridRelativeGram
import RandSamp.OffGridBiasOperator
import RandSamp.OffGridAtomicRepresentation
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-!
# Separate trust-boundary audit for the near-linear off-grid theorem

The earlier admission-free `RandSamp.Audit` is unchanged. This audit permits
one direct admission only: the source-faithful, registered original BDJR
Theorem 1.1 in `External.BoundedRieszConcentration`. Every imported project
type and every other imported project proof must be admission-free, including
private declarations. Project axioms are never permitted.

The deterministic Fourier representation and normalization are separately
checked to use only standard Lean axioms. The concentration adapters and
final theorem may depend on `sorryAx` only through the one allowed original
external theorem; the imported-declaration inspection enforces that boundary.
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
  let originalModule := `External.BoundedRieszConcentration
  let env ← getEnv
  let mut directAdmissions : Nat := 0
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
        unless name == original && origin == originalModule do
          throwError "Unregistered admission in {origin}: {name}"
        directAdmissions := directAdmissions + 1
  unless directAdmissions == 1 do
    throwError "Expected exactly the registered original BDJR admission; found {directAdmissions}"
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
      unless ordinary.contains ax || ax == ``sorryAx do
        throwError "Unexpected axiom {ax} in off-grid result {name}"
  logInfo "Off-grid audit passed: exactly one registered original BDJR admission; all project adapters and deterministic results have no direct admissions or project axioms."
