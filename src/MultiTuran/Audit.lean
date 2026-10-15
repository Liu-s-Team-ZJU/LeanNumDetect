import MultiTuran.Main
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-! Kernel-level audit of the MultiTuran results and every imported
project declaration. No project axiom or admitted result is permitted. -/

open Lean Elab Command

run_cmd do
  let roots : Array Name := #[`MultiTuran, `General, `SegmentedVDM, `NumDetect, `RandSamp, `External]
  let ordinary : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if roots.any (fun root => root.isPrefixOf origin) then
      if let .axiomInfo _ := info then
        throwError "Unexpected project axiom in {origin}: {name}"
      if info.type.hasSorry || (info.value? true).any Expr.hasSorry then
        throwError "Unexpected admission in {origin}: {name}"
  for theoremName in #[
      ``LeanNumDetect.MultiTuran.reciprocal_minimumSingularValue_le_of_interpolation,
      ``LeanNumDetect.MultiTuran.minimumSingularValue_ge_of_energy_lower,
      ``LeanNumDetect.MultiTuran.minimumSingularValue_ge_of_continuousNorming,
      ``LeanNumDetect.MultiTuran.minimumSingularValue_characterization,
      ``LeanNumDetect.MultiTuran.elementary_fullCube_lower,
      ``LeanNumDetect.MultiTuran.elementary_fullCube_no_wrap_lower,
      ``LeanNumDetect.MultiTuran.fullAperture_L2_lower,
      ``LeanNumDetect.MultiTuran.fullAperture_elementary_no_wrap_L2_lower,
      ``LeanNumDetect.MultiTuran.exponentialSum_endpoint_norm_sq_le,
      ``LeanNumDetect.MultiTuran.exponentialSum_unitSupNorm_le,
      ``LeanNumDetect.MultiTuran.exponentialSum_intervalUnion_supNorm_le,
      ``LeanNumDetect.MultiTuran.exponentialSum_product_supNorm_le,
      ``LeanNumDetect.MultiTuran.derivative_matrix_operatorNorm_le,
      ``LeanNumDetect.MultiTuran.finiteHilbert_derivative_norm_le,
      ``LeanNumDetect.MultiTuran.exponentialSum_derivative_energy_norm_le,
      ``LeanNumDetect.MultiTuran.exponentialSum_unit_derivative_norm_le,
      ``LeanNumDetect.MultiTuran.exponentialSum_interval_derivative_norm_le,
      ``LeanNumDetect.MultiTuran.continuousNorming_half_of_blockCondition,
      ``LeanNumDetect.MultiTuran.continuousNorming_half_of_localized_blockCondition,
      ``LeanNumDetect.MultiTuran.apertureL2_le_of_supNorm_restriction,
      ``LeanNumDetect.MultiTuran.segmentedArrayLowerBound_le_of_supNorm_comparison,
      ``LeanNumDetect.MultiTuran.complexExponentialSum_disk_norm_le,
      ``LeanNumDetect.MultiTuran.exists_bounded_zeroFree_blaschke_factor,
      ``LeanNumDetect.MultiTuran.integral_effectiveLogPotential_le,
      ``LeanNumDetect.MultiTuran.cauchySum_weak_bound,
      ``LeanNumDetect.MultiTuran.analytic_logDerivative_weak_bound_of_growth,
      ``LeanNumDetect.MultiTuran.exponentialSum_unit_geometric_turan,
      ``LeanNumDetect.MultiTuran.oneDimensional_turan_comparison,
      ``LeanNumDetect.MultiTuran.exponentialSum_convexBody_supNorm_le,
      ``LeanNumDetect.MultiTuran.exponentialSum_convexBody_eLpNorm_top_le,
      ``LeanNumDetect.MultiTuran.aperture_supNorm_turan,
      ``LeanNumDetect.MultiTuran.segmentedArray_minimumSingularValue_lower,
      ``LeanNumDetect.MultiTuran.segmentedArrayLowerBound_le_minimumSingularValue,
      ``LeanNumDetect.MultiTuran.vandermondeMatrix_singularValues_translateNodes,
      ``LeanNumDetect.MultiTuran.aperture_quotient_lower,
      ``LeanNumDetect.MultiTuran.aperture_quotient_mul_diameter_le_pi] do
    for ax in ← collectAxioms theoremName do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in {theoremName}"
  logInfo "MultiTuran audit passed: no project axioms or admissions."
