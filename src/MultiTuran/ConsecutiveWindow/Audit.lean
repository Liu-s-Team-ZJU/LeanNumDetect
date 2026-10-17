import MultiTuran.ConsecutiveWindow.Results
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-! # Kernel audit of the consecutive-window supplement

Every imported project declaration is checked for admissions and axioms;
the principal public results may depend only on Lean's standard logical
axioms. The numerical and analytic inputs are proved in their import graph.
-/

open Lean Elab Command

run_cmd do
  let roots : Array Name := #[`MultiTuran, `General, `SegmentedVDM, `NumDetect, `RandSamp, `External]
  let ordinary : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if roots.any (fun root => root.isPrefixOf origin) then
      checked := checked + 1
      if let .axiomInfo _ := info then
        throwError "Unexpected project axiom in {origin}: {name}"
      if info.type.hasSorry || (info.value? true).any Expr.hasSorry then
        throwError "Unexpected admission in {origin}: {name}"
  for theoremName in #[
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.exists_translated_short_chart,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.exists_window_interpolation_coefficients,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.window_multiplicity_le,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.scalar_grid_block_energy_le,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.continuousNorming_of_long_consecutive_blocks,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.exists_chart_continuousNorming,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.window_restriction_lower_of_norming,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.window_product_restriction_lower,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.fullCube_elementary_bound,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.fullCube_no_wrap_separation,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.fullCube_elementary_no_wrap_bound,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.windowCube_prefactor_lower,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.windowCube_packetCount_lower,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.selected_multiClumpCubeLowerBound_le,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.fullAperture_clump_minimumSingularValue_lower,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.singleClump_minimumSingularValue_lower,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.consecutiveWindowProductArrayLowerBound_le_minimumSingularValue_of_slots,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.consecutiveWindowArray_minimumSingularValue_lower,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.consecutiveWindowProductArray_minimumSingularValue_lower,
      ``LeanNumDetect.MultiTuran.ConsecutiveWindow.consecutiveWindowRawProduct_minimumSingularValue_lower] do
    for ax in ← collectAxioms theoremName do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in {theoremName}"
  logInfo m!"Consecutive-window audit passed: {checked} imported project declarations; no project axioms or admissions."
