import MultiTuran.MultiClump.Results
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-! Kernel audit of the multi-clump theorem, including every imported
project declaration and all private proof bodies. -/

open Lean Elab Command

run_cmd do
  let roots : Array Name := #[`MultiTuran, `General, `SegmentedVDM, `NumDetect, `RandSamp, `External]
  let ordinary : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut declarationCount : Nat := 0
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if roots.any (fun root => root.isPrefixOf origin) then
      if let .axiomInfo _ := info then
        throwError "Unexpected project axiom in {origin}: {name}"
      if info.type.hasSorry || (info.value? true).any Expr.hasSorry then
        throwError "Unexpected admission in {origin}: {name}"
    if (`MultiTuran.MultiClump).isPrefixOf origin then
      declarationCount := declarationCount + 1
  for theoremName in #[
      ``LeanNumDetect.MultiTuran.MultiClump.multiClumpArray_minimumSingularValue_lower,
      ``LeanNumDetect.MultiTuran.MultiClump.multiClumpArrayLowerBound_le_minimumSingularValue,
      ``LeanNumDetect.MultiTuran.MultiClump.multiClumpProduct_minimumSingularValue_lower,
      ``LeanNumDetect.MultiTuran.MultiClump.generalProductArray_minimumSingularValue_lower,
      ``LeanNumDetect.MultiTuran.MultiClump.generalizedVandermonde_rowShift_minimumSingularValue,
      ``LeanNumDetect.MultiTuran.MultiClump.mem_normalizedProductGrid_rows,
      ``LeanNumDetect.MultiTuran.MultiClump.nodeSeparation_pos_iff_pairwise_torusDistance_pos,
      ``LeanNumDetect.MultiTuran.MultiClump.continuousNorming_of_multiclump_blocks,
      ``LeanNumDetect.MultiTuran.MultiClump.continuousNorming_of_linear_multiclump_blocks,
      ``LeanNumDetect.MultiTuran.MultiClump.coordinateBoxSweep_volume_le,
      ``LeanNumDetect.MultiTuran.MultiClump.continuousEnergy_translated_le_shortenedGrid_of_cardinality_le,
      ``LeanNumDetect.MultiTuran.MultiClump.linearGap_mass_budget,
      ``LeanNumDetect.MultiTuran.MultiClump.anchorRemainder_reconstruction,
      ``LeanNumDetect.NumDetect.liCubeClump_raw_ratio_of_slots,
      ``LeanNumDetect.NumDetect.liCubeClump_raw_lower_halfBandwidth_of_slots,
      ``LeanNumDetect.MultiTuran.MultiClump.blockCondition_minimumLength_lower,
      ``LeanNumDetect.MultiTuran.MultiClump.blockCondition_separationThreshold_le_pi,
      ``LeanNumDetect.MultiTuran.MultiClump.multiClumpCubeLowerBound_le,
      ``LeanNumDetect.MultiTuran.MultiClump.clump_selector_of_torus_separated_clumps,
      ``LeanNumDetect.MultiTuran.MultiClump.clump_discreteEnergy_le_of_selector,
      ``LeanNumDetect.MultiTuran.MultiClump.continuousEnergy_le_shortenedGrid,
      ``LeanNumDetect.MultiTuran.MultiClump.filtered_clump_norming_half,
      ``LeanNumDetect.MultiTuran.MultiClump.exists_simultaneous_clump_lifts,
      ``LeanNumDetect.MultiTuran.MultiClump.generalizedVandermonde_liftNodes,
      ``LeanNumDetect.MultiTuran.MultiClump.multiClumpNormingConstant_mul_energy_loss] do
    for ax in ← collectAxioms theoremName do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in {theoremName}"
  logInfo m!"MultiClump audit passed: {declarationCount} declarations, no project axioms or admissions."
