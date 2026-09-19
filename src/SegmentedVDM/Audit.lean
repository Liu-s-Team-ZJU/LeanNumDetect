import SegmentedVDM.PaperTheorem
import SegmentedVDM.Partition
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

/-! Check direct admissions in the full core import closure, then check that
constructive reductions have no dependency on an admitted external result. -/

open Lean Elab Command

#print axioms SegmentedVDM.scalar_frequency_quantization
#print axioms SegmentedVDM.neighbor_product
#print axioms SegmentedVDM.localization_product
#print axioms SegmentedVDM.singularValue_ge_of_packets
#print axioms SegmentedVDM.uniform_frame_half
#print axioms SegmentedVDM.small_clumps_singularValue

run_cmd do
  let roots : Array Name := #[`External, `General, `SegmentedVDM]
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if roots.any (fun root => root.isPrefixOf origin) then
      if let .axiomInfo _ := info then
        throwError "Unexpected project axiom in {origin}: {name}"
      if info.type.hasSorry || (info.value? true).any Expr.hasSorry then
        throwError "Unexpected admission in fully proved sampling theory {origin}: {name}"
  let ordinary : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SegmentedVDM.scalar_frequency_quantization,
      ``SegmentedVDM.neighbor_factor, ``SegmentedVDM.neighbor_product,
      ``SegmentedVDM.Clumps.neighbors_card,
      ``SegmentedVDM.Clumps.exists_of_label,
      ``SegmentedVDM.cardinal_coefficients_of_frame,
      ``SegmentedVDM.uniform_factor, ``SegmentedVDM.localization_product,
      ``SegmentedVDM.smoothedVector_norm_le,
      ``SegmentedVDM.singularValue_ge_of_packets,
      ``SegmentedVDM.bound_normalization,
      ``LeanNumDetect.cosineWeight_one_hasSum,
      ``LeanNumDetect.separated_sampling_half,
      ``SegmentedVDM.uniform_frame_half,
      ``SegmentedVDM.clump_packets, ``SegmentedVDM.clump_singularValue_bound,
      ``SegmentedVDM.small_clumps_singularValue] do
    for ax in ← collectAxioms name do
      unless ordinary.contains ax do
        throwError "Unexpected axiom {ax} in constructive reduction {name}"
  logInfo "SegmentedVDM audit passed: the cosine-window sampling bound and complete clump singular-value theorem use only standard Lean axioms."
