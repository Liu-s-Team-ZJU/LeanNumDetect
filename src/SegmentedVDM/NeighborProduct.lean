import SegmentedVDM.NeighborFactors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace SegmentedVDM

/-- All other nodes of a clump are annihilated within the budget `q floor T`.
The subsequent averaging uses one additional block of width `floor T`. -/
theorem neighbor_product {q : ℕ} {T D Δ : ℝ} (hT : 2 ≤ T) (hD : 0 < D)
    (hΔ : 0 < Δ) (u : Fin q → ℝ)
    (hΔu : ∀ i, Δ ≤ |u i|) (hu : ∀ i, |u i| ≤ Real.pi/(2*D))
    (hscale : T*D*Δ ≤ Real.pi) :
    ∃ P : Packet 0 (q*⌊T⌋₊), P.value D 0 = 1 ∧ (∀ i, P.value D (u i) = 0) ∧
      P.mass ≤ (Real.sqrt 2/(T*D*Δ/Real.pi))^q := by
  classical
  choose F hF using fun i => neighbor_factor hT hD hΔ (hΔu i) (hu i) hscale
  let P := (Packet.prod F).widen (by simp : q*0 ≤ 0) le_rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · simp only [P, Packet.value_widen, Packet.value_prod, fun i => (hF i).1, Finset.prod_const_one]
  · intro j
    simp only [P, Packet.value_widen, Packet.value_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact (hF j).2.1
  · simp only [P, Packet.mass_widen, Packet.mass_prod]
    calc
      _ ≤ ∏ _i : Fin q, Real.sqrt 2/(T*D*Δ/Real.pi) :=
        Finset.prod_le_prod (fun i _ => (F i).mass_nonneg) (fun i _ => (hF i).2.2)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SegmentedVDM
