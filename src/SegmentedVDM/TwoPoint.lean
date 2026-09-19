import SegmentedVDM.Packets
import SegmentedVDM.Quantization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SegmentedVDM

noncomputable def twoPoint (k : ℕ) (z : ℂ) : Packet 0 k where
  Index := Bool
  finite := inferInstance
  coarse b := if b then k else 0
  fine _ := 0
  coarse_le b := by cases b <;> simp
  fine_le _ := le_rfl
  coeff b := if b then (1-z)⁻¹ else -z/(1-z)

theorem twoPoint_value (k : ℕ) (z : ℂ) (D x : ℝ) :
    (twoPoint k z).value D x =
      (Complex.exp (Complex.I * ((k*D*x : ℝ) : ℂ))-z)/(1-z) := by
  simp [twoPoint, Packet.value, Fintype.sum_bool]
  ring

theorem twoPoint_at_zero (k : ℕ) (z : ℂ) (hz : z ≠ 1) (D : ℝ) :
    (twoPoint k z).value D 0 = 1 := by
  rw [twoPoint_value]
  simp [sub_ne_zero.mpr (Ne.symm hz)]

theorem twoPoint_vanishes (k : ℕ) (D u : ℝ) :
    (twoPoint k (Complex.exp (Complex.I * ((k*D*u : ℝ) : ℂ)))).value D u = 0 := by
  rw [twoPoint_value]
  simp

theorem twoPoint_mass (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    (twoPoint k z).mass = 2 / ‖1-z‖ := by
  simp [twoPoint, Packet.mass, Fintype.sum_bool, norm_div, hz]
  ring

/-- The scalar quantized two-point factor with its support and coefficient
ℓ¹ bound. Both signs of `u` are covered by the same nonnegative frequency. -/
theorem quantized_twoPoint {D α u : ℝ} (hD : 0 < D) (hα : 0 < α)
    (hu : 0 < |u|) (huα : |u| ≤ 2 * Real.pi * α) (hαD : α ≤ 1/(4*D)) :
    ∃ k : ℕ, (k : ℝ) ≤ 1/(2*D*α) ∧
      ∃ P : Packet 0 k, P.value D 0 = 1 ∧ P.value D u = 0 ∧
        P.mass ≤ 2 / (Real.sqrt 2 / (2 * Real.pi * α) * |u|) := by
  obtain ⟨k, hk, _, _, hden⟩ := scalar_frequency_quantization hD hα hu huα hαD
  let z := Complex.exp (Complex.I * ((k*D*u : ℝ) : ℂ))
  have he : Complex.exp (Complex.I * ((D*k*u : ℝ) : ℂ)) = z := by
    congr 2
    push_cast
    ring
  rw [he] at hden
  have hp : 0 < Real.sqrt 2 / (2 * Real.pi * α) * |u| := by positivity
  have hzn : 0 < ‖1-z‖ := hp.trans_le hden
  have hz : z ≠ 1 := by intro hh; simp [hh] at hzn
  refine ⟨k, hk, twoPoint k z, twoPoint_at_zero k z hz D, twoPoint_vanishes k D u, ?_⟩
  rw [twoPoint_mass k z (by simp [z, Complex.norm_exp])]
  exact div_le_div_of_nonneg_left (by norm_num) hp hden

end SegmentedVDM
