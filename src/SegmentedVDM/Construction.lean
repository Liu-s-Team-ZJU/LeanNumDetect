import SegmentedVDM.ClumpGeometry
import SegmentedVDM.UniformFrame
import SegmentedVDM.NeighborProduct
import Mathlib.Algebra.Order.Floor.Semifield

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Matrix
namespace SegmentedVDM

theorem clump_packets {n s : ℕ} (C : Clumps n s) (hs : 1 ≤ s)
    (m₁ M : ℕ) (hM : 2*s ≤ M) (D Δ : ℝ) (hD : 0 < D) (hΔ : 0 < Δ)
    (x : Fin n → ℝ) {a : ℝ} (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hscale : ((M : ℝ)/s)*D*Δ ≤ Real.pi)
    (hsep : ∀ i j, i ≠ j → Δ ≤ |x i-x j|)
    (hdiam : ∀ i j, C.label i = C.label j → |x i-x j| ≤ Real.pi/(2*D))
    (hcross : ∀ i j, C.label i ≠ C.label j → ∀ p : ℤ,
      4*Real.pi/((m₁/s : ℕ)+1) ≤ |x i-x j-2*Real.pi*p|) (k : Fin n) :
    ∃ P : Packet m₁ (M-M/s),
      (∀ j, P.value D (x j-x k) = if k = j then 1 else 0) ∧
      P.mass ≤ (1/Real.sqrt a)^s *
        (Real.sqrt 2/(((M : ℝ)/s)*D*Δ/Real.pi))^(s-1) := by
  classical
  let K := m₁/s
  have hframe (ℓ : Fin s) (v : (C.colorClass k ℓ) → ℂ) :
      a*(K+1)*energy v ≤
        energy (uniformEvaluation K (fun j : C.colorClass k ℓ => x j) *ᵥ v) := by
    have hh := uniform_frame_half K (fun j : C.colorClass k ℓ => x j)
      (fun i j hij p => hcross i j (C.colorClass_labels_ne k ℓ i j hij) p) v
    apply le_trans _ hh
    have hN : (0 : ℝ) ≤ K+1 := by positivity
    have hE := energy_nonneg v
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right haHalf hN) hE
    nlinarith only [hh]
  obtain ⟨G, hG₀, hGzero, hGmass⟩ := localization_product K x k (C.colorClass k)
    (C.anchor_mem_colorClass k) (fun j => C.label j ≠ C.label k)
    (fun j hj => ⟨C.slot j, by simp [hj], fun he => hj (by simp [he])⟩) ha hframe
  let S := C.neighbors k
  let q := S.card
  let e : Fin q ≃ S := (Fintype.equivFinOfCardEq (by simp [q])).symm
  have hq : q ≤ s-1 := C.neighbors_card k
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hT : 2 ≤ (M : ℝ)/s := (le_div_iff₀ hsR).2 (by exact_mod_cast hM)
  have hsmall (i : Fin q) : Δ ≤ |x (e i)-x k| :=
    hsep _ _ ((C.mem_neighbors k (e i)).mp (e i).property).1
  have hdiam' (i : Fin q) : |x (e i)-x k| ≤ Real.pi/(2*D) :=
    hdiam _ _ ((C.mem_neighbors k (e i)).mp (e i).property).2
  obtain ⟨B, hB₀, hBzero, hBmass⟩ :=
    neighbor_product hT hD hΔ (fun i => x (e i)-x k) hsmall hdiam' hscale
  have hfloor : ⌊(M : ℝ)/s⌋₊ = M/s := by rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hcoarse : q*⌊(M : ℝ)/s⌋₊ ≤ M-M/s := by
    rw [hfloor]
    have hb := Nat.div_mul_le_self M s
    have hspos : 0 < s := hs
    have hz := Nat.div_le_self M s
    have hqs : q+1 ≤ s := by omega
    have hh := Nat.mul_le_mul_right (M/s) hqs
    have hsum : q*(M/s) + M/s ≤ M := by
      calc
        _ = (q+1)*(M/s) := by ring
        _ ≤ s*(M/s) := hh
        _ ≤ M := by simpa [Nat.mul_comm] using hb
    omega
  have hfine : s*K+0 ≤ m₁ := by
    have hh := Nat.div_mul_le_self m₁ s
    simpa [K, Nat.mul_comm] using hh
  let P := ((G.translate D (-x k)).mul B).widen hfine (by simpa using hcoarse)
  have hlocal : 0 < ((M : ℝ)/s)*D*Δ/Real.pi := by positivity
  have hlocal1 : ((M : ℝ)/s)*D*Δ/Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 hscale
  have hroot : 1 ≤ Real.sqrt 2 := (Real.one_le_sqrt).2 (by norm_num)
  have hfactor : 1 ≤ Real.sqrt 2/(((M : ℝ)/s)*D*Δ/Real.pi) :=
    (le_div_iff₀ hlocal).2 (by nlinarith)
  refine ⟨P, ?_, ?_⟩
  · intro j
    simp only [P, Packet.value_widen, Packet.value_mul, Packet.value_translate]
    have he : x j-x k-(-x k) = x j := by ring
    rw [he]
    by_cases hj : k = j
    · subst j
      rw [sub_self, hG₀, hB₀]
      simp
    · rw [if_neg hj]
      by_cases hc : C.label j = C.label k
      · have hjS : j ∈ S := by simp [S, Ne.symm hj, hc]
        let j' : S := ⟨j,hjS⟩
        have he' : (e (e.symm j')).val = j := congrArg Subtype.val (e.apply_symm_apply j')
        have hh := hBzero (e.symm j')
        rw [he'] at hh
        rw [hh, mul_zero]
      · rw [hGzero D j hc, zero_mul]
  · simp only [P, Packet.mass_widen, Packet.mass_mul, Packet.mass_translate]
    apply mul_le_mul hGmass _ B.mass_nonneg (by positivity)
    exact hBmass.trans (pow_le_pow_right₀ hfactor hq)

end SegmentedVDM
