import MultiTuran.CardinalPackets
import General.MatrixAnalysis.SpectralInterval
import MultiTuran.Geometry

/-! Constructive full-cube Vandermonde estimates used in `thm:elementary-fullcube`.
The cardinal packet has precisely one factor for every other node. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Matrix WithLp
open LeanNumDetect

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The rectangular full-cube matrix `A_{M,s}` from the manuscript. -/
def fullCubeVandermonde {d n : ℕ} (M s : ℕ) (Y : Fin n → Fin d → ℝ) :
    Matrix (Fin d → Fin (s + 1)) (Fin n) ℂ :=
  fun k j => exponential (fun r => (k r).val) (fun r => (M : ℝ) * Y j r)

/-- Agreement with the general Vandermonde matrix on the dilated integer cube. -/
theorem fullCubeVandermonde_eq_vandermondeMatrix {d n : ℕ} (M s : ℕ)
    (Y : Fin n → Point d) :
    fullCubeVandermonde M s Y = vandermondeMatrix
      (fun k : Fin d → Fin (s+1) => fun r => (M : ℝ) * ((k r).val : ℝ)) Y := by
  ext k j
  unfold fullCubeVandermonde exponential vandermondeMatrix
  apply congrArg (fun a : ℝ => Complex.exp (Complex.I * (a : ℂ)))
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Scaling the nodes agrees with dilation of the cube frequencies. -/
@[simp] theorem fullCubeVandermonde_one_scale {d n : ℕ} (M s : ℕ)
    (Y : Fin n → Point d) :
    fullCubeVandermonde 1 s (fun j r => (M : ℝ) * Y j r) =
      fullCubeVandermonde M s Y := by
  ext k j
  simp only [fullCubeVandermonde, Nat.cast_one, one_mul]

/-- A cardinal product with exactly `m` factors for `m+1` nodes. -/
private def cardinalPacket {d m : ℕ} (Y : Fin (m+1) → Fin d → ℝ)
    (i : Fin (m+1)) (r : Fin m → Fin d) (δ : ℝ) : CubePacket d m := by
  exact (CubePacket.prod (fun a : Fin m =>
    (CubePacket.coordinateFactor 1 (r a) 1 (by omega)
      (Y i (r a)) (Y (i.succAbove a) (r a))).scale (δ : ℂ))).withBand (by omega)

private theorem cardinalPacket_value_center {d m : ℕ}
    (Y : Fin (m+1) → Fin d → ℝ) (i : Fin (m+1)) (r : Fin m → Fin d)
    (δ : ℝ)
    (hden : ∀ a, Complex.exp (Complex.I * (Y i (r a) : ℂ)) -
      Complex.exp (Complex.I * (Y (i.succAbove a) (r a) : ℂ)) ≠ 0) :
    (cardinalPacket Y i r δ).value (Y i) = (δ : ℂ) ^ m := by
  simp only [cardinalPacket, CubePacket.value_withBand, CubePacket.value_prod, CubePacket.value_scale,
    CubePacket.coordinateFactor_value, Nat.cast_one, one_mul,
    div_self (hden _), mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem cardinalPacket_value_other {d m : ℕ}
    (Y : Fin (m+1) → Fin d → ℝ) (i j : Fin (m+1)) (hji : j ≠ i)
    (r : Fin m → Fin d) (δ : ℝ) :
    (cardinalPacket Y i r δ).value (Y j) = 0 := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hji
  simp only [cardinalPacket, CubePacket.value_withBand, CubePacket.value_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp only [CubePacket.value_scale, CubePacket.coordinateFactor_value, ha,
    sub_self, zero_div, mul_zero]

private theorem cardinalPacket_mass_le {d m : ℕ}
    (Y : Fin (m+1) → Fin d → ℝ) (i : Fin (m+1)) (r : Fin m → Fin d)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hden : ∀ a, 0 < ‖Complex.exp (Complex.I * (Y i (r a) : ℂ)) -
      Complex.exp (Complex.I * (Y (i.succAbove a) (r a) : ℂ))‖)
    (hscale : ∀ a, δ ≤ ‖Complex.exp (Complex.I * (Y i (r a) : ℂ)) -
      Complex.exp (Complex.I * (Y (i.succAbove a) (r a) : ℂ))‖) :
    (cardinalPacket Y i r δ).mass ≤ (2 : ℝ)^m := by
  simp only [cardinalPacket, CubePacket.mass_withBand, CubePacket.mass_prod]
  calc
    _ ≤ ∏ _a : Fin m, (2 : ℝ) := Finset.prod_le_prod
      (fun _ _ => CubePacket.mass_nonneg _) (fun a _ => by
        simpa only [Nat.cast_one, one_mul] using
          CubePacket.scaled_coordinateFactor_mass_le 1 (r a) 1 (by omega)
            (Y i (r a)) (Y (i.succAbove a) (r a)) hδ
            (by simpa only [Nat.cast_one, one_mul] using hden a)
            (by simpa only [Nat.cast_one, one_mul] using hscale a))
    _ = _ := by simp

/-- Cardinal packets of bounded coefficient mass give the exact interpolation
singular-value bound, with no dependence on the number of cube rows. -/
theorem fullCube_singularValue_lower_of_packets {d n s Q : ℕ}
    (hn : 0 < n) (hband : Q ≤ s) (Y : Fin n → Fin d → ℝ)
    (G : Fin n → CubePacket d Q) {b B : ℝ} (hb : 0 ≤ b) (hB : 0 < B)
    (hmass : ∀ i, (G i).mass ≤ B)
    (hvalue : ∀ i j, (G i).value (Y j) = if i = j then (b : ℂ) else 0) :
    b / (Real.sqrt (n : ℝ) * B) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  classical
  let V := fullCubeVandermonde 1 s Y
  let H := fun i : Fin n => (G i).coefficientVector hband
  let C : Matrix (Fin n) (Frequency d s) ℂ := fun i k => ofLp (H i) k
  have hCV : C * V = Matrix.diagonal (fun _ => (b : ℂ)) := by
    ext i j
    simp only [Matrix.mul_apply, C, V, fullCubeVandermonde, Nat.cast_one, one_mul]
    change ofLp (H i) ⬝ᵥ (fun k => exponential (fun r => (k r).val) (Y j)) = _
    by_cases hij : i = j
    · subst j
      rw [CubePacket.coefficientVector_evaluation, hvalue]
      simp
    · rw [CubePacket.coefficientVector_evaluation, hvalue, if_neg hij]
      simp [Matrix.diagonal, hij]
  have hC (i : Fin n) : packetEnergy (C i) ≤ B^2 := by
    have h := (G i).coefficientVector_norm_le hband
    have hi : ‖H i‖ ≤ B := h.trans (hmass i)
    change (∑ k, ‖ofLp (H i) k‖ ^ 2) ≤ _
    rw [← EuclideanSpace.norm_sq_eq]
    exact (sq_le_sq₀ (norm_nonneg _) hB.le).mpr hi
  obtain ⟨z, hz, he⟩ := exists_unit_vector_norm_sq_eq_singularValue_sq V
    (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
  have henergy := packet_interpolation_energy_lower V C b hCV hC (ofLp z)
  change b^2 * (∑ i, ‖ofLp z i‖^2) ≤
    (n : ℝ) * B^2 * (∑ k, ‖(V *ᵥ ofLp z) k‖^2) at henergy
  rw [← EuclideanSpace.norm_sq_eq, hz, one_pow, mul_one] at henergy
  have heEnergy : (∑ k, ‖(V *ᵥ ofLp z) k‖^2) = ‖V.toEuclideanLin z‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [heEnergy, he] at henergy
  change b^2 ≤ (n : ℝ) * B^2 * V.toEuclideanLin.singularValues (n-1)^2 at henergy
  have hden : 0 < Real.sqrt (n : ℝ) * B := by positivity
  apply (div_le_iff₀ hden).mpr
  apply (sq_le_sq₀ hb (mul_nonneg (V.toEuclideanLin.singularValues_nonneg _) hden.le)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  nlinarith only [henergy]

/-- The elementary full-cube bound from a uniform lower bound on one coordinate
chord for each ordered pair.  The power is exactly `n-1`. -/
theorem elementary_fullCube_chord_lower {d n s M : ℕ}
    (hn : 0 < n) (hs : n - 1 ≤ s) (Y : Fin n → Fin d → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hchord : ∀ i j, i ≠ j → ∃ r : Fin d,
      δ ≤ ‖Complex.exp (Complex.I * (((M : ℝ) * Y i r : ℝ) : ℂ)) -
        Complex.exp (Complex.I * (((M : ℝ) * Y j r : ℝ) : ℂ))‖) :
    δ^(n-1) / (Real.sqrt (n : ℝ) * (2 : ℝ)^(n-1)) ≤
      matrixSingularValue (fullCubeVandermonde M s Y) (n-1) := by
  classical
  by_cases hδ0 : δ = 0
  · subst δ
    by_cases hn1 : n = 1
    · subst n
      let G : Fin 1 → CubePacket d 0 := fun _ => CubePacket.one d 0
      have h := fullCube_singularValue_lower_of_packets (n := 1) (by omega)
        (Nat.zero_le s) (fun j r => (M : ℝ) * Y j r) G
        (b := 1) (B := 1) (by norm_num) (by norm_num) (by intro i; simp [G])
        (by intro i j; have hij : i = j := Subsingleton.elim _ _; simp [G, hij])
      simpa only [fullCubeVandermonde_one_scale, Nat.cast_one, Real.sqrt_one,
        one_div_one, Nat.sub_self, pow_zero, mul_one] using h
    · have hnsub : n - 1 ≠ 0 := by omega
      simp only [zero_pow hnsub, zero_div]
      exact (fullCubeVandermonde M s Y).toEuclideanLin.singularValues_nonneg _
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let Z : Fin (m+1) → Fin d → ℝ := fun j r => (M : ℝ) * Y j r
  have hchoose (i : Fin (m+1)) (a : Fin m) : ∃ r : Fin d,
      δ ≤ ‖Complex.exp (Complex.I * (Z i r : ℂ)) -
        Complex.exp (Complex.I * (Z (i.succAbove a) r : ℂ))‖ :=
    hchord i (i.succAbove a) (Fin.succAbove_ne i a).symm
  choose r hr using hchoose
  let G : Fin (m+1) → CubePacket d m := fun i => cardinalPacket Z i (r i) δ
  have hden (i : Fin (m+1)) (a : Fin m) : 0 <
      ‖Complex.exp (Complex.I * (Z i (r i a) : ℂ)) -
        Complex.exp (Complex.I * (Z (i.succAbove a) (r i a) : ℂ))‖ :=
    hδpos.trans_le (hr i a)
  have hvalue (i j : Fin (m+1)) : (G i).value (Z j) =
      if i = j then ((δ^m : ℝ) : ℂ) else 0 := by
    by_cases hij : i = j
    · subst j
      simpa [G] using cardinalPacket_value_center Z i (r i) δ
        (fun a => norm_pos_iff.mp (hden i a))
    · simp only [if_neg hij]
      exact cardinalPacket_value_other Z i j (Ne.symm hij) (r i) δ
  have h := fullCube_singularValue_lower_of_packets (n := m+1) (by omega) (by simpa using hs)
    Z G (b := δ^m) (B := (2 : ℝ)^m) (by positivity) (by positivity)
    (fun i => cardinalPacket_mass_le Z i (r i) δ hδ (hden i) (hr i)) hvalue
  simpa only [Nat.succ_eq_add_one, Z, fullCubeVandermonde_one_scale, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one] using h

/-- Manuscript `thm:elementary-fullcube`, with precisely the stated angular
separation and constant. -/
theorem elementary_fullCube_lower {d n s M : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hs : n - 1 ≤ s)
    (Y : Fin n → Point d) :
    (1 / Real.sqrt (n : ℝ)) *
        (nodeSeparation (fun j r => (M : ℝ) * Y j r) / Real.pi)^(n-1) ≤
      matrixSingularValue (fullCubeVandermonde M s Y) (n-1) := by
  let Z : Fin n → Point d := fun j r => (M : ℝ) * Y j r
  have h := elementary_fullCube_chord_lower hn hs Y
    (δ := (2 / Real.pi) * nodeSeparation Z) (by
      exact mul_nonneg (by positivity) (nodeSeparation_nonneg Z))
    (fun i j hij => exists_coordinate_chord_lower hd Z i j hij)
  have he : ((2 / Real.pi) * nodeSeparation Z)^(n-1) /
      (Real.sqrt (n : ℝ) * (2 : ℝ)^(n-1)) =
      (1 / Real.sqrt (n : ℝ)) * (nodeSeparation Z / Real.pi)^(n-1) := by
    rw [mul_comm (Real.sqrt (n : ℝ)), ← div_div, ← div_pow]
    have hr : (2 / Real.pi * nodeSeparation Z) / 2 = nodeSeparation Z / Real.pi := by
      ring
    rw [hr]
    ring
  rw [he] at h
  exact h

/-- The no-aliasing version of manuscript `thm:elementary-fullcube`. -/
theorem elementary_fullCube_no_wrap_lower {d n s M : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hs : n - 1 ≤ s)
    (Y : Fin n → Point d) (hshort : (M : ℝ) * nodeDiameter Y ≤ Real.pi) :
    (1 / Real.sqrt (n : ℝ)) * ((M : ℝ) * nodeSeparation Y / Real.pi)^(n-1) ≤
      matrixSingularValue (fullCubeVandermonde M s Y) (n-1) := by
  have h := elementary_fullCube_lower (M := M) hd hn hs Y
  rw [nodeSeparation_mul_nat M Y hshort] at h
  exact h

end
end LeanNumDetect.MultiTuran
