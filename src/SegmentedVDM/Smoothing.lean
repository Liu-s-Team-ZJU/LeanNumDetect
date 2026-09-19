import SegmentedVDM.Packets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open WithLp Matrix
namespace SegmentedVDM

noncomputable def spread {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ρ]
    (f : ι → ρ) (c : ι → ℂ) : EuclideanSpace ℂ ρ :=
  ∑ i, c i • EuclideanSpace.single (f i) 1

theorem norm_spread_sq {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ρ]
    (f : ι → ρ) (hf : Function.Injective f) (c : ι → ℂ) :
    ‖spread f c‖ ^ 2 = energy c := by
  have ho := (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := ρ)).comp f hf
  have hh := ho.inner_sum c c Finset.univ
  change inner ℂ (spread f c) (spread f c) = _ at hh
  have hr := congrArg Complex.re hh
  rw [inner_self_eq_norm_sq_to_K] at hr
  simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, energy] using hr

theorem spread_dotProduct {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ρ]
    (f : ι → ρ) (c : ι → ℂ) (v : ρ → ℂ) :
    ofLp (spread f c) ⬝ᵥ v = ∑ i, c i * v (f i) := by
  simp only [spread, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
    sum_dotProduct, smul_dotProduct, single_dotProduct, smul_eq_mul, one_mul]

def shiftedRow {m r : ℕ} (P : Packet m r) (b z : ℕ) (i : P.Index)
    (j : Fin (z+1) × Fin (b+1)) : Fin (r+z+1) × Fin (m+b+1) :=
  (⟨P.coarse i + j.1, by have h := P.coarse_le i; omega⟩,
   ⟨P.fine i + j.2, by have h := P.fine_le i; omega⟩)

theorem shiftedRow_injective {m r : ℕ} (P : Packet m r) (b z : ℕ) (i : P.Index) :
    Function.Injective (shiftedRow P b z i) := by
  intro a c h
  have h₁ := congrArg (fun j => j.1.val) h
  have h₂ := congrArg (fun j => j.2.val) h
  apply Prod.ext <;> apply Fin.ext <;> dsimp [shiftedRow] at * <;> omega

noncomputable def averagingVector {m r : ℕ} (P : Packet m r) (b z : ℕ) (i : P.Index) :
    EuclideanSpace ℂ (Fin (r+z+1) × Fin (m+b+1)) :=
  spread (shiftedRow P b z i) (fun _ => (1 / (((z+1)*(b+1) : ℕ) : ℂ)))

theorem averagingVector_norm {m r : ℕ} (P : Packet m r) (b z : ℕ) (i : P.Index) :
    ‖averagingVector P b z i‖ = 1 / Real.sqrt (((z+1)*(b+1) : ℕ) : ℝ) := by
  have hN : (0 : ℝ) < ((z+1)*(b+1) : ℕ) := by positivity
  have hh := norm_spread_sq (shiftedRow P b z i) (shiftedRow_injective P b z i)
    (fun _ => (1 / (((z+1)*(b+1) : ℕ) : ℂ)))
  change ‖averagingVector P b z i‖ ^ 2 = _ at hh
  have he : energy (fun _ : Fin (z+1) × Fin (b+1) =>
      (1 / (((z+1)*(b+1) : ℕ) : ℂ))) = 1 / (((z+1)*(b+1) : ℕ) : ℝ) := by
    simp [energy, norm_div, ← Nat.cast_mul, abs_of_pos hN]
    field_simp
  rw [he] at hh
  have hs := Real.sq_sqrt hN.le
  have hp := Real.sqrt_pos.mpr hN
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hh, div_pow, one_pow, hs]

noncomputable def smoothedVector {m r : ℕ} (P : Packet m r) (b z : ℕ) :
    EuclideanSpace ℂ (Fin (r+z+1) × Fin (m+b+1)) :=
  ∑ i, P.coeff i • averagingVector P b z i

theorem smoothedVector_norm_le {m r : ℕ} (P : Packet m r) (b z : ℕ) :
    ‖smoothedVector P b z‖ ≤ P.mass / Real.sqrt (((z+1)*(b+1) : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ i, ‖P.coeff i • averagingVector P b z i‖ := norm_sum_le _ _
    _ = _ := by
      simp only [norm_smul, averagingVector_norm, mul_one_div, ← Finset.sum_div, Packet.mass]

noncomputable def steering (m r : ℕ) (D x : ℝ) : Fin (r+1) × Fin (m+1) → ℂ :=
  fun j => Complex.exp (Complex.I * (((j.1.val : ℝ)*D+j.2.val)*x : ℝ))

noncomputable def meanKernel (b z : ℕ) (D x : ℝ) : ℂ :=
  ∑ j : Fin (z+1) × Fin (b+1),
    (1 / (((z+1)*(b+1) : ℕ) : ℂ)) * steering b z D x j

@[simp] theorem meanKernel_zero (b z : ℕ) (D : ℝ) : meanKernel b z D 0 = 1 := by
  simp [meanKernel, steering]
  field_simp

theorem averagingVector_evaluation {m r : ℕ} (P : Packet m r) (b z : ℕ)
    (i : P.Index) (D x : ℝ) :
    ofLp (averagingVector P b z i) ⬝ᵥ steering (m+b) (r+z) D x =
      Complex.exp (Complex.I * (((P.coarse i : ℝ)*D+P.fine i)*x : ℝ)) *
        meanKernel b z D x := by
  rw [averagingVector, spread_dotProduct]
  unfold meanKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : steering (m+b) (r+z) D x (shiftedRow P b z i j) =
      Complex.exp (Complex.I * (((P.coarse i : ℝ)*D+P.fine i)*x : ℝ)) *
        steering b z D x j := by
    unfold steering shiftedRow
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem smoothedVector_evaluation {m r : ℕ} (P : Packet m r) (b z : ℕ) (D x : ℝ) :
    ofLp (smoothedVector P b z) ⬝ᵥ steering (m+b) (r+z) D x =
      P.value D x * meanKernel b z D x := by
  simp only [smoothedVector, WithLp.ofLp_sum, sum_dotProduct,
    WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, averagingVector_evaluation]
  simp only [Packet.value, Finset.sum_mul, mul_assoc]

noncomputable def modulation {m r : ℕ} (c : Fin (r+1) × Fin (m+1) → ℂ)
    (D y : ℝ) : Fin (r+1) × Fin (m+1) → ℂ :=
  fun j => c j * steering m r D (-y) j

theorem energy_modulation {m r : ℕ} (c : Fin (r+1) × Fin (m+1) → ℂ) (D y : ℝ) :
    energy (modulation c D y) = energy c := by
  simp [energy, modulation, steering, norm_mul, Complex.norm_exp]

theorem modulation_evaluation {m r : ℕ} (c : Fin (r+1) × Fin (m+1) → ℂ)
    (D y x : ℝ) :
    modulation c D y ⬝ᵥ steering m r D x = c ⬝ᵥ steering m r D (x-y) := by
  apply Finset.sum_congr rfl
  intro j _
  dsimp [modulation, steering]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end SegmentedVDM
