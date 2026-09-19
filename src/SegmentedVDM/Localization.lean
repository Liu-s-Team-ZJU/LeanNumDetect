import SegmentedVDM.Packets
import SegmentedVDM.UniformInterpolation
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Matrix
namespace SegmentedVDM

noncomputable def uniformEvaluation {ι : Type*} (K : ℕ) (x : ι → ℝ) :
    Matrix (Fin (K+1)) ι ℂ := fun h j => Complex.exp (Complex.I * ((h.val*x j : ℝ) : ℂ))

/-- The localization factor for one well-separated class. The only analytic
input is the explicitly stated uniform-block lower frame inequality. -/
theorem uniform_factor {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℕ)
    (x : ι → ℝ) (j : ι) {a : ℝ} (ha : 0 < a)
    (hframe : ∀ v, (a*(K+1))*energy v ≤ energy (uniformEvaluation K x *ᵥ v)) :
    ∃ P : Packet K 0, (∀ D k, P.value D (x k) = if j = k then 1 else 0) ∧
      P.mass ≤ 1/Real.sqrt a := by
  obtain ⟨c, hc, hcnorm⟩ := cardinal_coefficients_of_frame (uniformEvaluation K x)
    (by positivity : 0 < a*(K+1)) hframe j
  let P : Packet K 0 := {
    Index := Fin (K+1)
    finite := inferInstance
    coarse := fun _ => 0
    fine := Fin.val
    coarse_le := fun _ => le_rfl
    fine_le := fun i => by omega
    coeff := c }
  refine ⟨P, ?_, ?_⟩
  · intro D k
    convert! hc k using 1
    simp [P, Packet.value, uniformEvaluation, dotProduct]
  · have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖c i‖)
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hs
    have hsq : P.mass^2 ≤ 1/a := by
      have h := mul_le_mul_of_nonneg_left hcnorm (show 0 ≤ (K : ℝ)+1 by positivity)
      have he : ((K : ℝ)+1) * (1/(a*(K+1))) = 1/a := by field_simp
      rw [he] at h
      exact hs.trans h
    have he : (1/Real.sqrt a)^2 = 1/a := by rw [div_pow, one_pow, Real.sq_sqrt ha.le]
    exact (sq_le_sq₀ P.mass_nonneg (by positivity)).mp (by rwa [he])

/-- Multiply one uniform interpolation factor per separated color. The
covering hypothesis is used only to choose a zero factor. -/
theorem localization_product {n s : ℕ} (K : ℕ) (x : Fin n → ℝ) (j : Fin n)
    (W : Fin s → Finset (Fin n)) (hj : ∀ ℓ, j ∈ W ℓ)
    (outside : Fin n → Prop) (hcover : ∀ k, outside k → ∃ ℓ, k ∈ W ℓ ∧ j ≠ k)
    {a : ℝ} (ha : 0 < a)
    (hframe : ∀ ℓ (v : (W ℓ) → ℂ), a*(K+1)*energy v ≤
      energy (uniformEvaluation K (fun k : (W ℓ) => x k) *ᵥ v)) :
    ∃ P : Packet (s*K) 0, (∀ D, P.value D (x j) = 1) ∧
      (∀ D k, outside k → P.value D (x k) = 0) ∧ P.mass ≤ (1/Real.sqrt a)^s := by
  classical
  choose F hF using fun ℓ => uniform_factor K (fun k : (W ℓ) => x k)
    ⟨j, hj ℓ⟩ ha (hframe ℓ)
  let P := (Packet.prod F).widen le_rfl (by simp : s*0 ≤ 0)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro D
    simp only [P, Packet.value_widen, Packet.value_prod]
    have h (ℓ : Fin s) : (F ℓ).value D (x j) = 1 := by
      simpa using (hF ℓ).1 D ⟨j, hj ℓ⟩
    simp [h]
  · intro D k hk
    obtain ⟨ℓ, hkW, hjk⟩ := hcover k hk
    simp only [P, Packet.value_widen, Packet.value_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ ℓ)
    have h := (hF ℓ).1 D ⟨k, hkW⟩
    simpa [Subtype.ext_iff, hjk] using h
  · simp only [P, Packet.mass_widen, Packet.mass_prod]
    calc
      _ ≤ ∏ _ℓ : Fin s, 1/Real.sqrt a :=
        Finset.prod_le_prod (fun ℓ _ => (F ℓ).mass_nonneg) (fun ℓ _ => (hF ℓ).2)
      _ = _ := by simp

end SegmentedVDM
