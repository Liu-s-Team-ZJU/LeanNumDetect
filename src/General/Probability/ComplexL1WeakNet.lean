import General.Probability.AtomicEmpiricalApproximation

/-!
# Weak empirical nets for a complex ℓ¹ ball

All averages of `L` signed coordinate atoms form a finite net. For each point
of the complex ℓ¹ ball, a suitable average approximates its row evaluations
outside an exceptional set of exponentially small relative size. The net
cardinality depends on `N` and `L`, independently of the number of tested
rows. This is the empirical approximation step underlying Maurey's method.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanNumDetect.BoundedRieszConcentration

noncomputable def complexAtomicAverage {N L : ℕ} (R : ℝ)
    (ω : Fin L → Option (Fin N × Fin 4)) : ComplexVector N :=
  (Complex.ofReal ((L : ℝ)⁻¹)) • ∑ l, complexCoordinateAtom R (ω l)

noncomputable def complexAtomicAverageNet (N L : ℕ) (R : ℝ) : Finset (ComplexVector N) := by
  classical
  exact Finset.univ.image (complexAtomicAverage (N := N) (L := L) R)

theorem complexAtomicAverageNet_card_le (N L : ℕ) (R : ℝ) :
    (complexAtomicAverageNet N L R).card ≤ (4 * N + 1) ^ L := by
  classical
  have h := Finset.card_image_le (f := complexAtomicAverage (N := N) (L := L) R)
    (s := Finset.univ)
  simpa only [complexAtomicAverageNet, Finset.card_univ, Fintype.card_fun,
    Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm N 4] using h

theorem rowPairing_complexAtomicAverage {N L : ℕ} (R : ℝ)
    (ω : Fin L → Option (Fin N × Fin 4)) (x : ComplexVector N) :
    rowPairing (complexAtomicAverage R ω) x =
      (L : ℝ)⁻¹ • (∑ l, rowPairing (complexCoordinateAtom R (ω l)) x) := by
  rw [complexAtomicAverage, rowPairing_ofReal_smul, rowPairing_sum_left]
  simp only [Complex.real_smul]

/-- The weak approximation can be selected as an actual atomic word,
which is useful for counting causal prefixes of approximation choices. -/
theorem complexL1Ball_weakAtomicWord {N : ℕ} {κ : Type*} [Fintype κ]
    (rows : κ → ComplexVector N) {s K r : ℝ}
    (hs : 0 < s) (hK : 0 < K) (hr : 0 < r)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K) {L : ℕ} (hL : 0 < L)
    (f : ComplexVector N) (hf : coefficientL1Norm f ≤ Real.sqrt s) :
    ∃ ω : Fin L → Option (Fin N × Fin 4),
      ((Finset.univ.filter fun i => r <
        ‖rowPairing (f - complexAtomicAverage (2 * Real.sqrt s) ω) (rows i)‖).card : ℝ) ≤
        4 * (Fintype.card κ : ℝ) *
          Real.exp (-((L : ℝ) * r ^ 2 / (32 * s * K ^ 2))) := by
  classical
  let R := 2 * Real.sqrt s
  have hR : 0 < R := by dsimp [R]; positivity
  let α := Option (Fin N × Fin 4)
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  let w := complexCoordinateWeights R f
  have hw : ∀ a, 0 ≤ w a := complexCoordinateWeights_nonneg hR f (by dsimp [R]; linarith)
  have hsum : ∑ a, w a = 1 := sum_complexCoordinateWeights f
  let p := finiteSimplexPMF w hw hsum
  let μ := p.toMeasure
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let y := fun (i : κ) (a : α) => rowPairing (complexCoordinateAtom R a) (rows i)
  have hB : 0 < R * K := mul_pos hR hK
  have hy : ∀ i a, ‖y i a‖ ≤ R * K := by
    intro i a
    exact (rowPairing_norm_le _ _ (hrows i)).trans
      ((mul_le_mul_of_nonneg_left (coefficientL1Norm_complexCoordinateAtom_le hR.le a) hK.le).trans_eq
        (mul_comm K R))
  have hmean (i : κ) : (∫ a, y i a ∂μ) = rowPairing f (rows i) := by
    rw [integral_finiteSimplexPMF w hw hsum]
    simp only [y, Complex.real_smul]
    simp_rw [← rowPairing_ofReal_smul]
    rw [← rowPairing_sum_left]
    rw [sum_weights_complexCoordinateAtom hR.ne' f]
  obtain ⟨ω, hω⟩ := exists_iid_complex_weak_approximation μ y hB hr hy hL
  refine ⟨ω, ?_⟩
  have hnorm (i : κ) :
      ‖(L : ℝ)⁻¹ • (∑ l, y i (ω l)) - ∫ a, y i a ∂μ‖ =
        ‖rowPairing (f - complexAtomicAverage R ω) (rows i)‖ := by
    rw [hmean, rowPairing_sub_left, rowPairing_complexAtomicAverage, norm_sub_rev]
  have hexp : -((L : ℝ) * r ^ 2 / (8 * (R * K) ^ 2)) =
      -((L : ℝ) * r ^ 2 / (32 * s * K ^ 2)) := by
    dsimp [R]
    rw [mul_pow, mul_pow, Real.sq_sqrt hs.le]
    ring
  simp_rw [hnorm] at hω
  rw [hexp] at hω
  exact hω

/-- A complex ℓ¹ ball admits a weak net with cardinality `(4N+1)^L` and an
exceptional-row count at most `4m exp(-Lρ²/(32sK²))`. No row-count logarithm
appears in the net size. -/
theorem complexL1Ball_weakNet {N : ℕ} {κ : Type*} [Fintype κ]
    (rows : κ → ComplexVector N) {s K r : ℝ}
    (hs : 0 < s) (hK : 0 < K) (hr : 0 < r)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K) {L : ℕ} (hL : 0 < L) :
    ∃ C : Finset (ComplexVector N), C.card ≤ (4 * N + 1) ^ L ∧
      ∀ f : ComplexVector N, coefficientL1Norm f ≤ Real.sqrt s →
      ∃ g ∈ C,
        ((Finset.univ.filter fun i => r < ‖rowPairing (f - g) (rows i)‖).card : ℝ) ≤
          4 * (Fintype.card κ : ℝ) *
            Real.exp (-((L : ℝ) * r ^ 2 / (32 * s * K ^ 2))) := by
  classical
  let R := 2 * Real.sqrt s
  refine ⟨complexAtomicAverageNet N L R, complexAtomicAverageNet_card_le N L R, ?_⟩
  intro f hf
  obtain ⟨ω, hω⟩ := complexL1Ball_weakAtomicWord rows hs hK hr hrows hL f hf
  exact ⟨complexAtomicAverage R ω, Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩, hω⟩

end LeanNumDetect.BoundedRieszConcentration
