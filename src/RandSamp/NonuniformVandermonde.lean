import RandSamp.TaylorFactorization

/-!
The nonuniform Fourier--Vandermonde theorem in manuscript form: arbitrary
cluster center and a larger sampling family containing a well-spaced `n`-row
subfamily.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace RandSamp

noncomputable section

def fourierVandermonde {m n : ℕ} (frequency : Fin m → ℝ) (node : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℂ :=
  fun i j => Complex.exp (Complex.I * ((frequency i * node j : ℝ) : ℂ))

theorem fourierVandermonde_eq_centered {m n : ℕ} (frequency : Fin m → ℝ)
    (node : Fin n → ℝ) (center : ℝ) :
    fourierVandermonde frequency node =
      Matrix.diagonal (fun i =>
        Complex.exp (Complex.I * ((frequency i * center : ℝ) : ℂ))) *
        centeredFourierVandermonde frequency (fun j => node j - center) := by
  classical
  ext i j
  simp only [fourierVandermonde, Matrix.mul_apply, Matrix.diagonal_apply,
    centeredFourierVandermonde]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · intro b _ hbi
    rw [if_neg hbi.symm]
    simp
  · simp

theorem unitPhaseDiagonal_action_norm {m n : ℕ} (phase : Fin m → ℂ)
    (hphase : ∀ i, ‖phase i‖ = 1) (A : Matrix (Fin m) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖(Matrix.diagonal phase * A).toEuclideanLin v‖ = ‖A.toEuclideanLin v‖ := by
  have hsq : ‖(Matrix.diagonal phase * A).toEuclideanLin v‖ ^ 2 =
      ‖A.toEuclideanLin v‖ ^ 2 := by
    change ‖toLp 2 ((Matrix.diagonal phase * A) *ᵥ ofLp v)‖ ^ 2 =
      ‖toLp 2 (A *ᵥ ofLp v)‖ ^ 2
    rw [← Matrix.mulVec_mulVec]
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_mul, hphase i, one_mul]
  nlinarith [norm_nonneg ((Matrix.diagonal phase * A).toEuclideanLin v),
    norm_nonneg (A.toEuclideanLin v)]

theorem fourierVandermonde_action_norm_eq_centered {m n : ℕ}
    (frequency : Fin m → ℝ) (node : Fin n → ℝ) (center : ℝ)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖(fourierVandermonde frequency node).toEuclideanLin v‖ =
      ‖(centeredFourierVandermonde frequency (fun j => node j - center)).toEuclideanLin v‖ := by
  rw [fourierVandermonde_eq_centered]
  apply unitPhaseDiagonal_action_norm
  intro i
  simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (frequency i * center)

theorem matrixSingularValue_submatrix_rows_le {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (f : Fin r ↪ Fin m) (hn : 0 < n) :
    matrixSingularValue (A.submatrix f id) (n - 1) ≤ matrixSingularValue A (n - 1) := by
  apply le_singularValues_of_subspace A.toEuclideanLin
    (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one) ⊤
  · simp [Nat.sub_add_cancel hn]
  · intro v _
    have hsub : ‖(A.submatrix f id).toEuclideanLin v‖ ≤ ‖A.toEuclideanLin v‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
        EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      change (∑ i : Fin r, ‖(A *ᵥ ofLp v) (f i)‖ ^ 2) ≤
        ∑ i : Fin m, ‖(A *ᵥ ofLp v) i‖ ^ 2
      rw [← Finset.sum_image
        (f := fun i : Fin m => ‖(A *ᵥ ofLp v) i‖ ^ 2) f.injective.injOn]
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun _ _ _ => sq_nonneg _)
    calc
      matrixSingularValue (A.submatrix f id) (n - 1) * ‖v‖
          ≤ ‖(A.submatrix f id).toEuclideanLin v‖ := by
        simpa only [Fintype.card_fin] using
          lastMatrixSingularValue_mul_norm_le (A.submatrix f id) (by simpa using hn) v
      _ ≤ _ := hsub

/-- Manuscript theorem `thm:nonuniform_vdm_scaling`.  The embedding `select`
is the `n`-point subset witnessing a lower bound `γ` for the sampling spread.
The cluster radius is `ρ`; taking `ρ = τΔ/2` gives the manuscript's notation. -/
theorem nonuniformVandermonde_minimumSingularValue_of_witness {M n : ℕ}
    (frequency : Fin M → ℝ) (node : Fin n → ℝ) (select : Fin n ↪ Fin M)
    (center : ℝ) (hn : 0 < n) {W ρ γ Δ : ℝ}
    (hW : 0 < W) (hfreq : ∀ i, |frequency i| ≤ W)
    (hγ : 0 < γ)
    (hfreqSep : ∀ i j, i ≠ j → γ ≤ |frequency (select i) - frequency (select j)|)
    (hρ : 0 < ρ) (hcluster : ∀ j, |node j - center| ≤ ρ)
    (hΔ : 0 < Δ) (hnodeSep : ∀ i j, i ≠ j → Δ ≤ |node i - node j|)
    (hscale : W * ρ ≤ 1)
    (hremainder :
      (n : ℝ) * ((W * ρ) ^ n * exponentialRemainderCoefficient n) ≤
        (1 / 2 : ℝ) * nonuniformVandermondeConstant n * (γ * Δ) ^ (n - 1)) :
    (1 / 2 : ℝ) * nonuniformVandermondeConstant n * (γ * Δ) ^ (n - 1) ≤
      matrixSingularValue (fourierVandermonde frequency node) (n - 1) := by
  let selectedFrequency : Fin n → ℝ := fun i => frequency (select i)
  let offset : Fin n → ℝ := fun j => node j - center
  have hselectedBound : ∀ i, |selectedFrequency i| ≤ W := fun i => hfreq (select i)
  have hcentered := centeredFourierVandermonde_minimumSingularValue
    selectedFrequency offset hn hW hselectedBound hγ hfreqSep hρ hcluster hΔ
    (by simpa [offset, sub_sub_sub_cancel_right] using hnodeSep) hscale hremainder
  have hshift : matrixSingularValue
      (centeredFourierVandermonde selectedFrequency offset) (n - 1) ≤
      matrixSingularValue (fourierVandermonde selectedFrequency node) (n - 1) := by
    apply le_singularValues_of_subspace
      (fourierVandermonde selectedFrequency node).toEuclideanLin
      (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one) ⊤
    · simp [Nat.sub_add_cancel hn]
    · intro v _
      rw [fourierVandermonde_action_norm_eq_centered selectedFrequency node center v]
      simpa only [Fintype.card_fin, offset] using
        lastMatrixSingularValue_mul_norm_le
          (centeredFourierVandermonde selectedFrequency offset) (by simpa using hn) v
  have hrows : matrixSingularValue (fourierVandermonde selectedFrequency node) (n - 1) ≤
      matrixSingularValue (fourierVandermonde frequency node) (n - 1) := by
    have heq : fourierVandermonde selectedFrequency node =
        (fourierVandermonde frequency node).submatrix select id := by rfl
    rw [heq]
    exact matrixSingularValue_submatrix_rows_le _ select hn
  exact hcentered.trans (hshift.trans hrows)

def distinctSelectionPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij => ij.1 ≠ ij.2

theorem distinctSelectionPairs_nonempty {n : ℕ} (hn : 2 ≤ n) :
    (distinctSelectionPairs n).Nonempty := by
  refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  simp [distinctSelectionPairs]

/-- Minimum pairwise spacing of the rows picked by one embedding. -/
noncomputable def selectionSpacing {M n : ℕ} (frequency : Fin M → ℝ)
    (select : Fin n ↪ Fin M) (hn : 2 ≤ n) : ℝ :=
  (distinctSelectionPairs n).inf' (distinctSelectionPairs_nonempty hn) fun ij =>
    |frequency (select ij.1) - frequency (select ij.2)|

theorem selectionSpacing_le {M n : ℕ} (frequency : Fin M → ℝ)
    (select : Fin n ↪ Fin M) (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    selectionSpacing frequency select hn ≤ |frequency (select i) - frequency (select j)| := by
  unfold selectionSpacing
  exact Finset.inf'_le
    (fun ij : Fin n × Fin n => |frequency (select ij.1) - frequency (select ij.2)|)
    (show (i, j) ∈ distinctSelectionPairs n by simp [distinctSelectionPairs, hij])

theorem selectionSpacing_pos {M n : ℕ} (frequency : Fin M → ℝ)
    (hfrequency : Function.Injective frequency) (select : Fin n ↪ Fin M) (hn : 2 ≤ n) :
    0 < selectionSpacing frequency select hn := by
  unfold selectionSpacing
  rw [Finset.lt_inf'_iff]
  intro ij hij
  simp only [distinctSelectionPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij
  rw [abs_pos, sub_ne_zero]
  exact fun heq => hij (select.injective (hfrequency heq))

/-- Sampling spread of order `n`: the largest minimum spacing among all
`n`-row selections from the frequency family. -/
noncomputable def finiteFamilySamplingSpread {M : ℕ} (frequency : Fin M → ℝ)
    (n : ℕ) (hnM : n ≤ M) (hn : 2 ≤ n) : ℝ :=
  (Finset.univ : Finset (Fin n ↪ Fin M)).sup'
    ⟨Fin.castLEEmb hnM, Finset.mem_univ _⟩ fun select => selectionSpacing frequency select hn

theorem exists_selectionSpacing_eq_finiteFamilySamplingSpread {M n : ℕ}
    (frequency : Fin M → ℝ) (hnM : n ≤ M) (hn : 2 ≤ n) :
    ∃ select : Fin n ↪ Fin M,
      selectionSpacing frequency select hn = finiteFamilySamplingSpread frequency n hnM hn := by
  unfold finiteFamilySamplingSpread
  obtain ⟨select, -, hselect⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin n ↪ Fin M)))
    ⟨Fin.castLEEmb hnM, Finset.mem_univ _⟩ (fun select => selectionSpacing frequency select hn)
  exact ⟨select, hselect.symm⟩

theorem finiteFamilySamplingSpread_pos {M n : ℕ} (frequency : Fin M → ℝ)
    (hfrequency : Function.Injective frequency) (hnM : n ≤ M) (hn : 2 ≤ n) :
    0 < finiteFamilySamplingSpread frequency n hnM hn := by
  obtain ⟨select, hselect⟩ :=
    exists_selectionSpacing_eq_finiteFamilySamplingSpread frequency hnM hn
  rw [← hselect]
  exact selectionSpacing_pos frequency hfrequency select hn

/-- Sampling-spread form with an explicit cluster radius. -/
theorem nonuniformVandermonde_minimumSingularValue_of_radius {M n : ℕ}
    (frequency : Fin M → ℝ) (node : Fin n → ℝ) (center : ℝ)
    (hnM : n ≤ M) (hn : 2 ≤ n) (hfrequency : Function.Injective frequency)
    {W ρ Δ : ℝ} (hW : 0 < W) (hfreq : ∀ i, |frequency i| ≤ W)
    (hρ : 0 < ρ) (hcluster : ∀ j, |node j - center| ≤ ρ)
    (hΔ : 0 < Δ) (hnodeSep : ∀ i j, i ≠ j → Δ ≤ |node i - node j|)
    (hscale : W * ρ ≤ 1)
    (hremainder :
      (n : ℝ) * ((W * ρ) ^ n * exponentialRemainderCoefficient n) ≤
        (1 / 2 : ℝ) * nonuniformVandermondeConstant n *
          (finiteFamilySamplingSpread frequency n hnM hn * Δ) ^ (n - 1)) :
    (1 / 2 : ℝ) * nonuniformVandermondeConstant n *
        (finiteFamilySamplingSpread frequency n hnM hn * Δ) ^ (n - 1) ≤
      matrixSingularValue (fourierVandermonde frequency node) (n - 1) := by
  obtain ⟨select, hselect⟩ :=
    exists_selectionSpacing_eq_finiteFamilySamplingSpread frequency hnM hn
  apply nonuniformVandermonde_minimumSingularValue_of_witness frequency node select center
    (W := W) (ρ := ρ) (γ := finiteFamilySamplingSpread frequency n hnM hn) (Δ := Δ)
    (lt_of_lt_of_le (by omega) hn)
  · exact hW
  · exact hfreq
  · exact finiteFamilySamplingSpread_pos frequency hfrequency hnM hn
  · intro i j hij
    rw [← hselect]
    exact selectionSpacing_le frequency select hn hij
  · exact hρ
  · exact hcluster
  · exact hΔ
  · exact hnodeSep
  · exact hscale
  · exact hremainder

/-- An explicit admissible upper bound for the source separation in manuscript
theorem `thm:nonuniform_vdm_scaling`.  The first term places the cluster in the
Taylor regime; the second absorbs the Taylor remainder into half of the
principal lower bound. -/
noncomputable def nonuniformVandermondeSmallnessThreshold
    (n : ℕ) (W τ γ : ℝ) : ℝ :=
  min (2 / (W * τ))
    (((1 / 2 : ℝ) * nonuniformVandermondeConstant n * γ ^ (n - 1)) /
      ((n : ℝ) * (W * τ / 2) ^ n * exponentialRemainderCoefficient n))

theorem nonuniformVandermondeSmallnessThreshold_pos
    {n : ℕ} (hn : 0 < n) {W τ γ : ℝ}
    (hW : 0 < W) (hτ : 0 < τ) (hγ : 0 < γ) :
    0 < nonuniformVandermondeSmallnessThreshold n W τ γ := by
  unfold nonuniformVandermondeSmallnessThreshold
  apply lt_min
  · positivity
  · have hc := nonuniformVandermondeConstant_pos hn
    have hR : 0 < exponentialRemainderCoefficient n := by
      unfold exponentialRemainderCoefficient
      positivity
    positivity

/-- Quantitative form of manuscript theorem `thm:nonuniform_vdm_scaling` for
a separation below the explicit smallness threshold. -/
theorem nonuniformVandermonde_minimumSingularValue_of_lt_threshold {M n : ℕ}
    (frequency : Fin M → ℝ) (node : Fin n → ℝ) (center : ℝ)
    (hnM : n ≤ M) (hn : 2 ≤ n) (hfrequency : Function.Injective frequency)
    {W τ Δ : ℝ} (hW : 0 < W) (hfreq : ∀ i, |frequency i| ≤ W)
    (hτ : 0 < τ) (hΔ : 0 < Δ)
    (hcluster : ∀ j, |node j - center| ≤ τ * Δ / 2)
    (hnodeSep : ∀ i j, i ≠ j → Δ ≤ |node i - node j|)
    (hsmall :
      Δ < nonuniformVandermondeSmallnessThreshold n W τ
        (finiteFamilySamplingSpread frequency n hnM hn)) :
    (1 / 2 : ℝ) * nonuniformVandermondeConstant n *
        (finiteFamilySamplingSpread frequency n hnM hn * Δ) ^ (n - 1) ≤
      matrixSingularValue (fourierVandermonde frequency node) (n - 1) := by
  let γ := finiteFamilySamplingSpread frequency n hnM hn
  have hnPos : 0 < n := by omega
  have hγ : 0 < γ := finiteFamilySamplingSpread_pos frequency hfrequency hnM hn
  have hsmallScale : Δ < 2 / (W * τ) :=
    hsmall.trans_le (min_le_left _ _)
  have hWτ : 0 < W * τ := mul_pos hW hτ
  have hprod : Δ * (W * τ) < 2 := (lt_div_iff₀ hWτ).mp hsmallScale
  have hscale : W * (τ * Δ / 2) ≤ 1 := by
    nlinarith
  let A : ℝ :=
    (n : ℝ) * (W * τ / 2) ^ n * exponentialRemainderCoefficient n
  let B : ℝ :=
    (1 / 2 : ℝ) * nonuniformVandermondeConstant n * γ ^ (n - 1)
  have hR : 0 < exponentialRemainderCoefficient n := by
    unfold exponentialRemainderCoefficient
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hsmallRemainder : Δ < B / A := by
    exact hsmall.trans_le (min_le_right _ _)
  have hAB : A * Δ < B := by
    have := (lt_div_iff₀ hA).mp hsmallRemainder
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hAB)
    (pow_nonneg hΔ.le (n - 1))
  have hpow : Δ ^ n = Δ ^ (n - 1) * Δ := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), pow_succ]
  have hremainder :
      (n : ℝ) * ((W * (τ * Δ / 2)) ^ n * exponentialRemainderCoefficient n) ≤
        (1 / 2 : ℝ) * nonuniformVandermondeConstant n *
          (γ * Δ) ^ (n - 1) := by
    rw [show W * (τ * Δ / 2) = (W * τ / 2) * Δ by ring,
      mul_pow, hpow, mul_pow]
    dsimp [A, B] at hmul
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact nonuniformVandermonde_minimumSingularValue_of_radius frequency node center
    hnM hn hfrequency hW hfreq (by positivity) hcluster hΔ hnodeSep hscale hremainder

/-- Manuscript theorem `thm:nonuniform_vdm_scaling`.  There is an explicit
positive threshold below which every cluster with minimum separation `Δ`
obeys the stated singular-value scaling law. -/
theorem nonuniformVandermonde_minimumSingularValue {M n : ℕ}
    (frequency : Fin M → ℝ) (node : Fin n → ℝ) (center : ℝ)
    (hnM : n ≤ M) (hn : 2 ≤ n) (hfrequency : Function.Injective frequency)
    {W τ : ℝ} (hW : 0 < W) (hfreq : ∀ i, |frequency i| ≤ W)
    (hτ : 0 < τ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {Δ : ℝ}, 0 < Δ → Δ < ε →
        (∀ j, |node j - center| ≤ τ * Δ / 2) →
        (∀ i j, i ≠ j → Δ ≤ |node i - node j|) →
        (1 / 2 : ℝ) * nonuniformVandermondeConstant n *
            (finiteFamilySamplingSpread frequency n hnM hn * Δ) ^ (n - 1) ≤
          matrixSingularValue (fourierVandermonde frequency node) (n - 1) := by
  let γ := finiteFamilySamplingSpread frequency n hnM hn
  let ε := nonuniformVandermondeSmallnessThreshold n W τ γ
  have hγ : 0 < γ := finiteFamilySamplingSpread_pos frequency hfrequency hnM hn
  refine ⟨ε, nonuniformVandermondeSmallnessThreshold_pos (by omega) hW hτ hγ, ?_⟩
  intro Δ hΔ hsmall hcluster hnodeSep
  exact nonuniformVandermonde_minimumSingularValue_of_lt_threshold
    frequency node center hnM hn hfrequency hW hfreq hτ hΔ hcluster hnodeSep hsmall

end

end RandSamp
end LeanNumDetect
