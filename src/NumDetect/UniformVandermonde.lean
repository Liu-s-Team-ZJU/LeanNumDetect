import NumDetect.UniformInterpolation

/-! The contiguous-grid Vandermonde lower bound from the NumDetect manuscript. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Manuscript Lemma `lem:uniform-Vandermonde`. -/
theorem uniformVandermonde_minimumSingularValue
    {d n s : ℕ} {Ω : ℝ} (μ : AtomicMeasure d n)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω)
    (hcluster : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j))
    (hs : 4 * n ≤ s) (hseven : Even s) :
    uniformVandermondeLowerBound s Ω μ.node hn ≤
      matrixSingularValue (uniformVandermonde s Ω μ.node) (n - 1) := by
  classical
  let D : ℝ := Ω / s
  let Δ : ℝ := minimumL1Separation μ.node hn
  let θ : ℝ := normalizedMinimumSeparation Ω μ.node hn
  let b : ℕ := s / (2 * n)
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hs0 : 0 < s :=
    lt_of_lt_of_le (by positivity : 0 < 4 * n) hs
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hΔ : 0 < Δ := by
    exact CenteredPacket.minimumL1Separation_pos μ.node hn μ.node_injective
  have hθ : 0 < θ := by
    dsimp [θ, normalizedMinimumSeparation]
    positivity
  have hsep (i j : Fin n) (hij : i ≠ j) :
      Δ ≤ l1Norm (μ.node i - μ.node j) := by
    exact CenteredPacket.minimumL1Separation_le μ.node hn hij
  have hnode (j : Fin n) :
      l1Norm (μ.node j) < Real.pi * n / Ω := by
    simpa [InOpenL1Ball] using hcluster j
  have hdiam (i j : Fin n) :
      l1Norm (μ.node i - μ.node j) ≤ Real.pi / (2 * D) := by
    calc
      l1Norm (μ.node i - μ.node j) ≤
          l1Norm (μ.node i) + l1Norm (μ.node j) :=
        CenteredPacket.l1Norm_sub_le _ _
      _ ≤ 2 * (Real.pi * n / Ω) :=
        (by nlinarith [hnode i, hnode j] :
          l1Norm (μ.node i) + l1Norm (μ.node j) <
            2 * (Real.pi * n / Ω)).le
      _ ≤ Real.pi / (2 * D) := by
        have hsR : (4 * n : ℝ) ≤ s := by exact_mod_cast hs
        have hpi : 0 < Real.pi := Real.pi_pos
        dsimp [D]
        field_simp
        nlinarith
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hΔupper : Δ < 2 * (Real.pi * n / Ω) := by
    calc
      Δ ≤ l1Norm (μ.node i0 - μ.node i1) := hsep i0 i1 hi01
      _ ≤ l1Norm (μ.node i0) + l1Norm (μ.node i1) :=
        CenteredPacket.l1Norm_sub_le _ _
      _ < 2 * (Real.pi * n / Ω) := by
        nlinarith [hnode i0, hnode i1]
  have hscale : ((s : ℝ) / (2 * n)) * D * Δ ≤ Real.pi := by
    have hnR : 0 < (n : ℝ) := by positivity
    have hsR : 0 < (s : ℝ) := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    dsimp [D]
    field_simp
    field_simp at hΔupper
    nlinarith
  have htheta :
      ((s : ℝ) / (2 * n)) * D * Δ / Real.pi = θ := by
    have hnR : 0 < (n : ℝ) := by positivity
    have hsR : 0 < (s : ℝ) := by positivity
    dsimp [D, Δ, θ, normalizedMinimumSeparation]
    field_simp
  obtain ⟨P, hPmass, hPinterp⟩ :=
    CenteredPacket.exists_centeredInterpolationPackets hn μ.node hs hD hΔ
      hsep hdiam hscale htheta
  have hsupport :
      (n - 1) * b + b ≤ s / 2 := by
    calc
      (n - 1) * b + b = (n - 1) * b + 1 * b := by rw [one_mul]
      _ = ((n - 1) + 1) * b := by rw [Nat.add_mul]
      _ = n * b := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = b * n := Nat.mul_comm _ _
      _ = (s / 2 / n) * n := by
        rw [Nat.div_div_eq_div_mul]
      _ ≤ s / 2 := Nat.div_mul_le_self _ _
  let H : ℝ := (Real.sqrt 2 / θ) ^ (n - 1)
  have hH : 0 < H := by
    dsimp [H]
    positivity
  have hPmass' (k : Fin n) : (P k).mass ≤ H := by
    dsimp [H]
    rw [CenteredPacket.sqrtTwo_div_pow]
    exact hPmass k
  have hsv := CenteredPacket.singularValue_ge_of_centeredPackets
    hn0 D μ.node P hsupport hseven hH hPmass' hPinterp
  have hfrequency :
      (fun (α : UniformIndex d s) => fun k => D * (α k : ℝ)) =
        uniformFrequency d s Ω := by
    funext α k
    simp only [D, uniformFrequency]
  have hsv' :
      Real.sqrt ((((2 * b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt n * H) ≤
        matrixSingularValue (uniformVandermonde s Ω μ.node) (n - 1) := by
    rw [hfrequency] at hsv
    simpa only [uniformVandermonde, Nat.cast_pow] using hsv
  have hnormalize := CenteredPacket.uniformPacket_normalization
    (n := n) (q := n - 1)
    (N := (((2 * b + 1 : ℕ) : ℝ) ^ d)) hn0
    (by positivity : 0 < (((2 * b + 1 : ℕ) : ℝ) ^ d)) hθ
  rw [uniformVandermondeLowerBound]
  change
    Real.sqrt
        (1 / ((n : ℝ) * 2 ^ (n - 1)) *
          (((2 * b + 1 : ℕ) : ℝ) ^ d)) *
        θ ^ (n - 1) ≤
      matrixSingularValue (uniformVandermonde s Ω μ.node) (n - 1)
  rw [hnormalize]
  exact hsv'

end

end NumDetect
end LeanNumDetect
