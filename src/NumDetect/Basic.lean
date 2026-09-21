import Mathlib

/-! Core objects in the NumDetect observation model. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- A point or frequency in `ℝ^d`. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- The Euclidean dot product used by the Fourier phase. -/
def dot {d : ℕ} (x y : Point d) : ℝ :=
  ∑ k, x k * y k

/-- The finite-dimensional `ℓ^p` expression for a real exponent `p`. -/
noncomputable def lpNorm {d : ℕ} (p : ℝ) (x : Point d) : ℝ :=
  (∑ k, |x k| ^ p) ^ (1 / p)

/-- The `ℓ^1` norm, kept separately because all resolution bounds use it. -/
def l1Norm {d : ℕ} (x : Point d) : ℝ :=
  ∑ k, |x k|

/-- The `ℓ^∞` norm on `ℝ^d`. -/
def linftyNorm {d : ℕ} (x : Point d) : ℝ :=
  ‖x‖

/-- The manuscript's range of norm indices, including `p = ∞`. -/
inductive LpIndex where
  | finite (p : ℝ) (one_le : 1 ≤ p)
  | infinity

/-- The norm selected by a finite exponent or by `∞`. -/
noncomputable def normAt {d : ℕ} : LpIndex → Point d → ℝ
  | .finite p _ => lpNorm p
  | .infinity => linftyNorm

/-- The open `ℓ^p` ball from the manuscript. -/
def InOpenLpBall {d : ℕ} (p δ : ℝ) (center y : Point d) : Prop :=
  lpNorm p (y - center) < δ

/-- The open `ℓ^1` ball used in the clustered-source hypothesis. -/
def InOpenL1Ball {d : ℕ} (δ : ℝ) (center y : Point d) : Prop :=
  l1Norm (y - center) < δ

/-- The open cube `Q_δ^d(center) = B_{δ,∞}^d(center)`. -/
def InOpenCube {d : ℕ} (δ : ℝ) (center y : Point d) : Prop :=
  linftyNorm (y - center) < δ

/-- The closed frequency band `[-Ω, Ω]^d`. -/
def InFrequencyBand {d : ℕ} (Ω : ℝ) (ω : Point d) : Prop :=
  ∀ k, |ω k| ≤ Ω

/-- The angular-torus representative convention `(-π, π]^d`. -/
def InAngularCube {d : ℕ} (x : Point d) : Prop :=
  ∀ k, -Real.pi < x k ∧ x k ≤ Real.pi

/-- A reduced finite atomic measure: nodes are distinct and amplitudes are nonzero. -/
structure AtomicMeasure (d n : ℕ) where
  amplitude : Fin n → ℂ
  node : Fin n → Point d
  amplitude_ne_zero : ∀ j, amplitude j ≠ 0
  node_injective : Function.Injective node

/-- A reduced atomic measure with positive real amplitudes. -/
def AtomicMeasure.IsPositive {d n : ℕ} (μ : AtomicMeasure d n) : Prop :=
  ∀ j, ∃ a : ℝ, 0 < a ∧ μ.amplitude j = a

/-- The Fourier transform of a finite atomic measure under the manuscript's normalization. -/
noncomputable def fourier {d n : ℕ} (μ : AtomicMeasure d n) (ω : Point d) : ℂ :=
  ∑ j, μ.amplitude j * Complex.exp (Complex.I * (dot (μ.node j) ω : ℂ))

/-- A positive-size `Fin` type has a nonempty universal finset. -/
theorem fin_univ_nonempty {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The intrinsic minimum amplitude of a nonempty reduced atomic measure. -/
noncomputable def minAmplitude {d n : ℕ} (μ : AtomicMeasure d n) (hn : 0 < n) : ℝ :=
  Finset.univ.inf' (fin_univ_nonempty hn) fun j => ‖μ.amplitude j‖

/-- A bounded-noise Fourier measurement on `[-Ω, Ω]^d`. -/
def IsBandMeasurement {d n : ℕ} (μ : AtomicMeasure d n)
    (Ω σ : ℝ) (Y : Point d → ℂ) : Prop :=
  ∃ W : Point d → ℂ,
    (∀ ω, InFrequencyBand Ω ω → ‖W ω‖ < σ) ∧
    ∀ ω, InFrequencyBand Ω ω → Y ω = fourier μ ω + W ω

/-- A reduced discrete measure whose Fourier data are within `σ` of `Y` on the band. -/
def IsAdmissible {d k : ℕ} (ν : AtomicMeasure d k)
    (Ω σ : ℝ) (Y : Point d → ℂ) : Prop :=
  ∀ ω, InFrequencyBand Ω ω → ‖fourier ν ω - Y ω‖ < σ

/-- Positive admissibility, as used for the positive-amplitude CRL. -/
def IsPositiveAdmissible {d k : ℕ} (ν : AtomicMeasure d k)
    (Ω σ : ℝ) (Y : Point d → ℂ) : Prop :=
  ν.IsPositive ∧ IsAdmissible ν Ω σ Y

/-- Ordered pairs of distinct source indices. -/
def distinctPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij => ij.1 ≠ ij.2

theorem distinctPairs_nonempty {n : ℕ} (hn : 2 ≤ n) :
    (distinctPairs n).Nonempty := by
  refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  simp [distinctPairs]

/-- Minimum of a real-valued pair quantity over distinct source indices. -/
noncomputable def minimumOverDistinctPairs {n : ℕ} (hn : 2 ≤ n)
    (f : Fin n → Fin n → ℝ) : ℝ :=
  (distinctPairs n).inf' (distinctPairs_nonempty hn) fun ij => f ij.1 ij.2

/-- Euclidean `ℓ^1` minimum separation. -/
noncomputable def minimumL1Separation {d n : ℕ} (x : Fin n → Point d)
    (hn : 2 ≤ n) : ℝ :=
  minimumOverDistinctPairs hn fun i j => l1Norm (x i - x j)

/-- One-dimensional minimum separation. -/
noncomputable def minimumSeparation1D {n : ℕ} (x : Fin n → ℝ)
    (hn : 2 ≤ n) : ℝ :=
  minimumOverDistinctPairs hn fun i j => |x i - x j|

/-- The minimum one-dimensional separation of an injective finite family is
positive. -/
theorem minimumSeparation1D_pos {n : ℕ} (x : Fin n → ℝ)
    (hn : 2 ≤ n) (hx : Function.Injective x) :
    0 < minimumSeparation1D x hn := by
  rw [minimumSeparation1D, minimumOverDistinctPairs,
    Finset.lt_inf'_iff (distinctPairs_nonempty hn)]
  intro ij hij
  have hne : ij.1 ≠ ij.2 := by
    simpa [distinctPairs] using hij
  exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hne (hx h)))

/-- The one-dimensional minimum separation is bounded by every distinct pair
distance. -/
theorem minimumSeparation1D_le {n : ℕ} (x : Fin n → ℝ)
    (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    minimumSeparation1D x hn ≤ |x i - x j| := by
  rw [minimumSeparation1D, minimumOverDistinctPairs,
    Finset.inf'_le_iff (distinctPairs_nonempty hn)]
  exact ⟨(i, j), by simp [distinctPairs, hij], le_rfl⟩

/-- Sampling spread of order `n` for a finite integer frequency set. The `sSup`
form is equivalent to maximizing the minimum pairwise spacing over all `n`-subsets. -/
noncomputable def samplingSpread (n : ℕ) (Λ : Finset ℤ) : ℝ :=
  sSup {γ : ℝ | ∃ S : Finset ℤ,
    S ⊆ Λ ∧ S.card = n ∧
    ∀ lam ∈ S, ∀ mu ∈ S, lam ≠ mu → γ ≤ |(lam : ℝ) - (mu : ℝ)|}

/-- Maximum absolute frequency of an ordered one-dimensional integer sampling set. -/
noncomputable def maximumAbsFrequency {M : ℕ} (frequency : Fin M → ℤ)
    (hM : 0 < M) : ℝ :=
  Finset.univ.sup' (fin_univ_nonempty hM) fun j => |(frequency j : ℝ)|

/-- The local-cluster condition used by the external nonuniform Vandermonde estimate. -/
def IsLocalCluster1D {n : ℕ} (x : Fin n → ℝ) (hn : 2 ≤ n)
    (center τ : ℝ) : Prop :=
  ∀ j, |x j - center| ≤ τ * minimumSeparation1D x hn / 2

/-- Wrapped distance in one angular coordinate, for representatives in `(-π, π]`. -/
def periodicCoordinateDistance (u v : ℝ) : ℝ :=
  min |u - v| (2 * Real.pi - |u - v|)

/-- Periodic `ℓ^p` distance on the angular torus. -/
noncomputable def periodicLpDistance {d : ℕ} (p : ℝ) (u v : Point d) : ℝ :=
  (∑ k, periodicCoordinateDistance (u k) (v k) ^ p) ^ (1 / p)

/-- Periodic `ℓ^1` distance on the angular torus. -/
def periodicL1Distance {d : ℕ} (u v : Point d) : ℝ :=
  ∑ k, periodicCoordinateDistance (u k) (v k)

/-- Periodic `ℓ^∞` distance on the angular torus. -/
def periodicLInfDistance {d : ℕ} (u v : Point d) : ℝ :=
  ‖fun k => periodicCoordinateDistance (u k) (v k)‖

/-- Periodic distance selected by a finite exponent or by `∞`. -/
noncomputable def periodicDistance {d : ℕ} : LpIndex → Point d → Point d → ℝ
  | .finite p _ => periodicLpDistance p
  | .infinity => periodicLInfDistance

/-- The global periodic `ℓ^1` minimum separation `Δ₁(𝓧)`. -/
noncomputable def periodicMinimumL1Separation {d n : ℕ}
    (x : Fin n → Point d) (hn : 2 ≤ n) : ℝ :=
  minimumOverDistinctPairs hn fun i j => periodicL1Distance (x i) (x j)

/-- The global periodic `ℓ^∞` minimum separation `Δ∞(𝓧)`. -/
noncomputable def periodicMinimumLInfSeparation {d n : ℕ}
    (x : Fin n → Point d) (hn : 2 ≤ n) : ℝ :=
  minimumOverDistinctPairs hn fun i j => periodicLInfDistance (x i) (x j)

/-- Extended minimum separation, with value `+∞` for an empty pair set (in particular a singleton). -/
noncomputable def extendedPeriodicMinimumSeparation {d n : ℕ} (p : LpIndex)
    (x : Fin n → Point d) : WithTop ℝ :=
  (distinctPairs n).inf fun ij => (periodicDistance p (x ij.1) (x ij.2) : WithTop ℝ)

/-- The local periodic `ℓ^∞` neighborhood at scale `τ`. -/
def localNeighborhood {d n : ℕ} (x : Fin n → Point d) (j : Fin n)
    (τ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun k => periodicLInfDistance (x j) (x k) ≤ τ

/-- The local sparsity `ν∞(τ, 𝓧)`. -/
noncomputable def localSparsity {d n : ℕ} (x : Fin n → Point d)
    (τ : ℝ) (hn : 0 < n) : ℕ :=
  Finset.univ.sup' (fin_univ_nonempty hn) fun j => (localNeighborhood x j τ).card

/-- Exact finite-index formulation of `(A, ∞, τ, η, n⋆)` clumps. -/
def IsAngularClumpStructure {d n : ℕ} (x : Fin n → Point d)
    (A nStar : ℕ) (τ η : ℝ) : Prop :=
  2 ≤ nStar ∧
  0 < τ ∧
  τ ≤ η ∧
  (∀ j, InAngularCube (x j)) ∧
  ∃ label : Fin n → Fin A,
    Function.Surjective label ∧
    (∀ a, (Finset.univ.filter fun j => label j = a).card ≤ nStar) ∧
    (∃ a, (Finset.univ.filter fun j => label j = a).card = nStar) ∧
    (∀ i j, label i = label j → periodicLInfDistance (x i) (x j) ≤ τ) ∧
    ∀ i j, label i ≠ label j → η < periodicLInfDistance (x i) (x j)

/-- For manuscript clumps, the local sparsity at the clump diameter is exactly
the largest clump size. -/
theorem localSparsity_eq_of_angularClumpStructure
    {d n A nStar : ℕ} {x : Fin n → Point d} {τ η : ℝ}
    (hn : 0 < n) (hclumps : IsAngularClumpStructure x A nStar τ η) :
    localSparsity x τ hn = nStar := by
  rcases hclumps with
    ⟨_hnStar, _hτ, hτη, _hangular, label, _hsurj, hcard, hmax,
      hwithin, hcross⟩
  have hneighborhood (j : Fin n) :
      localNeighborhood x j τ = Finset.univ.filter fun k => label k = label j := by
    ext k
    simp only [localNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hdist
      by_contra hlabel
      have hfar := hcross j k (fun h => hlabel h.symm)
      linarith
    · intro hlabel
      exact hwithin j k hlabel.symm
  apply le_antisymm
  · unfold localSparsity
    apply Finset.sup'_le
    intro j _
    rw [hneighborhood]
    exact hcard (label j)
  · rcases hmax with ⟨a, ha⟩
    have hnonempty : (Finset.univ.filter fun j => label j = a).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨j, hj⟩ := hnonempty
    have hjlabel : label j = a := by simpa using hj
    unfold localSparsity
    calc
      nStar = (Finset.univ.filter fun k => label k = a).card := ha.symm
      _ = (localNeighborhood x j τ).card := by rw [hneighborhood j, hjlabel]
      _ ≤ Finset.univ.sup' (fin_univ_nonempty hn)
          fun k => (localNeighborhood x k τ).card :=
        Finset.le_sup' (fun k => (localNeighborhood x k τ).card) (Finset.mem_univ j)

/-- A separation threshold guarantees number detection if every admissible measure has at least
the true number of supports. -/
def NumberDetectionGuarantee (d n : ℕ) (p : LpIndex) (Ω σ mMin D : ℝ)
    (hn : 0 < n) : Prop :=
  ∀ μ : AtomicMeasure d n,
    minAmplitude μ hn = mMin →
    (∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j)) →
    (∀ i j, i ≠ j → D ≤ normAt p (μ.node i - μ.node j)) →
    ∀ Y, IsBandMeasurement μ Ω σ Y →
    ∀ (k : ℕ) (ν : AtomicMeasure d k), IsAdmissible ν Ω σ Y → n ≤ k

/-- The computational resolution limit for number detection. -/
noncomputable def numberDetectionCRL (d n : ℕ) (p : LpIndex) (Ω σ mMin : ℝ)
    (hn : 0 < n) : ℝ :=
  sInf {D : ℝ | 0 ≤ D ∧ NumberDetectionGuarantee d n p Ω σ mMin D hn}

/-- Positive-amplitude version of the number-detection guarantee. -/
def PositiveNumberDetectionGuarantee (d n : ℕ) (p : LpIndex) (Ω σ mMin D : ℝ)
    (hn : 0 < n) : Prop :=
  ∀ μ : AtomicMeasure d n,
    μ.IsPositive →
    minAmplitude μ hn = mMin →
    (∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j)) →
    (∀ i j, i ≠ j → D ≤ normAt p (μ.node i - μ.node j)) →
    ∀ Y, IsBandMeasurement μ Ω σ Y →
    ∀ (k : ℕ) (ν : AtomicMeasure d k), IsPositiveAdmissible ν Ω σ Y → n ≤ k

/-- The positive-amplitude computational resolution limit. -/
noncomputable def positiveNumberDetectionCRL (d n : ℕ) (p : LpIndex)
    (Ω σ mMin : ℝ)
    (hn : 0 < n) : ℝ :=
  sInf {D : ℝ | 0 ≤ D ∧ PositiveNumberDetectionGuarantee d n p Ω σ mMin D hn}

end

end NumDetect
end LeanNumDetect
