import NumDetect.Segmented.ClumpBasics
import General.Fourier.FineCubeFrame
import General.Fourier.TranslatedCubeFourier
import General.Fourier.TrigonometricPolynomialParseval
import NumDetect.Matrices
import NumDetect.UniformInterpolation
import SegmentedVDM.Interpolation
import SegmentedVDM.UniformFrame
import SegmentedVDM.UniformInterpolation
import Mathlib.LinearAlgebra.Matrix.Rank
import NumDetect.Segmented.Polynomial
import NumDetect.Segmented.NeighborFactors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The wrapped distance in one coordinate vanishes at equal points. -/
private theorem periodicCoordinateDistance_self (v : ℝ) :
    periodicCoordinateDistance v v = 0 := by
  unfold periodicCoordinateDistance
  rw [sub_self, abs_zero, sub_zero]
  exact min_eq_left (by positivity)

/-- The wrapped `ℓ^∞` distance of a point to itself vanishes. -/
private theorem periodicLInfDistance_self {d : ℕ} (u : Point d) :
    periodicLInfDistance u u = 0 := by
  have hfun : (fun k => periodicCoordinateDistance (u k) (u k)) = fun _ => (0:ℝ) := by
    funext k
    exact periodicCoordinateDistance_self (u k)
  unfold periodicLInfDistance
  rw [hfun]
  exact norm_zero

/-- The coefficient-mass constant `(1 / √a) ^ n` is the real power
`a ^ (-n / 2)` used by the manuscript. -/
private theorem inv_sqrt_pow_eq_rpow {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (1 / Real.sqrt a) ^ n = a ^ (-(n : ℝ) / 2) := by
  have hsqrt : (Real.sqrt a) ^ n = a ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha.le]
    congr 1
    ring
  have h : (1 / Real.sqrt a) ^ n = ((Real.sqrt a) ^ n)⁻¹ := by
    rw [one_div, inv_pow]
  rw [h, hsqrt, ← Real.rpow_neg ha.le ((n : ℝ) / 2)]
  congr 1
  exact (neg_div _ _).symm

/-- The frame constant `a_β = 2 - exp (1 / (2 * β))` of manuscript
`thm:well_separated_segmented` is positive in the range `β > 1 / (2 * log 2)`. -/
private theorem wellSeparatedFrameConstant_pos {β : ℝ}
    (hβ : 1 / (2 * Real.log 2) < β) : 0 < 2 - Real.exp (1 / (2 * β)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβpos : 0 < β :=
    (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hexponent : 1 / (2 * β) < Real.log 2 := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).1 hβ
    apply (div_lt_iff₀ (by positivity : 0 < 2 * β)).2
    nlinarith
  have hexp : Real.exp (1 / (2 * β)) < 2 := by
    calc
      Real.exp (1 / (2 * β)) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr hexponent
      _ = 2 := Real.exp_log (by norm_num)
  linarith

/-- The frame constant `a_β = 2 - exp (1 / (2 * β))` is at most one. -/
private theorem wellSeparatedFrameConstant_le_one {β : ℝ}
    (hβ : 1 / (2 * Real.log 2) < β) : 2 - Real.exp (1 / (2 * β)) ≤ 1 := by
  have hβpos : 0 < β :=
    (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hone : 1 ≤ Real.exp (1 / (2 * β)) :=
    Real.one_le_exp (by positivity)
  linarith

/-- The fine-cube Fourier energy of a node family is the squared `ℓ²` energy of
its evaluation on the nonnegative frequency cube. -/
private theorem fineCubeFourierEnergy_eq_energy_fineCubeEvaluation
    {d : ℕ} {ι : Type*} [Fintype ι] (K : ℕ) (x : ι → Point d)
    (v : ι → ℂ) :
    FineCubeFrame.fineCubeFourierEnergy K x v =
      SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v) := by
  classical
  simp only [FineCubeFrame.fineCubeFourierEnergy, SegmentedVDM.energy,
    fineCubeEvaluation, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro α _
  apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
  apply Finset.sum_congr rfl
  intro j _
  have hphase :
      Complex.I * (∑ k, ((α k : ℕ) : ℂ) * x j k) =
        Complex.I * ((∑ k, (α k : ℝ) * x j k : ℝ) : ℂ) := by
    congr 1
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [mul_comm (v j), hphase]

/-! ### Normalization bridge to the translated-cube frame

The remaining analytic input is the fine-cube lower frame bound with constant
`2 - exp (1 / (2 * β))`, i.e. the `r = 0`, `m = K` case of manuscript
`thm:well_separated_segmented`.  Its proved form
`BartonCubeFrame.fineCubeFourier_bounds_of_translatedCube` cannot be invoked
here because `General.Fourier.BartonCubeFrame` imports this module
(`NumDetect.Segmented.ClumpBounds`) to expose the `HasFineCubeFrame` interface.
The normalization bridge to the importable translated-cube frame
`External.translatedCubeFourier_lowerFrame` is the shared conversion
`FineCubeFrame.translatedCubeFourierEnergy_normalizedAngularPoint` through
`FineCubeFrame.normalizedAngularPoint`. -/

/-- The fine-cube lower frame bound with constant `a_β` on an `η`-separated
angular node family.  This is the `r = 0`, `m = K` case of manuscript
`thm:well_separated_segmented`, obtained from the proved translated-cube
Barton frame through the normalization bridge above. -/
private theorem fineCube_frame_of_angularSeparation
    {d : ℕ} {ι : Type} [Fintype ι] {K : ℕ} {β : ℝ}
    (hd : 1 ≤ d) (hK : 1 ≤ K) (hβ : 1 / (2 * Real.log 2) ≤ β)
    (x : ι → Point d)
    (hx : ∀ j, InAngularCube (x j))
    (hsep : ∀ i j, i ≠ j →
      4 * Real.pi * β * d / (K + 1) ≤ periodicLInfDistance (x i) (x j)) :
    ∀ v,
      (2 - Real.exp (1 / (2 * β))) * (((K + 1) ^ d : ℕ) : ℝ) *
          SegmentedVDM.energy v ≤
        SegmentedVDM.energy (fineCubeEvaluation K x *ᵥ v) := by
  intro v
  have hN : 2 ≤ K + 1 := by omega
  have hx' :
      ∀ j, External.InUnitHalfOpenCube
        (FineCubeFrame.normalizedAngularPoint (x j)) :=
    fun j => FineCubeFrame.normalizedAngularPoint_mem_halfOpenCube (hx j)
  have hsep' :
      ∀ i j, i ≠ j →
        2 * β * d / (K + 1) ≤
          External.unitPeriodicLInfDistance
            (FineCubeFrame.normalizedAngularPoint (x i))
            (FineCubeFrame.normalizedAngularPoint (x j)) := by
    intro i j hij
    rw [FineCubeFrame.normalizedAngularPoint_lInfDistance (hx i) (hx j)]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    calc
      (2 * β * d / (K + 1)) * (2 * Real.pi) =
          4 * Real.pi * β * d / (K + 1) := by ring
      _ ≤ periodicLInfDistance (x i) (x j) := hsep i j hij
  have h := External.translatedCubeFourier_lowerFrame β
    (fun j => FineCubeFrame.normalizedAngularPoint (x j)) hd hN hβ hx'
    (by simpa only [Nat.cast_add, Nat.cast_one] using hsep') v
  rw [FineCubeFrame.translatedCubeFourierEnergy_normalizedAngularPoint] at h
  rwa [← fineCubeFourierEnergy_eq_energy_fineCubeEvaluation]

/-- Product of one cardinal factor per color class, realizing the decomposition
of manuscript `prop:decomposition` by the injective slots of `C`.  The
anchor's value is one, every node of a family covered by the non-anchor labels
is annihilated, and the coefficient `ℓ¹` mass is at most `(1 / √a) ^ nStar`
when each color class carries a fine-cube frame with constant `a`.  This is the
constructive core of manuscript `lem:localization`. -/
theorem localizationPolynomial_of_colorCover
    {d n A nStar K D : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    (outside : Fin n → Prop)
    (hcover : ∀ j, outside j → C.label j ≠ C.label anchor)
    (hKD : K < D) (hprodD : nStar * K < D)
    {a : ℝ} (ha : 0 < a)
    (hframe : ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
      a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy
          (fineCubeEvaluation K
            (fun j : ↥(clumpColorClass C anchor color) => x j) *ᵥ v)) :
    ∃ P : SegmentedPolynomial d (nStar * K) 0 D,
      P.angularValue (x anchor) = 1 ∧
      (∀ j, outside j → P.angularValue (x j) = 0) ∧
      P.mass ≤ (1 / Real.sqrt a) ^ nStar := by
  classical
  choose F hF using fun color =>
    fineCube_cardinalPolynomial hKD
      (fun j : ↥(clumpColorClass C anchor color) => x j)
      ⟨anchor, anchor_mem_clumpColorClass C anchor color⟩ ha
      (hframe color)
  have hq : K * nStar < D := by simpa [Nat.mul_comm] using hprodD
  let Q := SegmentedPolynomial.prod nStar F hq
  let P : SegmentedPolynomial d (nStar * K) 0 D :=
    Q.widen (by simp [Nat.mul_comm]) (by simp) hprodD
  refine ⟨P, ?_, ?_, ?_⟩
  · simp only [P, SegmentedPolynomial.angularValue_widen,
      Q, SegmentedPolynomial.angularValue_prod]
    have hone (color : Fin nStar) : (F color).angularValue (x anchor) = 1 := by
      simpa using (hF color).1
        ⟨anchor, anchor_mem_clumpColorClass C anchor color⟩
    simp [hone]
  · intro j hj
    simp only [P, SegmentedPolynomial.angularValue_widen,
      Q, SegmentedPolynomial.angularValue_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (C.slot j))
    have hne : C.label j ≠ C.label anchor := hcover j hj
    have hmem : j ∈ clumpColorClass C anchor (C.slot j) := by
      simp [hne]
    have hzero := (hF (C.slot j)).1 ⟨j, hmem⟩
    have haj : anchor ≠ j := by
      intro he
      exact hne (congrArg C.label he.symm)
    simpa [Subtype.ext_iff, haj] using hzero
  · simp only [P, SegmentedPolynomial.mass_widen]
    calc
      Q.mass ≤ ∏ color : Fin nStar, (F color).mass :=
        SegmentedPolynomial.mass_prod_le F hq
      _ ≤ ∏ _color : Fin nStar, 1 / Real.sqrt a :=
        Finset.prod_le_prod
          (fun color _ => (F color).mass_nonneg)
          (fun color _ => (hF color).2)
      _ = _ := by simp

/-- Product of one cardinal factor per color eliminates every node outside the
anchor's clump.  This is the color-class form of the general localization
theorem `localizationPolynomial_of_angularClumpStructure` (manuscript
`lem:localization`): the vanishing set is phrased by non-anchor labels and the
fine-cube frame hypothesis is kept explicit. -/
theorem localizationPolynomial_of_colorFrames
    {d n A nStar K D : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    (hKD : K < D) (hprodD : nStar * K < D)
    {a : ℝ} (ha : 0 < a)
    (hframe : ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
      a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy
          (fineCubeEvaluation K
            (fun j : ↥(clumpColorClass C anchor color) => x j) *ᵥ v)) :
    ∃ P : SegmentedPolynomial d (nStar * K) 0 D,
      P.angularValue (x anchor) = 1 ∧
      (∀ j, C.label j ≠ C.label anchor → P.angularValue (x j) = 0) ∧
      P.mass ≤ (1 / Real.sqrt a) ^ nStar :=
  localizationPolynomial_of_colorCover C anchor
    (fun j => C.label j ≠ C.label anchor) (fun _ hj => hj)
    hKD hprodD ha hframe

/-- Combine localization outside the anchor's clump with quantized
interpolation inside that clump. -/
theorem segmentedInterpolationPolynomial_of_colorFrames
    {d n A nStar K m₁ r D : ℕ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    (hd : 1 ≤ d) (hnStar : 1 ≤ nStar) (hr : 2 * nStar ≤ r)
    (hD : 0 < D) (hm₁D : m₁ < D) {τ Δ a : ℝ} (hΔ : 0 < Δ)
    (hcube : ∀ j, InAngularCube (x j))
    (hsame : ∀ i j, C.label i = C.label j →
      periodicLInfDistance (x i) (x j) ≤ τ)
    (hτ : τ ≤ Real.pi / (2 * D * d))
    (hmin : ∀ i j, i ≠ j →
      Δ ≤ periodicL1Distance (x i) (x j))
    (hscale : Δ ≤ Real.pi * nStar / (r * D))
    (ha : 0 < a) (hK : nStar * K ≤ m₁)
    (hframe : ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
      a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
        SegmentedVDM.energy
          (fineCubeEvaluation K
            (fun j : ↥(clumpColorClass C anchor color) => x j) *ᵥ v)) :
    ∃ P : SegmentedPolynomial d m₁ (r - r / nStar) D,
      (∀ j, P.angularValue (x j) = if anchor = j then 1 else 0) ∧
      P.mass ≤
        (1 / Real.sqrt a) ^ nStar *
        (Real.sqrt 2 /
          (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1) := by
  classical
  have hKD : K < D := by
    have hKle : K ≤ nStar * K := by
      simpa using Nat.mul_le_mul_right K hnStar
    exact lt_of_le_of_lt (hKle.trans hK) hm₁D
  have hprodD : nStar * K < D := lt_of_le_of_lt hK hm₁D
  obtain ⟨G₀, hGanchor, hGzero, hGmass⟩ :=
    localizationPolynomial_of_colorFrames C anchor hKD hprodD ha hframe
  let G : SegmentedPolynomial d m₁ 0 D :=
    G₀.widen hK le_rfl hm₁D
  obtain ⟨B, hBvalue, hBmass⟩ :=
    withinClumpPolynomial C anchor hd hnStar hr hD hΔ hcube hsame hτ hmin hscale
  have hsum : m₁ + 0 < D := by simpa using hm₁D
  let P : SegmentedPolynomial d m₁ (r - r / nStar) D :=
    (G.mul B hsum).widen (by simp) (by simp) hm₁D
  refine ⟨P, ?_, ?_⟩
  · intro j
    simp only [P, SegmentedPolynomial.angularValue_widen,
      SegmentedPolynomial.angularValue_mul,
      G, SegmentedPolynomial.angularValue_widen]
    by_cases hj : C.label j = C.label anchor
    · rw [hBvalue j hj]
      by_cases haj : anchor = j
      · subst j
        simp [hGanchor]
      · simp [haj]
    · rw [hGzero j hj, zero_mul]
      have haj : anchor ≠ j := by
        intro h
        exact hj (congrArg C.label h.symm)
      simp [haj]
  · simp only [P, SegmentedPolynomial.mass_widen,
      G, SegmentedPolynomial.mass_widen]
    have hGmass' : G.mass ≤ (1 / Real.sqrt a) ^ nStar := by
      simpa [G] using hGmass
    calc
      (G.mul B hsum).mass ≤ G.mass * B.mass :=
        SegmentedPolynomial.mass_mul_le G B hsum
      _ ≤ (1 / Real.sqrt a) ^ nStar *
          (Real.sqrt 2 /
            (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1) :=
        mul_le_mul hGmass' hBmass B.mass_nonneg (by positivity)

/-- The support assumptions expose slot data for the manuscript decomposition. -/
theorem clumpStructure_has_slots
    {d n A nStar : ℕ} {x : Fin n → Point d} {τ η : ℝ}
    (h : IsAngularClumpStructure x A nStar τ η) :
    ∃ C : ClumpSlots (A := A) (nStar := nStar) x,
      (∀ i j, C.label i = C.label j →
        periodicLInfDistance (x i) (x j) ≤ τ) ∧
      ∀ i j, C.label i ≠ C.label j →
        η < periodicLInfDistance (x i) (x j) := by
  rcases h with ⟨_, _, _, _, label, _, hsize, _, hsame, hcross⟩
  obtain ⟨C, hC⟩ := exists_clumpSlots label hsize
  refine ⟨C, ?_, ?_⟩
  · intro i j hij
    exact hsame i j (by simpa only [hC] using hij)
  · intro i j hij
    exact hcross i j (by simpa only [hC] using hij)

/-- Manuscript `lem:localization`. For clumped nodes and `m < D`, the
localizing function belongs to the canonical space `𝒫(m,0,D,d)` and has the
stated interpolation values and torus `L∞` bound. The proof applies
`angularClump_decomposition` to the complement of the anchor's clump; each
partition class together with the anchor gives one cardinal factor. -/
theorem localizationPolynomial_of_angularClumpStructure
    {d n A nStar m D : ℕ} {x : Fin n → Point d} {τ η β : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η)
    (hDm : m < D) (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d / ((m / nStar : ℕ) + 1) ≤ η)
    (anchor : Fin n) :
    ∃ P : SegmentedPolynomial d m 0 D,
      P.angularValue (x anchor) = 1 ∧
      (∀ j, j ∉ localNeighborhood x anchor τ → P.angularValue (x j) = 0) ∧
      P.linftyNorm ≤
        (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) := by
  classical
  obtain ⟨C, hsame, hcross⟩ := clumpStructure_has_slots hclumps
  have hτ : 0 < τ := hclumps.2.1
  have hτη : τ ≤ η := hclumps.2.2.1
  have hcube : ∀ j, InAngularCube (x j) := hclumps.2.2.2.1
  have hneighborhood (j : Fin n) :
      localNeighborhood x j τ =
        Finset.univ.filter fun k => C.label k = C.label j :=
    localNeighborhood_eq_of_clumpLabels hτη hsame hcross j
  have hbridge (j : Fin n) (hj : j ∉ localNeighborhood x anchor τ) :
      C.label j ≠ C.label anchor := by
    intro hlabel
    apply hj
    rw [hneighborhood anchor]
    simp [hlabel]
  have haβpos : 0 < 2 - Real.exp (1 / (2 * β)) :=
    wellSeparatedFrameConstant_pos hβ
  have hrpow : (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar =
      (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) :=
    inv_sqrt_pow_eq_rpow haβpos nStar
  have hone : (1 : ℝ) ≤ (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) := by
    have haβle := wellSeparatedFrameConstant_le_one hβ
    have hneg : (-(nStar : ℝ) / 2) ≤ 0 := by
      rw [neg_div 2 (nStar : ℝ)]
      exact neg_nonpos.mpr
        (div_nonneg (Nat.cast_nonneg nStar) (by norm_num))
    calc
      (1 : ℝ) = (2 - Real.exp (1 / (2 * β))) ^ (0 : ℝ) :=
        (Real.rpow_zero _).symm
      _ ≤ (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_ge haβpos haβle hneg
  by_cases hout : ∃ j, j ∉ localNeighborhood x anchor τ
  · obtain ⟨j₀, hj₀⟩ := hout
    -- In the nontrivial case the dimension is positive.
    have hd : 1 ≤ d := by
      by_contra hnd
      have hd0 : d = 0 := by omega
      haveI hempty : IsEmpty (Fin d) :=
        ⟨fun i => by have hi := i.isLt; omega⟩
      haveI : Subsingleton (Point d) :=
        ⟨fun u v => funext fun k => hempty.elim k⟩
      have heq : x anchor = x j₀ := Subsingleton.elim _ _
      apply hj₀
      simp only [localNeighborhood, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rw [heq, periodicLInfDistance_self]
      exact hτ.le
    -- The manuscript argument gives `K = ⌊m / nStar⌋ ≥ 1`.
    have hK : 1 ≤ (m / nStar : ℕ) := by
      by_contra hnk
      have hK0 : (m / nStar : ℕ) = 0 := by
        by_contra hk
        exact hnk (Nat.one_le_iff_ne_zero.2 hk)
      have hη' : 4 * Real.pi * β * d ≤ η := by
        have hden : (((m / nStar : ℕ) : ℝ) + 1) = 1 := by
          rw [hK0]
          simp
        rw [hden, div_one] at hη
        exact hη
      have hquarter : (1 : ℝ) / 4 < 1 / (2 * Real.log 2) := by
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [Real.log_two_lt_d9]
      have hβq : (1 : ℝ) / 4 < β := hquarter.trans hβ
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hfac : (1 : ℝ) < 4 * β * d := by
        have h1 : (1 : ℝ) < 4 * β := by nlinarith
        calc
          (1:ℝ) = 1 * 1 := by ring
          _ < (4 * β) * 1 := by nlinarith
          _ ≤ (4 * β) * d := mul_le_mul_of_nonneg_left hdR (by positivity)
          _ = 4 * β * d := by ring
      have hlt : Real.pi < 4 * Real.pi * β * d := by
        have heq : 4 * Real.pi * β * d = Real.pi * (4 * β * d) := by ring
        rw [heq]
        simpa using mul_lt_mul_of_pos_left hfac Real.pi_pos
      have hfar : η < periodicLInfDistance (x anchor) (x j₀) :=
        hcross anchor j₀ (hbridge j₀ hj₀).symm
      have hle : periodicLInfDistance (x anchor) (x j₀) ≤ Real.pi :=
        periodicLInfDistance_le_pi (hcube anchor) (hcube j₀)
      linarith
    -- Decompose the complement as in manuscript `prop:decomposition`.
    let Y : Finset (Fin n) :=
      Finset.univ.filter fun j => j ∉ localNeighborhood x anchor τ
    have hY : Y.Nonempty := ⟨j₀, by simp [Y, hj₀]⟩
    obtain ⟨ν, pieces, _hνpos, hνle, _hpieces_nonempty,
      _hpieces_disjoint, hpieces_union, hpieces_sep⟩ :=
      angularClump_decomposition hclumps Y hY
    have hpieceY (ℓ : Fin ν) (j : Fin n) (hj : j ∈ pieces ℓ) : j ∈ Y := by
      rw [hpieces_union]
      exact Finset.mem_biUnion.mpr ⟨ℓ, Finset.mem_univ _, hj⟩
    have hYoutside (j : Fin n) (hj : j ∈ Y) :
        j ∉ localNeighborhood x anchor τ := by
      simpa [Y] using hj
    let W (ℓ : Fin ν) : Finset (Fin n) := insert anchor (pieces ℓ)
    have hWanchor (ℓ : Fin ν) : anchor ∈ W ℓ :=
      Finset.mem_insert_self _ _
    have hWsep (ℓ : Fin ν) (i j : ↥(W ℓ)) (hij : i ≠ j) :
        η < periodicLInfDistance (x i) (x j) := by
      have hi : (i : Fin n) = anchor ∨ (i : Fin n) ∈ pieces ℓ := by
        exact Finset.mem_insert.mp i.property
      have hj : (j : Fin n) = anchor ∨ (j : Fin n) ∈ pieces ℓ := by
        exact Finset.mem_insert.mp j.property
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact False.elim (hij (Subtype.ext (hi.trans hj.symm)))
      · rw [hi]
        exact hcross anchor j
          (hbridge j (hYoutside j (hpieceY ℓ j hj))).symm
      · rw [hj]
        exact hcross i anchor
          (hbridge i (hYoutside i (hpieceY ℓ i hi)))
      · exact hpieces_sep ℓ i j hi hj
          (fun h => hij (Subtype.ext h))
    -- Each partition class together with the anchor is separated and yields
    -- one cardinal factor on the fine frequency cube.
    have hframe (ℓ : Fin ν)
        (v : ↥(W ℓ) → ℂ) :
        (2 - Real.exp (1 / (2 * β))) *
            ((((m / nStar) + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
          SegmentedVDM.energy
            (fineCubeEvaluation (m / nStar)
              (fun j : ↥(W ℓ) => x j) *ᵥ v) := by
      refine fineCube_frame_of_angularSeparation hd hK (le_of_lt hβ)
        (fun j : ↥(W ℓ) => x j)
        (fun j => hcube j) (fun i j hij => ?_) v
      have hsep' :
          4 * Real.pi * β * d / ((m / nStar : ℕ) + 1) ≤
            periodicLInfDistance (x i) (x j) :=
        hη.trans (hWsep ℓ i j hij).le
      simpa using hsep'
    have hKD : m / nStar < D :=
      lt_of_le_of_lt (Nat.div_le_self m nStar) hDm
    choose F hF using fun ℓ =>
      fineCube_cardinalPolynomial hKD
        (fun j : ↥(W ℓ) => x j)
        ⟨anchor, hWanchor ℓ⟩ haβpos (hframe ℓ)
    have hprodFine : ν * (m / nStar) ≤ m := by
      calc
        ν * (m / nStar) ≤ nStar * (m / nStar) :=
          Nat.mul_le_mul_right (m / nStar) hνle
        _ = (m / nStar) * nStar := Nat.mul_comm _ _
        _ ≤ m := Nat.div_mul_le_self m nStar
    have hq : (m / nStar) * ν < D := by
      have h' := lt_of_le_of_lt hprodFine hDm
      simpa [Nat.mul_comm] using h'
    let Q := SegmentedPolynomial.prod ν F hq
    let P : SegmentedPolynomial d m 0 D :=
      Q.widen (by simpa [Nat.mul_comm] using hprodFine) (by simp) hDm
    have hPone : P.angularValue (x anchor) = 1 := by
      simp only [P, SegmentedPolynomial.angularValue_widen,
        Q, SegmentedPolynomial.angularValue_prod]
      have hone (ℓ : Fin ν) : (F ℓ).angularValue (x anchor) = 1 := by
        simpa using (hF ℓ).1 ⟨anchor, hWanchor ℓ⟩
      simp [hone]
    have hPzero (j : Fin n) (hj : j ∉ localNeighborhood x anchor τ) :
        P.angularValue (x j) = 0 := by
      simp only [P, SegmentedPolynomial.angularValue_widen,
        Q, SegmentedPolynomial.angularValue_prod]
      have hjY : j ∈ Y := by simp [Y, hj]
      rw [hpieces_union] at hjY
      obtain ⟨ℓ, _hℓ, hjpiece⟩ := Finset.mem_biUnion.mp hjY
      apply Finset.prod_eq_zero (Finset.mem_univ ℓ)
      have hjW : j ∈ W ℓ := Finset.mem_insert_of_mem hjpiece
      have hne : anchor ≠ j := by
        intro he
        apply hj
        rw [← he]
        simp only [localNeighborhood, Finset.mem_filter, Finset.mem_univ,
          true_and, periodicLInfDistance_self]
        exact hτ.le
      have hzero := (hF ℓ).1 ⟨j, hjW⟩
      simpa [Subtype.ext_iff, hne] using hzero
    have hbase : 1 ≤ 1 / Real.sqrt (2 - Real.exp (1 / (2 * β))) := by
      have hsqrtle : Real.sqrt (2 - Real.exp (1 / (2 * β))) ≤ 1 := by
        nlinarith [Real.sq_sqrt haβpos.le,
          Real.sqrt_nonneg (2 - Real.exp (1 / (2 * β))),
          wellSeparatedFrameConstant_le_one hβ]
      apply (le_div_iff₀ (Real.sqrt_pos.2 haβpos)).2
      simpa using hsqrtle
    have hPmass : P.mass ≤
        (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar := by
      simp only [P, SegmentedPolynomial.mass_widen]
      calc
        Q.mass ≤ ∏ ℓ : Fin ν, (F ℓ).mass :=
          SegmentedPolynomial.mass_prod_le F hq
        _ ≤ ∏ _ℓ : Fin ν,
                1 / Real.sqrt (2 - Real.exp (1 / (2 * β))) :=
          Finset.prod_le_prod
            (fun ℓ _ => (F ℓ).mass_nonneg)
            (fun ℓ _ => (hF ℓ).2)
        _ = (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ ν := by simp
        _ ≤ (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar :=
          pow_le_pow_right₀ hbase hνle
    refine ⟨P, ?_, ?_, ?_⟩
    · show P.angularValue (x anchor) = 1
      exact hPone
    · intro j hj
      show P.angularValue (x j) = 0
      exact hPzero j hj
    · show P.linftyNorm ≤
        (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2)
      calc
        P.linftyNorm ≤ P.mass := P.linftyNorm_le_mass
        _ ≤ (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar := hPmass
        _ = (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) := hrpow
  · -- The complement of the neighborhood is empty: the constant polynomial
    -- works, as in the manuscript.
    have hall : ∀ j : Fin n, j ∈ localNeighborhood x anchor τ := by
      intro j
      by_contra hk
      exact hout ⟨j, hk⟩
    let P : SegmentedPolynomial d m 0 D :=
      (SegmentedPolynomial.one d D (by omega)).widen
        (Nat.zero_le m) le_rfl hDm
    refine ⟨P, ?_, ?_, ?_⟩
    · show P.angularValue (x anchor) = 1
      change
        ((SegmentedPolynomial.one d D (by omega)).widen
          (Nat.zero_le m) le_rfl hDm).angularValue (x anchor) = 1
      rw [SegmentedPolynomial.angularValue_widen]
      exact SegmentedPolynomial.eval_one d D (by omega)
        (fun k => x anchor k / (2 * Real.pi))
    · intro j hj
      exact absurd (hall j) hj
    · show P.linftyNorm ≤
        (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2)
      calc
        P.linftyNorm ≤ P.mass := P.linftyNorm_le_mass
        _ = 1 := by simp [P]
        _ ≤ (2 - Real.exp (1 / (2 * β))) ^ (-(nStar : ℝ) / 2) := hone

/-- Complete segmented polynomial construction from fine-cube frame bounds. This
is the algebraic and geometric core of the manuscript theorem; the remaining
analytic input is exactly `hframe`. -/
theorem segmentedVandermonde_ge_of_colorFrames
    {d n A nStar m₁ b m r D K : ℕ} {τ η Δ a : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hsplit : m₁ + b = m) (hmD : m < D)
    (hK : nStar * K ≤ m₁)
    (hD : 0 < D) (hτ : τ ≤ Real.pi / (2 * D * d))
    (hr : 2 * nStar ≤ r) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j →
      Δ ≤ periodicL1Distance (μ.node i) (μ.node j))
    (hscale : Δ ≤ Real.pi * nStar / (r * D))
    (ha : 0 < a)
    (hframe :
      ∀ (C : ClumpSlots (A := A) (nStar := nStar) μ.node)
        (anchor : Fin n),
        (∀ i j, C.label i = C.label j →
          periodicLInfDistance (μ.node i) (μ.node j) ≤ τ) →
        (∀ i j, C.label i ≠ C.label j →
          η < periodicLInfDistance (μ.node i) (μ.node j)) →
        ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
          a * (((K + 1) ^ d : ℕ) : ℝ) * SegmentedVDM.energy v ≤
            SegmentedVDM.energy
              (fineCubeEvaluation K
                (fun j : ↥(clumpColorClass C anchor color) => μ.node j) *ᵥ v)) :
    let H :=
      (1 / Real.sqrt a) ^ nStar *
        (Real.sqrt 2 /
          (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1)
    Real.sqrt
          (((((r / nStar) + 1) * (b + 1)) ^ d : ℕ) : ℝ) /
        (Real.sqrt n * H) ≤
      matrixSingularValue
        (segmentedVandermonde m r D μ.node) (n - 1) := by
  classical
  dsimp only
  have hnStar : 1 ≤ nStar := (hclumps.1).trans' (by omega)
  have hm₁D : m₁ < D := by omega
  have hsum : m₁ + b < D := by simpa [hsplit] using hmD
  have hcube : ∀ j, InAngularCube (μ.node j) := hclumps.2.2.2.1
  obtain ⟨C, hsame, hcross⟩ := clumpStructure_has_slots hclumps
  choose P hPvalue hPmass using fun anchor =>
    segmentedInterpolationPolynomial_of_colorFrames C anchor hd hnStar hr hD hm₁D hΔ
      hcube hsame hτ hmin hscale ha hK
      (hframe C anchor hsame hcross)
  let H :=
    (1 / Real.sqrt a) ^ nStar *
      (Real.sqrt 2 /
        (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1)
  have hH : 0 < H := by
    dsimp [H]
    have hrPos : 0 < r := by omega
    have hnStarR : (0 : ℝ) < nStar := by exact_mod_cast hnStar
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have hrR : (0 : ℝ) < r := by exact_mod_cast hrPos
    have hden :
        0 < ((r : ℝ) / nStar) * D * Δ / Real.pi := by
      positivity
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hh :=
    SegmentedPolynomial.singularValue_ge_of_smoothedSegmentedPolynomials
      (Nat.zero_lt_of_lt hn) μ.node P hPvalue hsum hH hPmass
      (b := b) (z := r / nStar)
  rw [hsplit] at hh
  have hdiv : r / nStar ≤ r := Nat.div_le_self r nStar
  rw [Nat.sub_add_cancel hdiv] at hh
  exact hh

/-- Rewrite the coefficient-mass ratio into the explicit manuscript constant. -/
theorem segmentedLowerBound_le_smoothedRatio
    {d n nStar b r D : ℕ} {a Δ : ℝ}
    (hn : 0 < n) (hnStar : 0 < nStar) (hr : 0 < r) (hD : 0 < D)
    (ha : 0 < a) (hΔ : 0 < Δ) :
    1 / Real.sqrt n *
          a ^ ((nStar : ℝ) / 2) *
          Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt 2) ^ (nStar - 1) *
          ((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
            (nStar - 1)) ≤
      Real.sqrt
          (((((r / nStar) + 1) * (b + 1)) ^ d : ℕ) : ℝ) /
        (Real.sqrt n *
          ((1 / Real.sqrt a) ^ nStar *
            (Real.sqrt 2 /
              (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^
                (nStar - 1))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnStarR : (0 : ℝ) < nStar := by exact_mod_cast hnStar
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hz :
      (r : ℝ) / nStar ≤ ((r / nStar : ℕ) : ℝ) + 1 := by
    have hlt := Nat.lt_mul_div_succ r hnStar
    have hltR :
        (r : ℝ) < nStar * ((r / nStar : ℕ) + 1) := by
      exact_mod_cast hlt
    exact (div_le_iff₀ hnStarR).2 (by
      simpa only [mul_comm] using hltR.le)
  have hbase :
      (r : ℝ) / nStar * (b + 1) ≤
        (((r / nStar : ℕ) : ℝ) + 1) * (b + 1) := by
    gcongr
  have hpow :
      ((r : ℝ) / nStar * (b + 1)) ^ d ≤
        ((((r / nStar : ℕ) : ℝ) + 1) * (b + 1)) ^ d :=
    pow_le_pow_left₀ (by positivity) hbase d
  have hvolume :
      Real.sqrt
          (((r : ℝ) / nStar) ^ d *
            (((b + 1 : ℕ) : ℝ) ^ d)) ≤
        Real.sqrt
          (((((r / nStar) + 1) * (b + 1)) ^ d : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    push_cast
    simpa only [mul_pow] using hpow
  have hsqrtpow :
      (Real.sqrt a) ^ nStar = a ^ ((nStar : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha.le]
    congr 1
    ring
  have ht :
      ((r : ℝ) / nStar) * D * Δ / Real.pi =
        ((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ := by
    push_cast
    field_simp
  let H :=
    (1 / Real.sqrt a) ^ nStar *
      (Real.sqrt 2 /
        (((r : ℝ) / nStar) * D * Δ / Real.pi)) ^ (nStar - 1)
  have hH : 0 < H := by
    dsimp [H]
    positivity
  calc
    1 / Real.sqrt n *
          a ^ ((nStar : ℝ) / 2) *
          Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt 2) ^ (nStar - 1) *
          ((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
            (nStar - 1)) =
        Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt n * H) := by
      dsimp [H]
      rw [← hsqrtpow, ← ht]
      ring_nf
      field_simp [ne_of_gt hnStarR, ne_of_gt hrR, ne_of_gt hDR,
        ne_of_gt hΔ, ne_of_gt (Real.sqrt_pos.2 ha), Real.pi_ne_zero]
    _ ≤
        Real.sqrt
            (((((r / nStar) + 1) * (b + 1)) ^ d : ℕ) : ℝ) /
          (Real.sqrt n * H) :=
      div_le_div_of_nonneg_right hvolume (by positivity)

/-- Manuscript-shaped segmented Vandermonde bound from the exact one-sided
fine-cube frame input. -/
theorem segmentedVandermonde_minimumSingularValue_of_colorFrames
    {d n A nStar m₁ b m r D K : ℕ} {τ η Δ β : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hsplit : m₁ + b = m) (hmD : m < D)
    (hK : nStar * K ≤ m₁)
    (hD : 0 < D) (hτ : τ ≤ Real.pi / (2 * D * d))
    (hβ : 1 / (2 * Real.log 2) < β)
    (hr : 2 * nStar ≤ r) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j →
      Δ ≤ periodicL1Distance (μ.node i) (μ.node j))
    (hscale : Δ ≤ Real.pi * nStar / (r * D))
    (hframe :
      ∀ (C : ClumpSlots (A := A) (nStar := nStar) μ.node)
        (anchor : Fin n),
        (∀ i j, C.label i = C.label j →
          periodicLInfDistance (μ.node i) (μ.node j) ≤ τ) →
        (∀ i j, C.label i ≠ C.label j →
          η < periodicLInfDistance (μ.node i) (μ.node j)) →
        ∀ color (v : ↥(clumpColorClass C anchor color) → ℂ),
          (2 - Real.exp (1 / (2 * β))) *
                (((K + 1) ^ d : ℕ) : ℝ) *
                SegmentedVDM.energy v ≤
            SegmentedVDM.energy
              (fineCubeEvaluation K
                (fun j : ↥(clumpColorClass C anchor color) => μ.node j) *ᵥ v)) :
    1 / Real.sqrt n *
          (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
          Real.sqrt
            (((r : ℝ) / nStar) ^ d *
              (((b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt 2) ^ (nStar - 1) *
          ((((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ) ^
            (nStar - 1)) ≤
      matrixSingularValue
        (segmentedVandermonde m r D μ.node) (n - 1) := by
  let a := 2 - Real.exp (1 / (2 * β))
  have ha : 0 < a := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hβpos : 0 < β :=
      (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
    have hexponent : 1 / (2 * β) < Real.log 2 := by
      have h := (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).1 hβ
      apply (div_lt_iff₀ (by positivity : 0 < 2 * β)).2
      nlinarith
    have hexp : Real.exp (1 / (2 * β)) < 2 := by
      calc
        Real.exp (1 / (2 * β)) < Real.exp (Real.log 2) :=
          Real.exp_lt_exp.mpr hexponent
        _ = 2 := Real.exp_log (by norm_num)
    dsimp [a]
    linarith
  have hnStar : 0 < nStar :=
    (by omega : 0 < 2).trans_le hclumps.1
  have hrPos : 0 < r :=
    (Nat.mul_pos (by omega) hnStar).trans_le hr
  have hraw :=
    segmentedVandermonde_ge_of_colorFrames μ hd hn hclumps hsplit hmD hK hD
      hτ hr hΔ hmin hscale ha hframe
  exact
    (segmentedLowerBound_le_smoothedRatio
      (Nat.zero_lt_of_lt hn) hnStar hrPos hD ha hΔ).trans hraw

end

end NumDetect
end LeanNumDetect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Every frequency queried by a segmented GHM lies in its declared band. -/
theorem segmented_query_in_band
    {d m r D : ℕ} (α β : SegmentedIndex d m r) :
    InFrequencyBand (segmentedCutoff m r D) (fun k =>
      segmentedFrequency d m r D α k +
        segmentedFrequency d m r D β k - segmentedCutoff m r D) := by
  intro k
  simp only [segmentedFrequency, segmentedCutoff]
  have hαr : (α k).1.val ≤ r := Nat.le_of_lt_succ (α k).1.isLt
  have hβr : (β k).1.val ≤ r := Nat.le_of_lt_succ (β k).1.isLt
  have hαm : (α k).2.val ≤ m := Nat.le_of_lt_succ (α k).2.isLt
  have hβm : (β k).2.val ≤ m := Nat.le_of_lt_succ (β k).2.isLt
  have hα : D * (α k).1.val + (α k).2.val ≤ r * D + m := by
    nlinarith [Nat.mul_le_mul_left D hαr]
  have hβ : D * (β k).1.val + (β k).2.val ≤ r * D + m := by
    nlinarith [Nat.mul_le_mul_left D hβr]
  push_cast
  rw [abs_le]
  have hαR : (D : ℝ) * (α k).1.val + (α k).2.val ≤
      (r : ℝ) * D + m := by exact_mod_cast hα
  have hβR : (D : ℝ) * (β k).1.val + (β k).2.val ≤
      (r : ℝ) * D + m := by exact_mod_cast hβ
  constructor <;> nlinarith [show (0 : ℝ) ≤ D * (α k).1.val + (α k).2.val by positivity,
    show (0 : ℝ) ≤ D * (β k).1.val + (β k).2.val by positivity]

/-- Pointwise perturbation bound for the segmented measurement matrix. -/
theorem segmentedMeasurementMatrix_sub_fourier_entry_lt
    {d n m r D : ℕ} {σ : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hmeasurement : IsBandMeasurement μ (segmentedCutoff m r D) σ Y)
    (α β : SegmentedIndex d m r) :
    ‖(segmentedMeasurementMatrix m r D Y -
        segmentedMeasurementMatrix m r D (fourier μ)) α β‖ < σ := by
  rcases hmeasurement with ⟨W, hW, hY⟩
  let ω : Point d := fun k =>
    segmentedFrequency d m r D α k +
      segmentedFrequency d m r D β k - segmentedCutoff m r D
  have hband : InFrequencyBand (segmentedCutoff m r D) ω :=
    segmented_query_in_band α β
  have hvalue := hY ω hband
  have hnoise := hW ω hband
  simp only [segmentedMeasurementMatrix, Matrix.sub_apply]
  rw [hvalue, add_sub_cancel_left]
  exact hnoise

/-- Every singular value at or beyond the rank vanishes. -/
theorem matrixSingularValue_eq_zero_of_rank_le'
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {i : ℕ} (hi : A.rank ≤ i) :
    matrixSingularValue A i = 0 := by
  rw [matrixSingularValue]
  apply (A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range).2
  change Module.finrank ℂ (LinearMap.range
    ((Matrix.toLin (EuclideanSpace.basisFun n ℂ).toBasis
      (EuclideanSpace.basisFun m ℂ).toBasis) A)) ≤ i
  rw [← A.rank_eq_finrank_range_toLin
    (EuclideanSpace.basisFun m ℂ).toBasis
    (EuclideanSpace.basisFun n ℂ).toBasis]
  exact hi

/-- A product through `n` columns vanishes from singular-value index `n` onward. -/
theorem matrixSingularValue_mul_eq_zero_of_card_le'
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) {i : ℕ}
    (hi : Fintype.card n ≤ i) :
    matrixSingularValue (A * B) i = 0 := by
  apply matrixSingularValue_eq_zero_of_rank_le'
  exact (Matrix.rank_mul_le_left A B).trans
    ((Matrix.rank_le_card_width A).trans hi)

/-- The noiseless segmented matrix has no singular values beyond the source count. -/
theorem segmentedNoiseless_singularValue_eq_zero
    {d n m r D i : ℕ} (μ : AtomicMeasure d n) (hi : n ≤ i) :
    matrixSingularValue (segmentedNoiselessMatrix m r D μ) i = 0 := by
  rw [segmentedNoiselessMatrix]
  apply matrixSingularValue_eq_zero_of_rank_le'
  have hcard : Fintype.card (Fin n) ≤ i := by simpa using hi
  exact
    (Matrix.rank_mul_le_left
      (segmentedVandermonde m r D μ.node *
        Matrix.diagonal (segmentedPhaseAmplitude m r D μ))
      (segmentedColumnVandermonde m r D μ.node)ᵀ).trans
      ((Matrix.rank_le_card_width
        (segmentedVandermonde m r D μ.node *
          Matrix.diagonal (segmentedPhaseAmplitude m r D μ))).trans hcard)

end

end NumDetect
end LeanNumDetect
