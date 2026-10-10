import NumDetect.Segmented.ClumpBounds
import General.Fourier.BartonCubeFrame
import General.MatrixAnalysis.Reindex
import RandSamp.MultidimensionalMultiClumpSampling

/-! A fully proved angular, normalized version of Li's cube clump bound.
The manuscript can cite the deterministic result; the formalization proves
its discrete version from the already proved interpolation constructions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect.NumDetect
noncomputable section

namespace SegmentedPolynomial

def coarseFineIndexEquiv (d R : ℕ) : SegmentedIndex d 0 R ≃ SegmentedIndex d R 0 where
  toFun a := fun k => ((a k).2, (a k).1)
  invFun a := fun k => ((a k).2, (a k).1)
  left_inv _ := rfl
  right_inv _ := rfl

def coarseToFine {d R D : ℕ} (P : SegmentedPolynomial d 0 R 1)
    (hRD : R < D) : SegmentedPolynomial d R 0 D where
  hD := hRD
  coeff a := P.coeff ((coarseFineIndexEquiv d R).symm a)

@[simp] theorem angularValue_coarseToFine {d R D : ℕ}
    (P : SegmentedPolynomial d 0 R 1) (hRD : R < D) (x : Point d) :
    (P.coarseToFine hRD).angularValue x = P.angularValue x := by
  classical
  rw [angularValue_eq_angularTrigPolynomial, angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial
  apply Fintype.sum_equiv (coarseFineIndexEquiv d R).symm
  intro a
  simp only [coarseToFine]
  congr 2
  congr 1
  apply congrArg (fun z : ℝ => (z : ℂ))
  apply Finset.sum_congr rfl
  intro k _
  have hz : ((a k).1 : ℕ) = 0 := by omega
  simp [segmentedPolynomialFrequency, coarseFineIndexEquiv, hz]

@[simp] theorem mass_coarseToFine {d R D : ℕ}
    (P : SegmentedPolynomial d 0 R 1) (hRD : R < D) :
    (P.coarseToFine hRD).mass = P.mass := by
  classical
  unfold mass
  apply Fintype.sum_equiv (coarseFineIndexEquiv d R).symm
  intro a
  rfl

end SegmentedPolynomial

theorem liFrameConstant_pos {β : ℝ} (hβ : 1 / (2 * Real.log 2) < β) :
    0 < 2 - Real.exp (1 / (2 * β)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβpos : 0 < β := (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hexponent : 1 / (2 * β) < Real.log 2 := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).1 hβ
    apply (div_lt_iff₀ (by positivity : 0 < 2 * β)).2
    nlinarith
  have hexp : Real.exp (1 / (2 * β)) < 2 := by
    calc
      _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hexponent
      _ = 2 := Real.exp_log (by norm_num)
  linarith

def liCubeClumpLower (d n nStar L : ℕ) (β Δ : ℝ) : ℝ :=
  1 / Real.sqrt n * (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
    Real.sqrt ((((2 * (L / (4 * nStar)) + 1) ^ d : ℕ) : ℝ)) /
    (Real.sqrt (((L + 1) ^ d : ℕ) : ℝ) * (Real.sqrt 2) ^ (nStar - 1)) *
    ((L : ℝ) * Δ / (4 * Real.pi * nStar)) ^ (nStar - 1)

theorem liCubeClumpLower_pos {d n nStar L : ℕ} {β Δ : ℝ}
    (hn : 0 < n) (hs : 0 < nStar) (hL : 0 < L)
    (hβ : 1 / (2 * Real.log 2) < β) (hΔ : 0 < Δ) :
    0 < liCubeClumpLower d n nStar L β Δ := by
  unfold liCubeClumpLower
  have ha := liFrameConstant_pos hβ
  positivity

/-- The explicit coefficient depending on dimension, source count, maximal
clump size, bandwidth, and the localization parameter, with no spacing input. -/
def liCubeClumpCoefficient (d n nStar L : ℕ) (β : ℝ) : ℝ :=
  1 / Real.sqrt n * (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
    Real.sqrt ((((2 * (L / (4 * nStar)) + 1) ^ d : ℕ) : ℝ)) /
    (Real.sqrt (((L + 1) ^ d : ℕ) : ℝ) * (Real.sqrt 2) ^ (nStar - 1) *
      (4 * Real.pi * nStar) ^ (nStar - 1))

theorem liCubeClumpLower_eq_coefficient (d n nStar L : ℕ) (β Δ : ℝ) :
    liCubeClumpLower d n nStar L β Δ =
      liCubeClumpCoefficient d n nStar L β * ((L : ℝ) * Δ) ^ (nStar - 1) := by
  unfold liCubeClumpLower liCubeClumpCoefficient
  rw [div_pow]
  ring

theorem liCubeClumpCoefficient_pos {d n nStar L : ℕ} {β : ℝ}
    (hn : 0 < n) (hs : 0 < nStar)
    (hβ : 1 / (2 * Real.log 2) < β) :
    0 < liCubeClumpCoefficient d n nStar L β := by
  have ha := liFrameConstant_pos hβ
  unfold liCubeClumpCoefficient
  positivity

/-- A bandwidth-independent weakening of the exact Li coefficient. -/
def liCubeClumpUniformCoefficient (d n nStar : ℕ) (β : ℝ) : ℝ :=
  (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) /
    (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1) *
      (Real.sqrt (3 * nStar)) ^ d * (4 * Real.pi * nStar) ^ (nStar - 1))

theorem liCubeClumpUniformCoefficient_pos {d n nStar : ℕ} {β : ℝ}
    (hn : 0 < n) (hs : 0 < nStar) (hβ : 1 / (2 * Real.log 2) < β) :
    0 < liCubeClumpUniformCoefficient d n nStar β := by
  have ha := liFrameConstant_pos hβ
  unfold liCubeClumpUniformCoefficient
  positivity

private theorem liCubeClump_cardinality_ratio {d nStar L : ℕ}
    (hs : 0 < nStar) (hL : 8 * nStar ≤ L) :
    1 / (Real.sqrt (3 * nStar)) ^ d ≤
      Real.sqrt (((2 * (L / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
        Real.sqrt (((L + 1) ^ d : ℕ) : ℝ) := by
  let q := L / (4 * nStar)
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le (by omega : 0 < 4 * nStar)).mpr
    (by omega)
  have hlt : L < 4 * nStar * (q + 1) := by
    simpa only [q, Nat.mul_comm] using Nat.lt_mul_div_succ L (by omega : 0 < 4 * nStar)
  have hcount : L + 1 ≤ 3 * nStar * (2 * q + 1) := by nlinarith
  have hp : (L + 1) ^ d ≤ (3 * nStar * (2 * q + 1)) ^ d :=
    Nat.pow_le_pow_left hcount d
  have hroot : Real.sqrt (((L + 1) ^ d : ℕ) : ℝ) ≤
      (Real.sqrt (3 * nStar)) ^ d * Real.sqrt (((2 * q + 1) ^ d : ℕ) : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg _), mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
    have hpow : ((Real.sqrt (3 * nStar)) ^ d) ^ 2 = (3 * (nStar : ℝ)) ^ d := by
      rw [← pow_mul, Nat.mul_comm d 2, pow_mul,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3 * nStar)]
    rw [hpow]
    exact_mod_cast (by simpa only [Nat.mul_pow] using hp)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [q, one_mul, mul_comm] using hroot

theorem liCubeClumpUniformCoefficient_le_exact {d n nStar L : ℕ} {β : ℝ}
    (hn : 0 < n) (hs : 0 < nStar) (hL : 8 * nStar ≤ L)
    (hβ : 1 / (2 * Real.log 2) < β) :
    liCubeClumpUniformCoefficient d n nStar β ≤ liCubeClumpCoefficient d n nStar L β := by
  have ha := liFrameConstant_pos hβ
  let F := (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) /
    (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1) * (4 * Real.pi * nStar) ^ (nStar - 1))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have h := mul_le_mul_of_nonneg_left (liCubeClump_cardinality_ratio (d := d) hs hL) hF
  calc
    liCubeClumpUniformCoefficient d n nStar β = F * (1 / (Real.sqrt (3 * nStar)) ^ d) := by
      dsimp [liCubeClumpUniformCoefficient, F]
      ring
    _ ≤ F * (Real.sqrt (((2 * (L / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
        Real.sqrt (((L + 1) ^ d : ℕ) : ℝ)) := h
    _ = liCubeClumpCoefficient d n nStar L β := by
      dsimp [liCubeClumpCoefficient, F]
      ring

theorem liCubeClumpUniformLower_le_exact {d n nStar L : ℕ} {β Δ : ℝ}
    (hn : 0 < n) (hs : 0 < nStar) (hL : 8 * nStar ≤ L)
    (hβ : 1 / (2 * Real.log 2) < β) (hΔ : 0 ≤ Δ) :
    liCubeClumpUniformCoefficient d n nStar β * ((L : ℝ) * Δ) ^ (nStar - 1) ≤
      liCubeClumpLower d n nStar L β Δ := by
  rw [liCubeClumpLower_eq_coefficient]
  exact mul_le_mul_of_nonneg_right (liCubeClumpUniformCoefficient_le_exact hn hs hL hβ)
    (by positivity)

/-- Li's geometric hypotheses in the manuscript's angular coordinates.
`τ` is a freely chosen upper bound for the actual clump diameters. -/
def LiCubeClumpGeometry {d n : ℕ} (μ : AtomicMeasure d n)
    (A nStar L : ℕ) (τ η β : ℝ) (hn : 2 ≤ n) : Prop :=
  Even L ∧ 8 * n ≤ L ∧ IsAngularClumpStructure μ.node A nStar τ η ∧
    1 / (2 * Real.log 2) < β ∧
    8 * Real.pi * β * d * nStar / L ≤ τ ∧
    τ ≤ Real.pi / (2 * d) ∧
    periodicMinimumL1Separation μ.node hn ≤ 4 * Real.pi * nStar / L

private theorem liInterpolationPolynomial
    {d n A nStar M : ℕ} {τ η β Δ : ℝ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    (hd : 1 ≤ d) (hs : 1 ≤ nStar) (hM : 2 * nStar ≤ M)
    (hΔ : 0 < Δ) (hβ : 1 / (2 * Real.log 2) < β)
    (hcube : ∀ j, InAngularCube (x j))
    (hsame : ∀ i j, C.label i = C.label j → periodicLInfDistance (x i) (x j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → η < periodicLInfDistance (x i) (x j))
    (hτ : τ ≤ Real.pi / (2 * d))
    (hη : 4 * Real.pi * β * d / ((M / nStar : ℕ) + 1) ≤ η)
    (hmin : ∀ i j, i ≠ j → Δ ≤ periodicL1Distance (x i) (x j))
    (hscale : Δ ≤ 2 * Real.pi * nStar / M) :
    ∃ P : SegmentedPolynomial d (M + (M - M / nStar)) 0 (2 * M + 1),
      (∀ j, P.angularValue (x j) = if anchor = j then 1 else 0) ∧
      P.mass ≤ (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1) := by
  classical
  have ha := liFrameConstant_pos hβ
  have hK : nStar * (M / nStar) ≤ M := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self M nStar
  have hKD : M / nStar < 2 * M + 1 := by
    have hdiv := Nat.div_le_self M nStar
    omega
  have hprodD : nStar * (M / nStar) < 2 * M + 1 := by omega
  have hframe := BartonCubeFrame.hasFineCubeFrame_of_translatedCube hd hβ hη
  have hframes (color : Fin nStar) (v : ↥(clumpColorClass C anchor color) → ℂ) :
      (2 - Real.exp (1 / (2 * β))) * (((M / nStar + 1) ^ d : ℕ) : ℝ) *
        SegmentedVDM.energy v ≤ SegmentedVDM.energy
          (fineCubeEvaluation (M / nStar) (fun j : ↥(clumpColorClass C anchor color) => x j) *ᵥ v) := by
    apply @hframe (↥(clumpColorClass C anchor color)) inferInstance inferInstance
      (fun j => x j) (fun j => hcube j) _ v
    intro i j hij
    exact hcross i j (clumpColorClass_labels_ne C anchor color i j hij)
  obtain ⟨G₀, hG1, hG0, hGmass⟩ :=
    localizationPolynomial_of_colorFrames C anchor hKD hprodD ha hframes
  let G : SegmentedPolynomial d M 0 (2 * M + 1) := G₀.widen hK le_rfl (by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlocal : Δ / 2 ≤ Real.pi * nStar / ((M : ℝ) * 1) := by
    have h := (le_div_iff₀ hMR).mp hscale
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) * 1)).mpr
    nlinarith
  obtain ⟨B₀, hBvalue, hBmass⟩ := withinClumpPolynomial C anchor hd hs hM
    (D := 1) (by omega) (by positivity : 0 < Δ / 2) hcube hsame
    (by simpa using hτ) (fun i j hij => (by linarith [hmin i j hij])) (by simpa only [Nat.cast_one] using hlocal)
  have hR : M - M / nStar ≤ M := Nat.sub_le _ _
  let B : SegmentedPolynomial d (M - M / nStar) 0 (2 * M + 1) :=
    B₀.coarseToFine (by omega)
  have hsum : M + (M - M / nStar) < 2 * M + 1 := by omega
  let P := G.mul B hsum
  refine ⟨P, ?_, ?_⟩
  · intro j
    simp only [P, SegmentedPolynomial.angularValue_mul, B,
      SegmentedPolynomial.angularValue_coarseToFine, G, SegmentedPolynomial.angularValue_widen]
    by_cases hj : C.label j = C.label anchor
    · rw [hBvalue j hj]
      by_cases haj : anchor = j
      · subst j
        simp [hG1]
      · simp [haj]
    · rw [hG0 j hj, zero_mul]
      have haj : anchor ≠ j := fun h => hj (congrArg C.label h.symm)
      simp [haj]
  · have hBmass' : B.mass ≤
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1) := by
      simpa [B] using hBmass
    have hGmass' : G.mass ≤ (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar := by
      simpa [G] using hGmass
    exact (SegmentedPolynomial.mass_mul_le G B hsum).trans
      (mul_le_mul hGmass' hBmass' B.mass_nonneg (by positivity))


private theorem liClumpSize_le_sourceCount {d n A nStar : ℕ}
    {x : Fin n → Point d} {τ η : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η) : nStar ≤ n := by
  classical
  rcases hclumps.2.2.2.2 with ⟨label, _, _, ⟨a, ha⟩, _, _⟩
  have h := Finset.card_le_card (Finset.filter_subset (s := Finset.univ)
    (p := fun j => label j = a))
  simpa [ha] using h

private theorem liCubeClump_raw_ratio
    {d n A nStar M : ℕ} {τ η β Δ : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hM : 4 * n ≤ M) (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d * nStar / M ≤ τ)
    (hτ : τ ≤ Real.pi / (2 * d)) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j → Δ ≤ periodicL1Distance (μ.node i) (μ.node j))
    (hscale : Δ ≤ 2 * Real.pi * nStar / M) :
    let H := (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1)
    Real.sqrt (((M / nStar + 1) ^ d : ℕ) : ℝ) / (Real.sqrt n * H) ≤
      matrixSingularValue (segmentedVandermonde (2 * M) 0 (2 * M + 1) μ.node) (n - 1) := by
  classical
  dsimp only
  have hs : 0 < nStar := by have h := hclumps.1; omega
  have hsize := liClumpSize_le_sourceCount hclumps
  have hM0 : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have hβ0 : 0 < β := (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hK : (M : ℝ) ≤ nStar * (((M / nStar : ℕ) : ℝ) + 1) := by
    exact_mod_cast (Nat.lt_mul_div_succ M hs).le
  have hη' : 4 * Real.pi * β * d / ((M / nStar : ℕ) + 1) ≤ η := by
    apply le_trans _ (hη.trans hclumps.2.2.1)
    apply (div_le_div_iff₀ (by positivity) hMR).mpr
    convert mul_le_mul_of_nonneg_left hK
      (show 0 ≤ 4 * Real.pi * β * d by positivity) using 1 <;> ring
  obtain ⟨C, hsame, hcross⟩ := clumpStructure_has_slots hclumps
  choose P hPv hPm using fun anchor => liInterpolationPolynomial C anchor hd
    (by omega : 1 ≤ nStar) (by omega : 2 * nStar ≤ M) hΔ hβ
    hclumps.2.2.2.1 hsame hcross hτ hη' hmin hscale
  let H := (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1)
  have ha := liFrameConstant_pos hβ
  have hH : 0 < H := by dsimp [H]; positivity
  have hsum : M + (M - M / nStar) + M / nStar < 2 * M + 1 := by
    have := Nat.div_le_self M nStar
    omega
  have hh := SegmentedPolynomial.singularValue_ge_of_smoothedSegmentedPolynomials
    (Nat.zero_lt_of_lt hn) μ.node P hPv hsum hH hPm (b := M / nStar) (z := 0)
  have hbudget : M + (M - M / nStar) + M / nStar = 2 * M := by
    have := Nat.div_le_self M nStar
    omega
  rw [hbudget] at hh
  simpa only [H, Nat.add_zero, zero_add, zero_mul, one_mul] using hh

private theorem liCubeClump_packet_le {M nStar : ℕ} (hs : 0 < nStar) :
    2 * ((2 * M) / (4 * nStar)) + 1 ≤ M / nStar + 1 := by
  have hdiv := Nat.div_mul_le_self (2 * M) (4 * nStar)
  have hmul : (2 * ((2 * M) / (4 * nStar))) * nStar ≤ M := by nlinarith
  have h := (Nat.le_div_iff_mul_le hs).mpr hmul
  omega

private theorem liCubeClump_ratio_eq {d n nStar M : ℕ} {β Δ : ℝ}
    (hn : 0 < n) (hs : 0 < nStar) (hM : 0 < M)
    (hβ : 1 / (2 * Real.log 2) < β) (hΔ : 0 < Δ) :
    liCubeClumpLower d n nStar (2 * M) β Δ =
      Real.sqrt (((2 * ((2 * M) / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
        (Real.sqrt (((2 * M + 1) ^ d : ℕ) : ℝ) * Real.sqrt n *
          ((1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
            (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1))) := by
  have ha := liFrameConstant_pos hβ
  have hsqrtpow : (Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar =
      (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha.le]
    congr 1
    ring
  have ht : (((M : ℝ) / nStar) * (Δ / 2) / Real.pi) =
      ((2 * M : ℕ) : ℝ) * Δ / (4 * Real.pi * nStar) := by
    push_cast
    ring
  unfold liCubeClumpLower
  rw [← hsqrtpow, ht]
  simp only [div_pow, one_pow]
  push_cast
  field_simp [ne_of_gt (Real.sqrt_pos.mpr ha), ne_of_gt (Real.sqrt_pos.mpr
    (show (0 : ℝ) < n by exact_mod_cast hn)), Real.pi_ne_zero,
    ne_of_gt (show (0 : ℝ) < nStar by exact_mod_cast hs),
    ne_of_gt (show (0 : ℝ) < M by exact_mod_cast hM), hΔ.ne']
  <;> ring

private theorem segmentedVandermonde_oneBlock_singularValue {d n L : ℕ}
    (x : Fin n → Point d) (i : ℕ) :
    matrixSingularValue (segmentedVandermonde L 0 (L + 1) x) i =
      matrixSingularValue (fun k : RandSamp.CubeFrequency d L => RandSamp.cubeFourierRow x k) i := by
  have hmat : (segmentedVandermonde L 0 (L + 1) x).submatrix
      (SegmentedPolynomial.fineCubeIndexEquiv d L).symm (Equiv.refl (Fin n)) =
      (fun k : RandSamp.CubeFrequency d L => RandSamp.cubeFourierRow x k) := by
    ext k j
    simp [segmentedVandermonde, generalizedVandermonde, steeringVector,
      segmentedFrequency, SegmentedPolynomial.fineCubeIndexEquiv, RandSamp.cubeFourierRow, dot]
  rw [← hmat, matrixSingularValue_submatrix_equiv]

private theorem cubeNormalized_lower_of_raw {d n L : ℕ} (hn : 0 < n)
    (x : Fin n → Point d) {B : ℝ}
    (hB : B ≤ matrixSingularValue (segmentedVandermonde L 0 (L + 1) x) (n - 1)) :
    B / Real.sqrt (((L + 1) ^ d : ℕ) : ℝ) ≤
      matrixSingularValue (RandSamp.cubeFullVandermonde L x) (n - 1) := by
  classical
  let V : Matrix (RandSamp.CubeFrequency d L) (Fin n) ℂ :=
    fun k => RandSamp.cubeFourierRow x k
  have hB' : B ≤ matrixSingularValue V (n - 1) := by
    simpa only [segmentedVandermonde_oneBlock_singularValue] using hB
  have hN : 0 < Real.sqrt (((L + 1) ^ d : ℕ) : ℝ) := by positivity
  apply le_singularValues_of_subspace (RandSamp.cubeFullVandermonde L x).toEuclideanLin
    (i := n - 1) (by simpa using Nat.sub_lt hn (by omega : 0 < 1)) ⊤
    (by simp; omega)
  intro z _
  have h := (mul_le_mul_of_nonneg_right hB' (norm_nonneg z)).trans
    (by simpa only [Fintype.card_fin] using
      lastMatrixSingularValue_mul_norm_le V (by simpa using hn) z)
  have hact : (RandSamp.cubeFullVandermonde L x).toEuclideanLin z =
      ((Real.sqrt (((L + 1) ^ d : ℕ) : ℝ))⁻¹ : ℂ) • V.toEuclideanLin z := by
    apply ofLp_injective
    ext k
    simp [Matrix.toLpLin_apply, RandSamp.cubeFullVandermonde, V,
      Matrix.mulVec, dotProduct, mul_assoc, ← Finset.mul_sum]
  rw [hact, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hN.le]
  have h := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hN.le)
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Discrete cube clump bound with exactly Li's normalized coefficient.
The proof is valid in every positive dimension; the published cube corollary
is stated for dimension at least two. -/
theorem liCubeClumpVandermonde_normalized_lower_halfBandwidth
    {d n A nStar M : ℕ} {τ η β : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hM : 4 * n ≤ M) (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d * nStar / M ≤ τ)
    (hτ : τ ≤ Real.pi / (2 * d))
    (hscale : periodicMinimumL1Separation μ.node hn ≤ 2 * Real.pi * nStar / M) :
    liCubeClumpLower d n nStar (2 * M) β (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (RandSamp.cubeFullVandermonde (2 * M) μ.node) (n - 1) := by
  let Δ := periodicMinimumL1Separation μ.node hn
  have hΔ : 0 < Δ := segmented_periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  have hs : 0 < nStar := by have h := hclumps.1; omega
  have hM0 : 0 < M := by omega
  have hraw := liCubeClump_raw_ratio μ hd hn hclumps hM hβ hη hτ hΔ
    (fun i j hij => periodicMinimumL1Separation_le hn hij) hscale
  have hnorm := cubeNormalized_lower_of_raw (Nat.zero_lt_of_lt hn) μ.node hraw
  have hpacket : Real.sqrt (((2 * ((2 * M) / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) ≤
      Real.sqrt (((M / nStar + 1) ^ d : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.pow_le_pow_left (liCubeClump_packet_le hs) d
  rw [liCubeClump_ratio_eq (Nat.zero_lt_of_lt hn) hs hM0 hβ hΔ]
  apply le_trans _ hnorm
  have ha := liFrameConstant_pos hβ
  have hden : 0 ≤ Real.sqrt (((2 * M + 1) ^ d : ℕ) : ℝ) * Real.sqrt n *
      ((1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1)) := by positivity
  simpa only [div_div, mul_assoc, mul_left_comm, mul_comm] using
    div_le_div_of_nonneg_right hpacket hden

/-- Public even-bandwidth form of the normalized Li cube clump corollary. -/
theorem liCubeClumpVandermonde_normalized_lower
    {d n A nStar L : ℕ} {τ η β : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hgeom : LiCubeClumpGeometry μ A nStar L τ η β hn) :
    liCubeClumpLower d n nStar L β (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (RandSamp.cubeFullVandermonde L μ.node) (n - 1) := by
  rcases hgeom with ⟨⟨M, hML⟩, hL, hclumps, hβ, hη, hτ, hscale⟩
  have hML' : L = 2 * M := by omega
  rw [hML'] at hL hη hscale ⊢
  have hη' : 4 * Real.pi * β * d * nStar / M ≤ τ := by
    convert hη using 1 <;> push_cast <;> ring
  have hscale' : periodicMinimumL1Separation μ.node hn ≤ 2 * Real.pi * nStar / M := by
    convert hscale using 1 <;> push_cast <;> ring
  exact liCubeClumpVandermonde_normalized_lower_halfBandwidth μ hd hn hclumps
    (by omega : 4 * n ≤ M) hβ hη' hτ hscale'


/-- Bandwidth-independent deterministic lower coefficient, under exactly
Li's cube geometry. -/
theorem liCubeClumpVandermonde_normalized_uniform_lower
    {d n A nStar L : ℕ} {τ η β : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hgeom : LiCubeClumpGeometry μ A nStar L τ η β hn) :
    liCubeClumpUniformCoefficient d n nStar β *
        ((L : ℝ) * periodicMinimumL1Separation μ.node hn) ^ (nStar - 1) ≤
      matrixSingularValue (RandSamp.cubeFullVandermonde L μ.node) (n - 1) := by
  have hclumps := hgeom.2.2.1
  have hs : 0 < nStar := by have h := hclumps.1; omega
  have hsize := liClumpSize_le_sourceCount hclumps
  have hL : 8 * nStar ≤ L := (Nat.mul_le_mul_left 8 hsize).trans hgeom.2.1
  have hΔ := segmented_periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  exact (liCubeClumpUniformLower_le_exact (Nat.zero_lt_of_lt hn) hs hL hgeom.2.2.2.1 hΔ.le).trans
    (liCubeClumpVandermonde_normalized_lower μ hd hn hgeom)

#print axioms liCubeClumpVandermonde_normalized_lower
#print axioms liCubeClumpLower_pos
#print axioms liCubeClumpCoefficient_pos
#print axioms liCubeClumpVandermonde_normalized_uniform_lower
#print axioms liCubeClumpUniformCoefficient_pos

end
end LeanNumDetect.NumDetect
