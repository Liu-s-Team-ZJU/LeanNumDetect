import MultiTuran.FullCube
import MultiTuran.Energy
import MultiTuran.ResidueCubes
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The actual continuous full-aperture estimate `thm:universal-full-aperture`.
Finite cube evaluations are integrated over disjoint translated residue cubes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ENNReal
open Matrix WithLp MeasureTheory Set

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- Full-aperture admissibility from `def:admissible-pair`, with positive dilation. -/
structure FullApertureAdmissible {d : ℕ} (G : SegmentedGrid d) (M s : ℕ) : Prop where
  dilation_pos : 0 < M
  dilation_le : M ≤ G.minAperture
  last_lt : s * M < G.minAperture

/-- The exact positive residue width `h_{M,s}`. -/
def fullApertureWidth {d : ℕ} (G : SegmentedGrid d) (M s : ℕ) : ℕ :=
  min M (G.minAperture - s * M)

theorem fullApertureWidth_pos {d : ℕ} {G : SegmentedGrid d} {M s : ℕ}
    (h : FullApertureAdmissible G M s) : 0 < fullApertureWidth G M s := by
  unfold fullApertureWidth
  exact lt_min h.dilation_pos (Nat.sub_pos_of_lt h.last_lt)

theorem fullApertureWidth_le {d : ℕ} (G : SegmentedGrid d) (M s : ℕ) :
    fullApertureWidth G M s ≤ M := min_le_left _ _

theorem fullApertureWidth_last_le {d : ℕ} {G : SegmentedGrid d} {M s : ℕ}
    (h : FullApertureAdmissible G M s) :
    s * M + fullApertureWidth G M s ≤ G.minAperture := by
  have hw : fullApertureWidth G M s ≤ G.minAperture - s * M := min_le_right _ _
  have hlast := h.last_lt
  omega

/-- Multiplying the coefficient family by the diagonal unitary phase. -/
def phaseCoefficients {d n : ℕ} (Y : Fin n → Point d) (c : Fin n → ℂ)
    (a : Point d) : Fin n → ℂ := fun j => c j *
  Complex.exp (Complex.I * ((∑ q, a q * Y j q : ℝ) : ℂ))

@[simp] theorem norm_phaseCoefficients {d n : ℕ} (Y : Fin n → Point d)
    (c : Fin n → ℂ) (a : Point d) (j : Fin n) :
    ‖phaseCoefficients Y c a j‖ = ‖c j‖ := by
  unfold phaseCoefficients
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]

/-- The exact sampled shift identity `A_{M,s} D(a)c`. -/
theorem fullCube_mulVec_phaseCoefficients {d n : ℕ} (M s : ℕ)
    (Y : Fin n → Point d) (c : Fin n → ℂ) (a : Point d)
    (k : Fin d → Fin (s+1)) :
    (fullCubeVandermonde M s Y *ᵥ phaseCoefficients Y c a) k =
      exponentialSum Y c (a + residueShift M k) := by
  unfold Matrix.mulVec dotProduct fullCubeVandermonde exponential phaseCoefficients exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  have hsum : (∑ r, ((k r).val : ℝ) * ((M : ℝ) * Y j r)) +
      (∑ q, a q * Y j q) = ∑ q, (a + residueShift M k) q * Y j q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    simp only [Pi.add_apply, residueShift]
    ring
  have he : Complex.exp (Complex.I * ((∑ r, ((k r).val : ℝ) * ((M : ℝ) * Y j r) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((∑ q, a q * Y j q : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((∑ q, (a + residueShift M k) q * Y j q : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    apply congrArg Complex.exp
    rw [← mul_add, ← Complex.ofReal_add, hsum]
  calc
    _ = c j * (Complex.exp (Complex.I * ((∑ r, ((k r).val : ℝ) * ((M : ℝ) * Y j r) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((∑ q, a q * Y j q : ℝ) : ℂ))) := by ring
    _ = _ := by rw [he]

/-- The least singular value controls every shifted full-cube sample family. -/
theorem fullCube_shifted_energy_lower {d n : ℕ} (M s : ℕ)
    (Y : Fin n → Point d) (c : Fin n → ℂ) (hn : 0 < n) (a : Point d) :
    matrixSingularValue (fullCubeVandermonde M s Y) (n-1)^2 * (∑ j, ‖c j‖^2) ≤
      ∑ k : Fin d → Fin (s+1), ‖exponentialSum Y c (a + residueShift M k)‖^2 := by
  let z : EuclideanSpace ℂ (Fin n) := toLp 2 (phaseCoefficients Y c a)
  have h := lastMatrixSingularValue_mul_norm_le (fullCubeVandermonde M s Y)
    (by simpa using hn) z
  have hs := (sq_le_sq₀
    (mul_nonneg ((fullCubeVandermonde M s Y).toEuclideanLin.singularValues_nonneg _)
      (norm_nonneg z)) (norm_nonneg _)).mpr h
  have hznorm : ‖z‖^2 = ∑ j, ‖c j‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [z, norm_phaseCoefficients]
  have hnorm : ‖(fullCubeVandermonde M s Y).toEuclideanLin z‖^2 =
      ∑ k : Fin d → Fin (s+1), ‖exponentialSum Y c (a + residueShift M k)‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖(fullCubeVandermonde M s Y *ᵥ phaseCoefficients Y c a) k‖^2) = _
    simp only [fullCube_mulVec_phaseCoefficients]
  rw [mul_pow, hznorm, hnorm] at hs
  simpa only [Fintype.card_fin, matrixSingularValue] using hs

private theorem shifted_energy_integrableOn_base {d n : ℕ} (Y : Fin n → Point d)
    (c : Fin n → ℂ) (h : ℝ) (u : Point d) :
    IntegrableOn (fun a => ‖exponentialSum Y c (a + u)‖^2) (residueBaseCube d h) := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) h)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hf : Continuous (fun a : Point d => ‖exponentialSum Y c (a+u)‖^2) :=
    ((continuous_exponentialSum Y c).comp (continuous_id.add continuous_const)).norm.pow 2
  apply hf.continuousOn.integrableOn_compact hc |>.mono_set
  intro a ha q hq
  exact ⟨(ha q hq).1, (ha q hq).2.le⟩

/-- Lebesgue translation invariance, with the actual half-open residue cubes. -/
theorem integral_shift_residueCube {d s M : ℕ} (h : ℝ)
    (k : Fin d → Fin (s+1)) (f : Point d → ℝ) :
    (∫ a in residueBaseCube d h, f (a + residueShift M k)) =
      ∫ t in residueCube M h k, f t := by
  let u := residueShift M k
  have hmem (a : Point d) : a + u ∈ residueCube M h k ↔ a ∈ residueBaseCube d h := by
    simp only [residueCube, residueBaseCube, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Ico, Pi.add_apply, u]
    constructor
    · intro ha q
      constructor <;> linarith [(ha q).1, (ha q).2]
    · intro ha q
      constructor <;> linarith [(ha q).1, (ha q).2]
  have hind (a : Point d) : (residueBaseCube d h).indicator (fun x => f (x+u)) a =
      (residueCube M h k).indicator f (a+u) := by
    classical
    by_cases ha : a ∈ residueBaseCube d h
    · simp [ha, (hmem a).2 ha]
    · have hn : a + u ∉ residueCube M h k := fun hc => ha ((hmem a).1 hc)
      simp [ha, hn]
  calc
    _ = ∫ a, (residueBaseCube d h).indicator (fun x => f (x+u)) a :=
      (integral_indicator (residueBaseCube_measurableSet d h)).symm
    _ = ∫ a, (residueCube M h k).indicator f (a+u) := integral_congr_ae (Filter.Eventually.of_forall hind)
    _ = ∫ t, (residueCube M h k).indicator f t := integral_add_right_eq_self _ u
    _ = _ := integral_indicator (residueCube_measurableSet M h k)

/-- The genuine continuous-energy estimate from disjoint residue cubes. -/
theorem fullAperture_energy_lower_of_width {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) (hn : 0 < n)
    (h : ℝ) (hpos : 0 < h) (hM : h ≤ (M : ℝ))
    (hband : (s : ℝ) * (M : ℝ) + h ≤ G.minAperture) :
    h^d * matrixSingularValue (fullCubeVandermonde M s Y) (n-1)^2 * (∑ j, ‖c j‖^2) ≤
      setEnergy Y c G.apertureBox := by
  classical
  let A := fullCubeVandermonde M s Y
  let f : Point d → ℝ := fun t => ‖exponentialSum Y c t‖^2
  have hintJ : IntegrableOn f G.apertureBox :=
    exponentialSum_energy_integrableOn Y c G.apertureBox_isCompact
  have hint (k : Fin d → Fin (s+1)) : IntegrableOn f (residueCube M h k) :=
    hintJ.mono_set (residueCube_subset_apertureBox G M h hpos.le hband k)
  have hintbase (k : Fin d → Fin (s+1)) :
      IntegrableOn (fun a => f (a + residueShift M k)) (residueBaseCube d h) :=
    shifted_energy_integrableOn_base Y c h _
  have hintsum : IntegrableOn (fun a => ∑ k : Fin d → Fin (s+1),
      f (a + residueShift M k)) (residueBaseCube d h) := by
    exact integrable_finsetSum _ fun k _ => hintbase k
  have hfinite : volume (residueBaseCube d h) ≠ ∞ := by
    rw [residueBaseCube_volume d hpos.le]
    exact ENNReal.ofReal_ne_top
  have hlower := setIntegral_ge_of_const_le (residueBaseCube_measurableSet d h) hfinite
    (fun a _ => fullCube_shifted_energy_lower M s Y c hn a) hintsum
  change (volume (residueBaseCube d h)).toReal *
    (matrixSingularValue A (n-1)^2 * (∑ j, ‖c j‖^2)) ≤ _ at hlower
  rw [residueBaseCube_volume_toReal d hpos.le] at hlower
  have hsum : (∫ a in residueBaseCube d h,
      ∑ k : Fin d → Fin (s+1), f (a + residueShift M k)) =
      ∑ k : Fin d → Fin (s+1), ∫ a in residueBaseCube d h, f (a + residueShift M k) := by
    exact integral_finsetSum _ fun k _ => hintbase k
  have hunion : (∑ k : Fin d → Fin (s+1), ∫ t in residueCube M h k, f t) ≤
      ∫ t in G.apertureBox, f t := by
    rw [← integral_iUnion_fintype (fun k => residueCube_measurableSet M h k)
      (residueCubes_pairwise_disjoint M h hpos hM) hint]
    apply setIntegral_mono_set hintJ
    · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
    · exact Filter.Eventually.of_forall fun t ht => by
        obtain ⟨k,hk⟩ := Set.mem_iUnion.mp ht
        exact residueCube_subset_apertureBox G M h hpos.le hband k hk
  calc
    _ = h^d * (matrixSingularValue A (n-1)^2 * (∑ j, ‖c j‖^2)) := by ring
    _ ≤ ∫ a in residueBaseCube d h, ∑ k : Fin d → Fin (s+1),
        f (a + residueShift M k) := hlower
    _ = ∑ k : Fin d → Fin (s+1), ∫ a in residueBaseCube d h,
        f (a + residueShift M k) := hsum
    _ = ∑ k : Fin d → Fin (s+1), ∫ t in residueCube M h k, f t := by
      apply Finset.sum_congr rfl
      intro k _
      exact integral_shift_residueCube h k f
    _ ≤ ∫ t in G.apertureBox, f t := hunion
    _ = _ := rfl

/-- Squared-energy form of manuscript `thm:universal-full-aperture`. -/
theorem fullAperture_energy_lower {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) (hn : 0 < n)
    (hadm : FullApertureAdmissible G M s) :
    (fullApertureWidth G M s : ℝ)^d *
        matrixSingularValue (fullCubeVandermonde M s Y) (n-1)^2 * (∑ j, ‖c j‖^2) ≤
      setEnergy Y c G.apertureBox := by
  apply fullAperture_energy_lower_of_width G Y c hn _
  · exact_mod_cast fullApertureWidth_pos hadm
  · exact_mod_cast fullApertureWidth_le G M s
  · exact_mod_cast fullApertureWidth_last_le hadm

/-- Exact `L²` form of manuscript `thm:universal-full-aperture`, including
its real exponent `d/2`. -/
theorem fullAperture_L2_lower {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) (hn : 0 < n)
    (hadm : FullApertureAdmissible G M s) :
    (fullApertureWidth G M s : ℝ)^((d : ℝ)/2) *
        matrixSingularValue (fullCubeVandermonde M s Y) (n-1) *
        Real.sqrt (∑ j, ‖c j‖^2) ≤ Real.sqrt (setEnergy Y c G.apertureBox) := by
  have h := fullAperture_energy_lower G Y c hn hadm
  have hw : 0 ≤ (fullApertureWidth G M s : ℝ) := Nat.cast_nonneg _
  have he : Real.sqrt ((fullApertureWidth G M s : ℝ)^d) =
      (fullApertureWidth G M s : ℝ)^((d : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul hw]
    congr 1
    ring
  rw [← he]
  have hσ0 := (fullCubeVandermonde M s Y).toEuclideanLin.singularValues_nonneg (n-1)
  change 0 ≤ matrixSingularValue (fullCubeVandermonde M s Y) (n-1) at hσ0
  apply (sq_le_sq₀ (by positivity)
    (Real.sqrt_nonneg (setEnergy Y c G.apertureBox))).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (setEnergy_nonneg Y c G.apertureBox)]
  exact h

/-- Full residue width is available whenever `(s+1)M ≤ N_min`. -/
theorem fullApertureWidth_eq_dilation {d M s : ℕ} (G : SegmentedGrid d)
    (hfull : (s+1)*M ≤ G.minAperture) : fullApertureWidth G M s = M := by
  unfold fullApertureWidth
  apply min_eq_left
  rw [Nat.add_mul, one_mul] at hfull
  omega

/-- The full-residue specialization of the continuous-energy bound. -/
theorem fullAperture_energy_lower_full_residue {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) (hn : 0 < n)
    (hM : 0 < M) (hfull : (s+1)*M ≤ G.minAperture) :
    (M : ℝ)^d * matrixSingularValue (fullCubeVandermonde M s Y) (n-1)^2 *
        (∑ j, ‖c j‖^2) ≤ setEnergy Y c G.apertureBox := by
  have hadm : FullApertureAdmissible G M s := by
    constructor
    · exact hM
    · nlinarith
    · nlinarith
  have h := fullAperture_energy_lower G Y c hn hadm
  rwa [fullApertureWidth_eq_dilation G hfull] at h

/-- The full-residue specialization, with the exact `M^(d/2)` prefactor. -/
theorem fullAperture_L2_lower_full_residue {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) (hn : 0 < n)
    (hM : 0 < M) (hfull : (s+1)*M ≤ G.minAperture) :
    (M : ℝ)^((d : ℝ)/2) * matrixSingularValue (fullCubeVandermonde M s Y) (n-1) *
        Real.sqrt (∑ j, ‖c j‖^2) ≤ Real.sqrt (setEnergy Y c G.apertureBox) := by
  have hadm : FullApertureAdmissible G M s := by
    constructor
    · exact hM
    · nlinarith
    · nlinarith
  have h := fullAperture_L2_lower G Y c hn hadm
  rwa [fullApertureWidth_eq_dilation G hfull] at h

/-- Manuscript `cor:full-aperture-elementary`, including the exact constant. -/
theorem fullAperture_elementary_L2_lower {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) (hn : 0 < n)
    (hadm : FullApertureAdmissible G M s) (hs : n-1 ≤ s) :
    (fullApertureWidth G M s : ℝ)^((d : ℝ)/2) / Real.sqrt (n : ℝ) *
        (nodeSeparation (fun j r => (M : ℝ)*Y j r) / Real.pi)^(n-1) *
        Real.sqrt (∑ j, ‖c j‖^2) ≤ Real.sqrt (setEnergy Y c G.apertureBox) := by
  have hmat := elementary_fullCube_lower (M := M) G.dimension_pos hn hs Y
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmat
      (Real.rpow_nonneg (Nat.cast_nonneg (fullApertureWidth G M s)) ((d : ℝ)/2)))
    (Real.sqrt_nonneg (∑ j, ‖c j‖^2))
  calc
    _ = (fullApertureWidth G M s : ℝ)^((d : ℝ)/2) *
        ((1 / Real.sqrt (n : ℝ)) *
          (nodeSeparation (fun j r => (M : ℝ)*Y j r) / Real.pi)^(n-1)) *
        Real.sqrt (∑ j, ‖c j‖^2) := by ring
    _ ≤ _ := hmul.trans (fullAperture_L2_lower G Y c hn hadm)

/-- The no-wrap specialization of `cor:full-aperture-elementary`. -/
theorem fullAperture_elementary_no_wrap_L2_lower {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (c : Fin n → ℂ) (hn : 0 < n)
    (hadm : FullApertureAdmissible G M s) (hs : n-1 ≤ s)
    (hshort : (M : ℝ)*nodeDiameter Y ≤ Real.pi) :
    (fullApertureWidth G M s : ℝ)^((d : ℝ)/2) / Real.sqrt (n : ℝ) *
        ((M : ℝ)*nodeSeparation Y / Real.pi)^(n-1) *
        Real.sqrt (∑ j, ‖c j‖^2) ≤ Real.sqrt (setEnergy Y c G.apertureBox) := by
  have h := fullAperture_elementary_L2_lower G Y c hn hadm hs
  rwa [nodeSeparation_mul_nat M Y hshort] at h

end
end LeanNumDetect.MultiTuran
