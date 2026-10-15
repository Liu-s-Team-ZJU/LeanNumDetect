import MultiTuran.Volume

/-! # Disjoint residue cubes inside the full aperture

The half-open choice makes the translated residue cells genuinely disjoint,
including when the residue width equals the lattice spacing.
-/

set_option autoImplicit false
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The half-open residue box `[0,h)^d`. -/
def residueBaseCube (d : ℕ) (h : ℝ) : Set (Point d) :=
  Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) h)

/-- The integer lattice shift of a cube-frequency row. -/
def residueShift {d s : ℕ} (M : ℕ) (k : Fin d → Fin (s + 1)) : Point d :=
  fun q => (M : ℝ) * ((k q).val : ℝ)

/-- The residue cell `M k + [0,h)^d`. -/
def residueCube {d s : ℕ} (M : ℕ) (h : ℝ)
    (k : Fin d → Fin (s + 1)) : Set (Point d) :=
  Set.pi Set.univ (fun q =>
    Set.Ico (residueShift M k q) (residueShift M k q + h))

theorem residueBaseCube_measurableSet (d : ℕ) (h : ℝ) :
    MeasurableSet (residueBaseCube d h) :=
  MeasurableSet.pi (Set.countable_univ) (fun _ _ => measurableSet_Ico)

theorem residueCube_measurableSet {d s : ℕ} (M : ℕ) (h : ℝ)
    (k : Fin d → Fin (s + 1)) : MeasurableSet (residueCube M h k) :=
  MeasurableSet.pi (Set.countable_univ) (fun _ _ => measurableSet_Ico)

/-- Every row has its own disjoint residue cell when `h ≤ M`. -/
theorem residueCubes_pairwise_disjoint {d s : ℕ} (M : ℕ) (h : ℝ)
    (_hpos : 0 < h) (hM : h ≤ (M : ℝ)) :
    Pairwise (fun k l : Fin d → Fin (s + 1) =>
      Disjoint (residueCube M h k) (residueCube M h l)) := by
  intro k l hkl
  obtain ⟨q,hq⟩ := Function.ne_iff.mp hkl
  apply Set.disjoint_left.2
  intro t htk htl
  have hk := htk q (Set.mem_univ q)
  have hl := htl q (Set.mem_univ q)
  change residueShift M k q ≤ t q ∧ t q < residueShift M k q + h at hk
  change residueShift M l q ≤ t q ∧ t q < residueShift M l q + h at hl
  dsimp [residueShift] at hk hl
  obtain hlt | hgt := lt_or_gt_of_ne hq
  · have hgap : ((k q).val : ℝ) + 1 ≤ ((l q).val : ℝ) := by
      exact_mod_cast (show (k q).val + 1 ≤ (l q).val by omega)
    nlinarith [mul_nonneg (Nat.cast_nonneg M)
      (sub_nonneg.mpr hgap)]
  · have hgap : ((l q).val : ℝ) + 1 ≤ ((k q).val : ℝ) := by
      exact_mod_cast (show (l q).val + 1 ≤ (k q).val by omega)
    nlinarith [mul_nonneg (Nat.cast_nonneg M)
      (sub_nonneg.mpr hgap)]

/-- Every residue cell is inside the genuine aperture box. -/
theorem residueCube_subset_apertureBox {d s : ℕ} (G : SegmentedGrid d)
    (M : ℕ) (h : ℝ) (_hpos : 0 ≤ h)
    (hband : (s : ℝ) * (M : ℝ) + h ≤ (G.minAperture : ℝ))
    (k : Fin d → Fin (s + 1)) : residueCube M h k ⊆ G.apertureBox := by
  intro t ht q _
  have hq := ht q (Set.mem_univ q)
  change (M : ℝ) * ((k q).val : ℝ) ≤ t q ∧
    t q < (M : ℝ) * ((k q).val : ℝ) + h at hq
  have hk : ((k q).val : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast (show (k q).val ≤ s by omega)
  have hN : (G.minAperture : ℝ) ≤ (G.aperture q : ℝ) := by
    exact_mod_cast G.minAperture_le q
  refine ⟨(by positivity : (0 : ℝ) ≤ (M : ℝ) * ((k q).val : ℝ)).trans hq.1, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg M)
  linarith

theorem residueBaseCube_volume (d : ℕ) {h : ℝ} (hpos : 0 ≤ h) :
    volume (residueBaseCube d h) = ENNReal.ofReal (h ^ d) := by
  rw [residueBaseCube, volume_pi_pi]
  simp [Real.volume_Ico, ENNReal.ofReal_pow hpos]

/-- The residue cube contributes exactly the volume factor `h^d`. -/
theorem residueBaseCube_volume_toReal (d : ℕ) {h : ℝ} (hpos : 0 ≤ h) :
    (volume (residueBaseCube d h)).toReal = h ^ d := by
  rw [residueBaseCube_volume d hpos, ENNReal.toReal_ofReal (pow_nonneg hpos d)]

/-- Subtracting its shift maps a residue cell exactly onto the base cell. -/
theorem residueCube_eq_preimage_sub {d s : ℕ} (M : ℕ) (h : ℝ)
    (k : Fin d → Fin (s + 1)) :
    residueCube M h k = (fun t : Point d => t - residueShift M k) ⁻¹'
      residueBaseCube d h := by
  ext t
  change (∀ q ∈ Set.univ, residueShift M k q ≤ t q ∧
      t q < residueShift M k q + h) ↔
    ∀ q ∈ Set.univ, 0 ≤ t q - residueShift M k q ∧ t q - residueShift M k q < h
  constructor <;> intro ht q hq <;> obtain ⟨hl,hu⟩ := ht q hq <;> constructor <;> linarith

/-- The equivalent image form of the translated residue cell. -/
theorem residueCube_eq_image_add {d s : ℕ} (M : ℕ) (h : ℝ)
    (k : Fin d → Fin (s + 1)) :
    residueCube M h k = (fun t : Point d => t + residueShift M k) ''
      residueBaseCube d h := by
  rw [residueCube_eq_preimage_sub]
  ext t
  constructor
  · intro ht
    exact ⟨t - residueShift M k,ht,sub_add_cancel _ _⟩
  · rintro ⟨u,hu,rfl⟩
    simpa only [Set.mem_preimage, add_sub_cancel_right] using hu

end
end LeanNumDetect.MultiTuran
