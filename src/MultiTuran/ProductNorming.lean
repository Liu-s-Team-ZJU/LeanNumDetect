import MultiTuran.Bernstein
import MultiTuran.BernsteinVariation
import MultiTuran.NormingConstants
import MultiTuran.ProductDiscretization
import MultiTuran.ProductRestriction
import MultiTuran.Translation

/-! # Uniform norming from the literal segmented block condition

Actual scalar derivatives control coordinate oscillations on the measured
cells. Product Nikolskii then bounds those oscillations by the actual energy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- An explicit dimension-dependent sufficient-condition constant. -/
def discretizationConstant (d : ℕ) : ℝ := 80 * d * (4 : ℝ)^d

theorem discretizationConstant_pos {d : ℕ} (hd : 0 < d) :
    0 < discretizationConstant d := by unfold discretizationConstant; positivity

private theorem thickLength_le_omega {d : ℕ} (G : SegmentedGrid d)
    (q : Fin d) (m : G.Block q) : G.thickLength q m ≤ G.omega := by
  have h := G.block_end_le_last q m
  have hb : G.thickLength q m ≤ G.aperture q := by
    unfold SegmentedGrid.thickLength SegmentedGrid.aperture
    omega
  exact hb.trans (G.aperture_le_omega q)

/-- The genuine coordinate squared-modulus oscillation bound used for
multidimensional discretization. -/
theorem exponentialSum_cell_coordinate_lipschitz {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hn : 0 < n)
    (hY : ∀ j, InCube (2 * Real.pi / (G.omega : ℝ)) 0 (Y j))
    (c : Fin n → ℂ) (k : G.Row) (q : Fin d) (z : Point d)
    (hz : z ∈ G.unitCell k) {u : ℝ}
    (hu : u ∈ Set.Icc (G.rowPoint k q) (G.rowPoint k q + 1)) :
    |‖exponentialSum Y c (Function.update z q u)‖ ^ 2 -
      ‖exponentialSum Y c z‖ ^ 2| ≤
      ((40 * (4 : ℝ)^d) * (n : ℝ) ^ (4*d+5) /
        (G.minThickLength : ℝ)^(d+1) * continuousEnergy G Y c) * |u-z q| := by
  classical
  obtain ⟨m,hm⟩ := (G.mem_coordinateRows q _).1 (k q).property
  obtain ⟨hklo,hkhi⟩ := (G.mem_blockRows q m _).1 hm
  let a : ℝ := G.start q m
  let b : ℝ := (G.start q m + G.thickLength q m : ℕ)
  let L : ℝ := G.minThickLength
  let B : ℝ := (∏ r, Real.pi * n / (2 * Real.sqrt (G.coordinateMinLength r : ℝ))) *
    continuousL2Norm G Y c
  let v : Fin n → ℂ := fun j => c j * Complex.exp (Complex.I *
    ((∑ r ∈ Finset.univ.erase q, z r * Y j r : ℝ) : ℂ))
  let f : ℝ → ℂ := ExponentialSumEstimates.exponentialSum (fun j => Y j q) v
  have hrepr (t : ℝ) : f t = exponentialSum Y c (Function.update z q t) :=
    (exponentialSum_coordinate_section Y c z q t).symm
  have hL : 0 < L := by dsimp [L]; exact_mod_cast minThickLength_pos G
  have hB : 0 ≤ B := by dsimp [B, continuousL2Norm]; positivity
  have hlen : b-a = (G.thickLength q m : ℝ) := by dsimp [a,b]; push_cast; ring
  have hab : a < b := by rw [← sub_pos, hlen]; exact_mod_cast (show 0 < G.thickLength q m by
    unfold SegmentedGrid.thickLength; omega)
  have hLlen : L ≤ b-a := by
    rw [hlen]
    change (G.minThickLength : ℝ) ≤ (G.thickLength q m : ℝ)
    exact_mod_cast (minThickLength_le_coordinateMinLength G q).trans
      (G.coordinateMinLength_le q m)
  have hcell (t : ℝ) (ht : t ∈ Set.Icc (G.rowPoint k q) (G.rowPoint k q+1)) :
      t ∈ Set.Icc a b := by
    have hlo : a ≤ G.rowPoint k q := by
      change (G.start q m : ℝ) ≤ ((k q).val : ℝ)
      exact_mod_cast hklo
    have hhi : G.rowPoint k q + 1 ≤ b := by
      dsimp [b,SegmentedGrid.thickLength]
      push_cast
      have h : G.rowPoint k q ≤ (G.start q m : ℝ) + G.length q m := by
        change ((k q).val : ℝ) ≤ (G.start q m : ℝ) + G.length q m
        exact_mod_cast hkhi
      linarith
    exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩
  have hupdate (t : ℝ) (ht : t ∈ Set.Icc a b) :
      Function.update z q t ∈ G.thickening := by
    intro r hr
    by_cases he : r = q
    · subst r
      rw [Function.update_self]
      exact Set.mem_iUnion.2 ⟨m,ht⟩
    · rw [Function.update_of_ne he]
      exact G.unitCell_subset_thickening k hz r hr
  have hval : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ B := by
    intro t ht
    rw [hrepr]
    exact exponentialSum_product_norm_le G hn Y c (hupdate t ht)
  have hsup : setSupNorm f (Set.Icc a b) ≤ B := by
    apply Real.sSup_le
    · rintro w ⟨t,ht,rfl⟩
      exact hval t ht
    · exact hB
  have hfreq : ∀ j, |Y j q| * (b-a) ≤ 2 * Real.pi := by
    intro j
    have hnode : |Y j q| ≤ 2 * Real.pi / (G.omega : ℝ) := by simpa using hY j q
    have hω : (0 : ℝ) < G.omega := by exact_mod_cast G.omega_pos
    have hlenω : b-a ≤ (G.omega : ℝ) := by
      rw [hlen]
      exact_mod_cast thickLength_le_omega G q m
    calc
      _ ≤ (2 * Real.pi / (G.omega : ℝ)) * (b-a) :=
        mul_le_mul_of_nonneg_right hnode (sub_pos.mpr hab).le
      _ ≤ (2 * Real.pi / (G.omega : ℝ)) * G.omega :=
        mul_le_mul_of_nonneg_left hlenω (by positivity)
      _ = _ := by field_simp
  have hderiv : ∀ t ∈ Set.Icc a b, ‖deriv f t‖ ≤ 20 * (n : ℝ)^3 / L * B := by
    intro t ht
    have h := exponentialSum_interval_derivative_norm_le hn (fun j => Y j q) v hab hfreq ht
    change ‖deriv f t‖ ≤ 20 * (n : ℝ)^3 / (b-a) * setSupNorm f (Set.Icc a b) at h
    apply h.trans
    apply mul_le_mul
    · exact div_le_div_of_nonneg_left (by positivity) hL hLlen
    · exact hsup
    · exact setSupNorm_nonneg _ _
    · positivity
  have hvariation := norm_sq_variation_of_derivative_bound hB
    (fun t _ => ExponentialSumEstimates.differentiable_exponentialSum (fun j => Y j q) v t)
    hval hderiv (hcell _ (hz q (Set.mem_univ q))) (hcell u hu)
  change |‖f u‖ ^ 2 - ‖f (z q)‖ ^ 2| ≤
    (2 * B * (20 * (n : ℝ)^3 / L * B)) * |u-z q| at hvariation
  rw [hrepr u, hrepr (z q), Function.update_eq_self] at hvariation
  have hBsq : B^2 ≤ ((4 : ℝ)^d * (n : ℝ)^(2*d) / L^d) * continuousEnergy G Y c := by
    dsimp [B]
    rw [mul_pow, continuousL2Norm_sq]
    exact mul_le_mul_of_nonneg_right (productNikolskiiCoefficient_sq_le G)
      (continuousEnergy_nonneg G Y c)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ)^(2*d+3) ≤ (n : ℝ)^(4*d+5) :=
    pow_le_pow_right₀ hnR (by omega)
  have hcoef : 2 * B * (20 * (n : ℝ)^3 / L * B) ≤
      ((40 * (4 : ℝ)^d) * (n : ℝ)^(4*d+5) / L^(d+1)) * continuousEnergy G Y c := by
    calc
      _ = (40 * (n : ℝ)^3 / L) * B^2 := by ring
      _ ≤ (40 * (n : ℝ)^3 / L) *
          (((4 : ℝ)^d * (n : ℝ)^(2*d) / L^d) * continuousEnergy G Y c) :=
        mul_le_mul_of_nonneg_left hBsq (by positivity)
      _ = ((40 * (4 : ℝ)^d) * (n : ℝ)^(2*d+3) / L^(d+1)) *
          continuousEnergy G Y c := by
        rw [pow_add, pow_succ L d]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
          (by positivity)) (continuousEnergy_nonneg G Y c)
  exact hvariation.trans (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))

/-- Uniform norming `η₀=1/2` follows from the exact geometric block condition
for localized nodes. No norming or derivative premise is added. -/
theorem continuousNorming_half_of_blockCondition {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hn : 0 < n)
    (hY : ∀ j, InCube (2 * Real.pi / (G.omega : ℝ)) 0 (Y j))
    (hblock : SegmentedBlockCondition (discretizationConstant d) G n) :
    ContinuousNorming G Y (1 / 2) := by
  apply continuousNorming_half_of_blockCondition_and_coordinate_lipschitz G Y
    (K := 40 * (4 : ℝ)^d) (by positivity)
  · convert hblock using 1
    unfold discretizationConstant
    ring
  · intro c k q z hz u hu
    exact exponentialSum_cell_coordinate_lipschitz G Y hn hY c k q z hz hu

/-- The article's uniform norming conclusion, with the literal open-cube
localization and the permitted common translation of all nodes. -/
theorem continuousNorming_half_of_localized_blockCondition {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (center : Point d) (hn : 0 < n)
    (hY : ∀ j, InOpenCube (2 * Real.pi / (G.omega : ℝ)) center (Y j))
    (hblock : SegmentedBlockCondition (discretizationConstant d) G n) :
    ContinuousNorming G Y (1 / 2) := by
  have htranslated : ∀ j,
      InCube (2 * Real.pi / (G.omega : ℝ)) 0 (translateNodes Y center j) := by
    intro j q
    simpa only [InCube, translateNodes, Pi.zero_apply, sub_zero] using
      ((hY j).coordinate_lt q).le
  exact (continuousNorming_translateNodes_iff G Y center (1/2)).mp
    (continuousNorming_half_of_blockCondition G (translateNodes Y center) hn htranslated hblock)

end
end LeanNumDetect.MultiTuran
