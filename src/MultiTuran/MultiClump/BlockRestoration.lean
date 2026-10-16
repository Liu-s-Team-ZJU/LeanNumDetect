import MultiTuran.MultiClump.ShortenedGrid
import MultiTuran.Norming.ProductRestriction
import MultiTuran.Turan.Main

/-!
Returning each shortened sampling block to its full length. Both energies
are the genuine Lebesgue integrals over all product blocks. Boundary overlaps
are removed by half-open rectangles, which differ only on null sets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators ENNReal
open Set MeasureTheory Function

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

/-- The finite product of the original coordinate-block indices. -/
abbrev ProductBlock {d : ℕ} (G : SegmentedGrid d) := (q : Fin d) → G.Block q

/-- A closed coordinate rectangle. -/
def coordinateBox {d : ℕ} (a b : Point d) : Set (Point d) :=
  Set.pi Set.univ (fun q => Set.Icc (a q) (b q))

/-- One rectangular component of the true thickening. -/
def productBlockBox {d : ℕ} (G : SegmentedGrid d) (b : ProductBlock G) : Set (Point d) :=
  coordinateBox (fun q => (G.start q (b q) : ℝ))
    (fun q => ((G.start q (b q) + G.thickLength q (b q) : ℕ) : ℝ))

private def productBlockHalfOpen {d : ℕ} (G : SegmentedGrid d)
    (b : ProductBlock G) : Set (Point d) :=
  Set.pi Set.univ (fun q => Set.Ico (G.start q (b q) : ℝ)
    ((G.start q (b q) + G.thickLength q (b q) : ℕ) : ℝ))

theorem productBlockBox_isCompact {d : ℕ} (G : SegmentedGrid d) (b : ProductBlock G) :
    IsCompact (productBlockBox G b) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem thickening_eq_iUnion_productBlockBox {d : ℕ} (G : SegmentedGrid d) :
    G.thickening = ⋃ b : ProductBlock G, productBlockBox G b := by
  classical
  ext x
  constructor
  · intro hx
    have hex (q : Fin d) : ∃ m : G.Block q,
        x q ∈ Set.Icc (G.start q m : ℝ)
          ((G.start q m + G.thickLength q m : ℕ) : ℝ) :=
      Set.mem_iUnion.mp (hx q (Set.mem_univ q))
    choose b hb using hex
    exact Set.mem_iUnion.mpr ⟨b, fun q _ => hb q⟩
  · intro hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    intro q hq
    exact Set.mem_iUnion.mpr ⟨b q, hb q hq⟩

private theorem productBlockHalfOpen_ae_eq {d : ℕ} (G : SegmentedGrid d)
    (b : ProductBlock G) : productBlockHalfOpen G b =ᵐ[volume] productBlockBox G b := by
  exact Measure.ae_eq_set_pi (fun _ _ => Ico_ae_eq_Icc)

private theorem productBlockHalfOpen_pairwise_disjoint {d : ℕ} (G : SegmentedGrid d) :
    Pairwise (Disjoint on productBlockHalfOpen G) := by
  classical
  intro b c hbc
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hbc
  apply Set.disjoint_left.mpr
  intro x hxb hxc
  have hb := hxb q (Set.mem_univ q)
  have hc := hxc q (Set.mem_univ q)
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · have hnat : G.start q (b q) + G.thickLength q (b q) ≤ G.start q (c q) := by
      simpa only [SegmentedGrid.thickLength, Nat.add_assoc] using G.separated q _ _ hlt
    have hreal : ((G.start q (b q) + G.thickLength q (b q) : ℕ) : ℝ) ≤
        (G.start q (c q) : ℝ) := by exact_mod_cast hnat
    exact (not_lt_of_ge (hreal.trans hc.1)) hb.2
  · have hnat : G.start q (c q) + G.thickLength q (c q) ≤ G.start q (b q) := by
      simpa only [SegmentedGrid.thickLength, Nat.add_assoc] using G.separated q _ _ hgt
    have hreal : ((G.start q (c q) + G.thickLength q (c q) : ℕ) : ℝ) ≤
        (G.start q (b q) : ℝ) := by exact_mod_cast hnat
    exact (not_lt_of_ge (hreal.trans hb.1)) hc.2

/-- Exact decomposition into every original rectangular block, including
adjacent blocks whose closed thickenings share a boundary. -/
theorem continuousEnergy_eq_sum_productBlockBox {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    continuousEnergy G Y c = ∑ b : ProductBlock G, setEnergy Y c (productBlockBox G b) := by
  have hae : (⋃ b : ProductBlock G, productBlockHalfOpen G b) =ᵐ[volume] G.thickening := by
    rw [thickening_eq_iUnion_productBlockBox]
    exact Filter.EventuallyEq.countable_iUnion (productBlockHalfOpen_ae_eq G)
  unfold continuousEnergy setEnergy
  rw [← setIntegral_congr_set hae]
  rw [integral_iUnion_fintype (s := productBlockHalfOpen G)
    (fun b => show MeasurableSet (productBlockHalfOpen G b) from
      MeasurableSet.univ_pi (fun _ => measurableSet_Ico))
    (productBlockHalfOpen_pairwise_disjoint G)]
  · apply Finset.sum_congr rfl
    intro b _
    exact setIntegral_congr_set (productBlockHalfOpen_ae_eq G b)
  · intro b
    exact (exponentialSum_energy_integrableOn Y c (productBlockBox_isCompact G b)).mono_set
      (fun _ hx q hq => ⟨(hx q hq).1, (hx q hq).2.le⟩)

theorem coordinateBox_volume {d : ℕ} (a b : Point d) (hab : ∀ q, a q ≤ b q) :
    volume (coordinateBox a b) = ENNReal.ofReal (∏ q, (b q - a q)) := by
  rw [coordinateBox, volume_pi_pi]
  simp only [Real.volume_Icc]
  exact (ENNReal.ofReal_prod_of_nonneg (fun q _ => sub_nonneg.mpr (hab q))).symm

theorem coordinateBox_volume_toReal {d : ℕ} (a b : Point d) (hab : ∀ q, a q ≤ b q) :
    (volume (coordinateBox a b)).toReal = ∏ q, (b q - a q) := by
  rw [coordinateBox_volume a b hab,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun q _ => sub_nonneg.mpr (hab q))]


/-- Product Nikolskii on one genuine rectangle, with the original constants. -/
theorem exponentialSum_coordinateBox_norm_sq_le {d n : ℕ}
    (hn : 0 < n) (Y : Fin n → Point d) (c : Fin n → ℂ)
    (a b : Point d) (hab : ∀ q, a q < b q) {t : Point d}
    (ht : t ∈ coordinateBox a b) :
    ‖exponentialSum Y c t‖ ^ 2 ≤
      (Real.pi * n / 2) ^ (2 * d) / (∏ q, (b q - a q)) *
        setEnergy Y c (coordinateBox a b) := by
  classical
  let C : Fin d → ℝ := fun q => (Real.pi * n / 2) ^ 2 / (b q - a q)
  let F : Point d → ℝ≥0∞ := fun x => ENNReal.ofReal (‖exponentialSum Y c x‖ ^ 2)
  have hP := continuous_exponentialSum Y c
  have hC (q : Fin d) : 0 ≤ C q :=
    div_nonneg (sq_nonneg _) (sub_pos.mpr (hab q)).le
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hsection (q : Fin d) (x : Point d) (hx : x q ∈ Set.Icc (a q) (b q)) :
      F x ≤ ENNReal.ofReal (C q) * ∫⁻ u in Set.Icc (a q) (b q),
        F (Function.update x q u) := by
    let z := fun j => c j * Complex.exp (Complex.I *
      ((∑ r ∈ Finset.univ.erase q, x r * Y j r : ℝ) : ℂ))
    have hscalar := exponentialSum_intervalUnion_norm_sq_le_div hn (fun j => Y j q) z
      (fun _ : Unit => a q) (fun _ : Unit => b q) (sub_pos.mpr (hab q))
      (fun _ => le_refl _) (by simpa only [intervalUnion, iUnion_const] using hx)
    simp only [intervalUnion, iUnion_const] at hscalar
    have hrepr (u : ℝ) : ExponentialSumEstimates.exponentialSum (fun j => Y j q) z u =
        exponentialSum Y c (Function.update x q u) :=
      (exponentialSum_coordinate_section Y c x q u).symm
    simp_rw [hrepr] at hscalar
    simp only [Function.update_eq_self] at hscalar
    have hInt : IntegrableOn (fun u => ‖exponentialSum Y c (Function.update x q u)‖ ^ 2)
        (Set.Icc (a q) (b q)) := by
      have hc : Continuous (fun u => ‖exponentialSum Y c (Function.update x q u)‖ ^ 2) := by
        convert (ExponentialSumEstimates.continuous_exponentialSum (fun j => Y j q) z).norm.pow 2
          using 1
        funext u
        exact congrArg (fun v : ℂ => ‖v‖ ^ 2) (hrepr u).symm
      exact hc.continuousOn.integrableOn_compact isCompact_Icc
    have h := ENNReal.ofReal_le_ofReal hscalar
    rw [ENNReal.ofReal_mul (hC q), ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at h
    exact h
  have hpi := pi_coordinate_evaluation_bound d (fun q => Set.Icc (a q) (b q))
    (fun q => ENNReal.ofReal (C q)) F hF hsection t (fun q => ht q (Set.mem_univ q))
  change F t ≤ (∏ q, ENNReal.ofReal (C q)) * ∫⁻ x in coordinateBox a b, F x at hpi
  have hInt := exponentialSum_energy_integrableOn Y c
    (show IsCompact (coordinateBox a b) from isCompact_univ_pi (fun _ => isCompact_Icc))
  have henergy : ENNReal.ofReal (setEnergy Y c (coordinateBox a b)) =
      ∫⁻ x in coordinateBox a b, F x :=
    ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  rw [← ENNReal.ofReal_prod_of_nonneg (fun q _ => hC q), ← henergy,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun q _ => hC q))] at hpi
  have hreal : ‖exponentialSum Y c t‖ ^ 2 ≤
      (∏ q, C q) * setEnergy Y c (coordinateBox a b) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Finset.prod_nonneg (fun q _ => hC q))
      (setEnergy_nonneg Y c _))).mp hpi
  have hconstant : (∏ q, C q) = (Real.pi * n / 2) ^ (2 * d) /
      (∏ q, (b q - a q)) := by
    dsimp [C]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rwa [hconstant] at hreal

theorem coordinateBox_supNorm_sq_le {d n : ℕ}
    (hn : 0 < n) (Y : Fin n → Point d) (c : Fin n → ℂ)
    (a b : Point d) (hab : ∀ q, a q < b q) :
    setSupNorm (exponentialSum Y c) (coordinateBox a b) ^ 2 ≤
      (Real.pi * n / 2) ^ (2 * d) / (∏ q, (b q - a q)) *
        setEnergy Y c (coordinateBox a b) := by
  have hE : 0 ≤ (Real.pi * n / 2) ^ (2 * d) / (∏ q, (b q - a q)) *
      setEnergy Y c (coordinateBox a b) :=
    mul_nonneg (div_nonneg (by positivity)
      (Finset.prod_nonneg fun q _ => (sub_pos.mpr (hab q)).le)) (setEnergy_nonneg Y c _)
  have hsup : setSupNorm (exponentialSum Y c) (coordinateBox a b) ≤
      Real.sqrt ((Real.pi * n / 2) ^ (2 * d) / (∏ q, (b q - a q)) *
        setEnergy Y c (coordinateBox a b)) := by
    apply Real.sSup_le
    · rintro z ⟨t, ht, rfl⟩
      exact (Real.le_sqrt (norm_nonneg _) hE).mpr
        (exponentialSum_coordinateBox_norm_sq_le hn Y c a b hab ht)
    · exact Real.sqrt_nonneg _
  have hsquare := (sq_le_sq₀ (setSupNorm_nonneg _ _) (Real.sqrt_nonneg _)).mpr hsup
  rwa [Real.sq_sqrt hE] at hsquare

theorem coordinateBox_energy_le_volume_mul_supNorm_sq {d n : ℕ}
    (Y : Fin n → Point d) (c : Fin n → ℂ) (a b : Point d)
    (hab : ∀ q, a q ≤ b q) :
    setEnergy Y c (coordinateBox a b) ≤ (∏ q, (b q - a q)) *
      setSupNorm (exponentialSum Y c) (coordinateBox a b) ^ 2 := by
  have hcompact : IsCompact (coordinateBox a b) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hint := exponentialSum_energy_integrableOn Y c hcompact
  have hfinite : volume (coordinateBox a b) ≠ ∞ := hcompact.measure_lt_top.ne
  have hconst : IntegrableOn
      (fun _ : Point d => setSupNorm (exponentialSum Y c) (coordinateBox a b) ^ 2)
      (coordinateBox a b) := integrableOn_const hfinite
  have h := setIntegral_mono_on hint hconst hcompact.isClosed.measurableSet
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _)
      (norm_le_setSupNorm_on_compact _ (continuous_exponentialSum Y c) hcompact ht) 2)
  simpa only [setIntegral_const, smul_eq_mul, measureReal_def,
    coordinateBox_volume_toReal a b hab, setEnergy] using h


/-- Restoring a rectangle whose coordinate lengths were decreased by at most
one half, retaining the original multidimensional Turán exponent. -/
theorem coordinateBox_energy_restoration {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (Y : Fin n → Point d) (c : Fin n → ℂ) (a b b' : Point d)
    (hshort : ∀ q, a q < b' q) (hsub : ∀ q, b' q ≤ b q)
    (hhalf : ∀ q, b q - a q ≤ 2 * (b' q - a q)) :
    setEnergy Y c (coordinateBox a b) ≤
      (2 : ℝ)^d*(Real.pi*n/2)^(2*d)*
        ((2 : ℝ)^d*multidimensionalTuranConstant*(d : ℝ))^(2*(n-1))*
          setEnergy Y c (coordinateBox a b') := by
  let V : ℝ := ∏ q, (b q - a q)
  let V' : ℝ := ∏ q, (b' q - a q)
  let T : ℝ := (2 : ℝ)^d*multidimensionalTuranConstant*(d : ℝ)
  have hfull (q : Fin d) : a q < b q := (hshort q).trans_le (hsub q)
  have hV : 0 < V := Finset.prod_pos (fun q _ => sub_pos.mpr (hfull q))
  have hV' : 0 < V' := Finset.prod_pos (fun q _ => sub_pos.mpr (hshort q))
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (mul_nonneg (by positivity) multidimensionalTuranConstant_pos.le)
      (Nat.cast_nonneg d)
  have hvol : V ≤ (2 : ℝ)^d * V' := by
    calc
      V ≤ ∏ q, 2*(b' q-a q) :=
        Finset.prod_le_prod (fun q _ => (sub_pos.mpr (hfull q)).le) (fun q _ => hhalf q)
      _ = (2 : ℝ)^d*V' := by rw [Finset.prod_mul_distrib]; simp [V']
  have hratio : V/V' ≤ (2 : ℝ)^d := (div_le_iff₀ hV').mpr hvol
  have hbase : multidimensionalTuranConstant*(d : ℝ)*V/V' ≤ T := by
    calc
      _ = (multidimensionalTuranConstant*(d : ℝ))*(V/V') := by ring
      _ ≤ (multidimensionalTuranConstant*(d : ℝ))*(2 : ℝ)^d :=
        mul_le_mul_of_nonneg_left hratio
          (mul_nonneg multidimensionalTuranConstant_pos.le (Nat.cast_nonneg d))
      _ = T := by dsimp [T]; ring
  have hcompact : IsCompact (coordinateBox a b) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hconvex : Convex ℝ (coordinateBox a b) := convex_pi (fun _ _ => convex_Icc _ _)
  have hshortCompact : IsCompact (coordinateBox a b') := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsubset : coordinateBox a b' ⊆ coordinateBox a b := by
    intro x hx q hq
    exact ⟨(hx q hq).1, (hx q hq).2.trans (hsub q)⟩
  have hpos : 0 < volume (coordinateBox a b') := by
    rw [coordinateBox_volume a b' (fun q => (hshort q).le)]
    exact ENNReal.ofReal_pos.mpr hV'
  have hrestr := exponentialSum_convexBody_supNorm_le hd hn hcompact hconvex
    hshortCompact.isClosed.measurableSet hsubset hpos Y c
  rw [coordinateBox_volume_toReal a b (fun q => (hfull q).le),
    coordinateBox_volume_toReal a b' (fun q => (hshort q).le)] at hrestr
  have hrestr' : setSupNorm (exponentialSum Y c) (coordinateBox a b) ≤
      T^(n-1)*setSupNorm (exponentialSum Y c) (coordinateBox a b') := by
    apply hrestr.trans
    apply mul_le_mul_of_nonneg_right _ (setSupNorm_nonneg _ _)
    exact pow_le_pow_left₀
      (div_nonneg (mul_nonneg (mul_nonneg multidimensionalTuranConstant_pos.le
        (Nat.cast_nonneg d)) hV.le) hV'.le) hbase (n-1)
  have hpower : (T^(n-1))^2 = T^(2*(n-1)) := by rw [← pow_mul]; congr 1; omega
  have hN := coordinateBox_supNorm_sq_le hn Y c a b' hshort
  have hE := coordinateBox_energy_le_volume_mul_supNorm_sq Y c a b (fun q => (hfull q).le)
  have hEshort := setEnergy_nonneg Y c (coordinateBox a b')
  calc
    setEnergy Y c (coordinateBox a b) ≤
        V*(T^(n-1)*setSupNorm (exponentialSum Y c) (coordinateBox a b'))^2 :=
      hE.trans (mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (setSupNorm_nonneg _ _)
          (mul_nonneg (pow_nonneg hT _) (setSupNorm_nonneg _ _))).mpr hrestr') hV.le)
    _ = V*T^(2*(n-1))*setSupNorm (exponentialSum Y c) (coordinateBox a b')^2 := by
      rw [mul_pow, hpower]
      ring
    _ ≤ V*T^(2*(n-1))*((Real.pi*n/2)^(2*d)/V'*
        setEnergy Y c (coordinateBox a b')) :=
      mul_le_mul_of_nonneg_left hN (mul_nonneg hV.le (pow_nonneg hT _))
    _ = (V/V')*((Real.pi*n/2)^(2*d)*T^(2*(n-1))*
        setEnergy Y c (coordinateBox a b')) := by ring
    _ ≤ (2 : ℝ)^d*((Real.pi*n/2)^(2*d)*T^(2*(n-1))*
        setEnergy Y c (coordinateBox a b')) :=
      mul_le_mul_of_nonneg_right hratio
        (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hT _)) hEshort)
    _ = _ := by dsimp [T]; ring

/-- The block-restoration lemma on every measured block, with no geometric row loss
beyond the explicitly shortened endpoints. -/
theorem continuousEnergy_le_shortenedGrid {d n : ℕ} (G : SegmentedGrid d)
    (W : ℕ) (hW : 2*W < G.minThickLength) (hn : 0 < n)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    continuousEnergy G Y c ≤
      (2 : ℝ)^d*(Real.pi*n/2)^(2*d)*
        ((2 : ℝ)^d*multidimensionalTuranConstant*(d : ℝ))^(2*(n-1))*
          continuousEnergy (shortenedGrid G W) Y c := by
  have hblock (b : ProductBlock G) : setEnergy Y c (productBlockBox G b) ≤
      (2 : ℝ)^d*(Real.pi*n/2)^(2*d)*
        ((2 : ℝ)^d*multidimensionalTuranConstant*(d : ℝ))^(2*(n-1))*
          setEnergy Y c (productBlockBox (shortenedGrid G W) b) := by
    apply coordinateBox_energy_restoration G.dimension_pos hn
    · intro q
      dsimp
      have hpos : 0 < (shortenedGrid G W).thickLength q (b q) := by
        unfold SegmentedGrid.thickLength
        omega
      exact_mod_cast Nat.lt_add_of_pos_right hpos
    · intro q
      dsimp
      have h := Nat.sub_le (G.length q (b q)) W
      simp only [SegmentedGrid.thickLength, shortenedGrid_length]
      exact_mod_cast (show G.start q (b q) + (G.length q (b q)-W+1) ≤
        G.start q (b q) + (G.length q (b q)+1) by omega)
    · intro q
      simp only [shortenedGrid_start, Nat.cast_add, add_sub_cancel_left]
      exact_mod_cast shortenedGrid_half_thickLength G W hW q (b q)
  rw [continuousEnergy_eq_sum_productBlockBox G,
    continuousEnergy_eq_sum_productBlockBox (shortenedGrid G W), Finset.mul_sum]
  exact Finset.sum_le_sum (fun b _ => hblock b)

end
end LeanNumDetect.MultiTuran.MultiClump
