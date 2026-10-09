import RandSamp.MultidimensionalMultiClumpModel
import General.Fourier.AngularClumpSectionBounds
import General.Fourier.QuantitativeClumpCrossCorrelation
import General.Fourier.QuantitativePolynomialVariationCrossCorrelation
import General.Fourier.WeightedClumpCrossBounds
import RandSamp.ClumpMomentBounds
import General.Finite.ProductEnergyBounds
import General.Finite.AlmostOrthogonalEnergy

/-!
# Gap-free clump leverage on integer frequency cubes

Coordinate sections are ordinary one-dimensional angular Fourier signals.
The one-dimensional companion bounds allow repeated projected frequencies.
Their row estimates iterate exactly, while one separated coordinate controls
the full cross inner product by Cauchy--Schwarz on all other coordinates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace
open Matrix WithLp Set

namespace LeanNumDetect.RandSamp
open AngularClumpSectionBounds ProductEnergyBounds AlmostOrthogonalEnergy
noncomputable section

/-- The unnormalized cube Fourier signal. -/
def cubeFourierSignal {d s : ℕ} (M : ℕ) (Y : Fin s → Fin d → ℝ) (c : Fin s → ℂ) :
    EuclideanSpace ℂ (CubeFrequency d M) :=
  toLp 2 (fun k => ∑ j, cubeFourierRow Y k j * c j)

/-- Actual cube Fourier column space, including repeated projected nodes. -/
def cubeFourierColumnSpace {d s : ℕ} (M : ℕ) (Y : Fin s → Fin d → ℝ) :
    Submodule ℂ (EuclideanSpace ℂ (CubeFrequency d M)) :=
  Submodule.span ℂ (Set.range fun j : Fin s => toLp 2 (fun k => cubeFourierRow Y k j))

theorem cubeFourierColumnSpace_coefficient_representation {d s M : ℕ}
    (Y : Fin s → Fin d → ℝ) (u : EuclideanSpace ℂ (CubeFrequency d M))
    (hu : u ∈ cubeFourierColumnSpace M Y) :
    ∃ c : Fin s → ℂ, u = cubeFourierSignal M Y c := by
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, rfl⟩ := hu
    refine ⟨Pi.single j 1, ?_⟩
    ext k
    simp [cubeFourierSignal, Pi.single_apply]
  | zero =>
    refine ⟨0, ?_⟩
    ext k
    simp [cubeFourierSignal]
  | add u v hu hv ihu ihv =>
    obtain ⟨c, rfl⟩ := ihu
    obtain ⟨e, rfl⟩ := ihv
    refine ⟨c + e, ?_⟩
    ext k
    simp [cubeFourierSignal, mul_add, Finset.sum_add_distrib]
  | smul z u hu ihu =>
    obtain ⟨c, rfl⟩ := ihu
    refine ⟨z • c, ?_⟩
    ext k
    simp [cubeFourierSignal, Finset.mul_sum, mul_left_comm]

theorem cubeFourierSignal_mem_columnSpace {d s M : ℕ}
    (Y : Fin s → Fin d → ℝ) (c : Fin s → ℂ) :
    cubeFourierSignal M Y c ∈ cubeFourierColumnSpace M Y := by
  classical
  have he : cubeFourierSignal M Y c = ∑ j, c j • toLp 2 (fun k => cubeFourierRow Y k j) := by
    ext k
    simp [cubeFourierSignal, mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Changing one frequency coordinate factors off its one-dimensional phase. -/
theorem cubeFourierRow_update_factor {d s M : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (q : Fin d) (l : Fin (M + 1)) (j : Fin s) :
    cubeFourierRow Y (Function.update k q l) j =
      cubeFourierRow Y (Function.update k q 0) j *
        ClusteredVandermonde.vandermonde M (fun i => Y i q) l j := by
  classical
  have hsum : (∑ r, (((Function.update k q l) r).val : ℝ) * Y j r) =
      (∑ r, (((Function.update k q 0) r).val : ℝ) * Y j r) + (l.val : ℝ) * Y j q := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ q)]
    simp only [Function.update_self, Fin.val_zero, Nat.cast_zero, zero_mul]
    have he : (∑ r ∈ Finset.univ.erase q, (((Function.update k q l) r).val : ℝ) * Y j r) =
        ∑ r ∈ Finset.univ.erase q, (((Function.update k q 0) r).val : ℝ) * Y j r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hr),
        Function.update_of_ne (Finset.ne_of_mem_erase hr)]
    rw [he]
    ring
  simp only [cubeFourierRow, ClusteredVandermonde.vandermonde]
  rw [hsum, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- Every coordinate section of an actual cube column-space vector belongs
to the corresponding one-dimensional column span. -/
theorem cubeFourierColumnSpace_section_mem {d s M : ℕ}
    (Y : Fin s → Fin d → ℝ) (u : EuclideanSpace ℂ (CubeFrequency d M))
    (hu : u ∈ cubeFourierColumnSpace M Y) (q : Fin d) (k : CubeFrequency d M) :
    toLp 2 (fun l : Fin (M + 1) => u (Function.update k q l)) ∈
      ClusteredVandermonde.clusterSubspace M (fun j => Y j q) := by
  classical
  obtain ⟨c, rfl⟩ := cubeFourierColumnSpace_coefficient_representation Y u hu
  have he : toLp 2 (fun l : Fin (M + 1) =>
      cubeFourierSignal M Y c (Function.update k q l)) =
      ClumpJetApproximation.angularSignal M (fun j => Y j q)
        (fun j => cubeFourierRow Y (Function.update k q 0) j * c j) := by
    ext l
    simp only [ofLp_toLp, cubeFourierSignal, ClumpJetApproximation.angularSignal]
    apply Finset.sum_congr rfl
    intro j _
    rw [cubeFourierRow_update_factor]
    ring
  rw [he]
  have he' : ClumpJetApproximation.angularSignal M (fun j => Y j q)
      (fun j => cubeFourierRow Y (Function.update k q 0) j * c j) =
      ∑ j, (cubeFourierRow Y (Function.update k q 0) j * c j) •
        toLp 2 (fun l : Fin (M + 1) => ClusteredVandermonde.vandermonde M
          (fun j => Y j q) l j) := by
    ext l
    simp [ClumpJetApproximation.angularSignal]
  rw [he']
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem cube_split_section_eq_update {d M : ℕ} (q : Fin d)
    (y : {i : Fin d // i ≠ q} → Fin (M + 1)) (l : Fin (M + 1)) :
    (Equiv.funSplitAt q (Fin (M + 1))).symm (l, y) =
      Function.update ((Equiv.funSplitAt q (Fin (M + 1))).symm (0, y)) q l := by
  classical
  ext r
  by_cases hr : r = q
  · subst r
    simp [Equiv.funSplitAt_symm_apply]
  · simp [Equiv.funSplitAt_symm_apply, hr]

theorem cubeFourierColumnSpace_split_section_mem {d s M : ℕ}
    (Y : Fin s → Fin d → ℝ) (u : EuclideanSpace ℂ (CubeFrequency d M))
    (hu : u ∈ cubeFourierColumnSpace M Y) (q : Fin d)
    (y : {i : Fin d // i ≠ q} → Fin (M + 1)) :
    toLp 2 (fun l : Fin (M + 1) => u ((Equiv.funSplitAt q (Fin (M + 1))).symm (l, y))) ∈
      ClusteredVandermonde.clusterSubspace M (fun j => Y j q) := by
  have h := cubeFourierColumnSpace_section_mem Y u hu q
    ((Equiv.funSplitAt q (Fin (M + 1))).symm (0, y))
  convert h using 1
  ext l
  simpa only [ofLp_toLp] using congrArg (fun k => u k) (cube_split_section_eq_update q y l)

/-- The absolute one-dimensional row constant iterates exactly on the cube. -/
theorem cubeColumnSpace_row_bound_of_sections {d s M : ℕ}
    (Y : Fin s → Fin d → ℝ)
    (hsections : ∀ q : Fin d, ∀ u ∈ ClusteredVandermonde.clusterSubspace M (fun j => Y j q),
      ∀ l : Fin (M + 1), (M + 1 : ℝ) * ‖u l‖ ^ 2 ≤ 512 * (s : ℝ) ^ 2 * ‖u‖ ^ 2)
    (u : EuclideanSpace ℂ (CubeFrequency d M)) (hu : u ∈ cubeFourierColumnSpace M Y)
    (k : CubeFrequency d M) :
    (M + 1 : ℝ) ^ d * ‖u k‖ ^ 2 ≤ 512 ^ d * (s : ℝ) ^ (2 * d) * ‖u‖ ^ 2 := by
  have h := product_row_energy_bound (ofLp u) (by positivity : (0 : ℝ) ≤ M + 1)
    (by positivity : (0 : ℝ) ≤ 512 * (s : ℝ) ^ 2) (fun q x => ?_) k
  · simpa only [EuclideanSpace.norm_sq_eq, mul_pow, ← pow_mul] using h
  · have hh := hsections q _ (cubeFourierColumnSpace_section_mem Y u hu q x) (x q)
    simpa only [Function.update_eq_self, ofLp_toLp, EuclideanSpace.norm_sq_eq] using hh

theorem cubeColumnSpace_row_bound_of_sections_with_constant {d s M : ℕ}
    {q : ℝ} (hq : 0 ≤ q) (Y : Fin s → Fin d → ℝ)
    (hsections : ∀ coord : Fin d, ∀ u ∈ ClusteredVandermonde.clusterSubspace M (fun j => Y j coord),
      ∀ l : Fin (M + 1), (M + 1 : ℝ) * ‖u l‖ ^ 2 ≤ q * (s : ℝ) ^ 2 * ‖u‖ ^ 2)
    (u : EuclideanSpace ℂ (CubeFrequency d M)) (hu : u ∈ cubeFourierColumnSpace M Y)
    (k : CubeFrequency d M) :
    (M + 1 : ℝ) ^ d * ‖u k‖ ^ 2 ≤ q ^ d * (s : ℝ) ^ (2 * d) * ‖u‖ ^ 2 := by
  have h := product_row_energy_bound (ofLp u) (by positivity : (0 : ℝ) ≤ M + 1)
    (by positivity : (0 : ℝ) ≤ q * (s : ℝ) ^ 2) (fun coord x => ?_) k
  · simpa only [EuclideanSpace.norm_sq_eq, mul_pow, ← pow_mul] using h
  · have hh := hsections coord _ (cubeFourierColumnSpace_section_mem Y u hu coord x) (x coord)
    simpa only [Function.update_eq_self, ofLp_toLp, EuclideanSpace.norm_sq_eq] using hh


theorem cubeColumnSpace_row_bound_of_sections_tight {d s M : ℕ}
    (Y : Fin s → Fin d → ℝ)
    (hsections : ∀ q : Fin d, ∀ u ∈ ClusteredVandermonde.clusterSubspace M (fun j => Y j q),
      ∀ l : Fin (M + 1), (M + 1 : ℝ) * ‖u l‖ ^ 2 ≤ 24 * (s : ℝ) ^ 2 * ‖u‖ ^ 2)
    (u : EuclideanSpace ℂ (CubeFrequency d M)) (hu : u ∈ cubeFourierColumnSpace M Y)
    (k : CubeFrequency d M) :
    (M + 1 : ℝ) ^ d * ‖u k‖ ^ 2 ≤ 24 ^ d * (s : ℝ) ^ (2 * d) * ‖u‖ ^ 2 := by
  have h := product_row_energy_bound (ofLp u) (by positivity : (0 : ℝ) ≤ M + 1)
    (by positivity : (0 : ℝ) ≤ 24 * (s : ℝ) ^ 2) (fun q x => ?_) k
  · simpa only [EuclideanSpace.norm_sq_eq, mul_pow, ← pow_mul] using h
  · have hh := hsections q _ (cubeFourierColumnSpace_section_mem Y u hu q x) (x q)
    simpa only [Function.update_eq_self, ofLp_toLp, EuclideanSpace.norm_sq_eq] using hh


/-- A separating coordinate, chosen for this pair of clumps, controls their
full column-space correlation with no loss depending on dimension. -/
theorem cubeColumnSpace_cross_bound_of_section {d s t M : ℕ}
    (Y : Fin s → Fin d → ℝ) (Z : Fin t → Fin d → ℝ) (q : Fin d)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsection : ∀ u ∈ ClusteredVandermonde.clusterSubspace M (fun j => Y j q),
      ∀ v ∈ ClusteredVandermonde.clusterSubspace M (fun j => Z j q),
        ‖⟪u, v⟫_ℂ‖ ≤ ε * ‖u‖ * ‖v‖)
    (u : EuclideanSpace ℂ (CubeFrequency d M)) (hu : u ∈ cubeFourierColumnSpace M Y)
    (v : EuclideanSpace ℂ (CubeFrequency d M)) (hv : v ∈ cubeFourierColumnSpace M Z) :
    ‖⟪u, v⟫_ℂ‖ ≤ ε * ‖u‖ * ‖v‖ := by
  have h := product_cross_inner_bound q (ofLp u) (ofLp v) hε (fun y => ?_)
  · simpa only [PiLp.inner_apply, RCLike.inner_apply', RCLike.star_def,
      EuclideanSpace.norm_eq] using h
  · have hh := hsection _ (cubeFourierColumnSpace_split_section_mem Y u hu q y)
      _ (cubeFourierColumnSpace_split_section_mem Z v hv q y)
    simpa only [PiLp.inner_apply, ofLp_toLp, RCLike.inner_apply', RCLike.star_def,
      EuclideanSpace.norm_eq] using hh

theorem cubeFourierSignal_average_energy {d s M : ℕ} (Y : Fin s → Fin d → ℝ)
    (z : EuclideanSpace ℂ (Fin s)) :
    ((M + 1 : ℝ) ^ d)⁻¹ * ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2 =
      FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
  simpa only [cubeFullGram, cubeFourierSignal, EuclideanSpace.norm_sq_eq,
    ofLp_toLp, cubeFourierRowEnergy] using (quadratic_cubeFourier_mean Y z).symm

/-- Local row estimates assemble with the actual clump energy factor. -/
theorem row_bound_of_clump_bounds_with_energy {A : ℕ} {κ : Type*} [Fintype κ]
    (v : Fin A → EuclideanSpace ℂ κ) (L : Fin A → ℝ)
    (hL : ∀ a, 0 ≤ L a)
    (hlocal : ∀ a (k : κ), ‖v a k‖^2 ≤ L a * ‖v a‖^2)
    {γ : ℝ} (hγ : 0 < γ)
    (henergy : γ * (∑ a, ‖v a‖^2) ≤ ‖∑ a, v a‖^2) (k : κ) :
    ‖(∑ a, v a) k‖^2 ≤ ((∑ a, L a) / γ) * ‖∑ a, v a‖^2 := by
  have hn (a : Fin A) : ‖v a k‖ ≤ Real.sqrt (L a) * ‖v a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
    rw [mul_pow, Real.sq_sqrt (hL a)]
    exact hlocal a k
  have he : (∑ a, v a) k = ∑ a, v a k := by simp
  rw [he]
  have ht : ‖∑ a, v a k‖ ≤ ∑ a, Real.sqrt (L a) * ‖v a‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hn a)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => Real.sqrt (L a)) (fun a => ‖v a‖)
  simp only [Real.sq_sqrt (hL _)] at hs
  have hsq := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
    fun a _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2 ht
  have hsumL : 0 ≤ ∑ a, L a := Finset.sum_nonneg fun a _ => hL a
  have henergy' : (∑ a, ‖v a‖^2) ≤ ‖∑ a, v a‖^2 / γ :=
    (le_div_iff₀ hγ).2 (by nlinarith only [henergy])
  exact (hsq.trans hs).trans ((mul_le_mul_of_nonneg_left henergy' hsumL).trans_eq (by ring))

namespace ClumpPartition
variable {n A : ℕ} (P : ClumpPartition n A)

/-- Unnormalized signal contributed by exactly one clump. -/
def cubeSignal {d : ℕ} (M : ℕ) (Y : Fin n → Fin d → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (a : Fin A) :
    EuclideanSpace ℂ (CubeFrequency d M) :=
  cubeFourierSignal M (P.multidimensionalNodes Y a) (ofLp (P.coefficients a z))

theorem sum_cubeSignals {d : ℕ} (M : ℕ) (Y : Fin n → Fin d → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) :
    (∑ a, P.cubeSignal M Y z a) = cubeFourierSignal M Y (ofLp z) := by
  ext k
  simp only [WithLp.ofLp_sum, Finset.sum_apply, cubeSignal, cubeFourierSignal,
    coefficients, ofLp_toLp]
  change (∑ a, ∑ j : Fin (P.size a), cubeFourierRow Y k (P.enumeration a j).val *
    z (P.enumeration a j).val) = ∑ j, cubeFourierRow Y k j * z j
  exact P.sum_clumps (fun j : Fin n => cubeFourierRow Y k j * z j)

theorem cubeSignal_mem_columnSubspace {d : ℕ} (M : ℕ) (Y : Fin n → Fin d → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (a : Fin A) :
    P.cubeSignal M Y z a ∈ P.cubeColumnSubspace M Y a := by
  exact cubeFourierSignal_mem_columnSpace (P.multidimensionalNodes Y a)
    (ofLp (P.coefficients a z))

end ClumpPartition

/-- Assemble cube row bounds with only the factor two coming from the
proved half-energy comparison of the clumps. -/
theorem cubeClump_leverage_of_signal_bounds_with_energy {d n A M : ℕ}
    {q γ : ℝ} (hq : 0 ≤ q) (hγ : 0 < γ)
    (P : ClumpPartition n A) (Y : Fin n → Fin d → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hlocal : ∀ a (k : CubeFrequency d M),
      (M + 1 : ℝ)^d * ‖P.cubeSignal M Y z a k‖^2 ≤
        q^d * (P.size a : ℝ)^(2*d) * ‖P.cubeSignal M Y z a‖^2)
    (henergy : γ * (∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
      ‖cubeFourierSignal M Y (ofLp z)‖^2) (k : CubeFrequency d M) :
    cubeFourierRowEnergy Y k (ofLp z) ≤
      (q^d / γ * (P.sizePowerSum d : ℝ)) *
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
  let L : Fin A → ℝ := fun a => q^d * (P.size a : ℝ)^(2*d) / (M + 1 : ℝ)^d
  have hQ : 0 < (M + 1 : ℝ)^d := by positivity
  have hpoint (a : Fin A) (l : CubeFrequency d M) :
      ‖P.cubeSignal M Y z a l‖^2 ≤ L a * ‖P.cubeSignal M Y z a‖^2 := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hQ).2 (by simpa only [mul_comm] using hlocal a l)
  have h := row_bound_of_clump_bounds_with_energy (P.cubeSignal M Y z) L
    (fun _ => by dsimp [L]; positivity) hpoint hγ
    (by simpa only [P.sum_cubeSignals] using henergy) k
  rw [P.sum_cubeSignals] at h
  have hsum : (∑ a, L a) = q^d * (P.sizePowerSum d : ℝ) / (M + 1 : ℝ)^d := by
    dsimp [L]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    simp only [ClumpPartition.sizePowerSum, Nat.cast_sum, Nat.cast_pow]
  rw [hsum] at h
  have he : ((q^d * (P.sizePowerSum d : ℝ) / (M + 1 : ℝ)^d) / γ) *
      ‖cubeFourierSignal M Y (ofLp z)‖^2 =
      (q^d / γ * (P.sizePowerSum d : ℝ)) *
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
    rw [← cubeFourierSignal_average_energy]
    ring
  exact h.trans_eq he

theorem cubeClump_leverage_of_signal_bounds {d n A M : ℕ} (hd : 1 ≤ d)
    (P : ClumpPartition n A) (Y : Fin n → Fin d → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hlocal : ∀ a (k : CubeFrequency d M),
      (M + 1 : ℝ) ^ d * ‖P.cubeSignal M Y z a k‖ ^ 2 ≤
        512 ^ d * (P.size a : ℝ) ^ (2 * d) * ‖P.cubeSignal M Y z a‖ ^ 2)
    (henergy : (1 / 2 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖ ^ 2) ≤
      ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2)
    (k : CubeFrequency d M) :
    cubeFourierRowEnergy Y k (ofLp z) ≤
      (1024 * 512 ^ (d - 1) * (P.sizePowerSum d : ℝ)) *
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
  let L : Fin A → ℝ := fun a => 512 ^ d * (P.size a : ℝ) ^ (2 * d) / (M + 1 : ℝ) ^ d
  have hQ : 0 < (M + 1 : ℝ) ^ d := by positivity
  have hpoint (a : Fin A) (l : CubeFrequency d M) :
      ‖P.cubeSignal M Y z a l‖ ^ 2 ≤ L a * ‖P.cubeSignal M Y z a‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hQ).2 (by simpa only [mul_comm] using hlocal a l)
  have h := row_bound_of_clump_bounds (P.cubeSignal M Y z) L (fun _ => by dsimp [L]; positivity)
    hpoint (by simpa only [P.sum_cubeSignals] using henergy) k
  rw [P.sum_cubeSignals] at h
  have hsum : (∑ a, L a) = 512 ^ d * (P.sizePowerSum d : ℝ) / (M + 1 : ℝ) ^ d := by
    dsimp [L]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    simp only [ClumpPartition.sizePowerSum, Nat.cast_sum, Nat.cast_pow]
  rw [hsum] at h
  have hconst : (2 : ℝ) * 512 ^ d = 1024 * 512 ^ (d - 1) := by
    calc
      (2 : ℝ) * 512 ^ d = 2 * (512 ^ (d - 1) * 512) := by
        congr 1
        rw [← pow_succ]
        congr 1
        omega
      _ = _ := by ring
  have he : (2 : ℝ) * (512 ^ d * (P.sizePowerSum d : ℝ) / (M + 1 : ℝ) ^ d) *
      ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2 =
      (1024 * 512 ^ (d - 1) * (P.sizePowerSum d : ℝ)) *
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
    rw [← cubeFourierSignal_average_energy]
    rw [← hconst]
    ring
  exact h.trans_eq he

theorem cubeClump_leverage_of_signal_bounds_tight {d n A M : ℕ} (_hd : 1 ≤ d)
    (P : ClumpPartition n A) (Y : Fin n → Fin d → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hlocal : ∀ a (k : CubeFrequency d M),
      (M + 1 : ℝ) ^ d * ‖P.cubeSignal M Y z a k‖ ^ 2 ≤
        24 ^ d * (P.size a : ℝ) ^ (2 * d) * ‖P.cubeSignal M Y z a‖ ^ 2)
    (henergy : (1 / 2 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖ ^ 2) ≤
      ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2)
    (k : CubeFrequency d M) :
    cubeFourierRowEnergy Y k (ofLp z) ≤
      (multidimensionalMultiClumpTightLeverageConstant d * (P.sizePowerSum d : ℝ)) *
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
  let L : Fin A → ℝ := fun a => 24 ^ d * (P.size a : ℝ) ^ (2 * d) / (M + 1 : ℝ) ^ d
  have hQ : 0 < (M + 1 : ℝ) ^ d := by positivity
  have hpoint (a : Fin A) (l : CubeFrequency d M) :
      ‖P.cubeSignal M Y z a l‖ ^ 2 ≤ L a * ‖P.cubeSignal M Y z a‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hQ).2 (by simpa only [mul_comm] using hlocal a l)
  have h := row_bound_of_clump_bounds (P.cubeSignal M Y z) L (fun _ => by dsimp [L]; positivity)
    hpoint (by simpa only [P.sum_cubeSignals] using henergy) k
  rw [P.sum_cubeSignals] at h
  have hsum : (∑ a, L a) = 24 ^ d * (P.sizePowerSum d : ℝ) / (M + 1 : ℝ) ^ d := by
    dsimp [L]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    simp only [ClumpPartition.sizePowerSum, Nat.cast_sum, Nat.cast_pow]
  rw [hsum] at h
  have he : (2 : ℝ) * (24 ^ d * (P.sizePowerSum d : ℝ) / (M + 1 : ℝ) ^ d) *
      ‖cubeFourierSignal M Y (ofLp z)‖ ^ 2 =
      (multidimensionalMultiClumpTightLeverageConstant d * (P.sizePowerSum d : ℝ)) *
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
    rw [← cubeFourierSignal_average_energy]
    unfold multidimensionalMultiClumpTightLeverageConstant
    ring
  exact h.trans_eq he

namespace ClumpPartition
variable {n A : ℕ} (P : ClumpPartition n A)

theorem cube_projected_within {d M : ℕ} (Y : Fin n → Fin d → ℝ)
    {c0 C0 : ℝ} (hgeometry : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (a : Fin A) (q : Fin d) :
    WithinAngularClump M (fun j => P.multidimensionalNodes Y a j q)
      (P.multidimensionalNodes Y a ⟨0, P.size_pos a⟩ q) c0 := by
  intro j
  apply (angularTorusDistance_le_iff _ _ _).1
  apply (angularTorusDistance_le_multidimensional _ _ q).trans
  exact hgeometry.within (P.enumeration a j).val
    (P.enumeration a ⟨0, P.size_pos a⟩).val (by rw [P.enumeration_label, P.enumeration_label])

end ClumpPartition

/-- The complete cube analytic bounds follow from geometry alone. A pair of
clumps may use a different separating coordinate from every other pair. -/
theorem cubeClump_analytic_thresholds (d n nstar : ℕ) (hd : 1 ≤ d)
    (hn : 0 < n) (hnstar : 0 < nstar) (B b : ℕ → ℝ)
    (hb : ∀ s, 1 ≤ s → s ≤ nstar → 0 < b s) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      (∀ s, 1 ≤ s → s ≤ nstar → B s ≤ C0 ∧ c0 ≤ b s) ∧
      (∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          ∀ a, ∀ u ∈ P.cubeColumnSubspace M Y a, ∀ k : CubeFrequency d M,
            (M + 1 : ℝ) ^ d * ‖u k‖ ^ 2 ≤
              512 ^ d * (P.size a : ℝ) ^ (2 * d) * ‖u‖ ^ 2) ∧
      (∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          ∀ a a', a ≠ a' → ∀ u ∈ P.cubeColumnSubspace M Y a,
            ∀ v ∈ P.cubeColumnSubspace M Y a',
              ‖⟪u, v⟫_ℂ‖ ≤ (1 / (2 * (n : ℝ))) * ‖u‖ * ‖v‖) := by
  obtain ⟨c0, C0, hc0, hc01, hC0, hlocal, hrow, hcross⟩ :=
    angularClump_section_thresholds n nstar hn hnstar B b hb
  refine ⟨c0, C0, hc0, hc01, hC0, hlocal, ?_, ?_⟩
  · intro M A hM Y P hmax hgeom a u hu k
    apply cubeColumnSpace_row_bound_of_sections (P.multidimensionalNodes Y a) ?_ u hu k
    intro q u' hu' l
    exact hrow (P.size a) M (P.size_pos a) (hmax.1 a) hM _ _
      (P.cube_projected_within Y hgeom a q) u' hu' l
  · intro M A hM Y P hmax hgeom a a' haa u hu v hv
    let x := P.multidimensionalNodes Y a ⟨0, P.size_pos a⟩
    let y := P.multidimensionalNodes Y a' ⟨0, P.size_pos a'⟩
    have hsep : C0 / (M : ℝ) ≤ multidimensionalAngularTorusDistance y x := by
      apply hgeom.between
      rw [P.enumeration_label, P.enumeration_label]
      exact Ne.symm haa
    obtain ⟨q, hq⟩ := (le_multidimensionalAngularTorusDistance_iff hd y x (C0 / M)).1 hsep
    apply cubeColumnSpace_cross_bound_of_section (P.multidimensionalNodes Y a)
      (P.multidimensionalNodes Y a') q (by positivity) ?_ u hu v hv
    intro u' hu' v' hv'
    apply hcross (P.size a) (P.size a') M (P.size_pos a) (hmax.1 a)
      (P.size_pos a') (hmax.1 a') hM _ _ (x q) (y q)
      (P.cube_projected_within Y hgeom a q) (P.cube_projected_within Y hgeom a' q) ?_ u' hu' v' hv'
    intro p
    have h := (le_angularTorusDistance_iff (y q) (x q) (C0 / M)).1 hq (-p)
    simpa only [Int.cast_neg, mul_neg, sub_eq_add_neg] using h

theorem cubeClump_analytic_thresholds_with_row_bound (d n nstar : ℕ) (hd : 1 ≤ d)
    (hn : 0 < n) (hnstar : 0 < nstar)
    {K q κ : ℝ} (hK : 1 ≤ K) (hq : K < q) (hκ : 0 < κ)
    (hpoly : ∀ (s : ℕ), 0 < s → s ≤ nstar → ∀ (a : Fin s → ℂ) (x : ℝ),
      x ∈ Icc (0 : ℝ) 1 →
      ‖PolynomialEvaluationBounds.jetPolynomialSignal a x‖^2 ≤ K * (s : ℝ)^2 *
        (∫ t in (0 : ℝ)..1, ‖PolynomialEvaluationBounds.jetPolynomialSignal a t‖^2))
    (B b : ℕ → ℝ)
    (hb : ∀ s, 1 ≤ s → s ≤ nstar → 0 < b s) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      (∀ s, 1 ≤ s → s ≤ nstar → B s ≤ C0 ∧ c0 ≤ b s) ∧
      (∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          ∀ a, ∀ u ∈ P.cubeColumnSubspace M Y a, ∀ k : CubeFrequency d M,
            (M + 1 : ℝ) ^ d * ‖u k‖ ^ 2 ≤
              q ^ d * (P.size a : ℝ) ^ (2 * d) * ‖u‖ ^ 2) ∧
      (∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          ∀ a a', a ≠ a' → ∀ u ∈ P.cubeColumnSubspace M Y a,
            ∀ v ∈ P.cubeColumnSubspace M Y a',
              ‖⟪u, v⟫_ℂ‖ ≤ κ * ‖u‖ * ‖v‖) := by
  obtain ⟨c0, C0, hc0, hc01, hC0, hlocal, hrow, hcross⟩ :=
    angularClump_section_thresholds_with_row_bound n nstar hn hnstar hK hq hκ hpoly B b hb
  refine ⟨c0, C0, hc0, hc01, hC0, hlocal, ?_, ?_⟩
  · intro M A hM Y P hmax hgeom a u hu k
    apply cubeColumnSpace_row_bound_of_sections_with_constant (show 0 ≤ q by linarith) (P.multidimensionalNodes Y a) ?_ u hu k
    intro coord u' hu' l
    exact hrow (P.size a) M (P.size_pos a) (hmax.1 a) hM _ _
      (P.cube_projected_within Y hgeom a coord) u' hu' l
  · intro M A hM Y P hmax hgeom a a' haa u hu v hv
    let x := P.multidimensionalNodes Y a ⟨0, P.size_pos a⟩
    let y := P.multidimensionalNodes Y a' ⟨0, P.size_pos a'⟩
    have hsep : C0 / (M : ℝ) ≤ multidimensionalAngularTorusDistance y x := by
      apply hgeom.between
      rw [P.enumeration_label, P.enumeration_label]
      exact Ne.symm haa
    obtain ⟨q, hq⟩ := (le_multidimensionalAngularTorusDistance_iff hd y x (C0 / M)).1 hsep
    apply cubeColumnSpace_cross_bound_of_section (P.multidimensionalNodes Y a)
      (P.multidimensionalNodes Y a') q hκ.le ?_ u hu v hv
    intro u' hu' v' hv'
    apply hcross (P.size a) (P.size a') M (P.size_pos a) (hmax.1 a)
      (P.size_pos a') (hmax.1 a') hM _ _ (x q) (y q)
      (P.cube_projected_within Y hgeom a q) (P.cube_projected_within Y hgeom a' q) ?_ u' hu' v' hv'
    intro p
    have h := (le_angularTorusDistance_iff (y q) (x q) (C0 / M)).1 hq (-p)
    simpa only [Int.cast_neg, mul_neg, sub_eq_add_neg] using h


theorem cubeClump_analytic_thresholds_tight (d n nstar : ℕ) (hd : 1 ≤ d)
    (hn : 0 < n) (hnstar : 0 < nstar) (B b : ℕ → ℝ)
    (hb : ∀ s, 1 ≤ s → s ≤ nstar → 0 < b s) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      (∀ s, 1 ≤ s → s ≤ nstar → B s ≤ C0 ∧ c0 ≤ b s) ∧
      (∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          ∀ a, ∀ u ∈ P.cubeColumnSubspace M Y a, ∀ k : CubeFrequency d M,
            (M + 1 : ℝ) ^ d * ‖u k‖ ^ 2 ≤
              24 ^ d * (P.size a : ℝ) ^ (2 * d) * ‖u‖ ^ 2) ∧
      (∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          ∀ a a', a ≠ a' → ∀ u ∈ P.cubeColumnSubspace M Y a,
            ∀ v ∈ P.cubeColumnSubspace M Y a',
              ‖⟪u, v⟫_ℂ‖ ≤ (1 / (2 * (n : ℝ))) * ‖u‖ * ‖v‖) := by
  obtain ⟨c0, C0, hc0, hc01, hC0, hlocal, hrow, hcross⟩ :=
    angularClump_section_thresholds_tight n nstar hn hnstar B b hb
  refine ⟨c0, C0, hc0, hc01, hC0, hlocal, ?_, ?_⟩
  · intro M A hM Y P hmax hgeom a u hu k
    apply cubeColumnSpace_row_bound_of_sections_tight (P.multidimensionalNodes Y a) ?_ u hu k
    intro q u' hu' l
    exact hrow (P.size a) M (P.size_pos a) (hmax.1 a) hM _ _
      (P.cube_projected_within Y hgeom a q) u' hu' l
  · intro M A hM Y P hmax hgeom a a' haa u hu v hv
    let x := P.multidimensionalNodes Y a ⟨0, P.size_pos a⟩
    let y := P.multidimensionalNodes Y a' ⟨0, P.size_pos a'⟩
    have hsep : C0 / (M : ℝ) ≤ multidimensionalAngularTorusDistance y x := by
      apply hgeom.between
      rw [P.enumeration_label, P.enumeration_label]
      exact Ne.symm haa
    obtain ⟨q, hq⟩ := (le_multidimensionalAngularTorusDistance_iff hd y x (C0 / M)).1 hsep
    apply cubeColumnSpace_cross_bound_of_section (P.multidimensionalNodes Y a)
      (P.multidimensionalNodes Y a') q (by positivity) ?_ u hu v hv
    intro u' hu' v' hv'
    apply hcross (P.size a) (P.size a') M (P.size_pos a) (hmax.1 a)
      (P.size_pos a') (hmax.1 a') hM _ _ (x q) (y q)
      (P.cube_projected_within Y hgeom a q) (P.cube_projected_within Y hgeom a' q) ?_ u' hu' v' hv'
    intro p
    have h := (le_angularTorusDistance_iff (y q) (x q) (C0 / M)).1 hq (-p)
    simpa only [Int.cast_neg, mul_neg, sub_eq_add_neg] using h


/-- Gap-free deterministic leverage with the dimension-dependent absolute
constant `1024*512^(d-1)`. No rank, approximation or leverage assumption is
added to the geometric hypotheses. -/
theorem cubeClump_leverage_thresholds (d n nstar : ℕ) (hd : 1 ≤ d)
    (hnstar : 2 ≤ nstar) (hn : nstar ≤ n) (B b : ℕ → ℝ)
    (hb : ∀ s, 1 ≤ s → s ≤ nstar → 0 < b s) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      (∀ s, 1 ≤ s → s ≤ nstar → B s ≤ C0 ∧ c0 ≤ b s) ∧
      ∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          ∀ (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin n)),
            cubeFourierRowEnergy Y k (ofLp z) ≤
              (1024 * 512 ^ (d - 1) * (P.sizePowerSum d : ℝ)) *
                FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
  have hn0 : 0 < n := by omega
  obtain ⟨c0, C0, hc0, hc01, hC0, hlocal, hrow, hcross⟩ :=
    cubeClump_analytic_thresholds d n nstar hd hn0 (by omega) B b hb
  refine ⟨c0, C0, hc0, hc01, hC0, hlocal, ?_⟩
  intro M A hM Y P hmax hgeom k z
  apply cubeClump_leverage_of_signal_bounds hd P Y z
    (fun a l => hrow M A hM Y P hmax hgeom a _ (P.cubeSignal_mem_columnSubspace M Y z a) l)
  have henergy := (clump_sum_half_energy hn0 P.clump_count_le (P.cubeSignal M Y z)
    (fun a a' haa => hcross M A hM Y P hmax hgeom a a' haa
      _ (P.cubeSignal_mem_columnSubspace M Y z a) _ (P.cubeSignal_mem_columnSubspace M Y z a'))).1
  simpa only [P.sum_cubeSignals] using henergy

/-- The same geometric thresholds provide both improved leverage and the
half-energy decomposition used in the full-cube spectral lower bound. -/
theorem cubeClump_leverage_energy_thresholds_tight (d n nstar : ℕ) (hd : 1 ≤ d)
    (hnstar : 2 ≤ nstar) (hn : nstar ≤ n) (B b : ℕ → ℝ)
    (hb : ∀ s, 1 ≤ s → s ≤ nstar → 0 < b s) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      (∀ s, 1 ≤ s → s ≤ nstar → B s ≤ C0 ∧ c0 ≤ b s) ∧
      ∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          (∀ (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin n)),
            cubeFourierRowEnergy Y k (ofLp z) ≤
              (multidimensionalMultiClumpTightLeverageConstant d * (P.sizePowerSum d : ℝ)) *
                FiniteMatrixSampling.quadratic (cubeFullGram M Y) z) ∧
          (∀ z : EuclideanSpace ℂ (Fin n),
            (1 / 2 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
              ‖cubeFourierSignal M Y (ofLp z)‖^2) := by
  have hn0 : 0 < n := by omega
  obtain ⟨c0, C0, hc0, hc01, hC0, hlocal, hrow, hcross⟩ :=
    cubeClump_analytic_thresholds_tight d n nstar hd hn0 (by omega) B b hb
  refine ⟨c0, C0, hc0, hc01, hC0, hlocal, ?_⟩
  intro M A hM Y P hmax hgeom
  have henergy (z : EuclideanSpace ℂ (Fin n)) :
      (1 / 2 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖^2 := by
    have h := (clump_sum_half_energy hn0 P.clump_count_le (P.cubeSignal M Y z)
      (fun a a' haa => hcross M A hM Y P hmax hgeom a a' haa
        _ (P.cubeSignal_mem_columnSubspace M Y z a)
        _ (P.cubeSignal_mem_columnSubspace M Y z a'))).1
    simpa only [P.sum_cubeSignals] using h
  refine ⟨?_, henergy⟩
  intro k z
  exact cubeClump_leverage_of_signal_bounds_tight hd P Y z
    (fun a l => hrow M A hM Y P hmax hgeom a _ (P.cubeSignal_mem_columnSubspace M Y z a) l)
    (henergy z) k

/-- All prescribed positive losses are absorbed into the geometry
thresholds, independently of the bandwidth and the source locations. -/
theorem cubeClump_leverage_energy_thresholds_with_row_bound
    (d n nstar : ℕ) (hd : 1 ≤ d) (hnstar : 2 ≤ nstar) (hn : nstar ≤ n)
    {K q γ : ℝ} (hK : 1 ≤ K) (hq : K < q) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hpoly : ∀ (s : ℕ), 0 < s → s ≤ nstar → ∀ (a : Fin s → ℂ) (x : ℝ),
      x ∈ Icc (0 : ℝ) 1 →
      ‖PolynomialEvaluationBounds.jetPolynomialSignal a x‖^2 ≤ K * (s : ℝ)^2 *
        (∫ t in (0 : ℝ)..1, ‖PolynomialEvaluationBounds.jetPolynomialSignal a t‖^2))
    (B b : ℕ → ℝ) (hb : ∀ s, 1 ≤ s → s ≤ nstar → 0 < b s) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      (∀ s, 1 ≤ s → s ≤ nstar → B s ≤ C0 ∧ c0 ≤ b s) ∧
      ∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          (∀ (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin n)),
            cubeFourierRowEnergy Y k (ofLp z) ≤
              (q^d / γ * (P.sizePowerSum d : ℝ)) *
                FiniteMatrixSampling.quadratic (cubeFullGram M Y) z) ∧
          (∀ z : EuclideanSpace ℂ (Fin n),
            γ * (∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
              ‖cubeFourierSignal M Y (ofLp z)‖^2) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let κ : ℝ := (1 - γ) / n
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨c0, C0, hc0, hc01, hC0, hlocal, hrow, hcross⟩ :=
    cubeClump_analytic_thresholds_with_row_bound d n nstar hd hn0 (by omega)
      hK hq hκ hpoly B b hb
  refine ⟨c0, C0, hc0, hc01, hC0, hlocal, ?_⟩
  intro M A hM Y P hmax hgeom
  have henergy (z : EuclideanSpace ℂ (Fin n)) :
      γ * (∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖^2 := by
    have h := (clump_sum_energy_bounds (P.cubeSignal M Y z) hκ.le
      (fun a a' haa => hcross M A hM Y P hmax hgeom a a' haa
        _ (P.cubeSignal_mem_columnSubspace M Y z a)
        _ (P.cubeSignal_mem_columnSubspace M Y z a'))).1
    have hAn : (A : ℝ) ≤ n := by exact_mod_cast P.clump_count_le
    have hcoef : κ * (A - 1 : ℝ) ≤ 1 - γ := by
      have ht := mul_le_mul_of_nonneg_left (show (A : ℝ) - 1 ≤ n by linarith) hκ.le
      have he : κ * (n : ℝ) = 1 - γ := by dsimp [κ]; field_simp
      nlinarith only [ht, he]
    have hsum : 0 ≤ ∑ a, ‖P.cubeSignal M Y z a‖^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have ht := mul_le_mul_of_nonneg_right hcoef hsum
    rw [P.sum_cubeSignals] at h
    nlinarith only [h, ht]
  refine ⟨?_, henergy⟩
  intro k z
  exact cubeClump_leverage_of_signal_bounds_with_energy (show 0 ≤ q by linarith) hγ P Y z
    (fun a l => hrow M A hM Y P hmax hgeom a _ (P.cubeSignal_mem_columnSubspace M Y z a) l)
    (henergy z) k

open QuantitativeClumpSectionBounds

/-- Explicit width, bandwidth, and separation are selected independently.
The attained maximal clump size controls the number of other clumps. -/
theorem cubeClump_quantitative_pair_leverage_energy_of_polynomial_correlation
    (d n nstar : ℕ) (hd : 1 ≤ d) (hnstar : 2 ≤ nstar) (hsize : nstar ≤ n)
    (hcorrelation : ∀ (s t M : ℕ), 0 < s → s ≤ nstar → 0 < t → t ≤ nstar →
      0 < M → PolynomialEnergyCorrelationBound s t M nstar) :
    let hnstar0 : 0 < nstar := by omega
    let c0 := quantitativeClumpRadius d (n - nstar) nstar hnstar0
    let C0 := quantitativeClumpBandwidth d n nstar hnstar0
    let Csep := quantitativeClumpPairSeparation d n nstar hnstar0
    0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧ 16 * (nstar : ℝ) ≤ C0 ∧
      ∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 Csep Y P →
          (∀ (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin n)),
            cubeFourierRowEnergy Y k (ofLp z) ≤
              ((3 / 2 : ℝ) * (P.sizePowerSum d : ℝ)) *
                FiniteMatrixSampling.quadratic (cubeFullGram M Y) z) ∧
          (∀ z : EuclideanSpace ℂ (Fin n),
            (3 / 4 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
              ‖cubeFourierSignal M Y (ofLp z)‖^2) := by
  classical
  dsimp only
  have hnstar0 : 0 < nstar := by omega
  have hn : 0 < n := by omega
  let c0 := quantitativeClumpRadius d (n - nstar) nstar hnstar0
  let C0 := quantitativeClumpBandwidth d n nstar hnstar0
  let Csep := quantitativeClumpPairSeparation d n nstar hnstar0
  have hc0 : 0 < c0 := quantitativeClumpRadius_pos hd hnstar0
  have hc01 : c0 < 1 := explicitSectionRadius_lt_one hnstar0 _
  have hC0 : (n : ℝ) ≤ C0 := quantitativeClumpBandwidth_ge_total hnstar0
  have hC016 : 16 * (nstar : ℝ) ≤ C0 := quantitativeClumpBandwidth_ge_spectral hnstar0
  refine ⟨hc0, hc01, hC0, hC016, ?_⟩
  intro M A hM Y P hmax hgeom
  have hMR : 0 < (M : ℝ) :=
    (by exact_mod_cast hn : (0 : ℝ) < n).trans_le (hC0.trans hM)
  have hMN : 0 < M := by exact_mod_cast hMR
  have hq : 0 ≤ sectionRowConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans (sectionRowConstant_gt_one hd).le
  have hrow (a : Fin A) (u : EuclideanSpace ℂ (CubeFrequency d M))
      (hu : u ∈ P.cubeColumnSubspace M Y a) (k : CubeFrequency d M) :
      (M + 1 : ℝ)^d * ‖u k‖^2 ≤
        (sectionRowConstant d)^d * (P.size a : ℝ)^(2*d) * ‖u‖^2 := by
    apply cubeColumnSpace_row_bound_of_sections_with_constant hq (P.multidimensionalNodes Y a) ?_ u hu k
    intro coord u' hu' l
    have hr := explicitSectionRadius_le hnstar0 (sectionJetRadius d (n - nstar)) (P.size_pos a) (hmax.1 a)
    exact (angularClump_explicit_section_bounds hd (P.size_pos a) hMN
      ((quantitativeClumpBandwidth_ge_grid hnstar0 (P.size_pos a) (hmax.1 a)).trans hM)
      _ _ ((P.cube_projected_within Y hgeom a coord).mono hMN hr) u' hu').1 l
  have hκ : 0 ≤ sectionCorrelationConstant (n - nstar) := by unfold sectionCorrelationConstant; positivity
  have hcross (a a' : Fin A) (haa : a ≠ a')
      (u : EuclideanSpace ℂ (CubeFrequency d M)) (hu : u ∈ P.cubeColumnSubspace M Y a)
      (v : EuclideanSpace ℂ (CubeFrequency d M)) (hv : v ∈ P.cubeColumnSubspace M Y a') :
      ‖⟪u, v⟫_ℂ‖ ≤ sectionCorrelationConstant (n - nstar) * ‖u‖ * ‖v‖ := by
    by_cases heq : n = nstar
    · have hA := hasMaxClumpSize_clumpCount_eq_one_of_total_eq_max hmax heq
      have hab : a = a' := Fin.ext (by have ha := a.isLt; have ha' := a'.isLt; omega)
      exact False.elim (haa hab)
    · have hless : nstar < n := by omega
      let x := P.multidimensionalNodes Y a ⟨0, P.size_pos a⟩
      let y := P.multidimensionalNodes Y a' ⟨0, P.size_pos a'⟩
      have hsep : Csep / (M : ℝ) ≤ multidimensionalAngularTorusDistance y x := by
        apply hgeom.between
        rw [P.enumeration_label, P.enumeration_label]
        exact Ne.symm haa
      obtain ⟨coord, hcoord⟩ := (le_multidimensionalAngularTorusDistance_iff hd y x (Csep / M)).1 hsep
      apply cubeColumnSpace_cross_bound_of_section (P.multidimensionalNodes Y a)
        (P.multidimensionalNodes Y a') coord hκ ?_ u hu v hv
      intro u' hu' v' hv'
      apply angularClump_explicit_cross_bound hd hnstar0 hless (P.size_pos a) (hmax.1 a)
        (P.size_pos a') (hmax.1 a') hM
        (hcorrelation _ _ _ (P.size_pos a) (hmax.1 a) (P.size_pos a') (hmax.1 a') hMN)
        _ _ (x coord) (y coord)
        (P.cube_projected_within Y hgeom a coord)
        (P.cube_projected_within Y hgeom a' coord) ?_ u' hu' v' hv'
      intro p
      have h := (le_angularTorusDistance_iff (y coord) (x coord) (Csep / M)).1 hcoord (-p)
      simpa only [Int.cast_neg, mul_neg, sub_eq_add_neg] using h
  have henergy (z : EuclideanSpace ℂ (Fin n)) :
      (3 / 4 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
        ‖cubeFourierSignal M Y (ofLp z)‖^2 := by
    have h := (clump_sum_energy_bounds (P.cubeSignal M Y z) hκ
      (fun a a' haa => hcross a a' haa _ (P.cubeSignal_mem_columnSubspace M Y z a)
        _ (P.cubeSignal_mem_columnSubspace M Y z a'))).1
    have hcoef : sectionCorrelationConstant (n - nstar) * ((A : ℝ) - 1) ≤ 1 / 4 := by
      by_cases heq : n = nstar
      · simp [heq, sectionCorrelationConstant]
      · have hh : 0 < n - nstar := by omega
        have hhR : (0 : ℝ) < (n - nstar : ℕ) := by exact_mod_cast hh
        have hcount : (A : ℝ) - 1 ≤ (n - nstar : ℕ) := by
          obtain ⟨a, _⟩ := hmax.2
          have hA : 1 ≤ A := by have ha := a.isLt; omega
          exact_mod_cast (show A - 1 ≤ n - nstar from hasMaxClumpSize_clumpCount_sub_one_le hmax)
        have ht := mul_le_mul_of_nonneg_left hcount hκ
        have he : sectionCorrelationConstant (n - nstar) * (n - nstar : ℕ) = 1 / 4 := by
          unfold sectionCorrelationConstant
          field_simp
        exact ht.trans_eq he
    have hsum : 0 ≤ ∑ a, ‖P.cubeSignal M Y z a‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have ht := mul_le_mul_of_nonneg_right hcoef hsum
    rw [P.sum_cubeSignals] at h
    nlinarith only [h, ht]
  refine ⟨?_, henergy⟩
  intro k z
  have hraw := cubeClump_leverage_of_signal_bounds_with_energy hq (by norm_num : (0 : ℝ) < 3 / 4)
    P Y z (fun a l => hrow a _ (P.cubeSignal_mem_columnSubspace M Y z a) l) (henergy z) k
  have hQ : 0 ≤ FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
    rw [← cubeFourierSignal_average_energy]
    positivity
  have ht := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sectionRowConstant_leverage_le hd) (Nat.cast_nonneg (P.sizePowerSum d))) hQ
  exact hraw.trans ht

/-- The smaller of the pairwise and weighted global separation thresholds
preserves the absolute sampling coefficient three. -/
theorem cubeClump_quantitative_leverage_energy
    (d n nstar : ℕ) (hd : 1 ≤ d) (hnstar : 2 ≤ nstar) (hsize : nstar ≤ n) :
    let hnstar0 : 0 < nstar := by omega
    let c0 := quantitativeClumpRadius d (n - nstar) nstar hnstar0
    let C0 := quantitativeClumpBandwidth d n nstar hnstar0
    let Csep := quantitativeClumpSeparation d n nstar hnstar0
    0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧ 16 * (nstar : ℝ) ≤ C0 ∧
      ∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultidimensionalMultiClumpGeometry M c0 Csep Y P →
          (∀ (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin n)),
            cubeFourierRowEnergy Y k (ofLp z) ≤
              ((3 / 2 : ℝ) * (P.sizePowerSum d : ℝ)) *
                FiniteMatrixSampling.quadratic (cubeFullGram M Y) z) ∧
          (∀ z : EuclideanSpace ℂ (Fin n),
            (3 / 4 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
              ‖cubeFourierSignal M Y (ofLp z)‖^2) := by
  classical
  dsimp only
  have hnstar0 : 0 < nstar := by omega
  have hn : 0 < n := by omega
  let c0 := quantitativeClumpRadius d (n - nstar) nstar hnstar0
  let C0 := quantitativeClumpBandwidth d n nstar hnstar0
  let S := quantitativeClumpGlobalSeparation d n nstar hnstar0
  have hpairAPI := cubeClump_quantitative_pair_leverage_energy_of_polynomial_correlation d n nstar hd hnstar hsize
    (fun s t M hs hsn ht htn hM c c' x y η hη hsep =>
      PolynomialCrossCorrelation.inner_modulatedPolynomial_norm_le_of_energy hs ht hM hsn htn c c' x y η hη hsep)
  obtain ⟨hc0, hc01, hC0, hC016, hcontrolPair⟩ := hpairAPI
  refine ⟨hc0, hc01, hC0, hC016, ?_⟩
  intro M A hM Y P hmax hgeom
  by_cases hpair : quantitativeClumpPairSeparation d n nstar hnstar0 ≤ S
  · apply hcontrolPair M A hM Y P hmax
    change MultidimensionalMultiClumpGeometry M c0
      (min (quantitativeClumpPairSeparation d n nstar hnstar0) S) Y P at hgeom
    rwa [min_eq_left hpair] at hgeom
  · have hless : nstar < n := by
      by_contra hnot
      have heq : n = nstar := by omega
      simp [S, quantitativeClumpPairSeparation, quantitativeClumpGlobalSeparation, heq] at hpair
    have hgeomS : MultidimensionalMultiClumpGeometry M c0 S Y P := by
      change MultidimensionalMultiClumpGeometry M c0
        (min (quantitativeClumpPairSeparation d n nstar hnstar0) S) Y P at hgeom
      rwa [min_eq_right (le_of_not_ge hpair)] at hgeom
    have hS : 0 < S := quantitativeClumpGlobalSeparation_pos hd hnstar0 hless
    have hMR : 0 < (M : ℝ) :=
      (by exact_mod_cast hn : (0 : ℝ) < n).trans_le (hC0.trans hM)
    have hMN : 0 < M := by exact_mod_cast hMR
    let H := maximumPolynomialEnergyConstant d (n - nstar) nstar hnstar0
    let Δ := maximumApproximationError d (n - nstar) nstar hnstar0
    let α := Real.pi * H^2 / S
    let β := 2 * Δ + Δ^2
    have hα : 0 ≤ α := by dsimp [α]; positivity
    have hΔ : 0 ≤ Δ := (maximumApproximationError_bounds hd (by omega) hnstar0).1
    have hβ : 0 ≤ β := by dsimp [β]; positivity
    have hq : 0 ≤ sectionRowConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans (sectionRowConstant_gt_one hd).le
    have hrow (a : Fin A) (u : EuclideanSpace ℂ (CubeFrequency d M))
        (hu : u ∈ P.cubeColumnSubspace M Y a) (k : CubeFrequency d M) :
        (M + 1 : ℝ)^d * ‖u k‖^2 ≤
          (sectionRowConstant d)^d * (P.size a : ℝ)^(2*d) * ‖u‖^2 := by
      apply cubeColumnSpace_row_bound_of_sections_with_constant hq (P.multidimensionalNodes Y a) ?_ u hu k
      intro coord u' hu' l
      have hr := explicitSectionRadius_le hnstar0 (sectionJetRadius d (n - nstar)) (P.size_pos a) (hmax.1 a)
      exact (angularClump_explicit_section_bounds hd (P.size_pos a) hMN
        ((quantitativeClumpBandwidth_ge_grid hnstar0 (P.size_pos a) (hmax.1 a)).trans hM)
        _ _ ((P.cube_projected_within Y hgeomS a coord).mono hMN hr) u' hu').1 l
    have hcross (a a' : Fin A) (haa : a ≠ a')
        (u : EuclideanSpace ℂ (CubeFrequency d M)) (hu : u ∈ P.cubeColumnSubspace M Y a)
        (v : EuclideanSpace ℂ (CubeFrequency d M)) (hv : v ∈ P.cubeColumnSubspace M Y a') :
        ‖⟪u, v⟫_ℂ‖ ≤
          (α * ((P.size a : ℝ) * (P.size a' : ℝ) +
            ((P.size a : ℝ)^2 + (P.size a' : ℝ)^2) / 2) + β) * ‖u‖ * ‖v‖ := by
      let x := P.multidimensionalNodes Y a ⟨0, P.size_pos a⟩
      let y := P.multidimensionalNodes Y a' ⟨0, P.size_pos a'⟩
      have hsep : S / (M : ℝ) ≤ multidimensionalAngularTorusDistance y x := by
        apply hgeomS.between
        rw [P.enumeration_label, P.enumeration_label]
        exact Ne.symm haa
      obtain ⟨coord, hcoord⟩ := (le_multidimensionalAngularTorusDistance_iff hd y x (S / M)).1 hsep
      have hcoef : 0 ≤ α * ((P.size a : ℝ) * (P.size a' : ℝ) +
          ((P.size a : ℝ)^2 + (P.size a' : ℝ)^2) / 2) + β := by positivity
      apply cubeColumnSpace_cross_bound_of_section (P.multidimensionalNodes Y a)
        (P.multidimensionalNodes Y a') coord hcoef ?_ u hu v hv
      intro u' hu' v' hv'
      have hpolyCorr : PolynomialSizeEnergyCorrelationBound (P.size a) (P.size a') M :=
        fun c c' x y η hη hsep =>
          PolynomialCrossCorrelation.inner_modulatedPolynomial_norm_le_of_size_energy
            (P.size_pos a) (P.size_pos a') hMN c c' x y η hη hsep
      have hsepCoord : ∀ p : ℤ, S / (M : ℝ) ≤ |y coord - x coord - 2 * Real.pi * p| := by
        intro p
        have h := (le_angularTorusDistance_iff (y coord) (x coord) (S / M)).1 hcoord (-p)
        simpa only [Int.cast_neg, mul_neg, sub_eq_add_neg] using h
      have h := angularClump_explicit_size_cross_bound hd hnstar0 hless (P.size_pos a) (hmax.1 a)
        (P.size_pos a') (hmax.1 a') hM hpolyCorr _ _ (x coord) (y coord) S hS
        (P.cube_projected_within Y hgeomS a coord)
        (P.cube_projected_within Y hgeomS a' coord) hsepCoord u' hu' v' hv'
      simpa only [α, β, H, Δ, add_assoc] using h
    have henergy (z : EuclideanSpace ℂ (Fin n)) :
        (3 / 4 : ℝ) * (∑ a, ‖P.cubeSignal M Y z a‖^2) ≤
          ‖cubeFourierSignal M Y (ofLp z)‖^2 := by
      have h := WeightedClumpCrossBounds.sizeWeighted_clump_sum_energy_lower
        (P.cubeSignal M Y z) (fun a => (P.size a : ℝ)) (fun a => Nat.cast_nonneg _)
        hα hβ (fun a a' haa => hcross a a' haa _ (P.cubeSignal_mem_columnSubspace M Y z a)
          _ (P.cubeSignal_mem_columnSubspace M Y z a'))
      have hmoment : (∑ a : Fin A, (P.size a : ℝ)^2) +
          Real.sqrt ((A : ℝ) * ∑ a : Fin A, (P.size a : ℝ)^4) ≤
          quantitativeClumpGlobalMomentConstant n nstar := by
        simpa only [quantitativeClumpGlobalMomentConstant, Nat.cast_add, Nat.cast_sub hsize, Nat.cast_one] using
          P.real_globalMomentCoefficient_le hmax
      have hcount : (A : ℝ) - 1 ≤ (n - nstar : ℕ) := by
        have hcount := hasMaxClumpSize_clumpCount_le_sub_add_one_real hmax
        rw [Nat.cast_sub hsize]
        linarith only [hcount]
      have hbudget : α * quantitativeClumpGlobalMomentConstant n nstar + β * ((n - nstar : ℕ) : ℝ) = 1 / 4 :=
        quantitativeClumpGlobalSeparation_budget hd hnstar0 hless
      have h₁ := mul_le_mul_of_nonneg_left hmoment hα
      have h₂ := mul_le_mul_of_nonneg_left hcount hβ
      have hcoef : (3 / 4 : ℝ) ≤ 1 - α * ((∑ a : Fin A, (P.size a : ℝ)^2) +
          Real.sqrt ((A : ℝ) * ∑ a : Fin A, (P.size a : ℝ)^4)) - β * ((A : ℝ) - 1) := by
        nlinarith only [hbudget, h₁, h₂]
      rw [P.sum_cubeSignals] at h
      exact (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans h
    refine ⟨?_, henergy⟩
    intro k z
    have hraw := cubeClump_leverage_of_signal_bounds_with_energy hq (by norm_num : (0 : ℝ) < 3 / 4)
      P Y z (fun a l => hrow a _ (P.cubeSignal_mem_columnSubspace M Y z a) l) (henergy z) k
    have hQ : 0 ≤ FiniteMatrixSampling.quadratic (cubeFullGram M Y) z := by
      rw [← cubeFourierSignal_average_energy]
      positivity
    have ht := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sectionRowConstant_leverage_le hd) (Nat.cast_nonneg (P.sizePowerSum d))) hQ
    exact hraw.trans ht

end
end LeanNumDetect.RandSamp
