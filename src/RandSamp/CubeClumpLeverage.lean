import RandSamp.MultidimensionalMultiClumpModel
import General.Fourier.AngularClumpSectionBounds
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

end
end LeanNumDetect.RandSamp
