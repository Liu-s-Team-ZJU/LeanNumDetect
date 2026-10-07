import RandSamp.MultiClumpModel
import General.Fourier.ClusteredVandermonde
import General.Fourier.ClumpJetApproximation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Fintype.EquivFin

/-! Gap-free orthogonality of short Fourier clump subspaces.

The companion evolution converges uniformly to a polynomial jet basis as a
clump contracts, even through frequency collisions. A weighted geometric
sum bound then controls cross-clump polynomial signals, and a relative
perturbation estimate transfers the bound to the actual column spaces.
Every step is proved; no original principal-angle estimate is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace
open Matrix WithLp Set

namespace LeanNumDetect.RandSamp
noncomputable section

/-- Canonical angular representative for comparing circle-distance conventions. -/
def canonicalAngle (x : ℝ) : ℝ := toIocMod Real.two_pi_pos (-Real.pi) x

theorem canonicalAngle_mem (x : ℝ) : canonicalAngle x ∈ Ioc (-Real.pi) Real.pi := by
  have h := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) x
  simpa only [canonicalAngle, show -Real.pi + 2 * Real.pi = Real.pi by ring] using h

theorem canonicalAngle_winding (x : ℝ) :
    ∃ p : ℤ, canonicalAngle x = x + 2 * Real.pi * p := by
  refine ⟨-toIocDiv Real.two_pi_pos (-Real.pi) x, ?_⟩
  simp only [canonicalAngle, toIocMod, zsmul_eq_mul, Int.cast_neg]
  ring

theorem angularTorusDistance_eq_abs_of_abs_le_pi {x : ℝ} (hx : |x| ≤ Real.pi) :
    angularTorusDistance x 0 = |x| := by
  apply le_antisymm
  · simpa using angularTorusDistance_le_winding x 0 0
  · apply (le_angularTorusDistance_iff _ _ _).2
    intro p
    by_cases hp : p = 0
    · simp [hp]
    · have hp1 : (1 : ℝ) ≤ |(p : ℝ)| := by
        have h : (1 : ℤ) ≤ |p| := Int.one_le_abs hp
        exact_mod_cast h
      have htriangle := abs_sub (x + 2 * Real.pi * p) x
      have he : x + 2 * Real.pi * p - x = 2 * Real.pi * p := by ring
      rw [he, abs_mul, abs_of_pos Real.two_pi_pos] at htriangle
      simp only [sub_zero]
      nlinarith [Real.pi_pos]

theorem angularTorusDistance_canonicalAngle (x y : ℝ) :
    angularTorusDistance (canonicalAngle x) (canonicalAngle y) = angularTorusDistance x y := by
  obtain ⟨p, hp⟩ := canonicalAngle_winding x
  obtain ⟨q, hq⟩ := canonicalAngle_winding y
  rw [hp, hq, angularTorusDistance_add_winding_left,
    angularTorusDistance_add_winding_right]

/-- The source's `arg(exp(i(x-y)))` distance is precisely the project's
nearest-winding angular distance, for arbitrary real lifts. -/
theorem source_angularDistance_eq (x y : ℝ) :
    ClusteredVandermonde.angularDistance x y = angularTorusDistance x y := by
  have hcan := canonicalAngle_mem (x - y)
  have habs : |canonicalAngle (x - y)| ≤ Real.pi :=
    abs_le.mpr ⟨hcan.1.le, hcan.2⟩
  have hw := angularTorusDistance_eq_abs_of_abs_le_pi habs
  have hdist : angularTorusDistance (canonicalAngle (x - y)) 0 =
      angularTorusDistance (x - y) 0 := by
    obtain ⟨p, hp⟩ := canonicalAngle_winding (x - y)
    rw [hp, angularTorusDistance_add_winding_left]
  rw [hdist] at hw
  have he : angularTorusDistance (x - y) 0 = angularTorusDistance x y := by
    simp [angularTorusDistance,
      MathExtras.NumberTheory.Analysis.LargeSieve.circleDist, sub_div]
  rw [he] at hw
  unfold ClusteredVandermonde.angularDistance
  rw [mul_comm Complex.I, Complex.arg_exp_mul_I]
  exact hw.symm

theorem fourierRow_canonicalAngle {s : ℕ} (Y : Fin s → ℝ) (k : ℕ) (j : Fin s) :
    fourierRow (fun i => canonicalAngle (Y i)) k j = fourierRow Y k j := by
  obtain ⟨p, hp⟩ := canonicalAngle_winding (Y j)
  unfold fourierRow
  change Complex.exp (Complex.I * (((k : ℝ) * canonicalAngle (Y j) : ℝ) : ℂ)) = _
  rw [hp]
  have he : Complex.I * (((k : ℝ) * (Y j + 2 * Real.pi * p) : ℝ) : ℂ) =
      Complex.I * (((k : ℝ) * Y j : ℝ) : ℂ) +
        (((k : ℤ) * p : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

namespace ClumpPartition
variable {n A : ℕ} (P : ClumpPartition n A)

/-- Enumerate a clump without altering its cardinality. -/
def enumeration (a : Fin A) : Fin (P.size a) ≃ P.members a :=
  (P.members a).equivFin.symm

/-- Original real lifts of the nodes in a single clump. -/
def nodes (Y : Fin n → ℝ) (a : Fin A) : Fin (P.size a) → ℝ :=
  fun j => Y (P.enumeration a j).val

/-- Actual Fourier column span of a clump. -/
def columnSubspace (M : ℕ) (Y : Fin n → ℝ) (a : Fin A) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (M + 1))) :=
  ClusteredVandermonde.clusterSubspace M (P.nodes Y a)

theorem enumeration_label (a : Fin A) (j : Fin (P.size a)) :
    P.label (P.enumeration a j).val = a :=
  (P.mem_members _ _).1 (P.enumeration a j).property

theorem canonical_nodes_injective (Y : Fin n → ℝ) (hd : DistinctAngularNodes Y)
    (a : Fin A) : Function.Injective (fun j => canonicalAngle (P.nodes Y a j)) := by
  intro i j hij
  change canonicalAngle (P.nodes Y a i) = canonicalAngle (P.nodes Y a j) at hij
  by_contra hne
  have hval : (P.enumeration a i).val ≠ (P.enumeration a j).val := by
    intro he
    exact hne ((P.enumeration a).injective (Subtype.ext he))
  have hpos := (distinctAngularNodes_iff_distance_pos Y).1 hd _ _ hval
  have hzero : angularTorusDistance (P.nodes Y a i) (P.nodes Y a j) = 0 := by
    rw [← angularTorusDistance_canonicalAngle, hij, angularTorusDistance_self]
  exact hpos.ne' hzero

theorem columnSubspace_canonicalAngle (M : ℕ) (Y : Fin n → ℝ) (a : Fin A) :
    ClusteredVandermonde.clusterSubspace M (fun j => canonicalAngle (P.nodes Y a j)) =
      P.columnSubspace M Y a := by
  unfold columnSubspace ClusteredVandermonde.clusterSubspace
  congr 1
  congr 1
  funext j
  congr 1
  funext k
  exact fourierRow_canonicalAngle (P.nodes Y a) k.val j

end ClumpPartition

/-- Convert a source principal-angle lower bound into a bound on every pair
of vectors in the actual cluster subspaces. -/
theorem inner_bound_of_principalAngle {N : ℕ}
    (U V : Submodule ℂ (EuclideanSpace ℂ (Fin (N + 1))))
    {ε : ℝ} (hε : 0 ≤ ε) (hεpi : ε ≤ Real.pi / 2)
    (hangle : Real.pi / 2 - ε ≤ ClusteredVandermonde.minimalPrincipalAngle U V)
    (u v : EuclideanSpace ℂ (Fin (N + 1))) (hu : u ∈ U) (hv : v ∈ V) :
    ‖⟪u, v⟫_ℂ‖ ≤ ε * ‖u‖ * ‖v‖ := by
  by_cases hu0 : u = 0
  · simp [hu0]
  by_cases hv0 : v = 0
  · simp [hv0]
  have hn : 0 < ‖u‖ * ‖v‖ := mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hv0)
  have hratio0 : 0 ≤ ‖⟪u, v⟫_ℂ‖ / (‖u‖ * ‖v‖) := div_nonneg (norm_nonneg _) hn.le
  have hratio1 : ‖⟪u, v⟫_ℂ‖ / (‖u‖ * ‖v‖) ≤ 1 :=
    (div_le_one hn).2 (norm_inner_le_norm u v)
  have hb : BddBelow {a : ℝ | ∃ u ∈ U, ∃ v ∈ V, u ≠ 0 ∧ v ≠ 0 ∧
      a = Real.arccos (‖⟪u, v⟫_ℂ‖ / (‖u‖ * ‖v‖))} := by
    refine ⟨0, ?_⟩
    rintro a ⟨u, _, v, _, _, _, rfl⟩
    exact Real.arccos_nonneg _
  have hle : ClusteredVandermonde.minimalPrincipalAngle U V ≤
      Real.arccos (‖⟪u, v⟫_ℂ‖ / (‖u‖ * ‖v‖)) :=
    csInf_le hb ⟨u, hu, v, hv, hu0, hv0, rfl⟩
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ Real.pi / 2 - ε)
    (Real.arccos_le_pi _) (hangle.trans hle)
  rw [Real.cos_arccos (by linarith) hratio1, Real.cos_pi_div_two_sub] at hc
  have hratio := hc.trans (Real.sin_le hε)
  have hmul := (div_le_iff₀ hn).1 hratio
  simpa only [mul_assoc] using hmul

/-- A short angular clump admits a polynomial approximation whose relative
error and coefficient norm are controlled uniformly through collisions. -/
theorem shortClump_polynomial_approximation {s M : ℕ} (hs : 0 < s) (hM : 0 < M)
    (Y : Fin s → ℝ) (center r D ε : ℝ) (hr : 0 ≤ r) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hclose : ∀ frequency : Fin s → ℂ, ‖frequency‖ ≤ r →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : Fin s,
        ‖NormedSpace.exp ((t : ℂ) • ExponentialCompanion.generator frequency) ⟨0, hs⟩ j -
          (t : ℂ) ^ j.val / (j.val.factorial : ℂ)‖ ≤ ε)
    (hjet : ∀ frequency jet : Fin s → ℂ, ‖frequency‖ ≤ r →
      ‖jet‖ ≤ D / Real.sqrt (M + 1 : ℝ) *
        ‖ClumpJetApproximation.evolutionVector hs M frequency jet 0‖)
    (hwithin : ∀ j, angularTorusDistance (Y j) center ≤ r / M)
    (u : EuclideanSpace ℂ (Fin (M + 1)))
    (hu : u ∈ ClusteredVandermonde.clusterSubspace M Y) :
    ∃ c : Fin s → ℂ,
      ‖u - PolynomialCrossCorrelation.modulatedPolynomial M center c‖ ≤
        ((s : ℝ) * ε * D) * ‖u‖ ∧
      (∑ j, ‖c j‖) ≤ ((s : ℝ) * D / Real.sqrt (M + 1 : ℝ)) * ‖u‖ := by
  classical
  obtain ⟨coefficient, rfl⟩ :=
    ClumpJetApproximation.clusterSubspace_coefficient_representation Y u hu
  choose p hp using fun j => (angularTorusDistance_le_iff (Y j) center (r / M)).1 (hwithin j)
  let frequency : Fin s → ℂ := fun j =>
    Complex.I * (((M : ℝ) * (Y j - center + 2 * Real.pi * p j) : ℝ) : ℂ)
  let jet := ExponentialCompanion.initialJet frequency coefficient
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hfrequency : ‖frequency‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg hr).2
    intro j
    simp only [frequency, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos hMR]
    simpa only [mul_comm] using (le_div_iff₀ hMR).1 (hp j)
  have heq := ClumpJetApproximation.angularSignal_eq_evolutionVector hs hM Y coefficient center p
  change ClumpJetApproximation.angularSignal M Y coefficient =
    ClumpJetApproximation.evolutionVector hs M frequency jet center at heq
  have hjet' : ‖jet‖ ≤ D / Real.sqrt (M + 1 : ℝ) *
      ‖ClumpJetApproximation.angularSignal M Y coefficient‖ := by
    rw [heq, ClumpJetApproximation.evolutionVector_norm_eq hs]
    exact hjet frequency jet hfrequency
  have hsqrt : 0 < Real.sqrt (M + 1 : ℝ) := by positivity
  refine ⟨ClumpJetApproximation.jetCoefficient jet, ?_, ?_⟩
  · rw [heq]
    have herr := ClumpJetApproximation.evolutionVector_polynomial_approximation
      hs hM frequency jet center ε hε (hclose frequency hfrequency)
    have hnorm : ‖jet‖ ≤ D / Real.sqrt (M + 1 : ℝ) *
        ‖ClumpJetApproximation.evolutionVector hs M frequency jet center‖ := by
      rwa [heq] at hjet'
    calc
      _ ≤ Real.sqrt (M + 1 : ℝ) * ((s : ℝ) * ε * ‖jet‖) := herr
      _ ≤ Real.sqrt (M + 1 : ℝ) * ((s : ℝ) * ε *
          (D / Real.sqrt (M + 1 : ℝ) *
            ‖ClumpJetApproximation.evolutionVector hs M frequency jet center‖)) := by
        gcongr
      _ = _ := by field_simp
  · exact (ClumpJetApproximation.jetCoefficient_sum_norm_le jet).trans
      ((mul_le_mul_of_nonneg_left hjet' (Nat.cast_nonneg s)).trans_eq (by ring))

/-- For a prescribed relative error, all sufficiently short clumps of one
fixed cardinality admit uniform polynomial approximation constants. -/
theorem exists_shortClump_polynomial_bounds (s : ℕ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r Q L : ℝ, 0 < r ∧ 0 < Q ∧ 0 < L ∧
      ∀ (M : ℕ), Q ≤ (M : ℝ) → 0 < M →
        ∀ (Y : Fin s → ℝ) (center : ℝ),
          (∀ j, angularTorusDistance (Y j) center ≤ r / M) →
          ∀ u ∈ ClusteredVandermonde.clusterSubspace M Y,
            ∃ c : Fin s → ℂ,
              ‖u - PolynomialCrossCorrelation.modulatedPolynomial M center c‖ ≤ ε * ‖u‖ ∧
              (∑ j, ‖c j‖) ≤ L / Real.sqrt (M + 1 : ℝ) * ‖u‖ := by
  obtain ⟨η, Q, D, hη, hQ, hD, hjet⟩ :=
    ClumpJetApproximation.exists_evolutionVector_jet_bounds hs
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  obtain ⟨r, hr, hclose⟩ := ExponentialCompanion.exists_uniform_jet_radius hs
    (ε / ((s : ℝ) * D)) (by positivity)
  refine ⟨min r η, Q, (s : ℝ) * D, lt_min hr hη, hQ, by positivity, ?_⟩
  intro M hsize hM Y center hwithin u hu
  obtain ⟨c, herr, hcoeff⟩ := shortClump_polynomial_approximation hs hM Y center
    (min r η) D (ε / ((s : ℝ) * D)) (le_of_lt (lt_min hr hη)) hD.le
    (by positivity)
    (fun frequency hf => hclose frequency (hf.trans (min_le_left _ _)))
    (fun frequency jet hf => hjet M hsize hM frequency jet (hf.trans (min_le_right _ _)))
    hwithin u hu
  refine ⟨c, ?_, hcoeff⟩
  convert herr using 1
  field_simp

/-- A single pair of geometric thresholds works for every clump cardinality
up to `nstar`.  Additional positive shortness bounds and arbitrary frequency
thresholds can be included before choosing these constants. -/
theorem multiClump_subspace_thresholds
    (n nstar : ℕ) (hnstar : 2 ≤ nstar) (hn : nstar ≤ n)
    (B b : ℕ → ℝ) (hb : ∀ s, 1 ≤ s → s ≤ nstar → 0 < b s) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      (∀ s, 1 ≤ s → s ≤ nstar → B s ≤ C0 ∧ c0 ≤ b s) ∧
      ∀ (M A : ℕ), C0 ≤ (M : ℝ) →
        ∀ (Y : Fin n → ℝ) (P : ClumpPartition n A),
          HasMaxClumpSize P nstar → MultiClumpGeometry M c0 C0 Y P →
          ∀ (a a' : Fin A), a ≠ a' →
            ∀ u ∈ P.columnSubspace M Y a, ∀ v ∈ P.columnSubspace M Y a',
              ‖⟪u, v⟫_ℂ‖ ≤ (1 / (2 * (n : ℝ))) * ‖u‖ * ‖v‖ := by
  classical
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  let ε : ℝ := 1 / (32 * (n : ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  choose r Q D hr hQ hD happrox using
    fun i : Fin nstar => exists_shortClump_polynomial_bounds (i.val + 1) (by omega) ε hε
  let f : Fin nstar → ℝ := fun i => max 1 (max (D i) (max |Q i|
    (max |B (i.val + 1)| (max (r i)⁻¹ (b (i.val + 1))⁻¹))))
  obtain ⟨L, hL⟩ := (Set.finite_range f).bddAbove
  have hbounds (i : Fin nstar) :
      1 ≤ L ∧ D i ≤ L ∧ |Q i| ≤ L ∧ |B (i.val + 1)| ≤ L ∧
        (r i)⁻¹ ≤ L ∧ (b (i.val + 1))⁻¹ ≤ L := by
    have h := hL (Set.mem_range_self i)
    simpa only [f, max_le_iff] using h
  let izero : Fin nstar := ⟨0, by omega⟩
  have hL1 : 1 ≤ L := (hbounds izero).1
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  let T : ℝ := max (n : ℝ) (max L (64 * (n : ℝ) * Real.pi * L ^ 2))
  have hnT : (n : ℝ) ≤ T := le_max_left _ _
  have hLT : L ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hcrossT : 64 * (n : ℝ) * Real.pi * L ^ 2 ≤ T :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hT0 : 0 < T := hL0.trans_le hLT
  have hT1 : 1 ≤ T := hL1.trans hLT
  have hsmall : 1 / (2 * T) ≤ 1 / L := by
    apply one_div_le_one_div_of_le hL0
    linarith
  have hinv (x : ℝ) (hx : 0 < x) (h : x⁻¹ ≤ L) : 1 / L ≤ x := by
    apply (div_le_iff₀ hL0).2
    have hh := mul_le_mul_of_nonneg_left h hx.le
    simpa only [mul_inv_cancel₀ hx.ne', mul_comm x L] using hh
  have hshort (i : Fin nstar) : 1 / (2 * T) ≤ r i :=
    hsmall.trans (hinv (r i) (hr i) (hbounds i).2.2.2.2.1)
  refine ⟨1 / (2 * T), T, by positivity,
    (div_lt_one (by positivity : 0 < 2 * T)).2 (by linarith), hnT, ?_, ?_⟩
  · intro s hs hsmax
    let i : Fin nstar := ⟨s - 1, by omega⟩
    have hi : i.val + 1 = s := by dsimp [i]; omega
    have h := hbounds i
    constructor
    · exact (le_abs_self (B s)).trans ((hi ▸ h.2.2.2.1).trans hLT)
    · exact hsmall.trans (hinv (b s) (hb s hs hsmax) (hi ▸ h.2.2.2.2.2))
  · intro M A hM Y P hmax hgeom a a' haa u hu v hv
    have hMR : 0 < (M : ℝ) := hT0.trans_le hM
    have hMN : 0 < M := by exact_mod_cast hMR
    let i : Fin nstar := ⟨P.size a - 1, by have := hmax.1 a; have := P.size_pos a; omega⟩
    let j : Fin nstar := ⟨P.size a' - 1, by have := hmax.1 a'; have := P.size_pos a'; omega⟩
    have hi : i.val + 1 = P.size a := by dsimp [i]; have := P.size_pos a; omega
    have hj : j.val + 1 = P.size a' := by dsimp [j]; have := P.size_pos a'; omega
    let x := P.nodes Y a ⟨0, P.size_pos a⟩
    let y := P.nodes Y a' ⟨0, P.size_pos a'⟩
    have hwithin (aa : Fin A) (ii : Fin nstar) (hii : ii.val + 1 = P.size aa) :
        ∀ k, angularTorusDistance (P.nodes Y aa k)
          (P.nodes Y aa ⟨0, P.size_pos aa⟩) ≤ r ii / M := by
      intro k
      have h := hgeom.within (P.enumeration aa k).val
        (P.enumeration aa ⟨0, P.size_pos aa⟩).val (by rw [P.enumeration_label, P.enumeration_label])
      exact h.trans (div_le_div_of_nonneg_right (hshort ii) hMR.le)
    have hQi : Q i ≤ (M : ℝ) := (le_abs_self _).trans
      ((hbounds i).2.2.1.trans (hLT.trans hM))
    have hQj : Q j ≤ (M : ℝ) := (le_abs_self _).trans
      ((hbounds j).2.2.1.trans (hLT.trans hM))
    have hai := happrox i
    have haj := happrox j
    rw [hi] at hai
    rw [hj] at haj
    obtain ⟨c, huc, hcnorm⟩ := hai M hQi hMN (P.nodes Y a) x (hwithin a i hi) u hu
    obtain ⟨d, hvd, hdnorm⟩ := haj M hQj hMN (P.nodes Y a') y (hwithin a' j hj) v hv
    have hsep : ∀ p : ℤ, T / M ≤ |y - x - 2 * Real.pi * p| := by
      intro p
      have h := hgeom.between
        (P.enumeration a' ⟨0, P.size_pos a'⟩).val
        (P.enumeration a ⟨0, P.size_pos a⟩).val (by
          rw [P.enumeration_label, P.enumeration_label]
          exact Ne.symm haa)
      have hw := (le_angularTorusDistance_iff y x (T / M)).1 h (-p)
      simpa only [Int.cast_neg, mul_neg, sub_eq_add_neg] using hw
    have hsqrt : 0 < Real.sqrt (M + 1 : ℝ) := by positivity
    have hcnorm' : (∑ k, ‖c k‖) ≤ L / Real.sqrt (M + 1 : ℝ) * ‖u‖ :=
      hcnorm.trans (by gcongr; exact (hbounds i).2.1)
    have hdnorm' : (∑ k, ‖d k‖) ≤ L / Real.sqrt (M + 1 : ℝ) * ‖v‖ :=
      hdnorm.trans (by gcongr; exact (hbounds j).2.1)
    have hpoly := PolynomialCrossCorrelation.inner_modulatedPolynomial_norm_le hMN c d x y
      (T / M) (by positivity) hsep
    have hpoly' : ‖⟪PolynomialCrossCorrelation.modulatedPolynomial M x c,
        PolynomialCrossCorrelation.modulatedPolynomial M y d⟫_ℂ‖ ≤
        (Real.pi * L ^ 2 / T) * ‖u‖ * ‖v‖ := by
      have hratio : (M : ℝ) / (M + 1 : ℝ) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        linarith
      calc
        _ ≤ (Real.pi / (T / M)) * (L / Real.sqrt (M + 1 : ℝ) * ‖u‖) *
            (L / Real.sqrt (M + 1 : ℝ) * ‖v‖) := hpoly.trans (by gcongr)
        _ = (Real.pi * L ^ 2 / T) * ((M : ℝ) / (M + 1 : ℝ)) * ‖u‖ * ‖v‖ := by
          field_simp
          rw [Real.sq_sqrt (by positivity : 0 ≤ (M + 1 : ℝ))]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio
            (show 0 ≤ Real.pi * L ^ 2 / T by positivity)
    have hκ : Real.pi * L ^ 2 / T ≤ 1 / (64 * (n : ℝ)) := by
      apply (div_le_div_iff₀ hT0 (by positivity)).2
      nlinarith [hcrossT]
    have hpoly'' : ‖⟪PolynomialCrossCorrelation.modulatedPolynomial M x c,
        PolynomialCrossCorrelation.modulatedPolynomial M y d⟫_ℂ‖ ≤
        (1 / (64 * (n : ℝ))) * ‖u‖ * ‖v‖ :=
      hpoly'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hκ (norm_nonneg u)) (norm_nonneg v))
    have hresult := PolynomialCrossCorrelation.inner_approximation_bound u v
      (PolynomialCrossCorrelation.modulatedPolynomial M x c)
      (PolynomialCrossCorrelation.modulatedPolynomial M y d) hε.le huc hvd
      hpoly''
    have heps : (1 / (64 * (n : ℝ)) + 2 * ε + ε ^ 2) ≤ 1 / (2 * (n : ℝ)) := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      dsimp [ε]
      field_simp
      nlinarith
    exact hresult.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right heps (norm_nonneg u)) (norm_nonneg v))

end
end LeanNumDetect.RandSamp
