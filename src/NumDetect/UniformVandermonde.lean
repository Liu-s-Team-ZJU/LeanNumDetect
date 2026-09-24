import NumDetect.UniformInterpolation
import NumDetect.UniformCentering

/-! The contiguous-grid Vandermonde lower bound from the NumDetect manuscript. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The manuscript's finite-set interpolation lemma supplies the packets used
by the contiguous Vandermonde estimate after rescaling to the unit torus. -/
private theorem centeredPackets_of_unitTorus
    {d n s : ℕ} (hn : 2 ≤ n) {D Δ θ : ℝ} (x : Fin n → Point d)
    (hs : 4 * n ≤ s) (hD : 0 < D) (hΔ : 0 < Δ)
    (hsep : ∀ i j, i ≠ j → Δ ≤ l1Norm (x i - x j))
    (hdiam : ∀ i j, l1Norm (x i - x j) ≤ Real.pi / (2 * D))
    (hscale : ((s : ℝ) / (2 * n)) * D * Δ ≤ Real.pi)
    (htheta : ((s : ℝ) / (2 * n)) * D * Δ / Real.pi = θ) :
    ∃ P : Fin n → CenteredPacket d ((n - 1) * (s / (2 * n))),
      (∀ k, (P k).mass ≤
        Real.sqrt ((2 : ℝ) ^ (n - 1)) * θ⁻¹ ^ (n - 1)) ∧
      ∀ k j, (P k).value D (x j - x k) =
        if k = j then 1 else 0 := by
  classical
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by positivity
  have hs0 : 0 < s := by omega
  have hsR : 0 < (s : ℝ) := by positivity
  let t : ℝ := D / (2 * Real.pi)
  have ht : 0 < t := by dsimp [t]; positivity
  have hDt : 2 * Real.pi * t = D := by
    dsimp [t]
    field_simp
  let y (k j : Fin n) : Point d :=
    fun a => t * (x j a - x k a)
  let U (k : Fin n) : Finset (Point d) :=
    Finset.univ.image (y k)
  have hxinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    rw [hij, sub_self] at h
    simp [l1Norm] at h
    linarith
  have hyinj (k : Fin n) : Function.Injective (y k) := by
    intro i j hij
    apply hxinj
    funext a
    have ha := congrFun hij a
    dsimp [y] at ha
    have hne : t ≠ 0 := ne_of_gt ht
    have := (mul_left_cancel₀ hne ha)
    linarith
  have hcard (k : Fin n) : (U k).card = n := by
    simp [U, Finset.card_image_of_injective _ (hyinj k)]
  have hykk (k : Fin n) : y k k = 0 := by
    funext a
    simp [y]
  have hzero (k : Fin n) : 0 ∈ U k := by
    rw [Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, hykk k⟩
  have hnorm (k j : Fin n) :
      l1Norm (y k j) = t * l1Norm (x j - x k) := by
    simpa only [y, Pi.sub_apply] using
      CenteredPacket.l1Norm_scale t ht.le (x j - x k)
  have hshort (k : Fin n) : ∀ u ∈ U k, l1Norm u ≤ 1 / 4 := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    rw [hnorm]
    calc
      t * l1Norm (x j - x k) ≤ t * (Real.pi / (2 * D)) := by
        exact mul_le_mul_of_nonneg_left (hdiam j k) ht.le
      _ = 1 / 4 := by
        dsimp [t]
        field_simp
        norm_num
  have hcube (k : Fin n) :
      ∀ u ∈ U k, ∀ a, -(1 / 2 : ℝ) ≤ u a ∧ u a < 1 / 2 := by
    intro u hu a
    have hcoordinate : |u a| ≤ l1Norm u := by
      unfold l1Norm
      exact Finset.single_le_sum (fun i _ => abs_nonneg (u i)) (Finset.mem_univ a)
    have hbound := hshort k u hu
    have habs := abs_le.mp (hcoordinate.trans hbound)
    constructor <;> linarith
  have hhalf : 2 * (n : ℝ) ≤ (s : ℝ) / 2 := by
    have hs' : (4 * n : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  have hfloor : ⌊((s : ℝ) / 2) / n⌋₊ = s / (2 * n) := by
    rw [show ((s : ℝ) / 2) / n = (s : ℝ) / (2 * n) by
      field_simp]
    rw [show (2 : ℝ) * n = ((2 * n : ℕ) : ℝ) by norm_num]
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hθ : 0 < θ := by
    rw [← htheta]
    positivity
  have hθle : θ ≤ 1 := by
    rw [← htheta]
    exact (div_le_one Real.pi_pos).mpr hscale
  have hθinv : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).mpr hθle
  have hθn : θ * (n : ℝ) = (s : ℝ) * t * Δ := by
    rw [← htheta]
    dsimp [t]
    field_simp
  have hPfactor (k : Fin n) :
      ∃ Q : CenteredPacket d (((U k).card - 1) * ⌊((s : ℝ) / 2) / n⌋₊),
        Q.value (2 * Real.pi) 0 = 1 ∧
        (∀ u ∈ U k, u ≠ 0 → Q.value (2 * Real.pi) u = 0) ∧
        Q.mass ≤ Real.sqrt ((2 : ℝ) ^ ((U k).card - 1)) *
          ∏ u ∈ (U k).filter (fun u =>
            0 < l1Norm u ∧ l1Norm u ≤ (n : ℝ) / (2 * ((s : ℝ) / 2))),
            (n : ℝ) / (2 * ((s : ℝ) / 2) * l1Norm u) := by
    obtain ⟨Q, _, hQ0, hQvan, hQmass, _⟩ :=
      CenteredPacket.exists_centeredUnitTorusInterpolation_withMass
        (U k) n ((s : ℝ) / 2) (hcube k) (by rw [hcard])
        (hzero k) (hshort k) hhalf
    exact ⟨Q, hQ0, hQvan, hQmass⟩
  choose Q hQ using hPfactor
  let P (k : Fin n) : CenteredPacket d ((n - 1) * (s / (2 * n))) :=
    (Q k).widen (by rw [hcard, hfloor])
  refine ⟨P, ?_, ?_⟩
  · intro k
    have hprod :
        (∏ u ∈ (U k).filter (fun u =>
            0 < l1Norm u ∧ l1Norm u ≤ (n : ℝ) / (2 * ((s : ℝ) / 2))),
            (n : ℝ) / (2 * ((s : ℝ) / 2) * l1Norm u)) ≤
          θ⁻¹ ^ (n - 1) := by
      let S := (U k).filter (fun u =>
        0 < l1Norm u ∧ l1Norm u ≤ (n : ℝ) / (2 * ((s : ℝ) / 2)))
      have hratio (u : Point d) (hu : u ∈ S) :
          (n : ℝ) / (2 * ((s : ℝ) / 2) * l1Norm u) ≤ θ⁻¹ := by
        have hu' : u ∈ U k ∧ 0 < l1Norm u := by
          have hu'' := Finset.mem_filter.mp hu
          exact ⟨hu''.1, hu''.2.1⟩
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu'.1
        have hjk : j ≠ k := by
          intro heq
          subst j
          rw [hykk] at hu'
          simp [l1Norm] at hu'
        have hnormlower : t * Δ ≤ l1Norm (y k j) := by
          rw [hnorm]
          exact mul_le_mul_of_nonneg_left (hsep j k hjk) ht.le
        have htarget : θ * (n : ℝ) ≤ (s : ℝ) * l1Norm (y k j) := by
          rw [hθn]
          nlinarith [mul_le_mul_of_nonneg_left hnormlower hsR.le]
        have hnormpos : 0 < l1Norm (y k j) := hu'.2
        rw [show 2 * ((s : ℝ) / 2) = (s : ℝ) by ring]
        rw [inv_eq_one_div]
        exact (div_le_div_iff₀ (by positivity : 0 < (s : ℝ) * l1Norm (y k j)) hθ).mpr
          (by nlinarith)
      have hSsub : S ⊆ (U k).erase 0 := by
        intro u hu
        have hu' := Finset.mem_filter.mp hu
        refine Finset.mem_erase.mpr ⟨?_, hu'.1⟩
        intro heq
        subst u
        simp [l1Norm] at hu'
      have hScard : S.card ≤ n - 1 := by
        calc
          S.card ≤ ((U k).erase 0).card := Finset.card_le_card hSsub
          _ = n - 1 := by rw [Finset.card_erase_of_mem (hzero k), hcard]
      calc
        (∏ u ∈ S, (n : ℝ) / (2 * ((s : ℝ) / 2) * l1Norm u)) ≤
            ∏ _u ∈ S, θ⁻¹ :=
          Finset.prod_le_prod (fun u hu => by
            have hu' := (Finset.mem_filter.mp hu).2.1
            positivity)
            (fun u hu => hratio u hu)
        _ = θ⁻¹ ^ S.card := by rw [Finset.prod_const]
        _ ≤ θ⁻¹ ^ (n - 1) := pow_le_pow_right₀ hθinv hScard
    have hmass := (hQ k).2.2
    simp only [P, CenteredPacket.mass_widen]
    have hmass' := hmass
    simp only [hcard k] at hmass'
    exact hmass'.trans (mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg _))
  · intro k j
    simp only [P, CenteredPacket.value_widen]
    rw [← CenteredPacket.value_scale (Q k) D t hDt (x j - x k)]
    by_cases hkj : k = j
    · subst j
      rw [if_pos rfl]
      change (Q k).value (2 * Real.pi) (y k k) = 1
      rw [hykk]
      exact (hQ k).1
    · rw [if_neg hkj]
      have hy0 : y k j ≠ 0 := by
        intro h
        have h' := hyinj k (show y k j = y k k by rw [hykk]; exact h)
        exact hkj h'.symm
      have hymem : y k j ∈ U k := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      change (Q k).value (2 * Real.pi) (y k j) = 0
      exact (hQ k).2.1 (y k j) hymem hy0

/-- Manuscript Lemma `lem:uniform-Vandermonde`. -/
theorem uniformVandermonde_minimumSingularValue
    {d n s : ℕ} {Ω : ℝ} (μ : AtomicMeasure d n)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω)
    (hcluster : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j))
    (hs : 4 * n ≤ s) (hseven : Even s) :
    uniformVandermondeLowerBound s Ω μ.node hn ≤
      matrixSingularValue (uniformVandermonde s Ω μ.node) (n - 1) := by
  classical
  let D : ℝ := Ω / s
  let Δ : ℝ := minimumL1Separation μ.node hn
  let θ : ℝ := normalizedMinimumSeparation Ω μ.node hn
  let b : ℕ := s / (2 * n)
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hs0 : 0 < s :=
    lt_of_lt_of_le (by positivity : 0 < 4 * n) hs
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hΔ : 0 < Δ := by
    exact CenteredPacket.minimumL1Separation_pos μ.node hn μ.node_injective
  have hθ : 0 < θ := by
    dsimp [θ, normalizedMinimumSeparation]
    positivity
  have hsep (i j : Fin n) (hij : i ≠ j) :
      Δ ≤ l1Norm (μ.node i - μ.node j) := by
    exact CenteredPacket.minimumL1Separation_le μ.node hn hij
  have hnode (j : Fin n) :
      l1Norm (μ.node j) < Real.pi * n / Ω := by
    simpa [InOpenL1Ball] using hcluster j
  have hdiam (i j : Fin n) :
      l1Norm (μ.node i - μ.node j) ≤ Real.pi / (2 * D) := by
    calc
      l1Norm (μ.node i - μ.node j) ≤
          l1Norm (μ.node i) + l1Norm (μ.node j) :=
        CenteredPacket.l1Norm_sub_le _ _
      _ ≤ 2 * (Real.pi * n / Ω) :=
        (by nlinarith [hnode i, hnode j] :
          l1Norm (μ.node i) + l1Norm (μ.node j) <
            2 * (Real.pi * n / Ω)).le
      _ ≤ Real.pi / (2 * D) := by
        have hsR : (4 * n : ℝ) ≤ s := by exact_mod_cast hs
        have hpi : 0 < Real.pi := Real.pi_pos
        dsimp [D]
        field_simp
        nlinarith
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hΔupper : Δ < 2 * (Real.pi * n / Ω) := by
    calc
      Δ ≤ l1Norm (μ.node i0 - μ.node i1) := hsep i0 i1 hi01
      _ ≤ l1Norm (μ.node i0) + l1Norm (μ.node i1) :=
        CenteredPacket.l1Norm_sub_le _ _
      _ < 2 * (Real.pi * n / Ω) := by
        nlinarith [hnode i0, hnode i1]
  have hscale : ((s : ℝ) / (2 * n)) * D * Δ ≤ Real.pi := by
    have hnR : 0 < (n : ℝ) := by positivity
    have hsR : 0 < (s : ℝ) := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    dsimp [D]
    field_simp
    field_simp at hΔupper
    nlinarith
  have htheta :
      ((s : ℝ) / (2 * n)) * D * Δ / Real.pi = θ := by
    have hnR : 0 < (n : ℝ) := by positivity
    have hsR : 0 < (s : ℝ) := by positivity
    dsimp [D, Δ, θ, normalizedMinimumSeparation]
    field_simp
  obtain ⟨P, hPmass, hPinterp⟩ :=
    centeredPackets_of_unitTorus hn μ.node hs hD hΔ
      hsep hdiam hscale htheta
  have hsupport :
      (n - 1) * b + b ≤ s / 2 := by
    calc
      (n - 1) * b + b = (n - 1) * b + 1 * b := by rw [one_mul]
      _ = ((n - 1) + 1) * b := by rw [Nat.add_mul]
      _ = n * b := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = b * n := Nat.mul_comm _ _
      _ = (s / 2 / n) * n := by
        rw [Nat.div_div_eq_div_mul]
      _ ≤ s / 2 := Nat.div_mul_le_self _ _
  let H : ℝ := (Real.sqrt 2 / θ) ^ (n - 1)
  have hH : 0 < H := by
    dsimp [H]
    positivity
  have hPmass' (k : Fin n) : (P k).mass ≤ H := by
    dsimp [H]
    rw [CenteredPacket.sqrtTwo_div_pow]
    exact hPmass k
  have hsv := CenteredPacket.singularValue_ge_of_centeredPackets
    hn0 D μ.node P hsupport hseven hH hPmass' hPinterp
  have hfrequency :
      (fun (α : UniformIndex d s) => fun k => D * (α k : ℝ)) =
        uniformFrequency d s Ω := by
    funext α k
    simp only [D, uniformFrequency]
  have hcenter := uniformVandermonde_centering Ω μ hs0 hseven
  have hsv' :
      Real.sqrt ((((2 * b + 1 : ℕ) : ℝ) ^ d)) /
          (Real.sqrt n * H) ≤
        matrixSingularValue
          (centeredUniformVandermonde s Ω μ.node) (n - 1) := by
    rw [hfrequency] at hsv
    rw [← hcenter.2.2.1 (n - 1)]
    simpa only [uniformVandermonde, Nat.cast_pow] using hsv
  have hnormalize := CenteredPacket.uniformPacket_normalization
    (n := n) (q := n - 1)
    (N := (((2 * b + 1 : ℕ) : ℝ) ^ d)) hn0
    (by positivity : 0 < (((2 * b + 1 : ℕ) : ℝ) ^ d)) hθ
  rw [uniformVandermondeLowerBound]
  change
    Real.sqrt
        (1 / ((n : ℝ) * 2 ^ (n - 1)) *
          (((2 * b + 1 : ℕ) : ℝ) ^ d)) *
        θ ^ (n - 1) ≤
      matrixSingularValue (uniformVandermonde s Ω μ.node) (n - 1)
  rw [hnormalize]
  rw [hcenter.2.2.1 (n - 1)]
  exact hsv'

end

end NumDetect
end LeanNumDetect
