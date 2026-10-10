import General.Fourier.ConnectedBasisBounds

/-! Subspace-thickness consequences of quantitative translated bases.
The common coefficient bounds and cube-coordinate tools are shared with the
connected-basis and direct logarithmic determinant estimates. -/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.TranslatedBasisThickness

export ConnectedBasisBounds
  (L1LowerBound one_sub_sum_le_prod_one_sub CubePoint CubeTranslations
   translatedPoint translatedPoint_injective card_cubeTranslations card_cubePoint
   card_cubeTranslations_lower L1LowerBound.map_lower append_lower_bound
   L1LowerBound.append residual_bound_on_span L1LowerBound.reindex basisCoefficient
   basisCoefficient_pos basisCoefficient_le_initial addCubeCoordinate sum_updated_width
   addCubeCoordinate_le_updated_width le_updated_width L1LowerBound.append_of_subspace
   residual_shift_bound recurrence_geometric_growth_bound recurrence_growth_bound
   residual_path_bound exists_unit_mem_orthogonal exists_residual_ge_one_of_isotropy
   BoundedShiftPath exists_large_basis_border L1LowerBound.cons_of_subspace)

section NormedSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Coefficient lower bounds pass to subfamilies. -/
theorem L1LowerBound.restrict
    {J : Type*} [Fintype J] {f : J → E} {c : ℝ}
    (hf : L1LowerBound f c) (s : Finset J) :
    L1LowerBound (fun j : s => f j) c := by
  classical
  intro a
  let a₀ : J → ℂ := fun j => if hj : j ∈ s then a ⟨j, hj⟩ else 0
  have hnorm : (∑ j : J, ‖a₀ j‖) = ∑ j : s, ‖a j‖ := by
    calc
      (∑ j : J, ‖a₀ j‖) = ∑ j ∈ s, ‖a₀ j‖ :=
        (Finset.sum_subset (Finset.subset_univ s) (by
          intro j hj hjs
          simp [a₀, hjs])).symm
      _ = ∑ j : s, ‖a j‖ := by
        rw [← s.sum_attach, ← Finset.univ_eq_attach]
        simp [a₀]
  have hvec : (∑ j : J, a₀ j • f j) = ∑ j : s, a j • f j := by
    calc
      (∑ j : J, a₀ j • f j) = ∑ j ∈ s, a₀ j • f j :=
        (Finset.sum_subset (Finset.subset_univ s) (by
          intro j hj hjs
          simp [a₀, hjs])).symm
      _ = ∑ j : s, a j • f j := by
        rw [← s.sum_attach, ← Finset.univ_eq_attach]
        simp [a₀]
  simpa [hnorm, hvec] using hf a₀

/-- A perturbation smaller than the coefficient lower bound remains independent. -/
theorem linearIndependent_of_l1LowerBound_perturbation
    {J : Type*} [Fintype J] (f u : J → E) {c θ : ℝ}
    (hf : L1LowerBound f c) (hθc : θ < c)
    (hu : ∀ j, ‖f j - u j‖ ≤ θ) : LinearIndependent ℂ u := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha j
  have hsum : (∑ i, a i • f i) = ∑ i, a i • (f i - u i) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ha, sub_zero]
  have hupper : ‖∑ i, a i • f i‖ ≤ θ * ∑ i, ‖a i‖ := by
    rw [hsum]
    calc
      ‖∑ i, a i • (f i - u i)‖ ≤ ∑ i, ‖a i • (f i - u i)‖ :=
        norm_sum_le _ _
      _ = ∑ i, ‖a i‖ * ‖f i - u i‖ := by simp only [norm_smul]
      _ ≤ ∑ i, ‖a i‖ * θ := by
        gcongr with i
        exact hu i
      _ = θ * ∑ i, ‖a i‖ := by rw [← Finset.sum_mul]; ring
  have hnonneg : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hzero : ∑ i, ‖a i‖ = 0 := by
    have hlower := hf a
    nlinarith
  have hj : ‖a j‖ = 0 := by
    have := Finset.single_le_sum (fun i _ => norm_nonneg (a i)) (Finset.mem_univ j)
    rw [hzero] at this
    exact le_antisymm this (norm_nonneg _)
  exact norm_eq_zero.mp hj

/-- Near rows of a quantitatively independent family cannot exceed a subspace's dimension. -/
theorem card_near_le_finrank
    {J : Type*} [Fintype J] (f : J → E) (U : Submodule ℂ E)
    [FiniteDimensional ℂ U] {c θ : ℝ}
    [DecidablePred (fun j => ∃ u : U, ‖f j - (u : E)‖ ≤ θ)] (hθc : θ < c)
    (hf : L1LowerBound f c) :
    Fintype.card {j : J // ∃ u : U, ‖f j - (u : E)‖ ≤ θ} ≤
      Module.finrank ℂ U := by
  classical
  let s : Finset J := Finset.univ.filter (fun j => ∃ u : U, ‖f j - (u : E)‖ ≤ θ)
  have hs : ∀ j : s, ∃ u : U, ‖f j - (u : E)‖ ≤ θ := by
    intro j
    exact (Finset.mem_filter.mp j.property).2
  choose u hu using hs
  have hli : LinearIndependent ℂ (fun j : s => (u j : E)) :=
    linearIndependent_of_l1LowerBound_perturbation (fun j : s => f j)
      (fun j : s => (u j : E)) (L1LowerBound.restrict hf s) hθc hu
  have hliU : LinearIndependent ℂ u :=
    (U.subtype.linearIndependent_iff_of_injOn (by
      intro x hx y hy h
      exact Subtype.ext h)).mp hli
  have hcard := hliU.fintype_card_le_finrank
  simpa [s] using hcard

/-- Double counting a finite collection of translated bases. -/
theorem good_card_mul_le
    {T J P : Type*} [Fintype T] [Fintype J] [Fintype P]
    (row : T → J → P) (good : P → Prop) [DecidablePred good]
    (k : ℕ)
    (hgood : ∀ t, k ≤ Fintype.card {j : J // good (row t j)})
    (hinj : ∀ j, Function.Injective (fun t => row t j)) :
    Fintype.card T * k ≤ Fintype.card {p : P // good p} * Fintype.card J := by
  classical
  let incidence := (t : T) × {j : J // good (row t j)}
  let encode : incidence → {p : P // good p} × J :=
    fun x => (⟨row x.1 x.2, x.2.property⟩, x.2)
  have he : Function.Injective encode := by
    intro x y hxy
    have hj : (x.2 : J) = y.2 := congrArg Prod.snd hxy
    have hp : row x.1 x.2 = row y.1 y.2 := congrArg (fun z => z.1.val) hxy
    have ht : x.1 = y.1 := hinj x.2 (hp.trans (by rw [hj]))
    cases x
    cases y
    simp only at ht hj
    subst ht
    congr 1
    exact Subtype.ext hj
  have hupper := Fintype.card_le_of_injective encode he
  have hlower : Fintype.card T * k ≤ Fintype.card incidence := by
    rw [Fintype.card_sigma]
    calc
      Fintype.card T * k = ∑ _t : T, k := by simp
      _ ≤ ∑ t : T, Fintype.card {j : J // good (row t j)} :=
        Finset.sum_le_sum fun t _ => hgood t
  exact hlower.trans (by simpa [Fintype.card_prod] using hupper)


/-- A row stays farther than `θ` from every vector of the specified subspace. -/
def FarFromSubspace (f : E) (U : Submodule ℂ E) (θ : ℝ) : Prop :=
  ∀ u : U, θ < ‖f - (u : E)‖

/-- Translated quantitative bases give a dimension-sensitive population count. -/
theorem thick_card_of_translated_l1LowerBound
    {T J P : Type*} [Fintype T] [Fintype J] [Fintype P]
    (row : T → J → P) (f : P → E) (U : Submodule ℂ E)
    [FiniteDimensional ℂ U] {c θ : ℝ} (hθc : θ < c)
    (hbase : ∀ t, L1LowerBound (fun j => f (row t j)) c)
    (hinj : ∀ j, Function.Injective (fun t => row t j))
    [DecidablePred (fun p => FarFromSubspace (f p) U θ)] :
    Fintype.card T * (Fintype.card J - Module.finrank ℂ U) ≤
      Fintype.card {p : P // FarFromSubspace (f p) U θ} * Fintype.card J := by
  classical
  apply good_card_mul_le row (fun p => FarFromSubspace (f p) U θ)
    (Fintype.card J - Module.finrank ℂ U) _ hinj
  intro t
  have hnear := card_near_le_finrank (fun j => f (row t j)) U hθc (hbase t)
  have hpartition := Fintype.card_subtype_compl
    (fun j => ∃ u : U, ‖f (row t j) - (u : E)‖ ≤ θ)
  have hfar : Fintype.card {j : J // ¬∃ u : U, ‖f (row t j) - (u : E)‖ ≤ θ} =
      Fintype.card {j : J // FarFromSubspace (f (row t j)) U θ} := by
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun j => by
      simp [FarFromSubspace]))
  rw [hfar] at hpartition
  omega


/-- Combining the translation count with quantitative independence yields the
strong codimension fraction used by capped frame weights. -/
theorem cube_thick_card
    {d L n : ℕ} (hn : 1 ≤ n) (f : CubePoint d L → E)
    (γ : Fin n → CubePoint d L) (g : Fin d → ℕ)
    (hγ : ∀ j l, (γ j l).val ≤ g l) (hg : ∀ l, g l ≤ L)
    (hwidth : 2 * n * (∑ l, g l) ≤ (n - 1) * L)
    (U : Submodule ℂ E) [FiniteDimensional ℂ U] {c θ : ℝ} (hθc : θ < c)
    (hbase : ∀ t : CubeTranslations d L g,
      L1LowerBound (fun j => f (translatedPoint γ g hγ t j)) c)
    [DecidablePred (fun p => FarFromSubspace (f p) U θ)] :
    (n + 1) * (n - Module.finrank ℂ U) * Fintype.card (CubePoint d L) ≤
      2 * n ^ 2 * Fintype.card {p : CubePoint d L // FarFromSubspace (f p) U θ} := by
  classical
  have ht := card_cubeTranslations_lower hn g hg hwidth
  have hb := thick_card_of_translated_l1LowerBound
    (fun t j => translatedPoint γ g hγ t j) f U hθc hbase
    (translatedPoint_injective γ g hγ)
  simp only [Fintype.card_fin] at hb
  calc
    (n + 1) * (n - Module.finrank ℂ U) * Fintype.card (CubePoint d L) =
        ((n + 1) * Fintype.card (CubePoint d L)) * (n - Module.finrank ℂ U) := by ring
    _ ≤ (2 * n * Fintype.card (CubeTranslations d L g)) *
        (n - Module.finrank ℂ U) := Nat.mul_le_mul_right _ ht
    _ = 2 * n * (Fintype.card (CubeTranslations d L g) *
        (n - Module.finrank ℂ U)) := by ring
    _ ≤ 2 * n * (Fintype.card {p : CubePoint d L // FarFromSubspace (f p) U θ} * n) :=
      Nat.mul_le_mul_left _ hb
    _ = 2 * n ^ 2 * Fintype.card {p : CubePoint d L // FarFromSubspace (f p) U θ} := by ring

end NormedSection

end LeanNumDetect.TranslatedBasisThickness

namespace LeanNumDetect.ConnectedBasisBounds
export TranslatedBasisThickness (L1LowerBound.restrict)
end LeanNumDetect.ConnectedBasisBounds
