import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect
namespace ConnectedBasisBounds

section NormedSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Quantitative independence in coefficient ℓ¹ norm. -/
def L1LowerBound {J : Type*} [Fintype J] (f : J → E) (c : ℝ) : Prop :=
  ∀ a : J → ℂ, c * ∑ j, ‖a j‖ ≤ ‖∑ j, a j • f j‖


/-- Union bound for the surviving proportions of coordinate intervals. -/
theorem one_sub_sum_le_prod_one_sub
    {I : Type*} (s : Finset I) (a : I → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self i s)
    have has : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 := by
      intro j hj
      exact ha j (Finset.mem_insert_of_mem hj)
    have hsum : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j hj => (has j hj).1
    have hih := ih has
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    calc
      1 - (a i + ∑ j ∈ s, a j) ≤
          (1 - a i) * (1 - ∑ j ∈ s, a j) := by nlinarith
      _ ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
        mul_le_mul_of_nonneg_left hih (by linarith)

abbrev CubePoint (d L : ℕ) := Fin d → Fin (L + 1)

abbrev CubeTranslations (d L : ℕ) (g : Fin d → ℕ) :=
  (l : Fin d) → Fin (L + 1 - g l)

/-- Add a contained pattern to every admissible cube translation. -/
def translatedPoint {d L n : ℕ} (γ : Fin n → CubePoint d L)
    (g : Fin d → ℕ) (hγ : ∀ j l, (γ j l).val ≤ g l)
    (t : CubeTranslations d L g) (j : Fin n) : CubePoint d L :=
  fun l => ⟨(γ j l).val + (t l).val, by
    have ht := (t l).isLt
    have hg := hγ j l
    omega⟩

/-- For a fixed pattern point, translation is injective. -/
theorem translatedPoint_injective {d L n : ℕ} (γ : Fin n → CubePoint d L)
    (g : Fin d → ℕ) (hγ : ∀ j l, (γ j l).val ≤ g l) (j : Fin n) :
    Function.Injective (fun t => translatedPoint γ g hγ t j) := by
  intro t u h
  funext l
  apply Fin.ext
  have he := congrArg (fun k : CubePoint d L => (k l).val) h
  simp only [translatedPoint] at he
  omega

/-- Exact number of admissible translates. -/
theorem card_cubeTranslations (d L : ℕ) (g : Fin d → ℕ) :
    Fintype.card (CubeTranslations d L g) = ∏ l, (L + 1 - g l) := by
  simp [CubeTranslations, Fintype.card_pi]

/-- Exact number of population rows. -/
theorem card_cubePoint (d L : ℕ) : Fintype.card (CubePoint d L) = (L + 1) ^ d := by
  simp [CubePoint, Fintype.card_pi]


/-- A pattern of total width at most `(n-1)L/(2n)` has at least
`(n+1)/(2n)` of all cube translations. -/
theorem card_cubeTranslations_lower {d L n : ℕ} (hn : 1 ≤ n)
    (g : Fin d → ℕ) (hg : ∀ l, g l ≤ L)
    (hwidth : 2 * n * (∑ l, g l) ≤ (n - 1) * L) :
    (n + 1) * Fintype.card (CubePoint d L) ≤
      2 * n * Fintype.card (CubeTranslations d L g) := by
  have hN : 0 < (L + 1 : ℝ) := by positivity
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hgR : ∀ l, (g l : ℝ) ≤ (L : ℝ) := fun l => by exact_mod_cast hg l
  have hwidthR : 2 * (n : ℝ) * (∑ l, (g l : ℝ)) ≤ ((n : ℝ) - 1) * (L : ℝ) := by
    have hh : ((2 * n * (∑ l, g l) : ℕ) : ℝ) ≤ (((n - 1) * L : ℕ) : ℝ) := by
      exact_mod_cast hwidth
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_sub hn,
      Nat.cast_one] using hh
  have hsum : (∑ l, (g l : ℝ)) / (L + 1 : ℝ) ≤ ((n : ℝ) - 1) / (2 * n) := by
    apply (div_le_div_iff₀ hN (by positivity)).2
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hprod := one_sub_sum_le_prod_one_sub Finset.univ
    (fun l : Fin d => (g l : ℝ) / (L + 1 : ℝ)) (by
      intro l hl
      constructor
      · positivity
      · apply (div_le_one hN).2
        have := hgR l
        linarith)
  have hsumdiv : (∑ l : Fin d, (g l : ℝ) / (L + 1 : ℝ)) =
      (∑ l : Fin d, (g l : ℝ)) / (L + 1 : ℝ) := by
    rw [Finset.sum_div]
  rw [hsumdiv] at hprod
  have hratio : ((n : ℝ) + 1) / (2 * n) ≤
      ∏ l : Fin d, (1 - (g l : ℝ) / (L + 1 : ℝ)) := by
    have he : ((n : ℝ) + 1) / (2 * n) = 1 - ((n : ℝ) - 1) / (2 * n) := by
      field_simp
      ring
    rw [he]
    linarith
  have hprodEq : (∏ l : Fin d, (1 - (g l : ℝ) / (L + 1 : ℝ))) =
      (Fintype.card (CubeTranslations d L g) : ℝ) / (L + 1 : ℝ) ^ d := by
    simp_rw [one_sub_div hN.ne']
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [card_cubeTranslations, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro l hl
    rw [Nat.cast_sub (by have := hg l; omega), Nat.cast_add, Nat.cast_one]
  rw [hprodEq] at hratio
  have hp : 0 < (L + 1 : ℝ) ^ d := pow_pos hN d
  have hh := (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) * n) hp).mp hratio
  have hcard : (Fintype.card (CubePoint d L) : ℝ) = (L + 1 : ℝ) ^ d := by
    rw [card_cubePoint]
    norm_cast
  rw [← hcard] at hh
  have hhN : (n + 1) * Fintype.card (CubePoint d L) ≤
      Fintype.card (CubeTranslations d L g) * (2 * n) := by exact_mod_cast hh
  nlinarith


/-- A common translation operator transports coefficient lower bounds. -/
theorem L1LowerBound.map_lower
    {J : Type*} [Fintype J] {f : J → E} {c K : ℝ}
    (hf : L1LowerBound f c) (A : E →L[ℂ] E) (hK : 0 < K)
    (hA : ∀ v, ‖v‖ ≤ K * ‖A v‖) :
    L1LowerBound (fun j => A (f j)) (c / K) := by
  intro a
  have h := (hf a).trans (hA (∑ j, a j • f j))
  rw [map_sum] at h
  simp only [map_smul] at h
  have h' : (c * ∑ j, ‖a j‖) / K ≤ ‖∑ j, a j • A (f j)‖ :=
    (div_le_iff₀ hK).mpr (by nlinarith)
  simpa only [div_mul_eq_mul_div] using h'


/-- Arithmetic form of the quantitative basis append estimate. -/
theorem append_lower_bound {c t M S b y : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hM : 0 < M) (hcM : c ≤ M) (htM : t ≤ M)
    (hy : 0 ≤ y) (hold : c * S ≤ y + M * b) (hnew : t * b ≤ y) :
    (c * t / (3 * M)) * (S + b) ≤ y := by
  have h1 := mul_le_mul_of_nonneg_left hold ht
  have h2 := mul_le_mul_of_nonneg_left hnew hM.le
  have h3 := mul_le_mul_of_nonneg_left hnew hc
  have h4 : (c + t + M) * y ≤ 3 * M * y := by nlinarith
  have h5 : c * t * (S + b) ≤ y * (3 * M) := by nlinarith
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (by positivity)).mpr h5

/-- Appending a vector detected by a unit-norm functional preserves a quantitative
coefficient lower bound. This is the connected-basis induction step. -/
theorem L1LowerBound.append
    {J E' : Type*} [Fintype J] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {f : J → E} {c t M : ℝ} (x : E)
    (hf : L1LowerBound f c) (hc : 0 ≤ c) (ht : 0 ≤ t) (hM : 0 < M)
    (hcM : c ≤ M) (htM : t ≤ M) (hx : ‖x‖ ≤ M)
    (ell : E →ₗ[ℂ] E') (hell : ∀ v, ‖ell v‖ ≤ ‖v‖)
    (hellf : ∀ j, ell (f j) = 0) (hellx : t ≤ ‖ell x‖) :
    L1LowerBound (fun j : Option J => j.elim x f) (c * t / (3 * M)) := by
  classical
  intro a
  let v := ∑ j : J, a (some j) • f j
  let y := a none • x + v
  have hellv : ell v = 0 := by
    simp [v, map_sum, hellf]
  have hnew : t * ‖a none‖ ≤ ‖y‖ := by
    have hly := hell y
    have helly : ell y = a none • ell x := by simp [y, hellv]
    rw [helly, norm_smul] at hly
    have := mul_le_mul_of_nonneg_left hellx (norm_nonneg (a none))
    nlinarith
  have hold : c * (∑ j : J, ‖a (some j)‖) ≤ ‖y‖ + M * ‖a none‖ := by
    have hh := hf (fun j => a (some j))
    have hv : v = y - a none • x := by simp [y]
    have hh2 : ‖v‖ ≤ ‖y‖ + M * ‖a none‖ := by
      rw [hv]
      calc
        ‖y - a none • x‖ ≤ ‖y‖ + ‖a none • x‖ := norm_sub_le _ _
        _ = ‖y‖ + ‖a none‖ * ‖x‖ := by rw [norm_smul]
        _ ≤ ‖y‖ + M * ‖a none‖ := by nlinarith [norm_nonneg (a none)]
    exact hh.trans hh2
  have h := append_lower_bound hc ht hM hcM htM (norm_nonneg y) hold hnew
  simpa [Fintype.sum_option, y, v, add_comm] using h


/-- A bound on basis residuals extends to their whole span. -/
theorem residual_bound_on_span
    {J E' : Type*} [Fintype J] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {f : J → E} {c t : ℝ} (hf : L1LowerBound f c) (hc : 0 < c) (ht : 0 ≤ t)
    (A : E →ₗ[ℂ] E) (P : E →ₗ[ℂ] E')
    (hborder : ∀ j, ‖P (A (f j))‖ ≤ t)
    (x : E) (hx : x ∈ Submodule.span ℂ (Set.range f)) :
    ‖P (A x)‖ ≤ (t / c) * ‖x‖ := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  have hcoef := hf a
  rw [ha] at hcoef
  have hsum : P (A x) = ∑ j, a j • P (A (f j)) := by
    rw [← ha, map_sum, map_sum]
    simp only [map_smul]
  have hup : ‖P (A x)‖ ≤ t * ∑ j, ‖a j‖ := by
    rw [hsum]
    calc
      ‖∑ j, a j • P (A (f j))‖ ≤ ∑ j, ‖a j • P (A (f j))‖ := norm_sum_le _ _
      _ = ∑ j, ‖a j‖ * ‖P (A (f j))‖ := by simp only [norm_smul]
      _ ≤ ∑ j, ‖a j‖ * t := by
        gcongr with j
        exact hborder j
      _ = t * ∑ j, ‖a j‖ := by rw [← Finset.sum_mul]; ring
  have hcoef' : (∑ j, ‖a j‖) ≤ ‖x‖ / c :=
    (le_div_iff₀ hc).mpr (by nlinarith)
  exact hup.trans (by
    have hh := mul_le_mul_of_nonneg_left hcoef' ht
    simpa only [mul_div_assoc, div_mul_eq_mul_div] using hh)


/-- Reindexing preserves the coefficient lower bound. -/
theorem L1LowerBound.reindex
    {J I : Type*} [Fintype J] [Fintype I] {f : J → E} {c : ℝ}
    (hf : L1LowerBound f c) (e : I ≃ J) :
    L1LowerBound (fun i => f (e i)) c := by
  intro a
  have h := hf (fun j => a (e.symm j))
  have hnorm : (∑ j, ‖a (e.symm j)‖) = ∑ i, ‖a i‖ := e.symm.sum_comp (fun i : I => ‖a i‖)
  have hvec : (∑ j, a (e.symm j) • f j) = ∑ i, a i • f (e i) := by
    convert e.symm.sum_comp (fun i => a i • f (e i)) using 1
    simp
  simpa [hnorm, hvec] using h

/-- Positive recurrence for the connected-basis coefficient lower bound. -/
noncomputable def basisCoefficient (c₀ M H : ℝ) : ℕ → ℝ
  | 0 => c₀
  | r + 1 => basisCoefficient c₀ M H r ^ 2 / (3 * M * H)

theorem basisCoefficient_pos {c₀ M H : ℝ} (hc₀ : 0 < c₀) (hM : 0 < M)
    (hH : 0 < H) (r : ℕ) : 0 < basisCoefficient c₀ M H r := by
  induction r with
  | zero => exact hc₀
  | succ r ih => simp only [basisCoefficient]; positivity

theorem basisCoefficient_le_initial {c₀ M H : ℝ} (hc₀ : 0 < c₀) (hM : 0 < M)
    (hH : 1 ≤ H) (hc₀M : c₀ ≤ M) (r : ℕ) : basisCoefficient c₀ M H r ≤ c₀ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hrp := basisCoefficient_pos hc₀ hM (show 0 < H by linarith) r
    have hrM : basisCoefficient c₀ M H r ≤ M := ih.trans hc₀M
    have hstep : basisCoefficient c₀ M H (r + 1) ≤ basisCoefficient c₀ M H r := by
      rw [basisCoefficient]
      apply (div_le_iff₀ (by positivity : 0 < 3 * M * H)).mpr
      have hmul : basisCoefficient c₀ M H r * M ≤
          basisCoefficient c₀ M H r * (3 * M * H) := by
        gcongr
        nlinarith
      nlinarith
    exact hstep.trans ih


/-- Add a nonnegative coarse step in one coordinate of the cube. -/
def addCubeCoordinate {d L : ℕ} (p : CubePoint d L) (l : Fin d) (q : ℕ)
    (hadd : (p l).val + q ≤ L) : CubePoint d L :=
  fun r => ⟨(p r).val + if r = l then q else 0, by
    by_cases hr : r = l
    · subst r
      simpa using Nat.lt_succ_of_le hadd
    · simp only [if_neg hr, Nat.add_zero]
      exact (p r).isLt⟩

/-- Coordinate widths increase by exactly the appended coarse step. -/
theorem sum_updated_width {d : ℕ} (g : Fin d → ℕ) (l : Fin d) (q : ℕ) :
    (∑ r, Function.update g l (g l + q) r) = (∑ r, g r) + q := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ l), Finset.sdiff_singleton_eq_erase]
  have he := Finset.sum_erase_add Finset.univ g (Finset.mem_univ l)
  omega

/-- The appended point and the previous points fit in the updated width vector. -/
theorem addCubeCoordinate_le_updated_width {d L : ℕ} (p : CubePoint d L)
    (g : Fin d → ℕ) (hg : ∀ r, (p r).val ≤ g r)
    (l : Fin d) (q : ℕ) (hadd : (p l).val + q ≤ L) :
    ∀ r, (addCubeCoordinate p l q hadd r).val ≤ Function.update g l (g l + q) r := by
  classical
  intro r
  by_cases hr : r = l
  · subst r
    simp [addCubeCoordinate]
    exact hg l
  · simp [addCubeCoordinate, hr]
    exact hg r

theorem le_updated_width {d : ℕ} (g : Fin d → ℕ) (l : Fin d) (q : ℕ) :
    ∀ r, g r ≤ Function.update g l (g l + q) r := by
  classical
  intro r
  by_cases hr : r = l
  · subst r
    simp
  · simp [Function.update_of_ne hr]

end NormedSection

section InnerProductSection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The residual projection supplies the append certificate directly. -/
theorem L1LowerBound.append_of_subspace
    {J : Type*} [Fintype J] {f : J → E}
    {c t M : ℝ} (x : E) (U : Submodule ℂ E) [Uᗮ.HasOrthogonalProjection]
    (hf : L1LowerBound f c) (hc : 0 ≤ c) (ht : 0 ≤ t) (hM : 0 < M)
    (hcM : c ≤ M) (htM : t ≤ M) (hx : ‖x‖ ≤ M)
    (hfU : ∀ j, f j ∈ U) (hres : t ≤ ‖Uᗮ.starProjection x‖) :
    L1LowerBound (fun j : Option J => j.elim x f) (c * t / (3 * M)) := by
  apply hf.append x hc ht hM hcM htM hx Uᗮ.starProjection.toLinearMap
  · exact Uᗮ.norm_starProjection_apply_le
  · intro j
    exact Submodule.starProjection_orthogonal_apply_eq_zero (hfU j)
  · exact hres

/-- A basis controls the residual growth under one coarse shift. -/
theorem residual_shift_bound
    {J : Type*} [Fintype J] {f : J → E}
    {c t B : ℝ} (hf : L1LowerBound f c) (hc : 0 < c) (ht : 0 ≤ t)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : U = Submodule.span ℂ (Set.range f))
    (A : E →L[ℂ] E) (hA : ∀ v, ‖A v‖ ≤ B * ‖v‖)
    (hborder : ∀ j, ‖Uᗮ.starProjection (A (f j))‖ ≤ t) (x : E) :
    ‖Uᗮ.starProjection (A x)‖ ≤
      (t / c) * ‖x‖ + B * ‖Uᗮ.starProjection x‖ := by
  have hspan : (U.starProjection x) ∈ Submodule.span ℂ (Set.range f) := by
    rw [← hU]
    exact U.starProjection_apply_mem x
  have hfirst := residual_bound_on_span hf hc ht A.toLinearMap
    Uᗮ.starProjection.toLinearMap hborder (U.starProjection x) hspan
  have hdecomp : x = U.starProjection x + Uᗮ.starProjection x := by
    rw [U.starProjection_orthogonal_val]
    abel
  calc
    ‖Uᗮ.starProjection (A x)‖ =
        ‖Uᗮ.starProjection (A (U.starProjection x)) +
          Uᗮ.starProjection (A (Uᗮ.starProjection x))‖ := by
      conv_lhs => rw [hdecomp]
      simp only [map_add]
    _ ≤ ‖Uᗮ.starProjection (A (U.starProjection x))‖ +
        ‖Uᗮ.starProjection (A (Uᗮ.starProjection x))‖ := norm_add_le _ _
    _ ≤ (t / c) * ‖U.starProjection x‖ + B * ‖Uᗮ.starProjection x‖ :=
      add_le_add hfirst ((Uᗮ.norm_starProjection_apply_le _).trans (hA _))
    _ ≤ (t / c) * ‖x‖ + B * ‖Uᗮ.starProjection x‖ := by
      gcongr
      exact U.norm_starProjection_apply_le x


/-- A geometric series controls the residual recurrence without a path-length factor. -/
theorem recurrence_geometric_growth_bound (r : ℕ) (u : ℕ → ℝ) {B a : ℝ}
    (hB : 2 ≤ B) (ha : 0 ≤ a) (hu0 : u 0 ≤ 0)
    (hstep : ∀ j < r, u (j + 1) ≤ B * u j + a) :
    u r ≤ (B ^ r - 1) * a := by
  induction r with
  | zero => simpa using hu0
  | succ r ih =>
    have hi := ih (fun j hj => hstep j (by omega))
    have hBa : 2 * a ≤ B * a := mul_le_mul_of_nonneg_right hB ha
    calc
      u (r + 1) ≤ B * u r + a := hstep r (by omega)
      _ ≤ B * ((B ^ r - 1) * a) + a :=
        add_le_add (mul_le_mul_of_nonneg_left hi (show 0 ≤ B by linarith)) le_rfl
      _ = (B ^ (r + 1) - B + 1) * a := by rw [pow_succ]; ring
      _ ≤ (B ^ (r + 1) - 1) * a := by nlinarith

/-- Finite geometric-growth estimate for approximate invariance. -/
theorem recurrence_growth_bound (r : ℕ) (u : ℕ → ℝ) {B a : ℝ}
    (hB : 2 ≤ B) (ha : 0 ≤ a) (hu0 : u 0 ≤ 0)
    (hstep : ∀ j < r, u (j + 1) ≤ B * u j + a) :
    u r ≤ B ^ r * a := by
  have h := recurrence_geometric_growth_bound r u hB ha hu0 hstep
  nlinarith

/-- Coarse-shift paths propagate the basis residual bound. -/
theorem residual_path_bound
    {J : Type*} [Fintype J] {f : J → E} {c t B M : ℝ}
    (hf : L1LowerBound f c) (hc : 0 < c) (ht : 0 ≤ t) (hB : 2 ≤ B)
    (hM : 0 ≤ M) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : U = Submodule.span ℂ (Set.range f))
    (r : ℕ) (v : ℕ → E) (A : ℕ → E →L[ℂ] E)
    (hv0 : v 0 ∈ U) (hvM : ∀ j ≤ r, ‖v j‖ ≤ M)
    (hnext : ∀ j < r, v (j + 1) = A j (v j))
    (hA : ∀ j < r, ∀ x, ‖A j x‖ ≤ B * ‖x‖)
    (hborder : ∀ j < r, ∀ k, ‖Uᗮ.starProjection (A j (f k))‖ ≤ t) :
    ‖Uᗮ.starProjection (v r)‖ ≤ B ^ r * (t / c * M) := by
  apply recurrence_growth_bound r (fun j => ‖Uᗮ.starProjection (v j)‖) hB (by positivity)
  · rw [Submodule.starProjection_orthogonal_apply_eq_zero hv0, norm_zero]
  · intro j hj
    rw [hnext j hj]
    have hs := residual_shift_bound hf hc ht U hU (A j) (hA j hj) (hborder j hj) (v j)
    have hm : (t / c) * ‖v j‖ ≤ (t / c) * M := by
      gcongr
      exact hvM j (by omega)
    nlinarith


/-- Every proper subspace has a unit vector orthogonal to it. -/
theorem exists_unit_mem_orthogonal (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : U ≠ ⊤) : ∃ u : E, u ∈ Uᗮ ∧ ‖u‖ = 1 := by
  have horth : Uᗮ ≠ ⊥ := by
    intro h
    exact hU ((Submodule.orthogonal_eq_bot_iff).mp h)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  let u : E := (‖w‖ : ℂ)⁻¹ • w
  refine ⟨u, Uᗮ.smul_mem _ hw, ?_⟩
  simp [u, norm_smul, norm_inv, Complex.norm_real, hn]

/-- Isotropy supplies a row with unit residual outside every proper subspace. -/
theorem exists_residual_ge_one_of_isotropy
    {P : Type*} [Fintype P] [Nonempty P] (f : P → E)
    (hiso : ∀ u : E, (∑ p, ‖inner ℂ u (f p)‖ ^ 2) = (Fintype.card P : ℝ) * ‖u‖ ^ 2)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] (hU : U ≠ ⊤) :
    ∃ p, 1 ≤ ‖Uᗮ.starProjection (f p)‖ := by
  classical
  obtain ⟨u, hu, hun⟩ := exists_unit_mem_orthogonal U hU
  by_contra h
  push Not at h
  have hinner : ∀ p, ‖inner ℂ u (f p)‖ ≤ ‖Uᗮ.starProjection (f p)‖ := by
    intro p
    have he : inner ℂ u (Uᗮ.starProjection (f p)) = inner ℂ u (f p) := by
      have hh := Uᗮ.inner_starProjection_left_eq_right u (f p)
      rw [Uᗮ.starProjection_eq_self_iff.mpr hu] at hh
      exact hh.symm
    rw [← he]
    simpa [hun] using norm_inner_le_norm u (Uᗮ.starProjection (f p))
  have hsq : ∀ p, ‖inner ℂ u (f p)‖ ^ 2 < 1 := by
    intro p
    have hn := norm_nonneg (inner ℂ u (f p))
    have hh := (hinner p).trans_lt (h p)
    nlinarith
  have hsum : (∑ p, ‖inner ℂ u (f p)‖ ^ 2) < ∑ _p : P, (1 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro p hp
      exact (hsq p).le
    · exact ⟨Classical.arbitrary P, Finset.mem_univ _, hsq _⟩
  rw [hiso u, hun] at hsum
  simp at hsum


/-- A finite path generated by a prescribed family of coarse shifts. -/
structure BoundedShiftPath {S : Type*} (A : S → E →L[ℂ] E)
    (x₀ x : E) (M : ℝ) where
  length : ℕ
  value : ℕ → E
  direction : ℕ → S
  start_eq : value 0 = x₀
  end_eq : value length = x
  norm_le : ∀ j ≤ length, ‖value j‖ ≤ M
  step_eq : ∀ j < length, value (j + 1) = A (direction j) (value j)

/-- Isotropy and coarse reachability force a quantitatively nonzero basis border. -/
theorem exists_large_basis_border
    {J S P : Type*} [Fintype J] [Nonempty J] [Fintype S] [Nonempty S]
    [Fintype P] [Nonempty P] (g : J → E) (f : P → E) (x₀ : E)
    {c B M H : ℝ} (hc : 0 < c) (hB : 2 ≤ B) (hM : 0 ≤ M) (hH : 0 < H)
    (hf : L1LowerBound g c) (A : S → E →L[ℂ] E)
    (hA : ∀ s x, ‖A s x‖ ≤ B * ‖x‖)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : U = Submodule.span ℂ (Set.range g)) (hproper : U ≠ ⊤) (hx₀ : x₀ ∈ U)
    (hiso : ∀ u : E, (∑ p, ‖inner ℂ u (f p)‖ ^ 2) = (Fintype.card P : ℝ) * ‖u‖ ^ 2)
    (e : ℕ) (hreach : ∀ p, ∃ path : BoundedShiftPath A x₀ (f p) M, path.length ≤ e)
    (hsize : B ^ e * M ≤ H) :
    ∃ s j, c / H ≤ ‖Uᗮ.starProjection (A s (g j))‖ := by
  classical
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (S × J))
    (fun q => ‖Uᗮ.starProjection (A q.1 (g q.2))‖) Finset.univ_nonempty
  let t := ‖Uᗮ.starProjection (A b.1 (g b.2))‖
  have ht : 0 ≤ t := norm_nonneg _
  have hborder : ∀ s j, ‖Uᗮ.starProjection (A s (g j))‖ ≤ t := by
    intro s j
    exact hmax (s, j) (Finset.mem_univ _)
  obtain ⟨p, hp⟩ := exists_residual_ge_one_of_isotropy f hiso U hproper
  obtain ⟨path, hlen⟩ := hreach p
  have hp0 : path.value 0 ∈ U := by rw [path.start_eq]; exact hx₀
  have hs := residual_path_bound hf hc ht hB hM U hU path.length path.value
    (fun j => A (path.direction j)) hp0 path.norm_le path.step_eq
    (fun j hj => hA (path.direction j)) (fun j hj k => hborder _ k)
  rw [path.end_eq] at hs
  have hpow := pow_le_pow_right₀ (show 1 ≤ B by linarith) hlen
  have hglobal : ‖Uᗮ.starProjection (f p)‖ ≤ H * (t / c) := by
    calc
      ‖Uᗮ.starProjection (f p)‖ ≤ B ^ path.length * (t / c * M) := hs
      _ ≤ B ^ e * (t / c * M) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (B ^ e * M) * (t / c) := by ring
      _ ≤ H * (t / c) := mul_le_mul_of_nonneg_right hsize (by positivity)
  refine ⟨b.1, b.2, ?_⟩
  have hprod : c ≤ H * t := by
    have hh := mul_le_mul_of_nonneg_right (hp.trans hglobal) hc.le
    field_simp [hc.ne'] at hh
    nlinarith
  change c / H ≤ t
  exact (div_le_iff₀ hH).mpr (by nlinarith)


/-- The append certificate in the article's finite row indexing. -/
theorem L1LowerBound.cons_of_subspace
    {r : ℕ} {f : Fin r → E} {c t M : ℝ} (x : E)
    (U : Submodule ℂ E) [Uᗮ.HasOrthogonalProjection]
    (hf : L1LowerBound f c) (hc : 0 ≤ c) (ht : 0 ≤ t) (hM : 0 < M)
    (hcM : c ≤ M) (htM : t ≤ M) (hx : ‖x‖ ≤ M)
    (hfU : ∀ j, f j ∈ U) (hres : t ≤ ‖Uᗮ.starProjection x‖) :
    L1LowerBound (Fin.cons x f) (c * t / (3 * M)) := by
  have h := (hf.append_of_subspace x U hc ht hM hcM htM hx hfU hres).reindex
    (finSuccEquiv r)
  convert h using 1
  funext j
  cases j using Fin.cases <;> simp [Fin.cons]

end InnerProductSection

end ConnectedBasisBounds
end LeanNumDetect
