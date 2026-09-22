import SegmentedVDM.Interpolation
import General.Fourier.TrigonometricPolynomialParseval
import General.MatrixAnalysis.SingularValueBounds
import Mathlib.Algebra.Order.Chebyshev

/-! Minimum-norm interpolation from full column rank, with both norm bounds. This
is a direct finite-dimensional proof of NumDetect `lem:interpolation_via_svd`, for
arbitrary target values; `cardinal_coefficients_of_frame` is its `w = e_j`
corollary. The interpolating trigonometric polynomial is represented by its
coefficient vector `c` through `LeanNumDetect.unitTorusTrigPolynomial`: the
coefficient form `Real.sqrt (energy c)` of its squared `L²` norm and the
coefficient `ℓ¹` mass `∑ i, ‖c i‖` bounding its `L∞` norm are
`interpolation_coefficients_of_fullColumnRank_coefficientNorms`, and
`interpolation_coefficients_of_fullColumnRank` converts them to the genuine
torus norms `L²(𝕋^d)` and `L^∞(𝕋^d)` through the Parseval bridge
`General.Fourier.TrigonometricPolynomialParseval`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix LeanNumDetect WithLp
open scoped BigOperators ComplexOrder

namespace SegmentedVDM

theorem gram_posDef_of_frame {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (V : Matrix ρ ι ℂ) {a : ℝ} (ha : 0 < a)
    (hframe : ∀ v, a * energy v ≤ energy (V *ᵥ v)) : (Vᴴ * V).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_conjTranspose_mul_self _, ?_⟩
  intro v hv
  apply RCLike.pos_iff.mpr
  constructor
  · change 0 < quadratic (Vᴴ * V) v
    rw [quadratic_gram]
    exact (mul_pos ha (energy_pos v hv)).trans_le (hframe v)
  · exact (isHermitian_conjTranspose_mul_self V).im_star_dotProduct_mulVec_self v

/-- The squared Euclidean norm of the `WithLp` form of a coefficient vector is its
energy; this is the Parseval identification `‖f‖_{L²} ^ 2 = energy c`. -/
private theorem norm_sq_toLp_eq_energy {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ ^ 2 = energy v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [energy]

/-- Injectivity of the plain matrix action is the full column rank condition for
the Euclidean linear map used by the singular value API. -/
private theorem toEuclideanLin_injective_of_mulVec_injective {ρ ι : Type*}
    [Fintype ρ] [Fintype ι] [DecidableEq ι] (V : Matrix ρ ι ℂ)
    (hV : ∀ u v : ι → ℂ, V *ᵥ u = V *ᵥ v → u = v) :
    Function.Injective V.toEuclideanLin := by
  intro x y hxy
  apply WithLp.ofLp_injective
  apply hV
  exact congrArg ofLp hxy

/-- The coefficient-form bounds behind NumDetect `lem:interpolation_via_svd`
(`interpolation_coefficients_of_fullColumnRank`). Let
`V : Matrix ρ ι ℂ` have full column rank
(`Function.Injective V.toEuclideanLin`, equivalently `HasFullColumnRank V`), the
role of the Vandermonde matrix `V_{Λ^d}(X)` of `defi:high_dim_uniform_poly` with
`Fintype.card ι` nodes and `Fintype.card ρ = |Λ^d| = [(r+1)(m+1)]^d` frequencies.
Then for every `w : ι → ℂ` there is a coefficient vector `c : ρ → ℂ` with

* `c ⬝ᵥ Vᵀ k = w k` for all `k`, the coefficient form of the interpolation
  condition `f (y_k / (2 * π)) = w k` of the manuscript;
* `Real.sqrt (energy c) ≤ Real.sqrt (energy w) / σ`, the coefficient form of
  the `L²` bound `‖f‖_{L²(𝕋^d)} ≤ ‖w‖_2 / σ_min`, since
  `Real.sqrt (energy w) = ‖w‖_2` and, for pairwise distinct frequencies,
  `Real.sqrt (energy c) = ‖f‖_{L²}` is the normalized torus `L²` norm by
  Parseval;
* `∑ i, ‖c i‖ ≤ Real.sqrt (Fintype.card ρ) * Real.sqrt (energy w) / σ`, the
  coefficient form of the `L∞` bound
  `‖f‖_{L^∞(𝕋^d)} ≤ √|Λ^d| ‖w‖_2 / σ_min`, since
  `‖f‖_{L^∞} ≤ ∑ i, ‖c i‖` by the triangle inequality and `Fintype.card ρ` is
  the frequency count `|Λ^d|` of `defi:high_dim_uniform_poly`, so
  `Real.sqrt (Fintype.card ρ)` is the factor `√|Λ^d|` (Cauchy–Schwarz converts
  the coefficient `ℓ¹` mass `∑ i, ‖c i‖`, `SegmentedVDM.Packet.mass` for
  packets, into the coefficient `ℓ²` norm),

where `σ = matrixSingularValue V (Fintype.card ι - 1)` is `σ_min` with zero-based
indices. The manuscript's genuine torus-norm conclusions are
`interpolation_coefficients_of_fullColumnRank`, derived from these
coefficient-form bounds through the Parseval bridge. -/
theorem interpolation_coefficients_of_fullColumnRank_coefficientNorms {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    [DecidableEq ι] (V : Matrix ρ ι ℂ) (hinj : Function.Injective V.toEuclideanLin)
    (w : ι → ℂ) :
    ∃ c : ρ → ℂ, (∀ k, c ⬝ᵥ Vᵀ k = w k) ∧
      Real.sqrt (energy c) ≤
        Real.sqrt (energy w) / matrixSingularValue V (Fintype.card ι - 1) ∧
      (∑ i, ‖c i‖) ≤ Real.sqrt (Fintype.card ρ) * Real.sqrt (energy w) /
        matrixSingularValue V (Fintype.card ι - 1) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · haveI : IsEmpty ι :=
      not_nonempty_iff.mp fun h => (Fintype.card_pos_iff.mpr h).ne' hn
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro k
      exact isEmptyElim k
    · simp [energy, Finset.univ_eq_empty]
    · simp [energy, Finset.univ_eq_empty]
  · set σ := matrixSingularValue V (Fintype.card ι - 1) with hσdef
    have hσ : 0 < σ := by
      apply V.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos.mp hinj
      simpa using Nat.sub_lt hn Nat.zero_lt_one
    -- The last singular value squared is a frame lower bound: the manuscript's
    -- `σ_min` step, `σ_min ‖v‖ ≤ ‖V v‖`.
    have hf1 : ∀ v : ι → ℂ, σ ^ 2 * energy v ≤ energy (V *ᵥ v) := by
      intro v
      have h := lastMatrixSingularValue_mul_norm_le V hn (WithLp.toLp 2 v)
      have hvv : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ ^ 2 = energy v :=
        norm_sq_toLp_eq_energy v
      have hVv : ‖V.toEuclideanLin (WithLp.toLp 2 v)‖ ^ 2 = energy (V *ᵥ v) := by
        show ‖(WithLp.toLp 2 (V *ᵥ v) : EuclideanSpace ℂ ρ)‖ ^ 2 = _
        exact norm_sq_toLp_eq_energy _
      have hsq := (sq_le_sq₀ (mul_nonneg hσ.le (norm_nonneg _)) (norm_nonneg _)).2 h
      rw [mul_pow, hvv, hVv] at hsq
      exact hsq
    have hG : (Vᴴ * V).PosDef := gram_posDef_of_frame V (pow_pos hσ 2) hf1
    have hdet : IsUnit (Vᴴ * V).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
    -- The normal-equations solution `c = star (V *ᵥ u)` with
    -- `(Vᴴ * V) *ᵥ u = star w` is the Moore--Penrose minimum-norm interpolant
    -- `A† *ᵥ w` for `A = Vᵀ`.
    let u : ι → ℂ := (Vᴴ * V)⁻¹ *ᵥ star w
    have hu : (Vᴴ * V) *ᵥ u = star w := by
      dsimp [u]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
    have hcV : star (V *ᵥ u) ᵥ* V = w := by
      have hh : star u ᵥ* (Vᴴ * V) = star (star w) := by
        rw [← hG.isHermitian.eq, ← Matrix.star_mulVec, hu]
      rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, hh]
      exact star_star w
    have hce : energy (star (V *ᵥ u)) = energy (V *ᵥ u) := by
      simp only [energy, Pi.star_apply, norm_star]
    -- Cauchy--Schwarz on the normal equations: `energy (V *ᵥ u) ≤ √U √‖w‖`.
    have hf2 : energy (V *ᵥ u) ≤ Real.sqrt (energy u) * Real.sqrt (energy w) := by
      have hcs := dotProduct_norm_sq_le (star u) (star w)
      have hesu : energy (star u) = energy u := by
        simp only [energy, Pi.star_apply, norm_star]
      have hesw : energy (star w) = energy w := by
        simp only [energy, Pi.star_apply, norm_star]
      have hz : ‖star u ⬝ᵥ star w‖ ≤ Real.sqrt (energy u * energy w) := by
        rw [← hesu, ← hesw]
        exact Real.le_sqrt_of_sq_le hcs
      rw [Real.sqrt_mul (energy_nonneg u)] at hz
      calc
        energy (V *ᵥ u) = (star u ⬝ᵥ ((Vᴴ * V) *ᵥ u)).re := (quadratic_gram V u).symm
        _ = (star u ⬝ᵥ star w).re := by rw [hu]
        _ ≤ ‖star u ⬝ᵥ star w‖ := Complex.re_le_norm _
        _ ≤ Real.sqrt (energy u) * Real.sqrt (energy w) := hz
    have hmain : σ ^ 2 * energy (V *ᵥ u) ≤ energy w := by
      by_cases hU : energy u = 0
      · have hP0 : energy (V *ᵥ u) = 0 := by
          apply le_antisymm _ (energy_nonneg _)
          have := hf2
          rw [hU] at this
          simpa using this
        rw [hP0]
        simpa using energy_nonneg w
      · have hUpos : 0 < energy u := lt_of_le_of_ne (energy_nonneg u) (Ne.symm hU)
        have hsqrtpos : 0 < Real.sqrt (energy u) := Real.sqrt_pos.mpr hUpos
        have hstep : σ ^ 2 * Real.sqrt (energy u) ≤ Real.sqrt (energy w) := by
          have h1 : σ ^ 2 * Real.sqrt (energy u) * Real.sqrt (energy u) =
              σ ^ 2 * energy u := by
            rw [mul_assoc, ← sq, Real.sq_sqrt (energy_nonneg u)]
          have hmul : σ ^ 2 * Real.sqrt (energy u) * Real.sqrt (energy u) ≤
              Real.sqrt (energy w) * Real.sqrt (energy u) := by
            rw [h1, mul_comm (Real.sqrt (energy w)) (Real.sqrt (energy u))]
            exact (hf1 u).trans hf2
          exact le_of_mul_le_mul_right hmul hsqrtpos
        have hfinal : σ ^ 2 * energy (V *ᵥ u) ≤ Real.sqrt (energy w) ^ 2 := by
          have h1 := mul_le_mul_of_nonneg_left hf2 (sq_nonneg σ)
          have h2 : σ ^ 2 * (Real.sqrt (energy u) * Real.sqrt (energy w)) =
              (σ ^ 2 * Real.sqrt (energy u)) * Real.sqrt (energy w) := by ring
          rw [h2] at h1
          have h3 := mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg (energy w))
          have hYY : Real.sqrt (energy w) * Real.sqrt (energy w) =
              Real.sqrt (energy w) ^ 2 := by ring
          rw [hYY] at h3
          exact h1.trans h3
        rwa [Real.sq_sqrt (energy_nonneg w)] at hfinal
    have hP : energy (star (V *ᵥ u)) ≤ energy w / σ ^ 2 := by
      rw [hce]
      exact (le_div_iff₀ (pow_pos hσ 2)).2 (by rwa [mul_comm])
    refine ⟨star (V *ᵥ u), ?_, ?_, ?_⟩
    · intro k
      change (star (V *ᵥ u)) ⬝ᵥ (fun i => V i k) = _
      have h := congrFun hcV k
      simpa [Matrix.vecMul] using h
    · have h1 : Real.sqrt (energy (star (V *ᵥ u))) ≤
          Real.sqrt (energy w / σ ^ 2) := Real.sqrt_le_sqrt hP
      rw [Real.sqrt_div (energy_nonneg w), Real.sqrt_sq hσ.le] at h1
      exact h1
    · have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i => ‖(star (V *ᵥ u)) i‖)
      simp only [Finset.card_univ] at hs
      have hmass : (∑ i, ‖(star (V *ᵥ u)) i‖) ^ 2 ≤
          (Fintype.card ρ : ℝ) * energy (star (V *ᵥ u)) := by
        simpa [energy] using hs
      have hm2 : (∑ i, ‖(star (V *ᵥ u)) i‖) ^ 2 ≤
          (Real.sqrt (Fintype.card ρ) * Real.sqrt (energy w) / σ) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
          Real.sq_sqrt (energy_nonneg w)]
        have h := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg (Fintype.card ρ))
        rw [mul_div] at h
        exact hmass.trans h
      exact (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          hσ.le)).mp hm2

/-- Minimum-norm interpolation with both norm bounds of NumDetect
`lem:interpolation_via_svd`, in the manuscript's own normalization. Let
`V : Matrix ρ ι ℂ` have full column rank (`Function.Injective V.toEuclideanLin`,
equivalently `HasFullColumnRank V`), the role of the Vandermonde matrix
`V_{Λ^d}(X)` of `defi:high_dim_uniform_poly` with `Fintype.card ι` nodes and
`Fintype.card ρ = |Λ^d| = [(r+1)(m+1)]^d` pairwise distinct frequency vectors,
presented by `s : ρ → Fin d → ℤ` with `hs : Function.Injective s` (the
$\Lambda^d$-is-a-set condition of `defi:high_dim_uniform_poly`). Then for every
`w : ι → ℂ` there is a coefficient vector `c : ρ → ℂ` with
`c ⬝ᵥ Vᵀ k = w k` for all `k`, the coefficient form of the interpolation
condition `f (y_k / (2 * π)) = w k` of the manuscript, such that the
trigonometric polynomial

$$
f(\bm\omega) = \sum_i c_i\, e^{2\pi i\, \mathbf s_i \cdot \bm\omega},
\qquad \bm\omega \in \mathbb T^d \cong [0,1)^d ,
$$

satisfies the manuscript's two bounds

$$
\|f\|_{L^2(\mathbb T^d)}\le\frac{\|\mathbf w\|_2}{\sigma_{\min}(\mathcal V)},
\qquad
\|f\|_{L^\infty(\mathbb T^d)}\le
\frac{\sqrt{|\Lambda^d|}\,\|\mathbf w\|_2}{\sigma_{\min}(\mathcal V)} ,
$$

with $\|f\|_{L^2(\mathbb T^d)}^2 = \int_{\mathbb T^d}\|f(\bm\omega)\|^2\,d\bm\omega$
the normalized torus $L^2$ norm, $\|\mathbf w\|_2 = $ `Real.sqrt (energy w)`,
$|\Lambda^d| =$ `Fintype.card ρ`, and $\sigma_{\min}(\mathcal V) = $
`matrixSingularValue V (Fintype.card ι - 1)` with zero-based indices.

Both conclusions are derived from the coefficient-form bounds
`interpolation_coefficients_of_fullColumnRank_coefficientNorms` through the
Parseval bridge `General.Fourier.TrigonometricPolynomialParseval`, in the safe
directions: `Real.sqrt (energy c) = ‖f‖_{L²(𝕋^d)}` by
`LeanNumDetect.unitTorusL2Norm_eq_sqrt` (an equality exactly because `hs` gives
pairwise distinct frequencies), and `‖f‖_{L^∞(𝕋^d)} ≤ ∑ i, ‖c i‖` by the
triangle inequality `LeanNumDetect.unitTorusLInfNorm_le`, with the
Cauchy--Schwarz step `LeanNumDetect.sum_norm_le_sqrt_card_mul_sqrt_sum_norm_sq`
(already inside the coefficient bound) producing the factor $\sqrt{|\Lambda^d|}$;
see `LeanNumDetect.unitTorusLInfNorm_le_sqrt_card_mul_unitTorusL2Norm` for the
combined one-step form. The distinctness `hs` is essential for the `L²` bound:
with repeated frequencies the presented polynomial can have larger `L²` norm
than `Real.sqrt (energy c)`, and the conclusion genuinely fails
(`LeanNumDetect.parseval_fails_of_repeated_frequencies`). -/
theorem interpolation_coefficients_of_fullColumnRank {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    [DecidableEq ι] {d : ℕ} (s : ρ → Fin d → ℤ) (hs : Function.Injective s)
    (V : Matrix ρ ι ℂ) (hinj : Function.Injective V.toEuclideanLin)
    (w : ι → ℂ) :
    ∃ c : ρ → ℂ, (∀ k, c ⬝ᵥ Vᵀ k = w k) ∧
      unitTorusL2Norm (unitTorusTrigPolynomial s c) ≤
        Real.sqrt (energy w) / matrixSingularValue V (Fintype.card ι - 1) ∧
      unitTorusLInfNorm (unitTorusTrigPolynomial s c) ≤
        Real.sqrt (Fintype.card ρ) * Real.sqrt (energy w) /
          matrixSingularValue V (Fintype.card ι - 1) := by
  obtain ⟨c, hinterp, hL2, hL1⟩ :=
    interpolation_coefficients_of_fullColumnRank_coefficientNorms V hinj w
  refine ⟨c, hinterp, ?_, ?_⟩
  · rw [unitTorusL2Norm_eq_sqrt hs c]
    show Real.sqrt (energy c) ≤
      Real.sqrt (energy w) / matrixSingularValue V (Fintype.card ι - 1)
    exact hL2
  · exact (unitTorusLInfNorm_le s c).trans hL1

/-- A cardinal interpolant with coefficient energy at most `1/a`. This is the
`w = e_j` corollary of NumDetect `lem:interpolation_via_svd`
(`interpolation_coefficients_of_fullColumnRank`), specialized to the frame
hypothesis: `‖w‖_2 = 1`, and `σ_min ^ 2 ≥ a` converts `1 / σ_min ≤ 1 / √a`
into `energy c ≤ 1 / a`. -/
theorem cardinal_coefficients_of_frame {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    [DecidableEq ι] (V : Matrix ρ ι ℂ) {a : ℝ} (ha : 0 < a)
    (hframe : ∀ v, a * energy v ≤ energy (V *ᵥ v)) (j : ι) :
    ∃ c : ρ → ℂ, (∀ k, c ⬝ᵥ Vᵀ k = if j = k then 1 else 0) ∧ energy c ≤ 1 / a := by
  have hV : ∀ u v : ι → ℂ, V *ᵥ u = V *ᵥ v → u = v := by
    intro u v huv
    have h0 : V *ᵥ (u - v) = (0 : ρ → ℂ) := by
      rw [Matrix.mulVec_sub, huv, sub_self]
    have hed : energy (u - v) = 0 := by
      by_contra hne
      have hpos : 0 < energy (u - v) := by
        apply energy_pos (u - v)
        intro hd
        apply hne
        rw [hd]
        simp [energy]
      have hle : a * energy (u - v) ≤ 0 := by
        have h := hframe (u - v)
        rw [h0] at h
        simp [energy] at h
        exact h
      have hz : a * energy (u - v) = 0 :=
        le_antisymm hle (mul_nonneg ha.le (energy_nonneg (u - v)))
      exact absurd hz (mul_ne_zero ha.ne' (ne_of_gt hpos))
    have hd : u - v = 0 := by
      by_contra hne
      exact (energy_pos (u - v) hne).ne' hed
    exact sub_eq_zero.mp hd
  have hinj : Function.Injective V.toEuclideanLin :=
    toEuclideanLin_injective_of_mulVec_injective V hV
  have hw : energy (fun k : ι => if j = k then (1:ℂ) else 0) = 1 := by
    have hr : ∀ i : ι, ‖(if j = i then (1:ℂ) else 0)‖ ^ 2 =
        (if j = i then (1:ℝ) else 0) := by
      intro i
      by_cases hij : j = i <;> simp [hij]
    simp only [energy, hr]
    exact Fintype.sum_ite_eq j fun _ => (1:ℝ)
  have hσpos : 0 < matrixSingularValue V (Fintype.card ι - 1) := by
    apply V.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos.mp hinj
    simpa using Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨j⟩) Nat.zero_lt_one
  obtain ⟨c, hinterp, hL2, _⟩ :=
    interpolation_coefficients_of_fullColumnRank_coefficientNorms V hinj
      (fun k => if j = k then 1 else 0)
  refine ⟨c, hinterp, ?_⟩
  rw [hw, Real.sqrt_one] at hL2
  have h2 : energy c ≤ 1 / matrixSingularValue V (Fintype.card ι - 1) ^ 2 := by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (div_nonneg (by norm_num) hσpos.le)).2 hL2
    rwa [Real.sq_sqrt (energy_nonneg c), div_pow, one_pow] at hsq
  -- The frame bound gives `σ_min ^ 2 ≥ a`.
  have h3 : a ≤ (matrixSingularValue V (Fintype.card ι - 1)) ^ 2 := by
    have hi : Fintype.card ι - 1 < Module.finrank ℂ (EuclideanSpace ℂ ι) := by
      simpa using Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨j⟩) Nat.zero_lt_one
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
    have hS : Module.finrank ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ ι)) =
        Fintype.card ι - 1 + 1 := by
      rw [finrank_top, finrank_euclideanSpace]
      omega
    have hbound : ∀ x ∈ (⊤ : Submodule ℂ (EuclideanSpace ℂ ι)),
        Real.sqrt a * ‖x‖ ≤ ‖V.toEuclideanLin x‖ := by
      intro x hx
      have h1 : ‖x‖ ^ 2 = energy (WithLp.ofLp x) := by
        show ‖(WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℂ ι)‖ ^ 2 = _
        exact norm_sq_toLp_eq_energy _
      have hVx : ‖V.toEuclideanLin x‖ ^ 2 = energy (V *ᵥ WithLp.ofLp x) := by
        show ‖(WithLp.toLp 2 (V *ᵥ WithLp.ofLp x) : EuclideanSpace ℂ ρ)‖ ^ 2 = _
        exact norm_sq_toLp_eq_energy _
      apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg x))
        (norm_nonneg _)).mp
      rw [mul_pow, Real.sq_sqrt ha.le, h1, hVx]
      exact hframe _
    have hle := le_singularValues_of_subspace V.toEuclideanLin hi ⊤ hS hbound
    have hσle : 0 ≤ matrixSingularValue V (Fintype.card ι - 1) := by
      show 0 ≤ V.toEuclideanLin.singularValues (Fintype.card ι - 1)
      exact V.toEuclideanLin.singularValues_nonneg _
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg a) hσle).2 hle
    rwa [Real.sq_sqrt ha.le] at hsq
  exact h2.trans (one_div_le_one_div_of_le ha h3)

end SegmentedVDM
