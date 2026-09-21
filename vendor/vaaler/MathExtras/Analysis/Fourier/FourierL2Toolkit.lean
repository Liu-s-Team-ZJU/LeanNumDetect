/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AnalyticNT.Diophantine.FourierL1L2Agreement

/-!
# A consolidated L²-Fourier toolkit (Plancherel isometry + L¹∩L² bridge)

Reusable wrappers around Mathlib's L²-Fourier isometry `MeasureTheory.Lp.fourierTransformₗᵢ`,
built so that Fourier-analytic residuals (Vaaler J-FT, Cesàro/Plancherel, the L²-only tail FTs)
do not re-derive the same plumbing.  See the `/fourier` skill for when to use each piece.

The load-bearing facts:
* **`eLpNorm_lpFT_sub_eq`** — the isometry preserves the L² distance, so the Fourier-side
  convergence `eLpNorm(𝓕 g_N − 𝓕 G) → 0` is *literally equal* to the spatial `eLpNorm(g_N − G)`:
  this collapses every "limit through 𝓕" obligation to its spatial counterpart, leaving only the
  *identity* of the limit (what `𝓕 G` IS) as genuine content.
* **`lpFT_coeFn_ae_eq_fourierIntegral`** — on `L¹∩L²`, the L² transform's coeFn agrees a.e. with
  the pointwise integral `𝓕` (the proven linchpin `fourierIntegral_ae_eq_fourierTransformₗᵢ`).
* **`lpFT_toLp_add`** — `𝓕` is additive, so `𝓕(L¹ core + L² tail)` splits (the route around
  `f ∉ L¹`).

No `axiom`, no `sorry`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform

namespace MathExtras.Analysis.Fourier.FourierL2Toolkit

/-- The L²-Fourier transform of an `L²` function `f`, packaged as an `Lp ℂ 2` element. -/
noncomputable def lpFT (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f)

/-- **Plancherel:** the L² transform preserves the `Lp` norm. -/
theorem norm_lpFT (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    ‖lpFT f hf‖ = ‖hf.toLp f‖ :=
  (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).norm_map _

/-- **L¹∩L² bridge (re-export of the proven linchpin):** the L² transform's coeFn agrees a.e.
with the pointwise Fourier integral `𝓕 f`. -/
theorem lpFT_coeFn_ae_eq_fourierIntegral (f : ℝ → ℂ)
    (hf1 : Integrable f (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    (⇑(lpFT f hf2) : ℝ → ℂ) =ᵐ[volume] 𝓕 f :=
  MathExtras.NumberTheory.Analysis.FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ
    hf1 hf2

/-- **Additivity on `Lp`:** `𝓕(a + b) = 𝓕 a + 𝓕 b` for the isometry. -/
theorem lpFT_add (a b : Lp ℂ 2 (volume : Measure ℝ)) :
    MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (a + b)
      = MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ a + MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ b :=
  map_add _ a b

/-- **The L¹+L² split (the route around `f ∉ L¹`):** if `f = g + h` as `Lp` classes (`g` the
`L¹∩L²` core, `h` the `L²`-only tail), then `𝓕 f` splits.  Combine with
`lpFT_coeFn_ae_eq_fourierIntegral` on `g` and an `L²`-transform computation on `h`. -/
theorem lpFT_toLp_add (f g h : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hh : MemLp h 2 (volume : Measure ℝ)) (hsum : f = fun x => g x + h x) :
    lpFT f hf
      = MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hg.toLp g)
        + MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hh.toLp h) := by
  have hae : f =ᵐ[volume] (fun x => g x + h x) :=
    Filter.Eventually.of_forall (fun x => by rw [hsum])
  have htoLp : hf.toLp f = hg.toLp g + hh.toLp h := by
    rw [← MemLp.toLp_add hg hh, MemLp.toLp_eq_toLp_iff hf (hg.add hh)]
    exact hae
  unfold lpFT
  rw [htoLp, lpFT_add]

/-- **The isometry preserves the L² distance (the killer lemma).**

`eLpNorm(⇑(𝓕 a) − ⇑(𝓕 b)) = eLpNorm(⇑a − ⇑b)`.  Consequently any Fourier-side `eLpNorm → 0`
goal equals its spatial counterpart, so "passing a limit through `𝓕`" is free; only the
*value* of the limit transform remains genuine content. -/
theorem eLpNorm_lpFT_sub_eq (a b : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (fun x => (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ a) x
        - (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ b) x) 2 (volume : Measure ℝ)
      = eLpNorm (fun x => a x - b x) 2 (volume : Measure ℝ) := by
  set Fa := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ a
  set Fb := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ b
  -- Rewrite both pointwise differences as the coeFn of the `Lp` difference.
  have hFsub : (fun x => (Fa : ℝ → ℂ) x - (Fb : ℝ → ℂ) x) =ᵐ[volume] ⇑(Fa - Fb) :=
    (MeasureTheory.Lp.coeFn_sub Fa Fb).symm
  have habsub : (fun x => (a : ℝ → ℂ) x - (b : ℝ → ℂ) x) =ᵐ[volume] ⇑(a - b) :=
    (MeasureTheory.Lp.coeFn_sub a b).symm
  rw [eLpNorm_congr_ae hFsub, eLpNorm_congr_ae habsub]
  -- `Fa - Fb = 𝓕 (a - b)`, and `𝓕` is an isometry, so the `Lp` norms agree; eLpNorms too.
  have hmap : Fa - Fb = MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (a - b) := by
    simp only [Fa, Fb, ← map_sub]
  have hnorm : ‖Fa - Fb‖ = ‖a - b‖ := by
    rw [hmap]; exact (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).norm_map _
  -- `‖·‖ = (eLpNorm ⇑· 2).toReal`, both finite ⟹ eLpNorms equal.
  have h1 : (eLpNorm (⇑(Fa - Fb)) 2 volume).toReal = (eLpNorm (⇑(a - b)) 2 volume).toReal := by
    rw [← MeasureTheory.Lp.norm_def, ← MeasureTheory.Lp.norm_def]; exact hnorm
  have hne1 : eLpNorm (⇑(Fa - Fb)) 2 volume ≠ ⊤ := (MeasureTheory.Lp.memLp _).eLpNorm_ne_top
  have hne2 : eLpNorm (⇑(a - b)) 2 volume ≠ ⊤ := (MeasureTheory.Lp.memLp _).eLpNorm_ne_top
  exact (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp h1

/-- **Limit through `𝓕` (the directly-usable convergence form).**

If `g N → G` in `L²` (`eLpNorm(g N − G) 2 → 0`, with all `MemLp`), then the L² transforms
converge: `eLpNorm(⇑(𝓕 (g N)) − ⇑(𝓕 G)) 2 → 0`.  Immediate from `eLpNorm_lpFT_sub_eq` (the two
`eLpNorm`s are equal for every `N`). -/
theorem tendsto_eLpNorm_lpFT_of_tendsto
    {g : ℕ → ℝ → ℂ} {G : ℝ → ℂ}
    (hg : ∀ N, MemLp (g N) 2 (volume : Measure ℝ)) (hG : MemLp G 2 (volume : Measure ℝ))
    (h : Tendsto (fun N => eLpNorm (fun x => g N x - G x) 2 (volume : Measure ℝ))
      atTop (𝓝 (0 : ℝ≥0∞))) :
    Tendsto (fun N => eLpNorm
        (fun x => (⇑(lpFT (g N) (hg N)) : ℝ → ℂ) x - (⇑(lpFT G hG) : ℝ → ℂ) x)
        2 (volume : Measure ℝ)) atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hpt : ∀ N, eLpNorm
      (fun x => (⇑(lpFT (g N) (hg N)) : ℝ → ℂ) x - (⇑(lpFT G hG) : ℝ → ℂ) x) 2 volume
      = eLpNorm (fun x => g N x - G x) 2 volume := by
    intro N
    have := eLpNorm_lpFT_sub_eq ((hg N).toLp (g N)) (hG.toLp G)
    -- rewrite the `toLp` coeFns back to `g N`, `G`.
    refine (this).trans ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hg N).coeFn_toLp, hG.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
  simp only [hpt]
  exact h

end MathExtras.Analysis.Fourier.FourierL2Toolkit
