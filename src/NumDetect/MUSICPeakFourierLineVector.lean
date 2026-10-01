import NumDetect.SegmentedMUSICGrowth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WithLp
namespace LeanNumDetect
namespace NumDetect
noncomputable section

theorem dot_add_smul (d : ℕ) (ω y u : Point d) (t : ℝ) :
    dot ω (y + t • u) = dot ω y + t * dot ω u := by
  simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem hasDerivAt_fourierPhase (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * ((a + s * b : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((a + t * b : ℝ) : ℂ)) * (Complex.I * (b : ℂ))) t := by
  have hreal : HasDerivAt (fun s : ℝ => a + s * b) b t := by
    simpa using ((hasDerivAt_id t).mul_const b).const_add a
  have hcomplex : HasDerivAt (fun s : ℝ => ((a + s * b : ℝ) : ℂ)) (b : ℂ) t :=
    hreal.ofReal_comp
  exact (hcomplex.const_mul Complex.I).cexp

theorem steeringCoordinate_hasDerivAt_line
    {d : ℕ} {ι : Type*} (frequency : ι → Point d)
    (y u : Point d) (i : ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ => steeringVector frequency (y + s • u) i)
      (steeringVector frequency (y + t • u) i *
        (Complex.I * (dot (frequency i) u : ℂ))) t := by
  have h := hasDerivAt_fourierPhase
    (dot (frequency i) y) (dot (frequency i) u) t
  simpa only [steeringVector, dot_add_smul] using h

theorem normalizedSteeringCoordinate_mul_hasDerivAt_line
    {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (y u : Point d)
    (C : ι → ℂ) (i : ι) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => C i * normalizedSteering frequency (y + s • u) i)
      (C i * (Complex.I * (dot (frequency i) u : ℂ)) *
        normalizedSteering frequency (y + t • u) i) t := by
  let κ : ℂ := (Real.sqrt (Fintype.card ι : ℝ) : ℂ)⁻¹
  have h := (steeringCoordinate_hasDerivAt_line frequency y u i t).const_mul (C i * κ)
  simpa [normalizedSteering, steeringVector_norm_eq_sqrt_card, κ,
    mul_assoc, mul_comm, mul_left_comm] using h

theorem normalizedSteeringVector_mul_hasDerivAt_line
    {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (y u : Point d)
    (C : ι → ℂ) (t : ℝ) :
    letI : AddCommGroup (PiLp 2 (fun _ : ι => ℂ)) :=
      (PiLp.normedAddCommGroup 2 (fun _ : ι => ℂ)).toAddCommGroup
    letI : Module ℝ (PiLp 2 (fun _ : ι => ℂ)) :=
      (PiLp.normedSpace 2 ℝ (fun _ : ι => ℂ)).toModule
    letI : TopologicalSpace (PiLp 2 (fun _ : ι => ℂ)) :=
      (PiLp.normedAddCommGroup 2 (fun _ : ι => ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    HasDerivAt
      (fun s : ℝ => toLp 2
        (fun i => C i * normalizedSteering frequency (y + s • u) i))
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℂ)).symm (fun i =>
        C i * (Complex.I * (dot (frequency i) u : ℂ)) *
          normalizedSteering frequency (y + t • u) i)) t := by
  have hpi : HasDerivAt
      (fun s : ℝ => fun i =>
        C i * normalizedSteering frequency (y + s • u) i)
      (fun i => C i * (Complex.I * (dot (frequency i) u : ℂ)) *
        normalizedSteering frequency (y + t • u) i) t :=
    hasDerivAt_pi.mpr fun i =>
      normalizedSteeringCoordinate_mul_hasDerivAt_line frequency y u C i t
  have houter := PiLp.hasFDerivAt_toLp (p := 2) (𝕜 := ℝ)
    (fun i => C i * normalizedSteering frequency (y + t • u) i)
  have hcomp := houter.comp_hasDerivAt t hpi
  convert hcomp using 1 <;> rfl

end
end NumDetect
end LeanNumDetect
