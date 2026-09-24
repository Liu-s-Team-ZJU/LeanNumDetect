import SegmentedVDM.TwoPoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SegmentedVDM

/-- The near/far split in NumDetect can be written as a single minimum. The
frequency budget is `T`, and `Δ` is any positive lower bound on the distances
inside the clump. -/
theorem neighbor_factor {T D Δ u : ℝ} (hT : 2 ≤ T) (hD : 0 < D)
    (hΔ : 0 < Δ) (hΔu : Δ ≤ |u|) (hu : |u| ≤ Real.pi / (2*D))
    (hscale : T*D*Δ ≤ Real.pi) :
    ∃ P : Packet 0 ⌊T⌋₊, P.value D 0 = 1 ∧ P.value D u = 0 ∧
      P.mass ≤ Real.sqrt 2 / (T*D*Δ/Real.pi) := by
  have hup : 0 < |u| := hΔ.trans_le hΔu
  have hTu : 2 ≤ Real.pi / (D*|u|) := by
    apply (le_div_iff₀ (by positivity)).2
    have h := (le_div_iff₀ (by positivity : 0 < 2*D)).mp hu
    nlinarith
  let t := min T (Real.pi / (D*|u|))
  have ht : 2 ≤ t := le_min hT hTu
  have htT : t ≤ T := min_le_left _ _
  have htU : t * D * |u| ≤ Real.pi := by
    have h := (le_div_iff₀ (by positivity : 0 < D*|u|)).mp (min_le_right T (Real.pi/(D*|u|)))
    simpa only [mul_assoc] using h
  have htΔ : T*D*Δ ≤ t*D*|u| := by
    dsimp [t]
    rw [min_mul_of_nonneg _ _ hD.le, min_mul_of_nonneg _ _ hup.le]
    apply le_min
    · gcongr
    · have he : Real.pi / (D*|u|) * D * |u| = Real.pi := by field_simp
      rwa [he]
  let k := ⌊t⌋₊
  have hk : (k : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hkh : t/2 ≤ (k : ℝ) := floor_ge_half ht
  have hkT : k ≤ ⌊T⌋₊ := Nat.floor_mono htT
  have hphase : |(k : ℝ)*D*u| = (k : ℝ)*D*|u| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hD]
  have hhi : |(k : ℝ)*D*u| ≤ Real.pi := by
    rw [hphase]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hD.le) hup.le).trans htU
  have hlo : t*D*|u|/2 ≤ |(k : ℝ)*D*u| := by
    rw [hphase]
    convert! mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkh hD.le) hup.le using 1 <;> ring
  have hbπ : t*D*|u|/2 ≤ Real.pi/2 := by linarith
  have htpos : 0 ≤ t := by linarith
  have hden := exp_sub_one_lower (by positivity : 0 ≤ t*D*|u|/2) hbπ hlo hhi
  let z := Complex.exp (Complex.I * ((k*D*u : ℝ) : ℂ))
  let a := T*D*Δ/Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have hden' : Real.sqrt 2 * a ≤ ‖1-z‖ := by
    have he : 2*Real.sqrt 2/Real.pi*(t*D*|u|/2) = Real.sqrt 2/Real.pi*(t*D*|u|) := by ring
    rw [he] at hden
    rw [norm_sub_rev]
    have hh := mul_le_mul_of_nonneg_left htΔ (show 0 ≤ Real.sqrt 2 / Real.pi by positivity)
    have heq : Real.sqrt 2 * a = Real.sqrt 2 / Real.pi * (T*D*Δ) := by dsimp [a]; ring
    rw [heq]
    exact hh.trans hden

  have hz : z ≠ 1 := by
    intro h
    have hp : 0 < Real.sqrt 2 * a := by positivity
    simp [h] at hden'
    linarith
  refine ⟨(twoPoint k z).widen le_rfl hkT, twoPoint_at_zero k z hz D,
    twoPoint_vanishes k D u, ?_⟩
  rw [Packet.mass_widen, twoPoint_mass k z (by simp [z, Complex.norm_exp])]
  calc
    2 / ‖1-z‖ ≤ 2 / (Real.sqrt 2 * a) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden'
    _ = Real.sqrt 2 / a := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      field_simp
      nlinarith

/-- The pointwise near-neighbor factor `π v/(M D ‖u‖_{p'})` of the NumDetect
manuscript's `lem:neighborset_segmented`, flattened to `1` at the far nodes
`π v/(M D) < ‖u‖_{p'}`. The product in the conclusion of that lemma runs only
over the near neighbors `0 < ‖u‖_{p'} ≤ π v/(M D)`; every node costs at most `√2`
times this factor. -/
noncomputable def neighborScaleFactor {d : ℕ} (q : ENNReal) (v M D : ℝ) (u : Fin d → ℝ) : ℝ :=
  if LeanNumDetect.lpNorm q u ≤ Real.pi * v / (M * D)
  then Real.pi * v / (M * D * LeanNumDetect.lpNorm q u) else 1

theorem neighborScaleFactor_of_le {d : ℕ} {q : ENNReal} {v M D : ℝ} {u : Fin d → ℝ}
    (h : LeanNumDetect.lpNorm q u ≤ Real.pi * v / (M * D)) :
    neighborScaleFactor q v M D u = Real.pi * v / (M * D * LeanNumDetect.lpNorm q u) :=
  if_pos h

theorem neighborScaleFactor_of_lt {d : ℕ} {q : ENNReal} {v M D : ℝ} {u : Fin d → ℝ}
    (h : Real.pi * v / (M * D) < LeanNumDetect.lpNorm q u) :
    neighborScaleFactor q v M D u = 1 :=
  if_neg (not_le.mpr h)

end SegmentedVDM
