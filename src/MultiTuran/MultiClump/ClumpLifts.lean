import MultiTuran.Geometry

/-! # Simultaneous real lifts of all short clumps

Each clump uses its own cut. The resulting ordinary coordinate diameters are
bounded by the original torus diameter. No common small cube for all nodes
is asserted or needed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

theorem coordinateDistance_le_lInfDistance {d : ℕ} (x y : Point d) (q : Fin d) :
    torusCoordinateDistance (x q) (y q) ≤ torusLInfDistance x y := by
  simpa only [torusLInfDistance, Real.norm_eq_abs,
    abs_of_nonneg (torusCoordinateDistance_nonneg _ _)] using
    norm_le_pi_norm (fun r => torusCoordinateDistance (x r) (y r)) q

/-- Integer windings can be chosen simultaneously so that every short
clump has its original coordinate diameter as an ordinary real diameter. -/
theorem exists_simultaneous_clump_lifts {d n A : ℕ} (hn : 0 < n)
    (Y : Fin n → Point d) (label : Fin n → Fin A) {τ : ℝ}
    (hτ : 0 ≤ τ) (hshort : 3*τ < 2*Real.pi)
    (hsame : ∀ i j, label i = label j → torusLInfDistance (Y i) (Y j) ≤ τ) :
    ∃ p : Fin n → Fin d → ℤ, ∀ i j, label i = label j → ∀ q,
      |(Y i q - 2*Real.pi*p i q) - (Y j q - 2*Real.pi*p j q)| ≤ τ := by
  classical
  let anchor : Fin A → Fin n := fun a =>
    if h : ∃ j, label j = a then h.choose else ⟨0,hn⟩
  have hanchor (i : Fin n) : label (anchor (label i)) = label i := by
    have h : ∃ j, label j = label i := ⟨i,rfl⟩
    simp only [anchor, dif_pos h]
    exact h.choose_spec
  have hwind (i : Fin n) (q : Fin d) : ∃ p : ℤ,
      |Y i q - Y (anchor (label i)) q - 2*Real.pi*p| ≤ τ := by
    obtain ⟨p,hp⟩ := exists_winding_eq_torusCoordinateDistance
      (Y i q) (Y (anchor (label i)) q)
    refine ⟨p, ?_⟩
    rw [← hp]
    exact (coordinateDistance_le_lInfDistance _ _ q).trans
      (hsame i (anchor (label i)) (hanchor i).symm)
  choose p hp using hwind
  refine ⟨p, ?_⟩
  intro i j hij q
  let u : ℝ := Y i q - 2*Real.pi*p i q
  let v : ℝ := Y j q - 2*Real.pi*p j q
  have hui : |u - Y (anchor (label i)) q| ≤ τ := by
    calc
      _ = |Y i q-Y (anchor (label i)) q-2*Real.pi*p i q| := by
        congr 1
        dsimp [u]
        ring
      _ ≤ τ := hp i q
  have hvj : |v - Y (anchor (label i)) q| ≤ τ := by
    rw [hij]
    calc
      _ = |Y j q-Y (anchor (label j)) q-2*Real.pi*p j q| := by
        congr 1
        dsimp [v]
        ring
      _ ≤ τ := hp j q
  have htwo : |u-v| ≤ 2*τ := by
    have he : u-v = (u-Y (anchor (label i)) q)-(v-Y (anchor (label i)) q) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  obtain ⟨r,hr⟩ := exists_winding_eq_torusCoordinateDistance (Y i q) (Y j q)
  have hrτ : |Y i q-Y j q-2*Real.pi*r| ≤ τ := by
    rw [← hr]
    exact (coordinateDistance_le_lInfDistance _ _ q).trans (hsame i j hij)
  let k : ℤ := r-p i q+p j q
  have hk : |u-v-2*Real.pi*k| ≤ τ := by
    convert hrτ using 1
    congr 1
    dsimp [u,v,k]
    push_cast
    ring
  have hab : 2*Real.pi*|(k : ℝ)| ≤ 3*τ := by
    have he : 2*Real.pi*(k : ℝ) = (u-v)-(u-v-2*Real.pi*k) := by ring
    have hh := abs_sub (u-v) (u-v-2*Real.pi*k)
    rw [← he, abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)] at hh
    linarith
  have hk0 : k = 0 := by
    by_contra hne
    have hi : (1 : ℝ) ≤ |(k : ℝ)| := by
      by_cases hkpos : 0 < k
      · rw [abs_of_pos (by exact_mod_cast hkpos)]
        exact_mod_cast (show 1 ≤ k by omega)
      · rw [abs_of_neg (by exact_mod_cast (show k < 0 by omega))]
        exact_mod_cast (show (1 : ℤ) ≤ -k by omega)
    nlinarith [Real.pi_pos]
  simpa only [hk0, Int.cast_zero, mul_zero, sub_zero] using hk

theorem clump_shortness_of_dimension_bound {d : ℕ} (hd : 2 ≤ d) {τ : ℝ}
    (hτ : τ ≤ Real.pi/(2*(d : ℝ))) : 3*τ < 2*Real.pi := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hτ' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2*d)).mp hτ
  nlinarith [Real.pi_pos]

end
end LeanNumDetect.MultiTuran.MultiClump
