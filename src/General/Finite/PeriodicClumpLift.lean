import General.Finite.FiniteRealGeometry
set_option autoImplicit false
namespace LeanNumDetect

/-- A sufficiently short clump in periodic distance admits real representatives
whose ordinary diameter has the same bound. -/
theorem periodic_clump_lift {q : ℕ} (hq : 0 < q) (x : Fin q → ℝ) {w : ℝ}
    (hw : 0 ≤ w) (hshort : 3*w < 2*Real.pi)
    (hpair : ∀ i j, ∃ p : ℤ, |x i-x j-2*Real.pi*p| ≤ w) :
    ∃ p : Fin q → ℤ,
      Metric.diam (Set.range (fun j => x j-2*Real.pi*p j)) ≤ w := by
  classical
  let j₀ : Fin q := ⟨0,hq⟩
  choose p hp using fun j => hpair j j₀
  let y j := x j-2*Real.pi*p j
  have hy (j : Fin q) : |y j-x j₀| ≤ w := by
    convert hp j using 1
    congr 1
    dsimp [y]
    ring
  have hd (i j : Fin q) : |y i-y j| ≤ w := by
    have htwo : |y i-y j| ≤ 2*w := by
      have he : y i-y j = (y i-x j₀)-(y j-x j₀) := by ring
      rw [he]
      exact (abs_sub _ _).trans (by linarith [hy i,hy j])
    obtain ⟨r,hr⟩ := hpair i j
    let k : ℤ := r-p i+p j
    have hk : |y i-y j-2*Real.pi*k| ≤ w := by
      convert hr using 1
      congr 1
      dsimp [y,k]
      push_cast
      ring
    have hab : 2*Real.pi*|(k : ℝ)| ≤ 3*w := by
      have he : 2*Real.pi*(k : ℝ) = (y i-y j)-(y i-y j-2*Real.pi*k) := by ring
      have hh := abs_sub (y i-y j) (y i-y j-2*Real.pi*k)
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
    simpa [hk0] using hk
  refine ⟨p, Metric.diam_le_of_forall_dist_le hw ?_⟩
  rintro a ⟨i,rfl⟩ b ⟨j,rfl⟩
  exact hd i j
end LeanNumDetect
