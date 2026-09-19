import General.SpectralPerturbation.PolynomialRootMatching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Quantitative matching inside unions of spectral discs

The graph joining intersecting discs has simple paths of at most $n-1$ edges.
Combining this diameter bound with preservation of root multiplicities gives
the factor $2n-1$ in the spectral matching estimate.
-/

noncomputable section
open Set
namespace LeanNumDetect

/-- Graph of intersecting closed discs with a common radius. -/
def spectralDiscGraph {n : ℕ} (a : Fin n → ℂ) (r : ℝ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ dist (a i) (a j) ≤ 2 * r
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by simpa only [dist_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

theorem spectralDiscGraph_reachable_of_near {n : ℕ}
    (a : Fin n → ℂ) (r : ℝ) (i j : Fin n) (w : ℂ)
    (hi : dist w (a i) ≤ r) (hj : dist w (a j) ≤ r) :
    (spectralDiscGraph a r).Reachable i j := by
  by_cases h : i = j
  · subst j; exact .rfl
  · apply SimpleGraph.Adj.reachable
    refine ⟨h, ?_⟩
    have := dist_triangle (a i) w (a j)
    rw [dist_comm (a i) w] at this
    linarith

/-- Removing repetitions from a path bounds its length by the number of centers. -/
theorem spectralDiscGraph_diameter {n : ℕ}
    (a : Fin n → ℂ) (r : ℝ) (hr : 0 ≤ r) (i j : Fin n)
    (h : (spectralDiscGraph a r).Reachable i j) :
    dist (a i) (a j) ≤ 2 * ((n : ℝ) - 1) * r := by
  have hwalk {u v : Fin n} (p : (spectralDiscGraph a r).Walk u v) :
      dist (a u) (a v) ≤ (p.length : ℝ) * (2 * r) := by
    induction p with
    | nil => simp
    | @cons u v w huv p ih =>
      calc
        dist (a u) (a w) ≤ dist (a u) (a v) + dist (a v) (a w) := dist_triangle _ _ _
        _ ≤ 2 * r + (p.length : ℝ) * (2 * r) := add_le_add huv.2 ih
        _ = _ := by simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]; ring
  obtain ⟨p, hp⟩ := h.exists_isPath
  have hlen : (p.length : ℝ) + 1 ≤ n := by
    have hnat : p.length < n := by simpa using hp.length_lt
    exact_mod_cast (Nat.succ_le_iff.mpr hnat)
  have hdist := hwalk p
  nlinarith

/-- The spectral-disc homotopy estimate, including all root multiplicities. -/
theorem spectral_disc_homotopy_matching {n : ℕ}
    (a z : Fin n → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (p : ℝ → ℂ → ℂ) (hp : ContinuousOn p (Icc 0 1))
    (hp0 : p 0 = rootProduct a) (hp1 : p 1 = rootProduct z)
    (hroots : ∀ t ∈ Icc (0 : ℝ) 1, ∃ b : Fin n → ℂ,
      p t = rootProduct b ∧ ∀ j, ∃ i, dist (b j) (a i) ≤ r) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i,
      ‖a i - z (σ i)‖ ≤ (2 * (n : ℝ) - 1) * r := by
  obtain ⟨σ, hσ⟩ := rootProduct_homotopy_matching a z r hr
    (spectralDiscGraph a r).Reachable (fun _ => .rfl)
    (fun h₁ h₂ => h₁.trans h₂) (spectralDiscGraph_reachable_of_near a r)
    p hp hp0 hp1 hroots
  refine ⟨σ, fun i => ?_⟩
  obtain ⟨j, hij, hj⟩ := hσ i
  have hd := spectralDiscGraph_diameter a r hr i j hij
  have ht := dist_triangle (a i) (a j) (z (σ i))
  rw [dist_comm (a j) (z (σ i))] at ht
  rw [← dist_eq_norm]
  linarith

end LeanNumDetect
