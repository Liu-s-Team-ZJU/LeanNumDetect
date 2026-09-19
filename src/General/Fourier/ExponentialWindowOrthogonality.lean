import General.Fourier.WeightedOrthogonality
import General.Fourier.CosineWindowOrthogonality
import General.Fourier.CosineWindowTransform
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace LeanNumDetect

theorem exponential_node_inner (x y t : ℝ) (a b : ℂ) :
    star (a * Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))) *
      (b * Complex.exp (Complex.I * ((t*y : ℝ) : ℂ))) =
      star a * b * Complex.exp (Complex.I * ((t*(y-x) : ℝ) : ℂ)) := by
  rw [star_mul, Complex.star_def, ← Complex.exp_conj]
  have he : (starRingEnd ℂ) (Complex.I * ((t*x : ℝ) : ℂ)) =
      -(Complex.I * ((t*x : ℝ) : ℂ)) := by simp
  rw [he]
  have ha : Complex.I * ((t*(y-x) : ℝ) : ℂ) =
      -(Complex.I * ((t*x : ℝ) : ℂ)) + Complex.I * ((t*y : ℝ) : ℂ) := by
    push_cast
    ring
  rw [ha, Complex.exp_add]
  ring

/-- Pairwise separation eliminates the cross energy of two complete exponential sums. -/
theorem exponentialSum_weighted_cross_hasSum {s q r : ℕ} (hs : 1 ≤ s) {eta T : ℝ}
    (heta : 0 < eta) (hT : 0 < T) (xi : Fin q → ℝ) (yi : Fin r → ℝ)
    (d : Fin q → ℂ) (e : Fin r → ℂ)
    (hsep : ∀ i j (p : ℤ), eta < |yi j - xi i - 2*Real.pi*p|) (shift : ℝ) :
    HasSum (fun k : ℤ => (cosineWeight s eta T ((k : ℝ)-shift) : ℂ) *
      (star (exponentialSum xi d ((k : ℝ)-shift)) * exponentialSum yi e ((k : ℝ)-shift))) 0 := by
  have hp (i : Fin q) (j : Fin r) :=
    (cosineWeight_cross_torus_hasSum hs heta hT (hsep i j) shift).mul_left (star (d i)*e j)
  have hh := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ => hp i j))
  have he (t : ℝ) : star (exponentialSum xi d t) * exponentialSum yi e t =
      ∑ i, ∑ j, star (d i)*e j*Complex.exp (Complex.I * ((t*(yi j-xi i) : ℝ) : ℂ)) := by
    unfold exponentialSum
    rw [star_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, exponential_node_inner]
  convert! hh using 1
  · funext k
    rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp
/-- Exact decoupling for a finite family of separated clumps. -/
theorem clump_weighted_energy_hasSum {A s : ℕ} (hs : 1 ≤ s) {eta T : ℝ}
    (heta : 0 < eta) (hT : 0 < T) (size : Fin A → ℕ)
    (xi : (a : Fin A) → Fin (size a) → ℝ)
    (d : (a : Fin A) → Fin (size a) → ℂ)
    (hsep : ∀ a b, a ≠ b → ∀ i j (p : ℤ), eta < |xi b j-xi a i-2*Real.pi*p|)
    (shift : ℝ) (E : Fin A → ℝ)
    (hlocal : ∀ a, HasSum (fun k : ℤ => cosineWeight s eta T ((k : ℝ)-shift) *
      ‖exponentialSum (xi a) (d a) ((k : ℝ)-shift)‖^2) (E a)) :
    HasSum (fun k : ℤ => cosineWeight s eta T ((k : ℝ)-shift) *
      ‖∑ a, exponentialSum (xi a) (d a) ((k : ℝ)-shift)‖^2) (∑ a, E a) := by
  apply LeanNumDetect.weighted_sum_energy_hasSum _ _ E hlocal
  intro a b hab
  have hh := Complex.hasSum_re (exponentialSum_weighted_cross_hasSum hs heta hT
    (xi a) (xi b) (d a) (d b) (hsep a b hab) shift)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.zero_re] using hh
end LeanNumDetect
