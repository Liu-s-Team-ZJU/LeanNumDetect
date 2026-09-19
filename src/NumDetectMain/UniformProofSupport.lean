import NumDetectMain.UniformDefinitions
import SegmentedVDM.NeighborFactors
import SegmentedVDM.Smoothing

/-!
Auxiliary finite Fourier constructions for the contiguous-grid results.

The packets below retain a finite presentation, rather than collecting equal
frequencies.  This makes products literal finite products and lets the final
cube average be estimated by the triangle inequality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- A finitely presented trigonometric polynomial with integer frequencies in
the centered cube `[-h,h]^d`. -/
structure CenteredPacket (d h : ℕ) where
  Index : Type
  finite : Fintype Index
  frequency : Index → Fin d → ℤ
  frequency_le : ∀ i k, (frequency i k).natAbs ≤ h
  coeff : Index → ℂ

attribute [instance] CenteredPacket.finite

namespace CenteredPacket

noncomputable def value {d h : ℕ} (P : CenteredPacket d h)
    (D : ℝ) (x : Point d) : ℂ :=
  ∑ i, P.coeff i * Complex.exp
    (Complex.I * ((D * ∑ k, (P.frequency i k : ℝ) * x k : ℝ) : ℂ))

noncomputable def mass {d h : ℕ} (P : CenteredPacket d h) : ℝ :=
  ∑ i, ‖P.coeff i‖

theorem mass_nonneg {d h : ℕ} (P : CenteredPacket d h) :
    0 ≤ P.mass :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Coordinate signs realizing the `ℓ¹` norm as a signed dot product. -/
def coordinateSign {d : ℕ} (x : Point d) (k : Fin d) : ℤ :=
  if 0 ≤ x k then 1 else -1

theorem coordinateSign_natAbs {d : ℕ} (x : Point d) (k : Fin d) :
    (coordinateSign x k).natAbs = 1 := by
  simp only [coordinateSign]
  split_ifs <;> simp

theorem coordinateSign_dot {d : ℕ} (x : Point d) :
    (∑ k, (coordinateSign x k : ℝ) * x k) = l1Norm x := by
  unfold l1Norm
  apply Finset.sum_congr rfl
  intro k _
  simp only [coordinateSign]
  split_ifs with hk
  · simp [abs_of_nonneg hk]
  · have hk' : x k ≤ 0 := le_of_not_ge hk
    simp [abs_of_nonpos hk']

/-- Lift a scalar packet to the line in signed coordinate direction `sign(x)`. -/
def liftScalar {d K : ℕ} (x : Point d) (P : SegmentedVDM.Packet 0 K) :
    CenteredPacket d K where
  Index := P.Index
  finite := P.finite
  frequency i k := (P.coarse i : ℤ) * coordinateSign x k
  frequency_le i k := by
    rw [Int.natAbs_mul, coordinateSign_natAbs, mul_one]
    exact P.coarse_le i
  coeff := P.coeff

theorem mass_liftScalar {d K : ℕ} (x : Point d) (P : SegmentedVDM.Packet 0 K) :
    (liftScalar x P).mass = P.mass := rfl

theorem value_liftScalar {d K : ℕ} (x y : Point d)
    (P : SegmentedVDM.Packet 0 K) (D : ℝ) :
    (liftScalar x P).value D y =
      P.value D (∑ k, (coordinateSign x k : ℝ) * y k) := by
  unfold value SegmentedVDM.Packet.value liftScalar
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  congr 2
  push_cast
  have hf : P.fine i = 0 := Nat.le_zero.mp (P.fine_le i)
  rw [hf, Nat.cast_zero, add_zero]
  have hsum :
      (∑ k, (P.coarse i : ℝ) * (coordinateSign x k : ℝ) * y k) =
        (P.coarse i : ℝ) *
          ∑ k, (coordinateSign x k : ℝ) * y k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  ring

/-- Spatial translation changes only coefficient phases. -/
def translate {d h : ℕ} (P : CenteredPacket d h) (D : ℝ) (y : Point d) :
    CenteredPacket d h :=
  { P with
    coeff := fun i => P.coeff i * Complex.exp
      (-Complex.I * ((D * ∑ k, (P.frequency i k : ℝ) * y k : ℝ) : ℂ)) }

theorem mass_translate {d h : ℕ} (P : CenteredPacket d h) (D : ℝ) (y : Point d) :
    (P.translate D y).mass = P.mass := by
  apply Finset.sum_congr rfl
  intro i _
  simp [translate, Complex.norm_exp]

theorem value_translate {d h : ℕ} (P : CenteredPacket d h)
    (D : ℝ) (y x : Point d) :
    (P.translate D y).value D x = P.value D (x - y) := by
  change
    (∑ i : P.Index, (P.coeff i *
      Complex.exp (-Complex.I *
        ((D * ∑ k, (P.frequency i k : ℝ) * y k : ℝ) : ℂ))) *
      Complex.exp (Complex.I *
        ((D * ∑ k, (P.frequency i k : ℝ) * x k : ℝ) : ℂ))) =
    ∑ i : P.Index, P.coeff i * Complex.exp
      (Complex.I *
        ((D * ∑ k, (P.frequency i k : ℝ) * (x - y) k : ℝ) : ℂ))
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [Pi.sub_apply]
  push_cast
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- Product of a finite family of packets, with the support boxes added. -/
def prod {d K : ℕ} {q : Type} [Fintype q] [DecidableEq q]
    (P : q → CenteredPacket d K) :
    CenteredPacket d (Fintype.card q * K) where
  Index := (i : q) → (P i).Index
  finite := inferInstance
  frequency a k := ∑ i, (P i).frequency (a i) k
  frequency_le a k := by
    calc
      (∑ i, (P i).frequency (a i) k).natAbs
          ≤ ∑ i, ((P i).frequency (a i) k).natAbs :=
        Int.natAbs_sum_le Finset.univ _
      _ ≤ ∑ _i : q, K :=
        Finset.sum_le_sum fun i _ => (P i).frequency_le (a i) k
      _ = Fintype.card q * K := by simp
  coeff a := ∏ i, (P i).coeff (a i)

theorem mass_prod {d K : ℕ} {q : Type} [Fintype q] [DecidableEq q]
    (P : q → CenteredPacket d K) :
    (prod P).mass = ∏ i, (P i).mass := by
  classical
  simp only [mass, prod, norm_prod]
  convert (Fintype.prod_sum (fun i a => ‖(P i).coeff a‖)).symm using 1

theorem value_prod {d K : ℕ} {q : Type} [Fintype q] [DecidableEq q]
    (P : q → CenteredPacket d K) (D : ℝ) (x : Point d) :
    (prod P).value D x = ∏ i, (P i).value D x := by
  classical
  change
    (∑ a : (i : q) → (P i).Index,
      (∏ i, (P i).coeff (a i)) * Complex.exp
        (Complex.I * ((D *
          ∑ k, ((∑ i, (P i).frequency (a i) k : ℤ) : ℝ) * x k : ℝ) : ℂ))) =
    ∏ i, ∑ a, (P i).coeff a * Complex.exp
      (Complex.I * ((D *
        ∑ k, ((P i).frequency a k : ℝ) * x k : ℝ) : ℂ))
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_mul_distrib]
  rw [← Complex.exp_sum]
  congr 1
  congr 2
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  simp_rw [Finset.mul_sum]

/-- The `ℓ¹` norm is subadditive under subtraction. -/
theorem l1Norm_sub_le {d : ℕ} (x y : Point d) :
    l1Norm (x - y) ≤ l1Norm x + l1Norm y := by
  unfold l1Norm
  simp only [Pi.sub_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => by
    simpa using abs_sub_le (x k) 0 (y k)

/-- Distinct points have strictly positive `ℓ¹` distance. -/
theorem l1Norm_sub_pos {d : ℕ} {x y : Point d} (hxy : x ≠ y) :
    0 < l1Norm (x - y) := by
  have hex : ∃ k, x k ≠ y k := by
    by_contra h
    apply hxy
    funext k
    exact not_ne_iff.mp (not_exists.mp h k)
  obtain ⟨k, hk⟩ := hex
  unfold l1Norm
  apply Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨k, Finset.mem_univ _, ?_⟩
  simpa only [Pi.sub_apply, abs_pos, sub_ne_zero] using hk

/-- The minimum `ℓ¹` separation of an injective finite node family is positive. -/
theorem minimumL1Separation_pos {d n : ℕ} (x : Fin n → Point d)
    (hn : 2 ≤ n) (hx : Function.Injective x) :
    0 < minimumL1Separation x hn := by
  rw [minimumL1Separation, minimumOverDistinctPairs,
    Finset.lt_inf'_iff (distinctPairs_nonempty hn)]
  intro ij hij
  have hne : ij.1 ≠ ij.2 := by
    simpa [distinctPairs] using hij
  exact l1Norm_sub_pos (fun h => hne (hx h))

/-- The minimum separation is bounded by every distinct pair distance. -/
theorem minimumL1Separation_le {d n : ℕ} (x : Fin n → Point d)
    (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    minimumL1Separation x hn ≤ l1Norm (x i - x j) := by
  rw [minimumL1Separation, minimumOverDistinctPairs,
    Finset.inf'_le_iff (distinctPairs_nonempty hn)]
  exact ⟨(i, j), by simp [distinctPairs, hij], le_rfl⟩

/-- Powers of the two-point mass constant in the form used by the manuscript. -/
theorem sqrtTwo_div_pow {q : ℕ} {θ : ℝ} :
    (Real.sqrt 2 / θ) ^ q =
      Real.sqrt ((2 : ℝ) ^ q) * θ⁻¹ ^ q := by
  rw [div_pow]
  have hsqrt :
      Real.sqrt ((2 : ℝ) ^ q) = (Real.sqrt 2) ^ q := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ q)]
    rw [← pow_mul, Nat.mul_comm q 2, pow_mul,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsqrt, inv_pow]
  simp only [div_eq_mul_inv]

/-- The square-root normalization that converts the packet estimate to the
constant in `eq:uniform-Vandermonde`. -/
theorem uniformPacket_normalization {n q : ℕ} {N θ : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hθ : 0 < θ) :
    Real.sqrt (1 / ((n : ℝ) * 2 ^ q) * N) * θ ^ q =
      Real.sqrt N / (Real.sqrt n * (Real.sqrt 2 / θ) ^ q) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) * 2 ^ q) * N)]
  rw [div_pow, Real.sq_sqrt hN.le, mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
  rw [div_pow, div_pow]
  simp only [← pow_mul]
  rw [Nat.mul_comm q 2, pow_mul (Real.sqrt 2) 2 q,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

/-- Enlarge the centered frequency box without changing the polynomial. -/
def widen {d h h' : ℕ} (P : CenteredPacket d h) (hh : h ≤ h') :
    CenteredPacket d h' where
  Index := P.Index
  finite := P.finite
  frequency := P.frequency
  frequency_le i k := (P.frequency_le i k).trans hh
  coeff := P.coeff

@[simp] theorem value_widen {d h h' : ℕ} (P : CenteredPacket d h)
    (hh : h ≤ h') (D : ℝ) (x : Point d) :
    (P.widen hh).value D x = P.value D x := rfl

@[simp] theorem mass_widen {d h h' : ℕ} (P : CenteredPacket d h)
    (hh : h ≤ h') :
    (P.widen hh).mass = P.mass := rfl

/-- For every anchor, multiply signed-direction two-point factors which
annihilate all other nodes.  Each factor uses bandwidth `floor (s/(2n))`. -/
theorem exists_centeredInterpolationPackets
    {d n s : ℕ} (hn : 2 ≤ n) {D Δ θ : ℝ} (x : Fin n → Point d)
    (hs : 4 * n ≤ s) (hD : 0 < D) (hΔ : 0 < Δ)
    (hsep : ∀ i j, i ≠ j → Δ ≤ l1Norm (x i - x j))
    (hdiam : ∀ i j, l1Norm (x i - x j) ≤ Real.pi / (2 * D))
    (hscale : ((s : ℝ) / (2 * n)) * D * Δ ≤ Real.pi)
    (htheta : ((s : ℝ) / (2 * n)) * D * Δ / Real.pi = θ) :
    ∃ P : Fin n → CenteredPacket d ((n - 1) * (s / (2 * n))),
      (∀ k, (P k).mass ≤
        Real.sqrt ((2 : ℝ) ^ (n - 1)) * θ⁻¹ ^ (n - 1)) ∧
      ∀ k j, (P k).value D (x j - x k) =
        if k = j then 1 else 0 := by
  classical
  let T : ℝ := (s : ℝ) / (2 * n)
  have hT : 2 ≤ T := by
    have hsR : (4 * n : ℝ) ≤ s := by exact_mod_cast hs
    have hnR : 0 < (n : ℝ) := by positivity
    dsimp [T]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
    nlinarith
  have hfloor : ⌊T⌋₊ = s / (2 * n) := by
    dsimp [T]
    rw [show (2 : ℝ) * n = ((2 * n : ℕ) : ℝ) by norm_num]
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hl1_nonneg (i j : Fin n) : 0 ≤ l1Norm (x i - x j) := by
    unfold l1Norm
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  let Other (k : Fin n) := {j : Fin n // j ≠ k}
  have hcard (k : Fin n) : Fintype.card (Other k) = n - 1 := by
    simp [Other]
  have hfactor (k : Fin n) (j : Other k) :
      ∃ Q : SegmentedVDM.Packet 0 ⌊T⌋₊,
        Q.value D 0 = 1 ∧
        Q.value D (l1Norm (x j.1 - x k)) = 0 ∧
        Q.mass ≤ Real.sqrt 2 / θ := by
    have hjk : j.1 ≠ k := j.2
    obtain ⟨Q, hQ0, hQj, hQmass⟩ := SegmentedVDM.neighbor_factor
      (u := l1Norm (x j.1 - x k)) hT hD hΔ
      (by simpa [abs_of_nonneg (hl1_nonneg j.1 k)] using hsep j.1 k hjk)
      (by simpa [abs_of_nonneg (hl1_nonneg j.1 k)] using hdiam j.1 k)
      (by simpa [T] using hscale)
    refine ⟨Q, hQ0, hQj, ?_⟩
    simpa [T, htheta] using hQmass
  choose Q hQ using hfactor
  let F (k : Fin n) (j : Other k) : CenteredPacket d ⌊T⌋₊ :=
    liftScalar (x j.1 - x k) (Q k j)
  have hbudget (k : Fin n) :
      Fintype.card (Other k) * ⌊T⌋₊ ≤ (n - 1) * (s / (2 * n)) := by
    rw [hcard, hfloor]
  let P (k : Fin n) : CenteredPacket d ((n - 1) * (s / (2 * n))) :=
    (prod (F k)).widen (hbudget k)
  refine ⟨P, ?_, ?_⟩
  · intro k
    simp only [P, mass_widen, mass_prod]
    calc
      ∏ j : Other k, (F k j).mass ≤
          ∏ _j : Other k, Real.sqrt 2 / θ :=
        Finset.prod_le_prod
          (fun j _ => mass_nonneg (F k j))
          (fun j _ => by simpa [F, mass_liftScalar] using (hQ k j).2.2)
      _ = (Real.sqrt 2 / θ) ^ (n - 1) := by
        rw [Finset.prod_const, Finset.card_univ, hcard]
      _ = Real.sqrt ((2 : ℝ) ^ (n - 1)) * θ⁻¹ ^ (n - 1) :=
        sqrtTwo_div_pow
  · intro k j
    simp only [P, value_widen, value_prod]
    by_cases hkj : k = j
    · subst j
      rw [if_pos rfl]
      apply Finset.prod_eq_one
      intro i _
      simp only [F, value_liftScalar]
      simpa using (hQ k i).1
    · rw [if_neg hkj]
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨j, Ne.symm hkj⟩ : Other k))
      simp only [F, value_liftScalar, coordinateSign_dot]
      exact (hQ k ⟨j, Ne.symm hkj⟩).2.1

/-- Integer points in the centered cube `[-b,b]^d`, represented by
coordinates in `{0, ..., 2b}`. -/
abbrev CubeIndex (d b : ℕ) := Fin d → Fin (2 * b + 1)

def cubeOffset {d b : ℕ} (q : CubeIndex d b) (k : Fin d) : ℤ :=
  (q k : ℤ) - b

theorem cubeOffset_natAbs_le {d b : ℕ} (q : CubeIndex d b) (k : Fin d) :
    (cubeOffset q k).natAbs ≤ b := by
  have hq : (q k).val ≤ 2 * b := by omega
  have habs : |cubeOffset q k| ≤ (b : ℤ) := by
    rw [abs_le]
    simp only [cubeOffset]
    omega
  rw [← Int.natCast_natAbs] at habs
  exact_mod_cast habs

/-- Convert a bounded integer to the corresponding finite index. -/
def boundedIntToFin {s : ℕ} (z : ℤ) (_hz0 : 0 ≤ z) (hzs : z ≤ s) :
    Fin (s + 1) :=
  ⟨z.toNat, by
    have : z.toNat ≤ s := Int.toNat_le.mpr hzs
    omega⟩

@[simp] theorem boundedIntToFin_val {s : ℕ} (z : ℤ)
    (hz0 : 0 ≤ z) (hzs : z ≤ s) :
    ((boundedIntToFin z hz0 hzs : Fin (s + 1)) : ℤ) = z := by
  simp only [boundedIntToFin]
  exact Int.toNat_of_nonneg hz0

/-- Add a centered smoothing frequency and then shift the result into the
nonnegative row cube `{0, ..., s}^d`. -/
def shiftedRow {d h b s : ℕ} (P : CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s)
    (i : P.Index) (q : CubeIndex d b) : UniformIndex d s :=
  fun k =>
    let z : ℤ := P.frequency i k + cubeOffset q k + (s / 2 : ℕ)
    boundedIntToFin z (by
      have hp := P.frequency_le i k
      have hq := cubeOffset_natAbs_le q k
      have hp' : |P.frequency i k| ≤ (h : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hp
      have hq' : |cubeOffset q k| ≤ (b : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hq
      have hlo : -(h : ℤ) ≤ P.frequency i k := (abs_le.mp hp').1
      have hqo : -(b : ℤ) ≤ cubeOffset q k := (abs_le.mp hq').1
      omega) (by
      have hp := P.frequency_le i k
      have hq := cubeOffset_natAbs_le q k
      have hp' : |P.frequency i k| ≤ (h : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hp
      have hq' : |cubeOffset q k| ≤ (b : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hq
      have hhi : P.frequency i k ≤ (h : ℤ) := (abs_le.mp hp').2
      have hqi : cubeOffset q k ≤ (b : ℤ) := (abs_le.mp hq').2
      have heven : 2 * (s / 2) = s := Nat.two_mul_div_two_of_even hseven
      omega)

theorem shiftedRow_frequency {d h b s : ℕ} (P : CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s)
    (i : P.Index) (q : CubeIndex d b) (k : Fin d) :
    ((shiftedRow P hsupport hseven i q k : ℕ) : ℤ) =
      P.frequency i k + cubeOffset q k + (s / 2 : ℕ) := by
  simp only [shiftedRow, boundedIntToFin_val]

theorem shiftedRow_injective {d h b s : ℕ} (P : CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s) (i : P.Index) :
    Function.Injective (shiftedRow P hsupport hseven i) := by
  intro q r hqr
  funext k
  have hk := congrArg (fun a => ((a k : ℕ) : ℤ)) hqr
  simp only [shiftedRow_frequency] at hk
  simp only [cubeOffset] at hk
  omega

/-- The normalized coefficient vector obtained by averaging one packet term
over a centered cube of shifts. -/
noncomputable def averagingVector {d h b s : ℕ} (P : CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s) (i : P.Index) :
    EuclideanSpace ℂ (UniformIndex d s) :=
  SegmentedVDM.spread (shiftedRow P hsupport hseven i)
    (fun _ => (1 / (((2 * b + 1) ^ d : ℕ) : ℂ)))

theorem averagingVector_norm {d h b s : ℕ} (P : CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s) (i : P.Index) :
    ‖averagingVector P hsupport hseven i‖ =
      1 / Real.sqrt (((2 * b + 1) ^ d : ℕ) : ℝ) := by
  have hN : (0 : ℝ) < ((2 * b + 1) ^ d : ℕ) := by positivity
  have hh := SegmentedVDM.norm_spread_sq
    (shiftedRow P hsupport hseven i)
    (shiftedRow_injective P hsupport hseven i)
    (fun _ => (1 / (((2 * b + 1) ^ d : ℕ) : ℂ)))
  change ‖averagingVector P hsupport hseven i‖ ^ 2 = _ at hh
  have hcard : Fintype.card (CubeIndex d b) = (2 * b + 1) ^ d := by
    simp [CubeIndex]
  have he : SegmentedVDM.energy
      (fun _ : CubeIndex d b => (1 / (((2 * b + 1) ^ d : ℕ) : ℂ))) =
      1 / (((2 * b + 1) ^ d : ℕ) : ℝ) := by
    unfold SegmentedVDM.energy
    simp only [norm_div, norm_one, Complex.norm_natCast, div_pow, one_pow,
      Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    field_simp
  rw [he] at hh
  have hsqrt := Real.sq_sqrt hN.le
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hh, div_pow, one_pow, hsqrt]

/-- The smoothed coefficient vector associated with a centered packet. -/
noncomputable def smoothedVector {d h b s : ℕ} (P : CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s) :
    EuclideanSpace ℂ (UniformIndex d s) :=
  ∑ i, P.coeff i • averagingVector P hsupport hseven i

theorem smoothedVector_norm_le {d h b s : ℕ} (P : CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s) :
    ‖smoothedVector P hsupport hseven‖ ≤
      P.mass / Real.sqrt (((2 * b + 1) ^ d : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ i, ‖P.coeff i • averagingVector P hsupport hseven i‖ :=
      norm_sum_le _ _
    _ = _ := by
      simp only [norm_smul, averagingVector_norm, mul_one_div, ← Finset.sum_div, mass]

/-- Steering vector on the nonnegative uniform cube. -/
noncomputable def uniformSteering (d s : ℕ) (D : ℝ) (x : Point d) :
    UniformIndex d s → ℂ :=
  fun α => Complex.exp
    (Complex.I * ((D * ∑ k, (α k : ℝ) * x k : ℝ) : ℂ))

theorem uniformSteering_eq_steeringVector (d s : ℕ) (D : ℝ) (x : Point d) :
    uniformSteering d s D x =
      steeringVector
        (fun (α : UniformIndex d s) => fun k => D * (α k : ℝ)) x := by
  funext α
  simp only [uniformSteering, steeringVector, dot]
  congr 2
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Centered Dirichlet mean used by cube smoothing. -/
noncomputable def centeredMeanKernel (d b : ℕ) (D : ℝ) (x : Point d) : ℂ :=
  ∑ q : CubeIndex d b,
    (1 / (((2 * b + 1) ^ d : ℕ) : ℂ)) *
      Complex.exp
        (Complex.I * ((D * ∑ k, (cubeOffset q k : ℝ) * x k : ℝ) : ℂ))

@[simp] theorem centeredMeanKernel_zero (d b : ℕ) (D : ℝ) :
    centeredMeanKernel d b D 0 = 1 := by
  have hcard : Fintype.card (CubeIndex d b) = (2 * b + 1) ^ d := by
    simp [CubeIndex]
  simp [centeredMeanKernel, hcard]
  apply div_self
  exact pow_ne_zero _ (by
    exact_mod_cast (show 2 * b + 1 ≠ 0 by omega))

theorem averagingVector_evaluation {d h b s : ℕ} (P : CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s) (i : P.Index)
    (D : ℝ) (x : Point d) :
    ofLp (averagingVector P hsupport hseven i) ⬝ᵥ uniformSteering d s D x =
      Complex.exp
          (Complex.I *
            ((D * ∑ k, (P.frequency i k : ℝ) * x k : ℝ) : ℂ)) *
        centeredMeanKernel d b D x *
        Complex.exp
          (Complex.I *
            ((D * ((s / 2 : ℕ) : ℝ) * ∑ k, x k : ℝ) : ℂ)) := by
  rw [averagingVector, SegmentedVDM.spread_dotProduct]
  unfold centeredMeanKernel
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  simp only [uniformSteering]
  have hrow (k : Fin d) :
      ((shiftedRow P hsupport hseven i q k : ℕ) : ℝ) =
        (P.frequency i k : ℝ) + (cubeOffset q k : ℝ) +
          ((s / 2 : ℕ) : ℝ) := by
    have hk := congrArg (fun z : ℤ => (z : ℝ))
      (shiftedRow_frequency P hsupport hseven i q k)
    simpa only [Int.cast_add, Int.cast_natCast] using hk
  have hsum :
      D * ∑ k, ((shiftedRow P hsupport hseven i q k : ℕ) : ℝ) * x k =
        D * ((s / 2 : ℕ) : ℝ) * ∑ k, x k +
        D * ∑ k, (P.frequency i k : ℝ) * x k +
        D * ∑ k, (cubeOffset q k : ℝ) * x k := by
    simp_rw [hrow, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    ring
  rw [show Complex.I *
      ((D * ∑ k, ((shiftedRow P hsupport hseven i q k : ℕ) : ℝ) * x k :
        ℝ) : ℂ) =
      Complex.I *
        ((D * ((s / 2 : ℕ) : ℝ) * ∑ k, x k : ℝ) : ℂ) +
      Complex.I *
        ((D * ∑ k, (P.frequency i k : ℝ) * x k : ℝ) : ℂ) +
      Complex.I *
        ((D * ∑ k, (cubeOffset q k : ℝ) * x k : ℝ) : ℂ) by
        rw [hsum]
        push_cast
        ring,
    Complex.exp_add, Complex.exp_add]
  ring

theorem smoothedVector_evaluation {d h b s : ℕ} (P : CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s)
    (D : ℝ) (x : Point d) :
    ofLp (smoothedVector P hsupport hseven) ⬝ᵥ uniformSteering d s D x =
      P.value D x * centeredMeanKernel d b D x *
        Complex.exp
          (Complex.I *
            ((D * ((s / 2 : ℕ) : ℝ) * ∑ k, x k : ℝ) : ℂ)) := by
  simp only [smoothedVector, WithLp.ofLp_sum, sum_dotProduct,
    WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, averagingVector_evaluation]
  unfold value
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Modulation translates the evaluation point and preserves coefficient
energy. -/
noncomputable def modulation {d s : ℕ} (c : UniformIndex d s → ℂ)
    (D : ℝ) (y : Point d) : UniformIndex d s → ℂ :=
  fun α => c α * uniformSteering d s D (-y) α

theorem energy_modulation {d s : ℕ} (c : UniformIndex d s → ℂ)
    (D : ℝ) (y : Point d) :
    SegmentedVDM.energy (modulation c D y) = SegmentedVDM.energy c := by
  simp [SegmentedVDM.energy, modulation, uniformSteering,
    Complex.norm_exp]

theorem modulation_evaluation {d s : ℕ} (c : UniformIndex d s → ℂ)
    (D : ℝ) (y x : Point d) :
    modulation c D y ⬝ᵥ uniformSteering d s D x =
      c ⬝ᵥ uniformSteering d s D (x - y) := by
  apply Finset.sum_congr rfl
  intro α _
  simp only [modulation, uniformSteering]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [Pi.neg_apply, Pi.sub_apply]
  push_cast
  simp_rw [mul_neg, mul_sub]
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  ring

/-- Cube smoothing and Lagrange duality turn centered interpolating packets
into a minimum-singular-value estimate for the contiguous Vandermonde matrix. -/
theorem singularValue_ge_of_centeredPackets
    {d n h b s : ℕ} (hn : 0 < n) (D : ℝ) (x : Fin n → Point d)
    (P : Fin n → CenteredPacket d h)
    (hsupport : h + b ≤ s / 2) (hseven : Even s)
    {H : ℝ} (hH : 0 < H) (hP : ∀ k, (P k).mass ≤ H)
    (hinterp : ∀ k j, (P k).value D (x j - x k) =
      if k = j then 1 else 0) :
    Real.sqrt (((2 * b + 1) ^ d : ℕ) : ℝ) / (Real.sqrt n * H) ≤
      matrixSingularValue
        (generalizedVandermonde
          (fun (α : UniformIndex d s) => fun k => D * (α k : ℝ)) x)
        (n - 1) := by
  classical
  let C : Matrix (Fin n) (UniformIndex d s) ℂ :=
    fun k => modulation (ofLp (smoothedVector (P k) hsupport hseven)) D (x k)
  have hCV :
      C * generalizedVandermonde
        (fun (α : UniformIndex d s) => fun k => D * (α k : ℝ)) x = 1 := by
    ext k j
    simp only [C, Matrix.mul_apply, generalizedVandermonde, Matrix.one_apply]
    rw [← uniformSteering_eq_steeringVector]
    change modulation (ofLp (smoothedVector (P k) hsupport hseven)) D (x k) ⬝ᵥ
      uniformSteering d s D (x j) = if k = j then 1 else 0
    rw [modulation_evaluation, smoothedVector_evaluation, hinterp]
    by_cases hkj : k = j
    · subst j
      simp
    · simp [hkj]
  have hC (k : Fin n) :
      SegmentedVDM.energy (C k) ≤
        (H / Real.sqrt (((2 * b + 1) ^ d : ℕ) : ℝ)) ^ 2 := by
    change SegmentedVDM.energy
      (modulation (ofLp (smoothedVector (P k) hsupport hseven)) D (x k)) ≤ _
    rw [energy_modulation]
    change (∑ i, ‖(smoothedVector (P k) hsupport hseven) i‖ ^ 2) ≤ _
    rw [← EuclideanSpace.norm_sq_eq]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
    exact (smoothedVector_norm_le (P k) hsupport hseven).trans
      (div_le_div_of_nonneg_right (hP k) (Real.sqrt_nonneg _))
  have hh := SegmentedVDM.singularValue_ge_of_interpolation
    (generalizedVandermonde
      (fun (α : UniformIndex d s) => fun k => D * (α k : ℝ)) x)
    C hCV hn (by positivity : 0 <
      H / Real.sqrt (((2 * b + 1) ^ d : ℕ) : ℝ)) hC
  convert! hh using 1
  field_simp

end CenteredPacket

end

end NumDetect
end LeanNumDetect
