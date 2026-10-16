import MultiTuran.FullAperture.FullCube

/-! # Elementary full-cube interfaces for consecutive-window bounds

These are direct applications of the main article's proved elementary
full-cube theorem and no-wrap identity. Correspondence: `lem:elementary`.
-/

set_option autoImplicit false

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

/-- The literal elementary bound for `A_{M,s}`, with its stated constant
and exponent and without a distinctness or separation premise. -/
theorem fullCube_elementary_bound {d n M s : ℕ}
    (hd : 0 < d) (hn : 0 < n) (_hM : 1 ≤ M) (hs : n-1 ≤ s)
    (Y : Fin n → Point d) :
    (1 / Real.sqrt (n : ℝ)) *
      (nodeSeparation (fun j q => (M : ℝ)*Y j q) / Real.pi)^(n-1) ≤
        matrixSingularValue (fullCubeVandermonde M s Y) (n-1) :=
  LeanNumDetect.MultiTuran.elementary_fullCube_lower hd hn hs Y

/-- The literal no-wrap equality in the second assertion of
`lem:elementary`. The diameter and both separations are the actual torus
quantities of the main article. -/
theorem fullCube_no_wrap_separation {d n M : ℕ} (Y : Fin n → Point d)
    (_hM : 1 ≤ M) (hshort : (M : ℝ)*nodeDiameter Y ≤ Real.pi) :
    nodeSeparation (fun j q => (M : ℝ)*Y j q) = (M : ℝ)*nodeSeparation Y :=
  nodeSeparation_mul_nat M Y hshort

/-- The elementary bound after applying the proved no-wrap identity. -/
theorem fullCube_elementary_no_wrap_bound {d n M s : ℕ}
    (hd : 0 < d) (hn : 0 < n) (_hM : 1 ≤ M) (hs : n-1 ≤ s)
    (Y : Fin n → Point d) (hshort : (M : ℝ)*nodeDiameter Y ≤ Real.pi) :
    (1 / Real.sqrt (n : ℝ)) * ((M : ℝ)*nodeSeparation Y / Real.pi)^(n-1) ≤
      matrixSingularValue (fullCubeVandermonde M s Y) (n-1) :=
  LeanNumDetect.MultiTuran.elementary_fullCube_no_wrap_lower hd hn hs Y hshort

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
