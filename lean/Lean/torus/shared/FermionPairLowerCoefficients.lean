import torus.shared.FermionRelativeFrameCoefficientsPaper

/-! Positive square-root recurrences for the unchanged paper m=1 pair weights.
These identities include all Nat orbital boundaries and do not use a cutoff. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.FermionRelativeFrame

/-- The factorial shift from lowering the first orbital, at every Nat label. -/
theorem paperPairWeight_lower_left (p i j : ℕ) :
    Real.sqrt (i+1:ℝ) * paperPairWeight (p+1) (i+1) j =
      Real.sqrt ((p+1:ℝ)/2) * paperPairWeight p i j := by
  have hf (n : ℕ) : (n.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hi : (i+1:ℝ) ≠ 0 := by positivity
  have hs :
      (Real.sqrt (i+1:ℝ) * paperPairWeight (p+1) (i+1) j)^2 =
      (Real.sqrt ((p+1:ℝ)/2) * paperPairWeight p i j)^2 := by
    unfold paperPairWeight
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp [hf, hi]
    <;> ring
  exact (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hs

theorem paperPairWeight_lower_right (p i j : ℕ) :
    Real.sqrt (j+1:ℝ) * paperPairWeight (p+1) i (j+1) =
      Real.sqrt ((p+1:ℝ)/2) * paperPairWeight p i j := by
  rw [paperPairWeight_symm (p+1) i (j+1), paperPairWeight_lower_left,
    paperPairWeight_symm p j i]

/-- The two shifted signed branches combine to the original sqrt(2(p+1)). -/
theorem paperPair_signed_lower (p i j : ℕ) :
    Real.sqrt (i+1:ℝ) * (((i+1:ℝ)-j) * paperPairWeight (p+1) (i+1) j) +
      Real.sqrt (j+1:ℝ) * (((i:ℝ)-(j+1)) * paperPairWeight (p+1) i (j+1)) =
        Real.sqrt (2*(p+1:ℝ)) * (((i:ℝ)-j) * paperPairWeight p i j) := by
  have hs : 2 * Real.sqrt ((p+1:ℝ)/2) = Real.sqrt (2*(p+1:ℝ)) := by
    have he : (2 * Real.sqrt ((p+1:ℝ)/2))^2 = (Real.sqrt (2*(p+1:ℝ)))^2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      ring
    exact (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp he
  calc
    _ = ((i+1:ℝ)-j) * (Real.sqrt (i+1:ℝ) * paperPairWeight (p+1) (i+1) j) +
        ((i:ℝ)-(j+1)) * (Real.sqrt (j+1:ℝ) * paperPairWeight (p+1) i (j+1)) := by ring
    _ = 2 * Real.sqrt ((p+1:ℝ)/2) * (((i:ℝ)-j)*paperPairWeight p i j) := by
      rw [paperPairWeight_lower_left, paperPairWeight_lower_right]
      ring
    _ = _ := by rw [hs]

#print axioms paperPairWeight_lower_left
#print axioms paperPairWeight_lower_right
#print axioms paperPair_signed_lower
end TorusLean.Shared.ThermalCoherentFermionCOMWords
