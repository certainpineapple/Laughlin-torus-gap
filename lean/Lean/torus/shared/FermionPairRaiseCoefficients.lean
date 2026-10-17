import torus.shared.FermionPairLowerCoefficients
import torus.shared.FermionLocalJetPairBound

/-! Independent upward factorial recurrence for the original unordered pair.
No upward identity is inferred from a downward identity by injectivity. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.FermionLocalJet

private theorem halfRoot_mul_doubleRoot (p : ℕ) :
    Real.sqrt ((p+1:ℝ)/2) * Real.sqrt (2*(p+1:ℝ)) = p+1 := by
  rw [← Real.sqrt_mul (by positivity), show ((p+1:ℝ)/2)*(2*(p+1))=(p+1)^2 by ring,
    Real.sqrt_sq (by positivity)]

theorem paperPairWeight_raise_left_scaled (p i j : ℕ) :
    Real.sqrt ((p+1:ℝ)/2) * Real.sqrt (i+1:ℝ) * paperPairWeight p i j =
      (i+1:ℝ) * paperPairWeight (p+1) (i+1) j := by
  calc
    _ = Real.sqrt (i+1:ℝ) * (Real.sqrt ((p+1:ℝ)/2)*paperPairWeight p i j) := by ring
    _ = Real.sqrt (i+1:ℝ) *
        (Real.sqrt (i+1:ℝ)*paperPairWeight (p+1) (i+1) j) := by
      rw [← paperPairWeight_lower_left]
    _ = _ := by rw [← mul_assoc, ← pow_two, Real.sq_sqrt (by positivity)]

theorem paperPairWeight_raise_right_scaled (p i j : ℕ) :
    Real.sqrt ((p+1:ℝ)/2) * Real.sqrt (j+1:ℝ) * paperPairWeight p i j =
      (j+1:ℝ) * paperPairWeight (p+1) i (j+1) := by
  rw [paperPairWeight_symm p i j, paperPairWeight_raise_left_scaled,
    paperPairWeight_symm (p+1) (j+1) i]

/-- Upward coefficient reconciliation in the actual i<j branch.  The zero
first-label term is proved separately, rather than treating Nat pred as an
integer. -/
theorem pair_raise_coefficient_lt (p i j : ℕ) (hij : i+j=p+2) (hlt : i<j) :
    pairLeftCoefficient p (i-1) * Real.sqrt (i:ℝ) +
      pairLeftCoefficient p i * Real.sqrt (j:ℝ) =
        Real.sqrt (2*(p+1:ℝ)) * pairLeftCoefficient (p+1) i := by
  have hr : Real.sqrt ((p+1:ℝ)/2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  apply mul_left_cancel₀ hr
  rw [← mul_assoc, halfRoot_mul_doubleRoot]
  cases i with
  | zero =>
    have hj : j=p+2 := by omega
    subst j
    have h := paperPairWeight_raise_right_scaled p 0 (p+1)
    simp only [pairLeftCoefficient, Nat.sub_zero, Nat.zero_sub, Nat.cast_zero,
      Real.sqrt_zero, mul_zero, zero_add,
      show 0<p+1 by omega, show 0<p+1+1 by omega, if_true,
      Nat.cast_add, Nat.cast_one, zero_sub] at h ⊢
    simp only [Nat.cast_ofNat, show (p:ℝ)+1+1 = p+2 by ring] at h ⊢
    linear_combination -(p+1:ℝ) * h
  | succ i =>
    cases j with
    | zero => omega
    | succ j =>
      have hp : p=i+j := by omega
      have hleft : pairLeftCoefficient p i =
          ((i:ℝ)-(j+1)) * paperPairWeight p i (j+1) := by
        simp only [pairLeftCoefficient, show p+1-i=j+1 by omega,
          show i<j+1 by omega, if_true, Nat.cast_add, Nat.cast_one]
      have hright : pairLeftCoefficient p (i+1) =
          ((i+1:ℝ)-j) * paperPairWeight p (i+1) j := by
        simp only [pairLeftCoefficient, show p+1-(i+1)=j by omega]
        split_ifs with h
        · push_cast; rfl
        · have he : i+1=j := by omega
          simp [← he]
      have htarget : pairLeftCoefficient (p+1) (i+1) =
          ((i+1:ℝ)-(j+1)) * paperPairWeight (p+1) (i+1) (j+1) := by
        simp only [pairLeftCoefficient, show p+1+1-(i+1)=j+1 by omega,
          show i+1<j+1 by omega, if_true, Nat.cast_add, Nat.cast_one]
      simp only [Nat.succ_sub_one, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      rw [hleft, hright, htarget]
      have h1 := paperPairWeight_raise_left_scaled p i (j+1)
      have h2 := paperPairWeight_raise_right_scaled p (i+1) j
      have hp' : (p:ℝ)=i+j := by exact_mod_cast hp
      linear_combination ((i:ℝ)-(j+1))*h1 + ((i+1:ℝ)-j)*h2 -
        (((i+1:ℝ)-(j+1))*paperPairWeight (p+1) (i+1) (j+1))*hp'

#print axioms paperPairWeight_raise_left_scaled
#print axioms paperPairWeight_raise_right_scaled
#print axioms pair_raise_coefficient_lt
end TorusLean.Shared.ThermalCoherentFermionCOMWords
