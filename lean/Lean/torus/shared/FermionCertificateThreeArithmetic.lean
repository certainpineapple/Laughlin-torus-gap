import torus.shared.FermionLocalJetRows

/-! Exact rational computation for all thirteen manuscript three-body
comparisons. The only row data are the already frozen original seven rows.
No decimal approximation or external computed sign is a proof input. -/
set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open TorusLean.Shared.FermionLocalJet
open scoped BigOperators

/-- Integer coefficient in eq:F-U, including its actual zero extension. -/
def integerCoupling (c z T p : ℕ) : ℤ :=
  if z ≤ T ∧ p ≤ T then
    ∑ h ∈ Finset.range (z+1), if h ≤ p ∧ p-h ≤ T-z then
      (-1:ℤ)^(z-h) * (z.choose h:ℤ) * ((T-z).choose (p-h):ℤ) * (c:ℤ)^(p-h)
    else 0
  else 0

/-- The squared positive factor in eq:F-s-rational, in factorial form.
The natural subtractions are only used inside the indicated valid range. -/
def couplingScaleQ (z T p : ℕ) : ℚ :=
  (2:ℚ)^z * (p.factorial:ℚ) * ((T-p).factorial:ℚ) /
    ((3:ℚ)^T * (2:ℚ)^p * (z.factorial:ℚ) * ((T-z).factorial:ℚ))

/-- The original integer row numerator X_(rho,T)(z). -/
def rowNumerator (r : CertificateRow) (z T : ℕ) : ℤ :=
  ∑ a : CertificateEntry r,
    if (certificateEntryData r a).1 + (certificateEntryData r a).2.1 = T then
      (certificateEntryData r a).2.2 * integerCoupling 2 z T (certificateEntryData r a).1
    else 0

/-- Literal rationalized eq:F-ez, with no independently inserted table. -/
def threeEigenvalueQ (z : ℕ) : ℚ :=
  ∑ r : CertificateRow, ∑ T ∈ Finset.range 16,
    if max z (certificateRowData r).1 ≤ T then
      couplingScaleQ z T (certificateRowData r).1 *
        (rowNumerator r z T:ℚ) *
        ((rowNumerator r z T:ℚ) + 2 * ((certificateRowData r).2.1:ℚ) *
          (integerCoupling 2 z T (certificateRowData r).1:ℚ)) / 10000000^2
    else 0

def relativeWeightQ (z : ℕ) : ℚ := (3*(z:ℚ)-1)*(-1/2:ℚ)^z

def threeMarginQ (z : ℕ) : ℚ := (3/2:ℚ)*relativeWeightQ z-threeEigenvalueQ z

def comparisonDegrees : Finset ℕ := {2,4,5,6,7,8,9,10,11,12,13,14,15}

theorem couplingScaleQ_nonneg (z T p : ℕ) : 0 ≤ couplingScaleQ z T p := by
  unfold couplingScaleQ
  positivity

private theorem choose_cast_factorial {p T : ℕ} (hp : p ≤ T) :
    (T.choose p:ℚ) = (T.factorial:ℚ)/((p.factorial:ℚ)*((T-p).factorial:ℚ)) := by
  apply (eq_div_iff (by positivity : (p.factorial:ℚ)*((T-p).factorial:ℚ) ≠ 0)).2
  have h : (T.choose p:ℚ)*(p.factorial:ℚ)*((T-p).factorial:ℚ) = (T.factorial:ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp
  simpa only [mul_assoc] using h

/-- This is exactly the binomial radicand printed in the appendix. -/
theorem couplingScaleQ_eq_binomial (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    couplingScaleQ z T p =
      (2:ℚ)^z*(T.choose z:ℚ)/((3:ℚ)^T*(2:ℚ)^p*(T.choose p:ℚ)) := by
  rw [choose_cast_factorial hz,choose_cast_factorial hp]
  unfold couplingScaleQ
  have hf (n : ℕ) : (n.factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hf]
  <;> ring

/-- The squared decoded alpha cancels the p-dependent coupling radicand.
This statement uses the real row support, including t<=p+j. -/
theorem certificateScaleSq_mul_coupling (r : CertificateRow) (a : CertificateEntry r)
    (z T : ℕ) (hT : (certificateEntryData r a).1 +
      (certificateEntryData r a).2.1 = T) :
    certificateScaleSq r a * couplingScaleQ z T (certificateEntryData r a).1 =
      couplingScaleQ z T (certificateRowData r).1 := by
  have hp : (certificateEntryData r a).1 ≤ T := by omega
  have hj : T-(certificateEntryData r a).1=(certificateEntryData r a).2.1 := by omega
  have hi : certificateJetIndex r a = T-(certificateRowData r).1 := by
    simp only [certificateJetIndex,hT]
  unfold certificateScaleSq couplingScaleQ
  rw [hj,hi]
  have hf (n : ℕ) : (n.factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hf]
  <;> ring

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
