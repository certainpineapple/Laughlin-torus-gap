import torus.shared.FermionCertificateThreeArithmetic

/-! Reconciliation of the exact rational certificate with the original
real seven-row alpha/lambda formula. The separate full-polynomial coupling
lemma must identify the explicit sThree coefficients with the actual
normalized rotation before this is used as a physical K3 theorem. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open TorusLean.Shared.FermionLocalJet
open scoped BigOperators

/-- Explicit original coefficient; integerCoupling supplies zero outside range. -/
def sThree (z T p : ℕ) : ℝ :=
  (integerCoupling 2 z T p:ℝ)*Real.sqrt (couplingScaleQ z T p:ℝ)

def rowCoupledCoefficient (r : CertificateRow) (z T : ℕ) : ℝ :=
  ∑ a : CertificateEntry r,
    if (certificateEntryData r a).1+(certificateEntryData r a).2.1=T then
      certificateAlpha r a*sThree z T (certificateEntryData r a).1
    else 0

/-- Literal eq:F-ez, before any cancellation of square roots. -/
def threeEigenvalue (z : ℕ) : ℝ :=
  ∑ r : CertificateRow, ∑ T ∈ Finset.range 16,
    if max z (certificateRowData r).1 ≤ T then
      2*certificateLambda r*sThree z T (certificateRowData r).1*
        rowCoupledCoefficient r z T + (rowCoupledCoefficient r z T)^2
    else 0

theorem certificateAlpha_mul_sThree (r : CertificateRow) (a : CertificateEntry r)
    (z T : ℕ) (hT : (certificateEntryData r a).1+
      (certificateEntryData r a).2.1=T) :
    certificateAlpha r a*sThree z T (certificateEntryData r a).1 =
      ((certificateEntryData r a).2.2:ℝ)/10000000 *
        (integerCoupling 2 z T (certificateEntryData r a).1:ℝ)*
        Real.sqrt (couplingScaleQ z T (certificateRowData r).1:ℝ) := by
  have hc : (certificateScaleSq r a:ℝ) *
      (couplingScaleQ z T (certificateEntryData r a).1:ℝ) =
      (couplingScaleQ z T (certificateRowData r).1:ℝ) := by
    exact_mod_cast certificateScaleSq_mul_coupling r a z T hT
  unfold certificateAlpha sThree
  calc
    _ = ((certificateEntryData r a).2.2:ℝ)/10000000 *
        (integerCoupling 2 z T (certificateEntryData r a).1:ℝ)*
        (Real.sqrt (certificateScaleSq r a:ℝ)*
          Real.sqrt (couplingScaleQ z T (certificateEntryData r a).1:ℝ)) := by ring
    _ = _ := by
      rw [← Real.sqrt_mul (by exact_mod_cast certificateScaleSq_nonneg r a),hc]

theorem rowCoupledCoefficient_rationalized (r : CertificateRow) (z T : ℕ) :
    rowCoupledCoefficient r z T = (rowNumerator r z T:ℝ)/10000000 *
      Real.sqrt (couplingScaleQ z T (certificateRowData r).1:ℝ) := by
  unfold rowCoupledCoefficient rowNumerator
  push_cast
  rw [Finset.sum_div,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs with hT
  · rw [certificateAlpha_mul_sThree r a z T hT]
    ring
  · simp

/-- All thirteen numerical roots ultimately consume this identity, rather
than an assumed equality between a floating table and the analytic source. -/
theorem threeEigenvalue_eq_rational (z : ℕ) :
    threeEigenvalue z = (threeEigenvalueQ z:ℝ) := by
  unfold threeEigenvalue threeEigenvalueQ
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro T hT
  split_ifs with h
  · rw [rowCoupledCoefficient_rationalized]
    unfold certificateLambda sThree
    have hs : (Real.sqrt (couplingScaleQ z T (certificateRowData r).1:ℝ))^2 =
        (couplingScaleQ z T (certificateRowData r).1:ℝ) :=
      Real.sq_sqrt (by exact_mod_cast couplingScaleQ_nonneg z T (certificateRowData r).1)
    calc
      _ = (Real.sqrt (couplingScaleQ z T (certificateRowData r).1:ℝ))^2 *
          (rowNumerator r z T:ℝ)*
          ((rowNumerator r z T:ℝ)+2*((certificateRowData r).2.1:ℝ)*
            (integerCoupling 2 z T (certificateRowData r).1:ℝ))/10000000^2 := by ring
      _ = _ := by
        rw [hs]
        push_cast <;> ring
  · simp

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
