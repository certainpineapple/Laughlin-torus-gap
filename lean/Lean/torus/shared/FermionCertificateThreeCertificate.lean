import torus.shared.FermionCertificateThreeDegree02
import torus.shared.FermionCertificateThreeDegree04
import torus.shared.FermionCertificateThreeDegree05
import torus.shared.FermionCertificateThreeDegree06
import torus.shared.FermionCertificateThreeDegree07
import torus.shared.FermionCertificateThreeDegree08
import torus.shared.FermionCertificateThreeDegree09
import torus.shared.FermionCertificateThreeDegree10
import torus.shared.FermionCertificateThreeDegree11
import torus.shared.FermionCertificateThreeDegree12
import torus.shared.FermionCertificateThreeDegree13
import torus.shared.FermionCertificateThreeDegree14
import torus.shared.FermionCertificateThreeDegree15
import torus.shared.FermionCertificateThreeDecode

/-! All thirteen comparisons for the original decoded seven-row formula.
The actual finite coupling/COM theorem must still identify this formula
with K3^0; this numerical theorem does not assert that physical interface. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open scoped BigOperators

theorem threeMarginQ_positive (z : ℕ) (hz : z ∈ comparisonDegrees) :
    0 < threeMarginQ z := by
  simp only [comparisonDegrees,Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact margin02_positive
  · exact margin04_positive
  · exact margin05_positive
  · exact margin06_positive
  · exact margin07_positive
  · exact margin08_positive
  · exact margin09_positive
  · exact margin10_positive
  · exact margin11_positive
  · exact margin12_positive
  · exact margin13_positive
  · exact margin14_positive
  · exact margin15_positive

theorem threeEigenvalueQ_strict (z : ℕ) (hz : z ∈ comparisonDegrees) :
    threeEigenvalueQ z < (3/2:ℚ)*relativeWeightQ z :=
  sub_pos.mp (threeMarginQ_positive z hz)

/-- Exact manuscript inequality for the real alpha/lambda expression. -/
theorem threeEigenvalue_strict (z : ℕ) (hz : z ∈ comparisonDegrees) :
    threeEigenvalue z < (3/2:ℝ)*(3*(z:ℝ)-1)*(-1/2:ℝ)^z := by
  rw [threeEigenvalue_eq_rational]
  have hc : (threeEigenvalueQ z:ℝ) < (((3/2:ℚ)*relativeWeightQ z:ℚ):ℝ) :=
    Rat.cast_lt.mpr (threeEigenvalueQ_strict z hz)
  simpa only [relativeWeightQ,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one,mul_assoc] using hc

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
