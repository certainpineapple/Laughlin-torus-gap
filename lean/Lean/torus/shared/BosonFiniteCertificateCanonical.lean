/- Concrete fixed planar three-particle certificate in the project's existing
canonical ThreeSector, and its already-normalized positive all-N lift.
This is not an identification with the geometry-dependent torus single3. -/
import torus.shared.BosonFiniteCertificateCanonical300
import torus.shared.BosonFiniteCertificateCanonical301
import torus.shared.BosonFiniteCertificateCanonical302
import torus.shared.BosonFiniteCertificateCanonical303
import torus.shared.BosonFiniteCertificateCanonical304
import torus.shared.BosonFiniteCertificateCanonical305
import torus.shared.BosonFiniteCertificateCanonical306
import torus.shared.BosonFiniteCertificateCanonical307
import torus.shared.BosonFiniteCertificateCanonical308
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization

def finitePlanarComparisonByDegree : Fin 9 →
    (ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9)) :=
  ![k300comparisonOperator, k301comparisonOperator, k302comparisonOperator, k303comparisonOperator, k304comparisonOperator, k305comparisonOperator, k306comparisonOperator, k307comparisonOperator, k308comparisonOperator]

def canonicalPlanarFiniteComparison : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  ∑ z, finitePlanarComparisonByDegree z

theorem canonicalPlanarFiniteComparison_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (canonicalPlanarFiniteComparison f).val).re := by
  simp only [canonicalPlanarFiniteComparison, LinearMap.sum_apply, Submodule.coe_sum,
    inner_sum_right, Complex.re_sum]
  apply Finset.sum_nonneg
  intro z hz
  fin_cases z
  · exact k300_comparison_operator_nonneg f
  · exact k301_comparison_operator_nonneg f
  · exact k302_comparison_operator_nonneg f
  · exact k303_comparison_operator_nonneg f
  · exact k304_comparison_operator_nonneg f
  · exact k305_comparison_operator_nonneg f
  · exact k306_comparison_operator_nonneg f
  · exact k307_comparison_operator_nonneg f
  · exact k308_comparison_operator_nonneg f

/-- A concrete original-row finite planar comparison, on the same canonical
core and the same normalized three-body lift as the physical bridge. This
statement does not substitute that comparison for torus singleContraction. -/
theorem canonicalPlanarFiniteComparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift canonicalPlanarFiniteComparison f)).re :=
  threeBodyLift_nonneg _ canonicalPlanarFiniteComparison_nonneg f

#print axioms canonicalPlanarFiniteComparison_nonneg
#print axioms canonicalPlanarFiniteComparison_lift_nonneg
end TorusLean.BosonFiniteCertificate
