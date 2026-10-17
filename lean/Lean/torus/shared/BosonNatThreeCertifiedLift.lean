import torus.shared.BosonNatThreeMatrixLift
import torus.shared.BosonFiniteCertificateNatRelativeRankComparison

/-! The original certified J E J coefficients are inserted through the
actual full-core three-body lift and original charge-three cell integral.
This positivity result is not, by itself, an identification with the
single-contraction form or with the physical original-row operator. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeCertifiedLift
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatThreeMatrixLift

def k300certifiedLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  natMatrixLiftForm G theta k300natRelativeFamily
    (natFamilyOfFin9_particle k300family) k300natComparisonCoefficient f

def k301certifiedLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  natMatrixLiftForm G theta k301natRelativeFamily
    (natFamilyOfFin9_particle k301family) k301natComparisonCoefficient f

def k302certifiedLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  natMatrixLiftForm G theta k302natRelativeFamily
    (natFamilyOfFin9_particle k302family) k302natComparisonCoefficient f

def k303certifiedLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  natMatrixLiftForm G theta k303natRelativeFamily
    (natFamilyOfFin9_particle k303family) k303natComparisonCoefficient f

def k304certifiedLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  natMatrixLiftForm G theta k304natRelativeFamily
    (natFamilyOfFin9_particle k304family) k304natComparisonCoefficient f

def k305certifiedLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  natMatrixLiftForm G theta k305natRelativeFamily
    (natFamilyOfFin9_particle k305family) k305natComparisonCoefficient f

def k306certifiedLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  natMatrixLiftForm G theta k306natRelativeFamily
    (natFamilyOfFin9_particle k306family) k306natComparisonCoefficient f

def k307certifiedLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  natMatrixLiftForm G theta k307natRelativeFamily
    (natFamilyOfFin9_particle k307family) k307natComparisonCoefficient f

def k308certifiedLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  natMatrixLiftForm G theta k308natRelativeFamily
    (natFamilyOfFin9_particle k308family) k308natComparisonCoefficient f

/-- All nine complete relative blocks use their actual inverse-Gram
rank coefficients, including the empty degree-one family. -/
def certifiedComparisonLift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  k300certifiedLift G theta f +
  k301certifiedLift G theta f +
  k302certifiedLift G theta f +
  k303certifiedLift G theta f +
  k304certifiedLift G theta f +
  k305certifiedLift G theta f +
  k306certifiedLift G theta f +
  k307certifiedLift G theta f +
  k308certifiedLift G theta f

theorem certifiedComparisonLift_nonneg (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    0 ≤ certifiedComparisonLift G theta f := by
  have hk300 : 0 ≤ k300certifiedLift G theta f :=
    natMatrixLiftForm_nonneg G theta k300natRelativeFamily
      (natFamilyOfFin9_particle k300family) k300natComparisonCoefficient
      k300_nat_comparison_coefficient_posSemidef f
  have hk301 : 0 ≤ k301certifiedLift G theta f :=
    natMatrixLiftForm_nonneg G theta k301natRelativeFamily
      (natFamilyOfFin9_particle k301family) k301natComparisonCoefficient
      k301_nat_comparison_coefficient_posSemidef f
  have hk302 : 0 ≤ k302certifiedLift G theta f :=
    natMatrixLiftForm_nonneg G theta k302natRelativeFamily
      (natFamilyOfFin9_particle k302family) k302natComparisonCoefficient
      k302_nat_comparison_coefficient_posSemidef f
  have hk303 : 0 ≤ k303certifiedLift G theta f :=
    natMatrixLiftForm_nonneg G theta k303natRelativeFamily
      (natFamilyOfFin9_particle k303family) k303natComparisonCoefficient
      k303_nat_comparison_coefficient_posSemidef f
  have hk304 : 0 ≤ k304certifiedLift G theta f :=
    natMatrixLiftForm_nonneg G theta k304natRelativeFamily
      (natFamilyOfFin9_particle k304family) k304natComparisonCoefficient
      k304_nat_comparison_coefficient_posSemidef f
  have hk305 : 0 ≤ k305certifiedLift G theta f :=
    natMatrixLiftForm_nonneg G theta k305natRelativeFamily
      (natFamilyOfFin9_particle k305family) k305natComparisonCoefficient
      k305_nat_comparison_coefficient_posSemidef f
  have hk306 : 0 ≤ k306certifiedLift G theta f :=
    natMatrixLiftForm_nonneg G theta k306natRelativeFamily
      (natFamilyOfFin9_particle k306family) k306natComparisonCoefficient
      k306_nat_comparison_coefficient_posSemidef f
  have hk307 : 0 ≤ k307certifiedLift G theta f :=
    natMatrixLiftForm_nonneg G theta k307natRelativeFamily
      (natFamilyOfFin9_particle k307family) k307natComparisonCoefficient
      k307_nat_comparison_coefficient_posSemidef f
  have hk308 : 0 ≤ k308certifiedLift G theta f :=
    natMatrixLiftForm_nonneg G theta k308natRelativeFamily
      (natFamilyOfFin9_particle k308family) k308natComparisonCoefficient
      k308_nat_comparison_coefficient_posSemidef f
  unfold certifiedComparisonLift
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (add_nonneg hk300 hk301) hk302) hk303) hk304) hk305) hk306) hk307) hk308

end TorusLean.Shared.BosonNatThreeCertifiedLift
