import torus.shared.BosonNatThreeRelativeEnergyLift
import torus.shared.BosonNatThreeCertifiedLift
import torus.shared.BosonNatThreeCellLinearity

/-! The old certified positive rank lift equals the actual energy dyad minus
its original finite COM average. Both Gram inverses and the full L3 are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeCertifiedEnergyIdentity
open TorusLean.Boson TorusLean.BosonFiniteCertificate TorusLean.M2 Matrix
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.BosonNatThreeCertifiedLift
open TorusLean.Shared.BosonNatThreeCellLift
open TorusLean.Shared.BosonNatThreeCellLinearity
open TorusLean.Shared.BosonNatThreeRelativeEnergyLift
open TorusLean.Shared.BosonThermalJacobiRows

theorem k300_certifiedLift_energy_difference (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    k300certifiedLift G theta f =
      (2*(-1/2:ℝ)^0+(delta:ℝ))*w3RelativeForm G theta 0 f -
      natMatrixCellLiftForm G theta 3 k300natRelativeFamily
        (natFamilyOfFin9_particle k300family)
        (complexify k300J * complexify c300averageRaw * complexify k300J) f := by
  have hC : k300natComparisonCoefficient = k300natRelativeEnergyCoefficient -
      complexify k300J * complexify c300averageRaw * complexify k300J := by
    simp only [k300natComparisonCoefficient,k300natRelativeEnergyCoefficient,
      inverseGramCoefficient,k300natRelativeEnergyMatrix,k300rowCertifiedComparison,
      k300_finite_descendant_source,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_sub,Matrix.sub_mul]
    abel
  unfold k300certifiedLift
  rw [←natMatrixCellLiftForm_charge_three,hC,natMatrixCellLiftForm_sub,
    k300_actual_relative_energy_lift,actual_relative_energy_integral]

theorem k301_certifiedLift_energy_difference (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    k301certifiedLift G theta f =
      (2*(-1/2:ℝ)^1+(delta:ℝ))*w3RelativeForm G theta 1 f -
      natMatrixCellLiftForm G theta 3 k301natRelativeFamily
        (natFamilyOfFin9_particle k301family)
        (complexify k301J * complexify c301averageRaw * complexify k301J) f := by
  have hC : k301natComparisonCoefficient = k301natRelativeEnergyCoefficient -
      complexify k301J * complexify c301averageRaw * complexify k301J := by
    simp only [k301natComparisonCoefficient,k301natRelativeEnergyCoefficient,
      inverseGramCoefficient,k301natRelativeEnergyMatrix,k301rowCertifiedComparison,
      k301_finite_descendant_source,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_sub,Matrix.sub_mul]
    abel
  unfold k301certifiedLift
  rw [←natMatrixCellLiftForm_charge_three,hC,natMatrixCellLiftForm_sub,
    k301_actual_relative_energy_lift,actual_relative_energy_integral]

theorem k302_certifiedLift_energy_difference (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    k302certifiedLift G theta f =
      (2*(-1/2:ℝ)^2+(delta:ℝ))*w3RelativeForm G theta 2 f -
      natMatrixCellLiftForm G theta 3 k302natRelativeFamily
        (natFamilyOfFin9_particle k302family)
        (complexify k302J * complexify c302averageRaw * complexify k302J) f := by
  have hC : k302natComparisonCoefficient = k302natRelativeEnergyCoefficient -
      complexify k302J * complexify c302averageRaw * complexify k302J := by
    simp only [k302natComparisonCoefficient,k302natRelativeEnergyCoefficient,
      inverseGramCoefficient,k302natRelativeEnergyMatrix,k302rowCertifiedComparison,
      k302_finite_descendant_source,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_sub,Matrix.sub_mul]
    abel
  unfold k302certifiedLift
  rw [←natMatrixCellLiftForm_charge_three,hC,natMatrixCellLiftForm_sub,
    k302_actual_relative_energy_lift,actual_relative_energy_integral]

theorem k303_certifiedLift_energy_difference (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    k303certifiedLift G theta f =
      (2*(-1/2:ℝ)^3+(delta:ℝ))*w3RelativeForm G theta 3 f -
      natMatrixCellLiftForm G theta 3 k303natRelativeFamily
        (natFamilyOfFin9_particle k303family)
        (complexify k303J * complexify c303averageRaw * complexify k303J) f := by
  have hC : k303natComparisonCoefficient = k303natRelativeEnergyCoefficient -
      complexify k303J * complexify c303averageRaw * complexify k303J := by
    simp only [k303natComparisonCoefficient,k303natRelativeEnergyCoefficient,
      inverseGramCoefficient,k303natRelativeEnergyMatrix,k303rowCertifiedComparison,
      k303_finite_descendant_source,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_sub,Matrix.sub_mul]
    abel
  unfold k303certifiedLift
  rw [←natMatrixCellLiftForm_charge_three,hC,natMatrixCellLiftForm_sub,
    k303_actual_relative_energy_lift,actual_relative_energy_integral]

theorem k304_certifiedLift_energy_difference (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    k304certifiedLift G theta f =
      (2*(-1/2:ℝ)^4+(delta:ℝ))*w3RelativeForm G theta 4 f -
      natMatrixCellLiftForm G theta 3 k304natRelativeFamily
        (natFamilyOfFin9_particle k304family)
        (complexify k304J * complexify c304averageRaw * complexify k304J) f := by
  have hC : k304natComparisonCoefficient = k304natRelativeEnergyCoefficient -
      complexify k304J * complexify c304averageRaw * complexify k304J := by
    simp only [k304natComparisonCoefficient,k304natRelativeEnergyCoefficient,
      inverseGramCoefficient,k304natRelativeEnergyMatrix,k304rowCertifiedComparison,
      k304_finite_descendant_source,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_sub,Matrix.sub_mul]
    abel
  unfold k304certifiedLift
  rw [←natMatrixCellLiftForm_charge_three,hC,natMatrixCellLiftForm_sub,
    k304_actual_relative_energy_lift,actual_relative_energy_integral]

theorem k305_certifiedLift_energy_difference (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    k305certifiedLift G theta f =
      (2*(-1/2:ℝ)^5+(delta:ℝ))*w3RelativeForm G theta 5 f -
      natMatrixCellLiftForm G theta 3 k305natRelativeFamily
        (natFamilyOfFin9_particle k305family)
        (complexify k305J * complexify c305averageRaw * complexify k305J) f := by
  have hC : k305natComparisonCoefficient = k305natRelativeEnergyCoefficient -
      complexify k305J * complexify c305averageRaw * complexify k305J := by
    simp only [k305natComparisonCoefficient,k305natRelativeEnergyCoefficient,
      inverseGramCoefficient,k305natRelativeEnergyMatrix,k305rowCertifiedComparison,
      k305_finite_descendant_source,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_sub,Matrix.sub_mul]
    abel
  unfold k305certifiedLift
  rw [←natMatrixCellLiftForm_charge_three,hC,natMatrixCellLiftForm_sub,
    k305_actual_relative_energy_lift,actual_relative_energy_integral]

theorem k306_certifiedLift_energy_difference (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    k306certifiedLift G theta f =
      (2*(-1/2:ℝ)^6+(delta:ℝ))*w3RelativeForm G theta 6 f -
      natMatrixCellLiftForm G theta 3 k306natRelativeFamily
        (natFamilyOfFin9_particle k306family)
        (complexify k306J * complexify c306averageRaw * complexify k306J) f := by
  have hC : k306natComparisonCoefficient = k306natRelativeEnergyCoefficient -
      complexify k306J * complexify c306averageRaw * complexify k306J := by
    simp only [k306natComparisonCoefficient,k306natRelativeEnergyCoefficient,
      inverseGramCoefficient,k306natRelativeEnergyMatrix,k306rowCertifiedComparison,
      k306_finite_descendant_source,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_sub,Matrix.sub_mul]
    abel
  unfold k306certifiedLift
  rw [←natMatrixCellLiftForm_charge_three,hC,natMatrixCellLiftForm_sub,
    k306_actual_relative_energy_lift,actual_relative_energy_integral]

theorem k307_certifiedLift_energy_difference (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    k307certifiedLift G theta f =
      (2*(-1/2:ℝ)^7+(delta:ℝ))*w3RelativeForm G theta 7 f -
      natMatrixCellLiftForm G theta 3 k307natRelativeFamily
        (natFamilyOfFin9_particle k307family)
        (complexify k307J * complexify c307averageRaw * complexify k307J) f := by
  have hC : k307natComparisonCoefficient = k307natRelativeEnergyCoefficient -
      complexify k307J * complexify c307averageRaw * complexify k307J := by
    simp only [k307natComparisonCoefficient,k307natRelativeEnergyCoefficient,
      inverseGramCoefficient,k307natRelativeEnergyMatrix,k307rowCertifiedComparison,
      k307_finite_descendant_source,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_sub,Matrix.sub_mul]
    abel
  unfold k307certifiedLift
  rw [←natMatrixCellLiftForm_charge_three,hC,natMatrixCellLiftForm_sub,
    k307_actual_relative_energy_lift,actual_relative_energy_integral]

theorem k308_certifiedLift_energy_difference (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    k308certifiedLift G theta f =
      (2*(-1/2:ℝ)^8+(delta:ℝ))*w3RelativeForm G theta 8 f -
      natMatrixCellLiftForm G theta 3 k308natRelativeFamily
        (natFamilyOfFin9_particle k308family)
        (complexify k308J * complexify c308averageRaw * complexify k308J) f := by
  have hC : k308natComparisonCoefficient = k308natRelativeEnergyCoefficient -
      complexify k308J * complexify c308averageRaw * complexify k308J := by
    simp only [k308natComparisonCoefficient,k308natRelativeEnergyCoefficient,
      inverseGramCoefficient,k308natRelativeEnergyMatrix,k308rowCertifiedComparison,
      k308_finite_descendant_source,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_sub,Matrix.sub_mul]
    abel
  unfold k308certifiedLift
  rw [←natMatrixCellLiftForm_charge_three,hC,natMatrixCellLiftForm_sub,
    k308_actual_relative_energy_lift,actual_relative_energy_integral]

end TorusLean.Shared.BosonNatThreeCertifiedEnergyIdentity
