import torus.shared.BosonFiniteCertificateNatRelativeEnergyRank300
import torus.shared.BosonFiniteCertificateNatRelativeEnergyRank301
import torus.shared.BosonFiniteCertificateNatRelativeEnergyRank302
import torus.shared.BosonFiniteCertificateNatRelativeEnergyRank303
import torus.shared.BosonFiniteCertificateNatRelativeEnergyRank304
import torus.shared.BosonFiniteCertificateNatRelativeEnergyRank305
import torus.shared.BosonFiniteCertificateNatRelativeEnergyRank306
import torus.shared.BosonFiniteCertificateNatRelativeEnergyRank307
import torus.shared.BosonFiniteCertificateNatRelativeEnergyRank308
import torus.shared.BosonNatThreeRankDensityExt
import torus.shared.PhysicalBosonSingleTailPayment

/-! Actual full L3 transport of the original low-relative H²-H+δH dyads. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeRelativeEnergyLift
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonNatThreeCellLift
open TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonNatThreeRankDensityExt
open TorusLean.Shared.PhysicalBosonSingleTailPayment
open TorusLean.Shared.ThermalCoherentAnchoredCOMSummability
open TorusLean.Shared.BosonThermalJacobiRows
open MeasureTheory
open scoped BigOperators

theorem actual_relative_energy_integral (G : Geometry) (theta : Twist)
    (d : ℕ) (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, natRelativeLowEnergyScalar d * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed d) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed d) f) ∂cellMeasure G 3).re =
    (2*(-1/2:ℝ)^d+(delta:ℝ))*w3RelativeForm G theta d f := by
  simp_rw [natThreeAnnihilator_ground G theta _ (w3RelativeSeed_bihomogeneous d).1]
  rw [integral_const_mul]
  change (natRelativeLowEnergyScalar d * anchoredRelativeCross G theta d f f).re = _
  have hs : natRelativeLowEnergyScalar d =
      Complex.ofReal (2*(-1/2:ℝ)^d+(delta:ℝ)) := by
    norm_num [natRelativeLowEnergyScalar,delta,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_pow]
  rw [hs,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    anchoredRelativeCross_self_re]

theorem k300_actual_relative_energy_lift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 k300natRelativeFamily
      (natFamilyOfFin9_particle k300family) k300natRelativeEnergyCoefficient f =
    (∫ R, natRelativeLowEnergyScalar 0 * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed 0) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed 0) f) ∂cellMeasure G 3).re := by
  obtain ⟨x,hx,hC⟩ := k300_nat_relative_energy_coefficient_rank
  have h := natMatrixCellLiftForm_synthesized_rank G theta 3 k300natRelativeFamily
    (natFamilyOfFin9_particle k300family) x (natRelativeLowEnergyScalar 0) f
  simpa only [←hC,hx] using h

theorem k301_actual_relative_energy_lift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 k301natRelativeFamily
      (natFamilyOfFin9_particle k301family) k301natRelativeEnergyCoefficient f =
    (∫ R, natRelativeLowEnergyScalar 1 * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed 1) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed 1) f) ∂cellMeasure G 3).re := by
  obtain ⟨x,hx,hC⟩ := k301_nat_relative_energy_coefficient_rank
  have h := natMatrixCellLiftForm_synthesized_rank G theta 3 k301natRelativeFamily
    (natFamilyOfFin9_particle k301family) x (natRelativeLowEnergyScalar 1) f
  simpa only [←hC,hx] using h

theorem k302_actual_relative_energy_lift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 k302natRelativeFamily
      (natFamilyOfFin9_particle k302family) k302natRelativeEnergyCoefficient f =
    (∫ R, natRelativeLowEnergyScalar 2 * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed 2) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed 2) f) ∂cellMeasure G 3).re := by
  obtain ⟨x,hx,hC⟩ := k302_nat_relative_energy_coefficient_rank
  have h := natMatrixCellLiftForm_synthesized_rank G theta 3 k302natRelativeFamily
    (natFamilyOfFin9_particle k302family) x (natRelativeLowEnergyScalar 2) f
  simpa only [←hC,hx] using h

theorem k303_actual_relative_energy_lift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 k303natRelativeFamily
      (natFamilyOfFin9_particle k303family) k303natRelativeEnergyCoefficient f =
    (∫ R, natRelativeLowEnergyScalar 3 * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed 3) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed 3) f) ∂cellMeasure G 3).re := by
  obtain ⟨x,hx,hC⟩ := k303_nat_relative_energy_coefficient_rank
  have h := natMatrixCellLiftForm_synthesized_rank G theta 3 k303natRelativeFamily
    (natFamilyOfFin9_particle k303family) x (natRelativeLowEnergyScalar 3) f
  simpa only [←hC,hx] using h

theorem k304_actual_relative_energy_lift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 k304natRelativeFamily
      (natFamilyOfFin9_particle k304family) k304natRelativeEnergyCoefficient f =
    (∫ R, natRelativeLowEnergyScalar 4 * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed 4) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed 4) f) ∂cellMeasure G 3).re := by
  obtain ⟨x,hx,hC⟩ := k304_nat_relative_energy_coefficient_rank
  have h := natMatrixCellLiftForm_synthesized_rank G theta 3 k304natRelativeFamily
    (natFamilyOfFin9_particle k304family) x (natRelativeLowEnergyScalar 4) f
  simpa only [←hC,hx] using h

theorem k305_actual_relative_energy_lift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 k305natRelativeFamily
      (natFamilyOfFin9_particle k305family) k305natRelativeEnergyCoefficient f =
    (∫ R, natRelativeLowEnergyScalar 5 * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed 5) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed 5) f) ∂cellMeasure G 3).re := by
  obtain ⟨x,hx,hC⟩ := k305_nat_relative_energy_coefficient_rank
  have h := natMatrixCellLiftForm_synthesized_rank G theta 3 k305natRelativeFamily
    (natFamilyOfFin9_particle k305family) x (natRelativeLowEnergyScalar 5) f
  simpa only [←hC,hx] using h

theorem k306_actual_relative_energy_lift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 k306natRelativeFamily
      (natFamilyOfFin9_particle k306family) k306natRelativeEnergyCoefficient f =
    (∫ R, natRelativeLowEnergyScalar 6 * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed 6) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed 6) f) ∂cellMeasure G 3).re := by
  obtain ⟨x,hx,hC⟩ := k306_nat_relative_energy_coefficient_rank
  have h := natMatrixCellLiftForm_synthesized_rank G theta 3 k306natRelativeFamily
    (natFamilyOfFin9_particle k306family) x (natRelativeLowEnergyScalar 6) f
  simpa only [←hC,hx] using h

theorem k307_actual_relative_energy_lift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 k307natRelativeFamily
      (natFamilyOfFin9_particle k307family) k307natRelativeEnergyCoefficient f =
    (∫ R, natRelativeLowEnergyScalar 7 * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed 7) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed 7) f) ∂cellMeasure G 3).re := by
  obtain ⟨x,hx,hC⟩ := k307_nat_relative_energy_coefficient_rank
  have h := natMatrixCellLiftForm_synthesized_rank G theta 3 k307natRelativeFamily
    (natFamilyOfFin9_particle k307family) x (natRelativeLowEnergyScalar 7) f
  simpa only [←hC,hx] using h

theorem k308_actual_relative_energy_lift (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 k308natRelativeFamily
      (natFamilyOfFin9_particle k308family) k308natRelativeEnergyCoefficient f =
    (∫ R, natRelativeLowEnergyScalar 8 * ip
      (natThreeAnnihilator G theta R (w3RelativeSeed 8) f)
      (natThreeAnnihilator G theta R (w3RelativeSeed 8) f) ∂cellMeasure G 3).re := by
  obtain ⟨x,hx,hC⟩ := k308_nat_relative_energy_coefficient_rank
  have h := natMatrixCellLiftForm_synthesized_rank G theta 3 k308natRelativeFamily
    (natFamilyOfFin9_particle k308family) x (natRelativeLowEnergyScalar 8) f
  simpa only [←hC,hx] using h

end TorusLean.Shared.BosonNatThreeRelativeEnergyLift
