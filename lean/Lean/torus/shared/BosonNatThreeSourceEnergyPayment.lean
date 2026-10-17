import torus.shared.BosonNatThreeSourceEnergyComparison
import torus.shared.PhysicalBosonSingleTailPayment
import torus.shared.BosonThermalJacobiCutoff

/-! Payment of the actual finite original M3 source density by the original
single-contraction form and the same-H / S4 thermal budget. The source-to-K3
normal-order identity is a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeSourceEnergyPayment
open TorusLean.Boson
open TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.PhysicalBosonS4 TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.BosonThermalJacobiCutoff
open TorusLean.Shared.PhysicalBosonSingleTailPayment
open TorusLean.Shared.BosonNatThreeSourceEnergyComparison
open TorusLean.Shared.BosonSystole20Scalar
open scoped BigOperators

/-- The genuine unweighted relative cutoff through degree eight uses the
original heat parameter 1/12 and the exact manuscript constant c3. -/
theorem actual_relative_cutoff_eight_payment (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (hG : 20 ≤ systole G) :
    (∑ d ∈ Finset.range 9, w3RelativeForm G theta d
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val) ≤
      c3 * sAllowance * (cAllowance * actualPositiveFourBodyForm G theta N f +
        actualParticleContactEnergy G ((N+2)+2) f.val) := by
  have h := actual_relative_cutoff_bound G theta (1/12) (by norm_num) 8 N f hG
  norm_num [c3] at h ⊢
  nlinarith

/-- The signed low relative spectrum is paid by the actual original S3,
with separate delta-cutoff and odd-tail contributions combined exactly. -/
theorem lowRelativeEnergyForm_le_originalSingleForm_payment
    (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (hG : 20 ≤ systole G) :
    lowRelativeEnergyForm G theta
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val ≤
    originalSingleForm G theta ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val +
      sAllowance * (c9 + TorusLean.Shared.BosonSystole20Scalar.delta * c3) *
        (cAllowance * actualPositiveFourBodyForm G theta N f +
          actualParticleContactEnergy G ((N+2)+2) f.val) := by
  let p : Core (OrbitalIndex G theta) ℂ :=
    ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val
  let B : ℝ := cAllowance * actualPositiveFourBodyForm G theta N f +
    actualParticleContactEnergy G ((N+2)+2) f.val
  let L : ℝ := ∑ d ∈ Finset.range 9, 2*(-1/2:ℝ)^d*w3RelativeForm G theta d p
  let Q : ℝ := ∑ d ∈ Finset.range 9, w3RelativeForm G theta d p
  change lowRelativeEnergyForm G theta p ≤ originalSingleForm G theta p +
    sAllowance * (c9 + TorusLean.Shared.BosonSystole20Scalar.delta * c3) * B
  have hcut : Q ≤ c3 * sAllowance * B := actual_relative_cutoff_eight_payment G theta N f hG
  have hdelta : 0 ≤ (TorusLean.BosonFiniteCertificate.delta : ℝ) := by
    norm_num [TorusLean.BosonFiniteCertificate.delta]
  have hpaid := mul_le_mul_of_nonneg_left hcut hdelta
  have htail := actual_originalSingleForm_low_payment G theta N f hG
  change L - c9 * sAllowance * B ≤ originalSingleForm G theta p at htail
  have hlow : L ≤ originalSingleForm G theta p + c9 * sAllowance * B :=
    sub_le_iff_le_add.mp htail
  have hexpand : lowRelativeEnergyForm G theta p =
      L + (TorusLean.BosonFiniteCertificate.delta : ℝ) * Q := by
    simp only [lowRelativeEnergyForm,L,Q,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  rw [hexpand]
  calc
    _ ≤ L + (TorusLean.BosonFiniteCertificate.delta : ℝ) * (c3 * sAllowance * B) :=
      by linarith only [hpaid]
    _ ≤ (originalSingleForm G theta p + c9 * sAllowance * B) +
        (TorusLean.BosonFiniteCertificate.delta : ℝ) * (c3 * sAllowance * B) :=
      by linarith only [hlow]
    _ = _ := by
      have hd : (TorusLean.BosonFiniteCertificate.delta : ℝ) =
          TorusLean.Shared.BosonSystole20Scalar.delta := by
        norm_num [TorusLean.BosonFiniteCertificate.delta,TorusLean.Shared.BosonSystole20Scalar.delta]
      rw [hd]
      ring

/-- Actual original nine-block M3 source L3 density, with the original mu2
source / mu3 relative transport already discharged, is bounded uniformly in N.
The right-hand side uses the unchanged original S3, H and S4 forms. -/
theorem originalM3SourceCellForm_le_originalSingleForm_payment
    (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (hG : 20 ≤ systole G) :
    originalM3SourceCellForm G theta
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val ≤
    originalSingleForm G theta ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val +
      sAllowance * (c9 + TorusLean.Shared.BosonSystole20Scalar.delta * c3) *
        (cAllowance * actualPositiveFourBodyForm G theta N f +
          actualParticleContactEnergy G ((N+2)+2) f.val) :=
  (originalM3SourceCellForm_le_low_energy G theta _).trans
    (lowRelativeEnergyForm_le_originalSingleForm_payment G theta N f hG)

#print axioms actual_relative_cutoff_eight_payment
#print axioms lowRelativeEnergyForm_le_originalSingleForm_payment
#print axioms originalM3SourceCellForm_le_originalSingleForm_payment
end TorusLean.Shared.BosonNatThreeSourceEnergyPayment
