import torus.shared.FermionLocalJetFourCouplingRowTransform

/-! Exact original K4 with both complete coupling transforms exposed.
All mixed relative degrees and all copy indices remain present under the
original mu2 integral. Continuity makes each matrix unit genuinely integrable.
No off-diagonal COM unit is deleted by coefficient simplification. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionM1NearProjectionPhysical (OccupationIndex)
open scoped BigOperators ComplexConjugate

 def fullFourCoupledCoefficient (rho : CertificateRow) (a b : CertificateEntry rho)
    (c d : HalfInputIndex (certificateFourTotal rho a b)) : ℂ :=
  (certificateAlpha rho a : ℂ) * (certificateAlpha rho b : ℂ) *
    paperS45 (fullCopyRelative _ c) (fullCopyDegree _ c) (certificateFourTotal rho a b)
      (certificateEntryData rho a).1 (certificateEntryData rho a).2.1 (certificateJetIndex rho b) *
    paperS45 (fullCopyRelative _ d) (fullCopyDegree _ d) (certificateFourTotal rho a b)
      (certificateEntryData rho b).1 (certificateEntryData rho b).2.1 (certificateJetIndex rho a)

 def fullFourDescendantUnit (G : Geometry) (theta : Twist) (T : ℕ)
    (c d : HalfInputIndex T) (R : ℂ) (x : Space (physicalQ G theta)) : ℂ :=
  occupationInner (physicalQ G theta)
    (descendantFourAmplitude G theta (fullCopyDegree T c) T (fullCopyRelative T c) R x)
    (descendantFourAmplitude G theta (fullCopyDegree T d) T (fullCopyRelative T d) R x)

 theorem descendantFourAmplitude_coordinate_continuous (G : Geometry) (theta : Twist)
    (D T r : ℕ) (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) :
    Continuous (fun R => (occupationBasis (physicalQ G theta)).repr
      (descendantFourAmplitude G theta D T r R x) A) := by
  simp only [descendantFourAmplitude, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact continuous_finsetSum _ (fun q _ => continuous_const.mul
    (fourInputAmplitude_coordinate_continuous G theta _ _ _ x A))

 theorem fullFourDescendantUnit_continuous (G : Geometry) (theta : Twist) (T : ℕ)
    (c d : HalfInputIndex T) (x : Space (physicalQ G theta)) :
    Continuous (fun R => fullFourDescendantUnit G theta T c d R x) := by
  unfold fullFourDescendantUnit occupationInner
  exact continuous_finsetSum _ (fun A _ =>
    (descendantFourAmplitude_coordinate_continuous G theta _ _ _ x A).star.mul
      (descendantFourAmplitude_coordinate_continuous G theta _ _ _ x A))

 theorem fullFourDescendantUnit_integrable (G : Geometry) (theta : Twist) (T charge : ℕ)
    (c d : HalfInputIndex T) (x : Space (physicalQ G theta)) :
    Integrable (fun R => fullFourDescendantUnit G theta T c d R x)
      (cellMeasure G charge) :=
  continuous_integrable_cellMeasure G charge
    (fullFourDescendantUnit_continuous G theta T c d x)

/-- Original negative ordered alpha-alpha density, both Gamma factors,
all mixed D,D' and all r,s, at the unchanged physical annihilators. -/
 theorem certificateFourEnergy_eq_full_coupled_integral (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateFourEnergy G theta x =
      ∫ R, ∑ rho : CertificateRow,
        (-(∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
          ∑ c : HalfInputIndex (certificateFourTotal rho a b),
          ∑ d : HalfInputIndex (certificateFourTotal rho a b),
            fullFourCoupledCoefficient rho a b c d *
              fullFourDescendantUnit G theta (certificateFourTotal rho a b) c d R x)).re
      ∂cellMeasure G 2 := by
  unfold certificateFourEnergy
  apply integral_congr_ae
  filter_upwards [] with R
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [certificateNormalFourAt_coupled]
  simp only [fullFourCoupledCoefficient, fullFourDescendantUnit,
    Finset.mul_sum, mul_assoc]

#print axioms descendantFourAmplitude_coordinate_continuous
#print axioms fullFourDescendantUnit_continuous
#print axioms fullFourDescendantUnit_integrable
#print axioms certificateFourEnergy_eq_full_coupled_integral
end TorusLean.Shared.FermionLocalJet.FourCoupling
