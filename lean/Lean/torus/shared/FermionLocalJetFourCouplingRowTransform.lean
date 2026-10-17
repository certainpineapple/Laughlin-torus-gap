import torus.shared.FermionLocalJetFourCouplingDescendants
import torus.shared.FermionLocalJetFourCouplingRowExpansion

/-! Exact change of basis of the original normal-four physical density.
All mixed relative degrees and copy indices remain present before COM
integration. This file does not discard off-diagonal COM matrix units. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open scoped BigOperators ComplexConjugate

/-- Full actual occupation matrix unit under the complete S transform.
The two inputs have the same original total degree, not necessarily the
same relative degree after transformation. -/
theorem fourInputAmplitude_inner_coupled (G : Geometry) (theta : Twist)
    (T p j k q l i : ℕ) (hp : p+j+k=T) (hq : q+l+i=T)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (fourInputAmplitude G theta p j k R x) (fourInputAmplitude G theta q l i R x) =
      ∑ c : HalfInputIndex T, ∑ d : HalfInputIndex T,
        paperS45 (fullCopyRelative T c) (fullCopyDegree T c) T p j k *
          paperS45 (fullCopyRelative T d) (fullCopyDegree T d) T q l i *
            occupationInner (physicalQ G theta)
              (descendantFourAmplitude G theta (fullCopyDegree T c) T (fullCopyRelative T c) R x)
              (descendantFourAmplitude G theta (fullCopyDegree T d) T (fullCopyRelative T d) R x) := by
  rw [descendantFourAmplitude_reconstruct G theta T p j k hp R x,
    descendantFourAmplitude_reconstruct G theta T q l i hq R x]
  simp only [occupationInner_sum_left,occupationInner_smul_left,
    occupationInner_sum_right,occupationInner_smul_right,paperS45_star,
    Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Literal F-normal4 after the finite orthogonal coupling. The two copy
degrees c.D and d.D have not been identified: that is a later true cell-ladder
integral theorem, not a formal coefficient simplification. -/
theorem certificateNormalFourAt_coupled (G : Geometry) (theta : Twist)
    (rho : CertificateRow) (R : ℂ) (x : Space (physicalQ G theta)) :
    certificateNormalFourAt G theta rho R x =
      -(∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
        (certificateAlpha rho a : ℂ) * (certificateAlpha rho b : ℂ) *
          (∑ c : HalfInputIndex (certificateFourTotal rho a b),
           ∑ d : HalfInputIndex (certificateFourTotal rho a b),
            paperS45 (fullCopyRelative _ c) (fullCopyDegree _ c) (certificateFourTotal rho a b)
                (certificateEntryData rho a).1 (certificateEntryData rho a).2.1 (certificateJetIndex rho b) *
              paperS45 (fullCopyRelative _ d) (fullCopyDegree _ d) (certificateFourTotal rho a b)
                (certificateEntryData rho b).1 (certificateEntryData rho b).2.1 (certificateJetIndex rho a) *
              occupationInner (physicalQ G theta)
                (descendantFourAmplitude G theta (fullCopyDegree _ c) (certificateFourTotal rho a b)
                  (fullCopyRelative _ c) R x)
                (descendantFourAmplitude G theta (fullCopyDegree _ d) (certificateFourTotal rho a b)
                  (fullCopyRelative _ d) R x))) := by
  rw [certificateNormalFourAt_eq_entries]
  apply congrArg (fun z : ℂ => -z)
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg (fun z : ℂ => (certificateAlpha rho a : ℂ) * (certificateAlpha rho b : ℂ) * z)
  exact fourInputAmplitude_inner_coupled G theta (certificateFourTotal rho a b)
    _ _ _ _ _ _ rfl (certificateFourTotal_exchange rho b a) R x

#print axioms fourInputAmplitude_inner_coupled
#print axioms certificateNormalFourAt_coupled
end TorusLean.Shared.FermionLocalJet.FourCoupling
