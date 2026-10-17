import torus.shared.FermionLocalJetFourCouplingRowMatrix
import torus.shared.FermionLocalJetDecomposition

/-! Original normal-four term expanded over the literal ordered row entries.
This preserves the true c_k c_j B_p amplitudes, the CAR minus sign, and mu2.
It is the physical input to the subsequent COM integration, not that integration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open scoped BigOperators ComplexConjugate

private theorem certificate_group_bisum {V : Type*} [AddCommMonoid V]
    (rho : CertificateRow) (f : CertificateEntry rho → CertificateEntry rho → V) :
    (∑ i : Fin 9, ∑ k : Fin 9,
      ∑ a ∈ Finset.univ.filter (fun a : CertificateEntry rho => certificateEntryJet rho a=i),
      ∑ b ∈ Finset.univ.filter (fun b : CertificateEntry rho => certificateEntryJet rho b=k),
        f a b) = ∑ a, ∑ b, f a b := by
  classical
  calc
    _ = ∑ i : Fin 9,
        ∑ a ∈ Finset.univ.filter (fun a : CertificateEntry rho => certificateEntryJet rho a=i),
        ∑ k : Fin 9,
        ∑ b ∈ Finset.univ.filter (fun b : CertificateEntry rho => certificateEntryJet rho b=k),
          f a b := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ i : Fin 9,
        ∑ a ∈ Finset.univ.filter (fun a : CertificateEntry rho => certificateEntryJet rho a=i),
        ∑ b, f a b := by simp_rw [certificate_group_sum]
    _ = _ := certificate_group_sum rho _

/-- The actual F-normal4 identity in precisely the manuscript's ordered
support indices i=p+j-t and k=q+l-t. No local Gram correction is inserted. -/
theorem certificateNormalFourAt_eq_entries (G : Geometry) (theta : Twist)
    (rho : CertificateRow) (R : ℂ) (x : Space (physicalQ G theta)) :
    certificateNormalFourAt G theta rho R x =
      -(∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
        (certificateAlpha rho a : ℂ) * (certificateAlpha rho b : ℂ) *
          occupationInner (physicalQ G theta)
            (fourInputAmplitude G theta (certificateEntryData rho a).1
              (certificateEntryData rho a).2.1 (certificateJetIndex rho b) R x)
            (fourInputAmplitude G theta (certificateEntryData rho b).1
              (certificateEntryData rho b).2.1 (certificateJetIndex rho a) R x)) := by
  classical
  have he (i k : Fin 9) :
      occupationInner (physicalQ G theta)
        (localJetAnnihilate G theta k R (certificateRowOutput G theta rho R x i))
        (localJetAnnihilate G theta i R (certificateRowOutput G theta rho R x k)) =
      ∑ a ∈ Finset.univ.filter (fun a : CertificateEntry rho => certificateEntryJet rho a=i),
      ∑ b ∈ Finset.univ.filter (fun b : CertificateEntry rho => certificateEntryJet rho b=k),
        (certificateAlpha rho a : ℂ) * (certificateAlpha rho b : ℂ) *
          occupationInner (physicalQ G theta)
            (fourInputAmplitude G theta (certificateEntryData rho a).1
              (certificateEntryData rho a).2.1 (certificateJetIndex rho b) R x)
            (fourInputAmplitude G theta (certificateEntryData rho b).1
              (certificateEntryData rho b).2.1 (certificateJetIndex rho a) R x) := by
    simp only [certificateRowOutput,map_sum,map_smul]
    rw [occupationInner_sum_left]
    apply Finset.sum_congr rfl
    intro a ha
    rw [occupationInner_smul_left,occupationInner_sum_right,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hi : certificateJetIndex rho a=i.val :=
      congrArg Fin.val (Finset.mem_filter.mp ha).2
    have hk : certificateJetIndex rho b=k.val :=
      congrArg Fin.val (Finset.mem_filter.mp hb).2
    simp only [occupationInner_smul_right,Complex.star_def,Complex.conj_ofReal,
      fourInputAmplitude,certificateAmplitude,hi,hk]
    ring
  unfold certificateNormalFourAt
  simp_rw [he]
  rw [certificate_group_bisum]

/-- The exact original K4 integral with the original mu2 and every ordered
entry pair. Its identification with E_D still requires the COM theorem. -/
theorem certificateFourEnergy_eq_entries (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateFourEnergy G theta x =
      ∫ R, ∑ rho : CertificateRow,
        (-(∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
          (certificateAlpha rho a : ℂ) * (certificateAlpha rho b : ℂ) *
            occupationInner (physicalQ G theta)
              (fourInputAmplitude G theta (certificateEntryData rho a).1
                (certificateEntryData rho a).2.1 (certificateJetIndex rho b) R x)
              (fourInputAmplitude G theta (certificateEntryData rho b).1
                (certificateEntryData rho b).2.1 (certificateJetIndex rho a) R x))).re
      ∂cellMeasure G 2 := by
  unfold certificateFourEnergy
  simp_rw [certificateNormalFourAt_eq_entries]

#print axioms certificateNormalFourAt_eq_entries
#print axioms certificateFourEnergy_eq_entries
end TorusLean.Shared.FermionLocalJet.FourCoupling
