import torus.shared.FermionLocalJetFourCouplingFiniteComparisonHermitian
import torus.shared.FermionLocalJetFourCouplingGramLift
import torus.shared.FermionLocalJetFourCouplingTarget

/-! The actual whole-Fock comparison at one cell point, obtained by raw
exterior insertion and its genuine occupation adjoint. No source isometry,
copy independence, Gram inverse, or pointwise positivity of K-E is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock Matrix
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open scoped BigOperators ComplexConjugate ComplexOrder

theorem original_four_pointwise_of_source_and_certificate (G : Geometry) (theta : Twist) (d : Fin 23)
    (hsource : ∀ r : OddMode (d.val+1),
      formalCoupledColumn (d.val+1) r =
        ∑ A : SlaterIndex (d.val+1),
          originalSlaterMatrix (d.val+1) A r • formalSlater (d.val+1) A)
    (hcert : (((originalSlaterMatrixFin (d.val+1))ᴴ * originalSlaterMatrixFin (d.val+1)) *
      fourComparisonFinMatrix (d.val+1) *
      ((originalSlaterMatrixFin (d.val+1))ᴴ * originalSlaterMatrixFin (d.val+1))).PosSemidef)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    (∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
      certificateFourMatrix (d.val+1) r.val.val s.val.val *
        occupationInner (physicalQ G theta)
          (coupledFourAmplitude G theta (d.val+1) r R x)
          (coupledFourAmplitude G theta (d.val+1) s R x)).re ≤
      2 * occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) (targetMode d.val) R x) +
      (3/1000000:ℝ) * ∑ r : OddMode (d.val+1), occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) r R x) := by
  classical
  let D := d.val+1
  let v (i : Fin ((D+1)/2)) := coupledFourAmplitude G theta D (originalCopyMode D i) R x
  let u (A : SlaterIndex D) := rawJetExteriorMap G theta R (formalSlater D A)
  have hv (i : Fin ((D+1)/2)) : v i =
      sourceRemoval (physicalQ G theta)
        (∑ A : SlaterIndex D, originalSlaterMatrixFin D A i • u A) x := by
    have hs : formalCoupledColumn D (originalCopyMode D i) =
        ∑ A : SlaterIndex D, originalSlaterMatrix D A (originalCopyMode D i) •
          formalSlater D A := hsource (originalCopyMode D i)
    dsimp only [v]
    rw [← formalRemoval_coupled]
    simp only [formalRemoval,hs,map_sum,map_smul,originalSlaterMatrixFin,u]
  have hp := sourceRemoval_gram_positive (physicalQ G theta) u
    (originalSlaterMatrixFin D) (fourComparisonFinMatrix D)
    (fourComparisonFinMatrix_hermitian D) hcert x
  simp_rw [← hv] at hp
  have hsub :
      (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2),
        fourComparisonFinMatrix D i j * occupationInner (physicalQ G theta) (v i) (v j)).re =
      (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2),
        fourCertificateDiagonal D i j * occupationInner (physicalQ G theta) (v i) (v j)).re -
      (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2),
        certificateFourMatrix D (2*i.val+1) (2*j.val+1) *
          occupationInner (physicalQ G theta) (v i) (v j)).re := by
    simp only [fourComparisonFinMatrix,Matrix.of_apply,Matrix.sub_apply,sub_mul,
      Finset.sum_sub_distrib,Complex.sub_re]
  have hE :
      (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2),
        certificateFourMatrix D (2*i.val+1) (2*j.val+1) *
          occupationInner (physicalQ G theta) (v i) (v j)) =
      ∑ r : OddMode D, ∑ s : OddMode D, certificateFourMatrix D r.val.val s.val.val *
        occupationInner (physicalQ G theta)
          (coupledFourAmplitude G theta D r R x) (coupledFourAmplitude G theta D s R x) := by
    let F (r s : OddMode D) := certificateFourMatrix D r.val.val s.val.val *
      occupationInner (physicalQ G theta)
        (coupledFourAmplitude G theta D r R x) (coupledFourAmplitude G theta D s R x)
    change (∑ i, ∑ j, F (originalCopyEquiv D i) (originalCopyEquiv D j)) = _
    rw [(originalCopyEquiv D).sum_comp (fun r => ∑ j, F r (originalCopyEquiv D j))]
    apply Finset.sum_congr rfl
    intro r hr
    exact (originalCopyEquiv D).sum_comp (F r)
  have hn :
      (∑ i : Fin ((D+1)/2), occupationNormSq (physicalQ G theta) (v i)) =
      ∑ r : OddMode D, occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta D r R x) :=
    (originalCopyEquiv D).sum_comp (fun r => occupationNormSq (physicalQ G theta)
      (coupledFourAmplitude G theta D r R x))
  let i0 : Fin ((D+1)/2) := ⟨0,by dsimp [D]; omega⟩
  have hi0 : originalCopyMode D i0=targetMode d.val := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  have hlabel (i : Fin ((D+1)/2)) : 2*i.val+1=1 ↔ i=i0 := by
    constructor
    · intro h
      apply Fin.ext
      dsimp only [i0]
      omega
    · rintro rfl
      rfl
  have hdiag :
      (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2),
        fourCertificateDiagonal D i j * occupationInner (physicalQ G theta) (v i) (v j)).re =
      2 * occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta D (targetMode d.val) R x) +
      (3/1000000:ℝ) * ∑ r : OddMode D, occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta D r R x) := by
    have hentry (i : Fin ((D+1)/2)) :
        ((((if 2*i.val+1=1 then 2 else 0)+(3/1000000:ℚ):ℚ):ℂ) *
          occupationInner (physicalQ G theta) (v i) (v i)).re =
        ((if 2*i.val+1=1 then 2 else 0)+(3/1000000:ℝ)) *
          occupationNormSq (physicalQ G theta) (v i) := by
      by_cases h : 2*i.val+1=1
      · simp only [if_pos h]
        norm_num [occupationInner_self,Complex.mul_re]
      · simp only [if_neg h]
        norm_num [occupationInner_self,Complex.mul_re]
    simp only [fourCertificateDiagonal,Matrix.diagonal_apply,ite_mul,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,if_true,Complex.re_sum]
    simp_rw [hentry,hlabel]
    simp only [add_mul,ite_mul,zero_mul,Finset.sum_add_distrib,
      Finset.sum_ite_eq',Finset.mem_univ,if_true,← Finset.mul_sum]
    rw [hn]
    simp only [v,hi0]
  rw [hsub,hdiag,hE] at hp
  exact sub_nonneg.mp hp


#print axioms original_four_pointwise_of_source_and_certificate
end TorusLean.Shared.FermionLocalJet.FourCoupling
