import torus.shared.FermionCertificateThreeSupport
import torus.shared.FermionLocalJetDecomposition

/-! The original seven-row normal-three-zero energy, not an abstract matrix
proxy, is the finite e_z relative energy in the manuscript's mu2 convention. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.PhysicalFermionHighTail
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAbsolute
open scoped BigOperators ComplexConjugate

/-- Real energy density of the actual relative removal D_z. -/
def relativeEnergy (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (z : ℕ) (R : ℂ) : ℝ :=
  occupationNormSq (physicalQ G theta) (paperRelativeRemoval G theta z R x)

theorem relativeEnergy_nonneg (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (z : ℕ) (R : ℂ) : 0≤relativeEnergy G theta x z R :=
  occupationNormSq_nonneg _ _

theorem relativeEnergy_integrable (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (z k : ℕ) :
    Integrable (relativeEnergy G theta x z) (cellMeasure G k) := by
  have h : Integrable (fun R => (relativeRemovalCross G theta x x z z R).re)
      (cellMeasure G k) := (relativeRemovalCross_integrable G theta x x z z k).re
  change Integrable (fun R => occupationNormSq (physicalQ G theta)
    (paperRelativeRemoval G theta z R x)) (cellMeasure G k)
  simpa only [relativeRemovalCross,formalRemoval_relative_eq_paper,
    occupationInner_self,Complex.ofReal_re] using h

theorem relativeCrossIntegral_self (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (z : ℕ) :
    relativeCrossIntegral G theta x x z=
      ((∫ R, relativeEnergy G theta x z R ∂cellMeasure G 3):ℂ) := by
  simp only [relativeCrossIntegral,relativeRemovalCross,formalRemoval_relative_eq_paper,
    occupationInner_self,relativeEnergy,integral_complex_ofReal]

theorem originalThreeRowBlock_integrable (G : Geometry) (theta : Twist)
    (r : CertificateRow) (i : Fin 9) (x : Space (physicalQ G theta)) :
    Integrable (fun R => originalThreeRowBlock G theta r i R x) (cellMeasure G 2) := by
  let T := (certificateRowData r).1+i.val
  let a : Fin (T+1) → ℝ := fun z => sThree z.val T (certificateRowData r).1
  let b : Fin (T+1) → ℝ := fun z => rowCoupledCoefficient r z.val T
  have hy (R : ℂ) : certificateRowOutput G theta r R x i=coupledRow G theta T b R x := by
    rw [certificateRowOutput_eq_degree,degreeRowOutput_coupled]
    rfl
  have hu (R : ℂ) : localJetAnnihilate G theta i.val R
      (pairDescendant G theta (certificateRowData r).1 R x)=coupledRow G theta T a R x :=
    certificateLambdaInput_coupled G theta r i R x
  simp only [originalThreeRowBlock,hy,hu]
  exact (((coupledRow_cross_integrable G theta T a b x x).add
    (coupledRow_cross_integrable G theta T b a x x)).const_mul _).add
      (coupledRow_cross_integrable G theta T b b x x)

/-- Full finite original physical sum, with its true charge-three COM factor. -/
theorem certificateThreeZeroEnergy_mu3_sum (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateThreeZeroEnergy G theta x=
      (2/3:ℝ)*∑ z ∈ Finset.range 16, threeEigenvalue z*
        (∫ R, relativeEnergy G theta x z R ∂cellMeasure G 3) := by
  have hi := integrable_finsetSum Finset.univ (fun r _ =>
    integrable_finsetSum Finset.univ (fun i _ => originalThreeRowBlock_integrable G theta r i x))
  have hr : (∫ R, (∑ r : CertificateRow, ∑ i : Fin 9,
      originalThreeRowBlock G theta r i R x).re ∂cellMeasure G 2)=
      (∫ R, ∑ r : CertificateRow, ∑ i : Fin 9,
        originalThreeRowBlock G theta r i R x ∂cellMeasure G 2).re := integral_re hi
  have hc : (∫ R, ∑ r : CertificateRow, ∑ i : Fin 9,
      originalThreeRowBlock G theta r i R x ∂cellMeasure G 2)=
      (2/3:ℂ)*∑ z ∈ Finset.range 16, (threeEigenvalue z:ℂ)*
        relativeCrossIntegral G theta x x z := by
    rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun i _ =>
      originalThreeRowBlock_integrable G theta r i x))]
    simp_rw [integral_finsetSum _ (fun i _ => originalThreeRowBlock_integrable G theta _ i x),
      originalThreeRowBlock_cell]
    simp_rw [← Finset.mul_sum]
    rw [original_three_blocks_aggregate (relativeCrossIntegral G theta x x)]
  unfold certificateThreeZeroEnergy
  simp_rw [certificateNormalThreeZeroAt_eq_blocks]
  simp only [Complex.re_sum] at hr
  rw [hr,hc]
  have htwo : (2/3:ℂ).re=(2/3:ℝ) := by norm_num [Complex.div_re]
  simp only [relativeCrossIntegral_self,integral_complex_ofReal,Complex.mul_re,Complex.mul_im,
    Complex.re_sum,Complex.im_sum,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,sub_zero,add_zero,Finset.sum_const_zero,htwo]

/-- Literal mu3/mu2 conversion for an arbitrary real integrand. -/
theorem two_thirds_mu3_integral (G : Geometry) (F : ℂ→ℝ) :
    (2/3:ℝ)*(∫ R, F R ∂cellMeasure G 3)=∫ R, F R ∂cellMeasure G 2 := by
  have hm : cellMeasure G 3=ENNReal.ofReal (3/2:ℝ) • cellMeasure G 2 := by
    unfold cellMeasure
    rw [smul_smul,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3/2)]
    exact congrArg (fun c : ℝ => ENNReal.ofReal c • volume.restrict (cell G))
      (by push_cast; ring)
  rw [hm,integral_smul_measure,ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤3/2),smul_eq_mul]
  ring

/-- Original K3^0 in exactly the manuscript's finite e_z, D_z, and mu2.
All lambda-crosses and squared rows are consumed from their physical definitions. -/
theorem certificateThreeZeroEnergy_eq_relative (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateThreeZeroEnergy G theta x=
      ∫ R, ∑ z ∈ Finset.range 16, threeEigenvalue z*
        occupationNormSq (physicalQ G theta) (paperRelativeRemoval G theta z R x)
          ∂cellMeasure G 2 := by
  rw [certificateThreeZeroEnergy_mu3_sum]
  have he : (∑ z ∈ Finset.range 16, threeEigenvalue z*
      (∫ R, relativeEnergy G theta x z R ∂cellMeasure G 3))=
      ∫ R, ∑ z ∈ Finset.range 16, threeEigenvalue z*relativeEnergy G theta x z R
        ∂cellMeasure G 3 := by
    rw [integral_finsetSum _ (fun z _ => (relativeEnergy_integrable G theta x z 3).const_mul _)]
    simp only [integral_const_mul]
  rw [he,two_thirds_mu3_integral]
  rfl

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
