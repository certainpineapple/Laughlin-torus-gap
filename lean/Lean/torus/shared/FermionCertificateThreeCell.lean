import torus.shared.FermionCertificateThreeRows
import torus.shared.ThermalCoherentFermionAnchoredJacobiAbsolute

/-! The actual lambda-cross and square at each original row/auxiliary
index, integrated using the genuine same-cell COM identity. No relative
orthogonality or S3 payment is assumed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAbsolute
open scoped BigOperators ComplexConjugate

def coupledRow (G : Geometry) (theta : Twist) (T : ℕ) (a : Fin (T+1) → ℝ)
    (R : ℂ) (x : Space (physicalQ G theta)) : Space (physicalQ G theta) :=
  ∑ z : Fin (T+1), (a z:ℂ) • coupledThreeRemoval G theta T z R x

private theorem coupledRow_cross_expand (G : Geometry) (theta : Twist) (T : ℕ)
    (a b : Fin (T+1) → ℝ) (x y : Space (physicalQ G theta)) (R : ℂ) :
    occupationInner (physicalQ G theta) (coupledRow G theta T a R x) (coupledRow G theta T b R y)=
      ∑ z : Fin (T+1), ∑ w : Fin (T+1), (a z:ℂ)*(b w:ℂ)*
        jacobiRemovalCross G theta x y (T-z.val) z.val (T-w.val) w.val R := by
  simp only [coupledRow,occupationInner_sum_left,occupationInner_sum_right,
    occupationInner_smul_left,occupationInner_smul_right,Complex.star_def,
    Complex.conj_ofReal,Finset.mul_sum,mul_assoc,coupledThreeRemoval,jacobiRemovalCross]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  ring

theorem coupledRow_cross_integrable (G : Geometry) (theta : Twist) (T : ℕ)
    (a b : Fin (T+1) → ℝ) (x y : Space (physicalQ G theta)) :
    Integrable (fun R => occupationInner (physicalQ G theta)
      (coupledRow G theta T a R x) (coupledRow G theta T b R y)) (cellMeasure G 2) := by
  simp_rw [coupledRow_cross_expand]
  exact integrable_finsetSum _ (fun z _ => integrable_finsetSum _ (fun w _ =>
    (jacobiRemovalCross_integrable G theta x y (T-z.val) z.val (T-w.val) w.val 2).const_mul _))

/-- Finite true COM trace for arbitrary original real coefficient rows. -/
theorem coupledRow_cross_cell (G : Geometry) (theta : Twist) (T : ℕ)
    (a b : Fin (T+1) → ℝ) (x y : Space (physicalQ G theta)) :
    (∫ R, occupationInner (physicalQ G theta)
      (coupledRow G theta T a R x) (coupledRow G theta T b R y) ∂cellMeasure G 2)=
      (2/3:ℂ)*∑ z : Fin (T+1), (a z:ℂ)*(b z:ℂ)*relativeCrossIntegral G theta x y z.val := by
  classical
  let J (z w : Fin (T+1)) (R : ℂ) : ℂ :=
    (a z:ℂ)*(b w:ℂ)*
      jacobiRemovalCross G theta x y (T-z.val) z.val (T-w.val) w.val R
  have hJ (z w : Fin (T+1)) : Integrable (J z w) (cellMeasure G 2) :=
    (jacobiRemovalCross_integrable G theta x y (T-z.val) z.val (T-w.val) w.val 2).const_mul
      ((a z:ℂ)*(b w:ℂ))
  have hsum (z : Fin (T+1)) :
      Integrable (fun R => ∑ w : Fin (T+1), J z w R) (cellMeasure G 2) :=
    integrable_finsetSum Finset.univ (fun w _ => hJ z w)
  simp_rw [coupledRow_cross_expand]
  change (∫ R, ∑ z : Fin (T+1), ∑ w : Fin (T+1), J z w R ∂cellMeasure G 2)=_
  rw [integral_finsetSum Finset.univ (fun z _ => hsum z),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [integral_finsetSum Finset.univ (fun w _ => hJ z w)]
  simp only [J]
  simp_rw [integral_const_mul,jacobiRemovalCross_same_cell]
  rw [Finset.sum_eq_single z]
  · simp only [if_true,relativeCrossIntegral]
    ring
  · intro w hw hne
    have hn : T-z.val ≠ T-w.val := by
      have hz' := z.isLt
      have hw' := w.isLt
      have hv : z.val≠w.val := fun h => hne (Fin.ext h.symm)
      omega
    simp only [if_neg hn,mul_zero]
  · simp

/-- Literal original row summand, including both Hermitian lambda-cross slots. -/
def originalThreeRowBlock (G : Geometry) (theta : Twist) (r : CertificateRow)
    (i : Fin 9) (R : ℂ) (x : Space (physicalQ G theta)) : ℂ :=
  (certificateLambda r:ℂ)*
    (occupationInner (physicalQ G theta)
      (localJetAnnihilate G theta i.val R (pairDescendant G theta (certificateRowData r).1 R x))
      (certificateRowOutput G theta r R x i)+
     occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
      (localJetAnnihilate G theta i.val R (pairDescendant G theta (certificateRowData r).1 R x)))+
    occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
      (certificateRowOutput G theta r R x i)

/-- Exact finite original normal-three-zero density. -/
theorem certificateNormalThreeZeroAt_eq_blocks (G : Geometry) (theta : Twist)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    certificateNormalThreeZeroAt G theta R x=
      ∑ r : CertificateRow, ∑ i : Fin 9, (originalThreeRowBlock G theta r i R x).re := by
  unfold certificateNormalThreeZeroAt
  apply Finset.sum_congr rfl
  intro r hr
  have he : (∑ i : Fin 9, originalThreeRowBlock G theta r i R x)=
      certificateCrossAt G theta r R x+
        ∑ i : Fin 9, occupationInner (physicalQ G theta)
          (certificateRowOutput G theta r R x i) (certificateRowOutput G theta r R x i) := by
    simp only [originalThreeRowBlock,certificateCrossAt,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  have h := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.add_re,occupationInner_self,Complex.ofReal_re] using h.symm

def rowEigenCoefficient (r : CertificateRow) (z T : ℕ) : ℝ :=
  2*certificateLambda r*sThree z T (certificateRowData r).1*rowCoupledCoefficient r z T+
    (rowCoupledCoefficient r z T)^2

/-- Each original physical block gives exactly the summand of eq:F-ez.
The 2/3 converts its mu3 highest source back to the original mu2 convention. -/
theorem originalThreeRowBlock_cell (G : Geometry) (theta : Twist)
    (r : CertificateRow) (i : Fin 9) (x : Space (physicalQ G theta)) :
    (∫ R, originalThreeRowBlock G theta r i R x ∂cellMeasure G 2)=
      (2/3:ℂ)*∑ z : Fin ((certificateRowData r).1+i.val+1),
        (rowEigenCoefficient r z.val ((certificateRowData r).1+i.val):ℂ)*
          relativeCrossIntegral G theta x x z.val := by
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
  have hcross : Integrable (fun R => (certificateLambda r:ℂ)*
      (occupationInner (physicalQ G theta) (coupledRow G theta T a R x) (coupledRow G theta T b R x)+
        occupationInner (physicalQ G theta) (coupledRow G theta T b R x) (coupledRow G theta T a R x)))
      (cellMeasure G 2) := by
    simpa only [Pi.add_apply] using
      ((coupledRow_cross_integrable G theta T a b x x).add
        (coupledRow_cross_integrable G theta T b a x x)).const_mul (certificateLambda r:ℂ)
  rw [integral_add hcross (coupledRow_cross_integrable G theta T b b x x),integral_const_mul,
    integral_add (coupledRow_cross_integrable G theta T a b x x)
      (coupledRow_cross_integrable G theta T b a x x)]
  simp_rw [coupledRow_cross_cell]
  simp only [mul_add,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp only [a,b,T,rowEigenCoefficient]
  push_cast
  ring

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
