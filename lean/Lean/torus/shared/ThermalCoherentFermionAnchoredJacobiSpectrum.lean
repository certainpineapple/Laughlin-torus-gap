import torus.shared.ThermalCoherentFermionAnchoredJacobiAbsolute

/-! Original physical S3 relative spectral identity. The full product series
is absolutely summable before the COM or antidiagonal rearrangement. Its
weights are derived from the two original columns and the real charge-three
COM trace; no relative spectrum or target payment is supplied as a premise. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSpectrum
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.PhysicalFermionHighTail
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOriginalSource
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAbsolute
open TorusLean.Fermion.LatticePacking TorusLean.Fermion.UniformTail
open scoped BigOperators ComplexConjugate

theorem physicalCOM_relative_hasSum (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    HasSum (fun d => (q d:ℂ)*relativeCrossIntegral G theta x y d)
      (∑' dn : ℕ×ℕ, physicalCOMTerm G theta x y dn) := by
  have hs := (physicalCOM_summable_norm G theta hG x y).of_norm
  have hn (d : ℕ) : HasSum (fun n => physicalCOMTerm G theta x y (d,n))
      ((q d:ℂ)*relativeCrossIntegral G theta x y d) := by
    have hw : HasSum (fun n => (fermionAnchoredJacobiCrossWeight d n:ℂ)) (q d:ℂ) :=
      Complex.hasSum_ofReal.mpr (hasSum_fermionAnchoredJacobiCrossWeight d)
    exact hw.mul_right (relativeCrossIntegral G theta x y d)
  exact HasSum.prod_fiberwise hs.hasSum hn

theorem physicalCOM_antidiagonal_hasSum (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    HasSum (fun l => ∑ d ∈ Finset.range (l+1),
      (fermionAnchoredJacobiCrossWeight d (l-d):ℂ)*relativeCrossIntegral G theta x y d)
      (∑' d, (q d:ℂ)*relativeCrossIntegral G theta x y d) := by
  have hs := (physicalCOM_summable_norm G theta hG x y).of_norm
  have h := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hs.hasSum).sigma
    (fun l => hasSum_fintype (fun dn : ↥(Finset.antidiagonal l) =>
      physicalCOMTerm G theta x y dn.val))
  have h' : HasSum (fun l => ∑ dn ∈ Finset.antidiagonal l, physicalCOMTerm G theta x y dn)
      (∑' dn : ℕ×ℕ, physicalCOMTerm G theta x y dn) := by
    apply HasSum.congr_fun h
    intro l
    exact (Finset.sum_coe_sort (Finset.antidiagonal l) (physicalCOMTerm G theta x y)).symm
  rw [← (physicalCOM_relative_hasSum G theta hG x y).tsum_eq] at h'
  simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,physicalCOMTerm] using h'

/-- Physical source through all analytic exchanges and true COM summation. -/
theorem matrixSingleContraction_relative_tsum (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) y)=
      ∑' d, (q d:ℂ)*relativeCrossIntegral G theta x y d := by
  have hs := matrixSingleContraction_original_source_hasSum G theta hG x y
  simp_rw [originalSourceCross_integral_jacobi] at hs
  exact hs.unique (physicalCOM_antidiagonal_hasSum G theta hG x y)

/-- The original torus S3, with the literal mu3 relative source integral. -/
theorem matrixSingleContraction_relative_integral (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) y)=
      ∫ R, ∑' d, (q d:ℂ)*relativeRemovalCross G theta x y d d R ∂cellMeasure G 3 := by
  have hi (d : ℕ) : Integrable (fun R => (q d:ℂ)*relativeRemovalCross G theta x y d d R)
      (cellMeasure G 3) := (relativeRemovalCross_integrable G theta x y d d 3).const_mul _
  have hh := hasSum_integral_of_summable_integral_norm hi
    (original_relative_series_summable_integral_norm G theta hG x y)
  simp_rw [integral_const_mul] at hh
  rw [matrixSingleContraction_relative_tsum G theta hG x y]
  exact hh.tsum_eq

/-- Whole-Fock real quadratic form with the original paper D_d and q_d.
The q_0 scalar is not used to fake a zero source. Pauli zeros are separate. -/
theorem matrixSingleContraction_paper_relative_energy (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x : Space (physicalQ G theta)) :
    (occupationInner (physicalQ G theta) x
      (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) x)).re=
      ∫ R, ∑' d, q d*occupationNormSq (physicalQ G theta)
        (paperRelativeRemoval G theta d R x) ∂cellMeasure G 3 := by
  have h := matrixSingleContraction_relative_integral G theta hG x x
  simp only [relativeRemovalCross,formalRemoval_relative_eq_paper,occupationInner_self,
    ← Complex.ofReal_mul,← Complex.ofReal_tsum,integral_complex_ofReal] at h
  exact congrArg Complex.re h

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSpectrum
