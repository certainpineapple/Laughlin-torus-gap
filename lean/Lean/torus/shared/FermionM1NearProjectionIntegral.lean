import torus.shared.FermionM1NearProjectionPhysical
import torus.shared.PhysicalFermionNormalSquareIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionM1NearProjectionPhysical
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.FermionRelativeFrame
open scoped BigOperators ComplexConjugate

theorem chargeTwo_operator_kernel (G : Geometry) (theta : Twist)
    (T : LLL G theta 2 →L[ℂ] LLL G theta 2) (R S : ℂ) :
    (T (evaluationKernel G theta 2 S)).val R =
      conj ((T.adjoint (evaluationKernel G theta 2 R)).val S) := by
  rw [← evaluationKernel_reproduces G theta 2 R,
    ← ContinuousLinearMap.adjoint_inner_left]
  rw [← evaluationKernel_reproduces G theta 2 S]
  exact (inner_conj_symm _ _).symm

theorem chargeTwo_operator_kernel_integrable (G : Geometry) (theta : Twist)
    (T : LLL G theta 2 →L[ℂ] LLL G theta 2) (f : LLL G theta 2) (R : ℂ) :
    Integrable (fun S => (T (evaluationKernel G theta 2 S)).val R * f.val S)
      (cellMeasure G 2) := by
  have h := cellInner_integrable G 2 _ _
    (rawLLL_continuous G theta 2 (T.adjoint (evaluationKernel G theta 2 R)))
    (rawLLL_continuous G theta 2 f)
  apply h.congr
  filter_upwards [] with S
  exact congrArg (fun z : ℂ => z * f.val S) (chargeTwo_operator_kernel G theta T R S).symm

theorem chargeTwo_operator_kernel_integral (G : Geometry) (theta : Twist)
    (T : LLL G theta 2 →L[ℂ] LLL G theta 2) (f : LLL G theta 2) (R : ℂ) :
    (∫ S, (T (evaluationKernel G theta 2 S)).val R * f.val S ∂cellMeasure G 2) =
      (T f).val R := by
  calc
    _ = ∫ S, conj ((T.adjoint (evaluationKernel G theta 2 R)).val S) * f.val S
        ∂cellMeasure G 2 := by
      apply integral_congr_ae
      filter_upwards [] with S
      rw [chargeTwo_operator_kernel]
    _ = inner ℂ (T.adjoint (evaluationKernel G theta 2 R)) f := rfl
    _ = _ := by rw [ContinuousLinearMap.adjoint_inner_left,evaluationKernel_reproduces]

/-- The actual double-CAR contraction is the operator kernel acting on the
original pair-output sections. The explicit kernel equality must be supplied
by the genuine QQ-adjoint theorem; no new Hamiltonian is defined here. -/
theorem matrixDoubleContraction_output_sections (G : Geometry) (theta : Twist)
    (T : LLL G theta 2 →L[ℂ] LLL G theta 2)
    (hT : ∀ R S, (T (evaluationKernel G theta 2 S)).val R = pairGramAt G theta R S)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta) y) =
      ∑ A : OccupationIndex G theta, inner ℂ (pairOutputSection G theta x A)
        (T (pairOutputSection G theta y A)) := by
  have hdensity (R S : ℂ) : occupationInner (physicalQ G theta) x
      ((pairCreateAt G theta R * pairAt G theta S) y) =
      ∑ A : OccupationIndex G theta, conj ((pairOutputSection G theta x A).val R) *
        (pairOutputSection G theta y A).val S := by
    rw [Module.End.mul_apply,pairCreateAt_adjoint_right]
    simp only [pairOutputSection_apply]
    rfl
  have hi (R : ℂ) (A : OccupationIndex G theta) :
      Integrable (fun S => (T (evaluationKernel G theta 2 S)).val R *
        (conj ((pairOutputSection G theta x A).val R) *
          (pairOutputSection G theta y A).val S)) (cellMeasure G 2) := by
    convert (chargeTwo_operator_kernel_integrable G theta T (pairOutputSection G theta y A) R).const_mul
      (conj ((pairOutputSection G theta x A).val R)) using 1
    funext S
    ring
  have he (R : ℂ) (A : OccupationIndex G theta) :
      (∫ S, (T (evaluationKernel G theta 2 S)).val R *
        (conj ((pairOutputSection G theta x A).val R) *
          (pairOutputSection G theta y A).val S) ∂cellMeasure G 2) =
      conj ((pairOutputSection G theta x A).val R) * (T (pairOutputSection G theta y A)).val R := by
    calc
      _ = ∫ S, conj ((pairOutputSection G theta x A).val R) *
          ((T (evaluationKernel G theta 2 S)).val R * (pairOutputSection G theta y A).val S)
          ∂cellMeasure G 2 := by
        apply integral_congr_ae
        filter_upwards [] with S
        ring
      _ = _ := by rw [integral_const_mul,chargeTwo_operator_kernel_integral]
  rw [matrixDoubleContraction_integral]
  calc
    _ = ∫ R, ∑ A : OccupationIndex G theta,
        conj ((pairOutputSection G theta x A).val R) * (T (pairOutputSection G theta y A)).val R
        ∂cellMeasure G 2 := by
      apply integral_congr_ae
      filter_upwards [] with R
      calc
        _ = ∫ S, ∑ A : OccupationIndex G theta,
            (T (evaluationKernel G theta 2 S)).val R *
              (conj ((pairOutputSection G theta x A).val R) *
                (pairOutputSection G theta y A).val S) ∂cellMeasure G 2 := by
          apply integral_congr_ae
          filter_upwards [] with S
          rw [hdensity,← hT,Finset.mul_sum]
        _ = _ := by
          rw [integral_finsetSum (Finset.univ : Finset (OccupationIndex G theta)) (fun A _ => hi R A)]
          apply Finset.sum_congr rfl
          intro A hA
          exact he R A
    _ = _ := by
      exact integral_finsetSum (Finset.univ : Finset (OccupationIndex G theta))
        (fun A _ => cellInner_integrable G 2 _ _ (rawLLL_continuous G theta 2 (pairOutputSection G theta x A))
          (rawLLL_continuous G theta 2 (T (pairOutputSection G theta y A))))

end TorusLean.Shared.FermionM1NearProjectionPhysical
