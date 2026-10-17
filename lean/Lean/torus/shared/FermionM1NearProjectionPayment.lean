import torus.shared.FermionM1NearProjectionIntegral
import torus.shared.FermionM1NearProjectionBound

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionM1NearProjectionPhysical
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionM1NearProjection
open TorusLean.Shared.PhysicalFermionExterior TorusLean.Shared.PhysicalFermionCarrier
open TorusLean.Shared.PhysicalFermionM1Contact
open scoped BigOperators ComplexConjugate

theorem matrixDoubleContraction_actual_QQ (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta) y) =
      ∑ A : OccupationIndex G theta, inner ℂ (pairOutputSection G theta x A)
        ((m1Q G theta) ((m1Q G theta).adjoint (pairOutputSection G theta y A))) :=
  matrixDoubleContraction_output_sections G theta ((m1Q G theta).comp (m1Q G theta).adjoint)
    (m1Q_gram_eq_pairGramAt G theta) x y

theorem matrixDoubleContraction_same_energy_error (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1≤L) (hL : L≤systole G) (x : Space (physicalQ G theta)) :
    |(occupationInner (physicalQ G theta) x
      (matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta) x)).re -
      (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re| ≤
      m1GramError L * (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  let E := (m1Q G theta).comp (m1Q G theta).adjoint - ContinuousLinearMap.id ℂ (LLL G theta 2)
  have he : (occupationInner (physicalQ G theta) x
      (matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta) x)).re -
      (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re =
      ∑ A : OccupationIndex G theta,
        (inner ℂ (pairOutputSection G theta x A) (E (pairOutputSection G theta x A))).re := by
    rw [matrixDoubleContraction_actual_QQ,physicalHamiltonian_output_sections]
    simp only [E,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,inner_sub_right,Complex.sub_re]
    rw [show ∀ v : OccupationIndex G theta → ℂ, (∑ A, v A).re = ∑ A, (v A).re from
      fun v => map_sum Complex.reCLM v Finset.univ]
    rw [show ∀ v : OccupationIndex G theta → ℂ, (∑ A, v A).re = ∑ A, (v A).re from
      fun v => map_sum Complex.reCLM v Finset.univ]
    exact (Finset.sum_sub_distrib _ _).symm
  rw [he,physicalHamiltonian_energy_output_sections,Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun A _ => m1Q_output_form_error G theta L hL1 hL (pairOutputSection G theta x A)))

theorem matrixDoubleContraction_same_energy_lower (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1≤L) (hL : L≤systole G) (x : Space (physicalQ G theta)) :
    (1-m1GramError L) * (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re ≤
      (occupationInner (physicalQ G theta) x
        (matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta) x)).re := by
  have h := (abs_le.mp (matrixDoubleContraction_same_energy_error G theta L hL1 hL x)).1
  nlinarith

theorem actual_doubleContraction_energy_lower (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1≤L) (hL : L≤systole G) (N : ℕ) (f : PhysicalFermion G theta N) :
    (1-m1GramError L)*actualFermionM1Energy G N f.val ≤
      (occupationInner (physicalQ G theta)
        ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta))
        (matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta)
          ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta)))).re := by
  rw [← physicalHamiltonian_actual_energy G theta N f]
  exact matrixDoubleContraction_same_energy_lower G theta L hL1 hL _

end TorusLean.Shared.FermionM1NearProjectionPhysical
