import torus.shared.FermionRelativeFrameSections

/-! The original CAR pair output, coefficient by coefficient in the actual
occupation basis, is a complete charge-two section.  This uses the proved
antisymmetrization of the original pair and does not change its Hamiltonian. -/
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

abbrev OccupationIndex (G : Geometry) (theta : Twist) := Finset (Fin (physicalQ G theta+1))

def pairOutputSection (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) : LLL G theta 2 :=
  ∑ p : FermionRelativeFrame.PairIndex G theta,
    ((occupationBasis (physicalQ G theta)).repr (modePairAnnihilate (physicalQ G theta) p x) A) •
      pairSection G theta p

theorem pairOutputSection_apply (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (A : OccupationIndex G theta) (R : ℂ) :
    (pairOutputSection G theta x A).val R =
      (occupationBasis (physicalQ G theta)).repr (pairAt G theta R x) A := by
  classical
  change lllEvaluation G theta 2 R (pairOutputSection G theta x A) = _
  rw [pairAt_section_expansion]
  simp only [pairOutputSection,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    lllEvaluation_apply,mul_comm]

theorem pairOutputSection_cross_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (A : OccupationIndex G theta) :
    Integrable (fun R => conj ((pairOutputSection G theta x A).val R) *
      (pairOutputSection G theta y A).val R) (cellMeasure G 2) :=
  cellInner_integrable G 2 _ _ (rawLLL_continuous G theta 2 _)
    (rawLLL_continuous G theta 2 _)

theorem physicalHamiltonian_output_sections (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x (physicalHamiltonian G theta y) =
      ∑ A : OccupationIndex G theta, inner ℂ (pairOutputSection G theta x A)
        (pairOutputSection G theta y A) := by
  have h (R : ℂ) : occupationInner (physicalQ G theta)
      (pairAt G theta R x) (pairAt G theta R y) =
      ∑ A : OccupationIndex G theta, conj ((pairOutputSection G theta x A).val R) *
        (pairOutputSection G theta y A).val R := by
    simp only [pairOutputSection_apply]
    rfl
  rw [physicalHamiltonian_inner_integral]
  simp_rw [h]
  exact integral_finsetSum (Finset.univ : Finset (OccupationIndex G theta))
    (fun A _ => pairOutputSection_cross_integrable G theta x y A)

theorem physicalHamiltonian_energy_output_sections (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re =
      ∑ A : OccupationIndex G theta, ‖pairOutputSection G theta x A‖^2 := by
  rw [physicalHamiltonian_output_sections]
  rw [show (∑ A : OccupationIndex G theta, inner ℂ (pairOutputSection G theta x A)
      (pairOutputSection G theta x A)).re = ∑ A : OccupationIndex G theta,
      (inner ℂ (pairOutputSection G theta x A) (pairOutputSection G theta x A)).re from
        map_sum Complex.reCLM _ _]
  apply Finset.sum_congr rfl
  intro A hA
  exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (pairOutputSection G theta x A)).symm

end TorusLean.Shared.FermionM1NearProjectionPhysical
