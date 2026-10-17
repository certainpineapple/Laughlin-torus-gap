import torus.shared.PhysicalFermionNormalSquareIntegral

/-! The constructed contact Hamiltonian genuinely preserves every exterior
particle sector. Its transport acts on the independently defined full physical
fermion carrier, so its squared form is the physical sector operator square. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionNormalSquare
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionCarrier
open TorusLean.Shared.PhysicalFermionExterior TorusLean.Shared.PhysicalFermionPairContraction
open TorusLean.Shared.PhysicalFermionPairLift TorusLean.Shared.PhysicalFermionM1Contact
open TorusLean.Shared.PhysicalBosonSector
open scoped BigOperators ComplexConjugate

lemma create_mem_exterior {Q N : ℕ} (i : Fin (Q+1)) (x : Exterior (Fin (Q+1)) N) :
    create i (x : Space Q) ∈ (⋀[ℂ]^(N+1) (Orbital Q)) := by
  classical
  have hx : (x : Space Q) = ∑ A : Occupation (Fin (Q+1)) N,
      (exteriorBasis _ N).repr x A • occupationBasis Q A.val := by
    conv_lhs => rw [← (exteriorBasis _ N).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, occupationBasis_eq_exteriorBasis]
  rw [hx, map_sum]
  apply Submodule.sum_mem
  intro A _
  rw [map_smul]
  apply Submodule.smul_mem
  by_cases hi : i ∈ A.val
  · rw [create_occupied Q i A.val hi]
    exact Submodule.zero_mem _
  · rw [create_unoccupied Q i A.val hi]
    apply Submodule.smul_mem
    have hc : (insert i A.val).card = N+1 := by rw [Finset.card_insert_of_notMem hi, A.property]
    rw [occupationBasis_eq_exteriorBasis (⟨insert i A.val,hc⟩ : Occupation (Fin (Q+1)) (N+1))]
    exact Subtype.property _

lemma rawCreate_mem_exterior {Q N : ℕ} (a : Orbital Q) (x : Exterior (Fin (Q+1)) N) :
    rawCreate Q a (x : Space Q) ∈ (⋀[ℂ]^(N+1) (Orbital Q)) := by
  change ExteriorAlgebra.ι ℂ a * (x : Space Q) ∈ _
  rw [vectorCreate_sum]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (create_mem_exterior i x)

lemma rawPairCreate_mem_exterior {Q N : ℕ} (a b : Orbital Q)
    (x : Exterior (Fin (Q+1)) N) :
    rawPairCreate Q a b (x : Space Q) ∈ (⋀[ℂ]^(N+2) (Orbital Q)) :=
  rawCreate_mem_exterior a ⟨rawCreate Q b x, rawCreate_mem_exterior b x⟩

/-- Degree preservation follows from the actual original pair operations,
including the scalar vacuum and one-particle sectors. -/
theorem matrixHamiltonian_mem_exterior {Q : ℕ}
    (W : Matrix (PairIndex Q) (PairIndex Q) ℂ) (N : ℕ) (x : Exterior (Fin (Q+1)) N) :
    matrixHamiltonian Q W (x : Space Q) ∈ (⋀[ℂ]^N (Orbital Q)) := by
  classical
  match N with
  | 0 =>
      simp only [matrixHamiltonian, LinearMap.sum_apply, LinearMap.smul_apply,
        Module.End.mul_apply, modePairAnnihilate, rawPairAnnihilate_zero_sector,
        map_zero, smul_zero, Finset.sum_const_zero]
      exact Submodule.zero_mem _
  | 1 =>
      simp only [matrixHamiltonian, LinearMap.sum_apply, LinearMap.smul_apply,
        Module.End.mul_apply, modePairAnnihilate, rawPairAnnihilate_one_sector,
        map_zero, smul_zero, Finset.sum_const_zero]
      exact Submodule.zero_mem _
  | N+2 =>
      simp only [matrixHamiltonian, LinearMap.sum_apply, LinearMap.smul_apply]
      apply Submodule.sum_mem
      intro p _
      apply Submodule.sum_mem
      intro q _
      apply Submodule.smul_mem
      exact rawPairCreate_mem_exterior (mode p.1) (mode p.2)
        (exteriorPairAnnihilate (mode q.1) (mode q.2) x)

def sectorHamiltonian (G : Geometry) (theta : Twist) (N : ℕ) :
    Module.End ℂ (Exterior (Fin (physicalQ G theta+1)) N) :=
  ((physicalHamiltonian G theta).comp ((⋀[ℂ]^N (Orbital (physicalQ G theta)))).subtype).codRestrict
    _ (matrixHamiltonian_mem_exterior (contactMatrix G theta) N)

/-- The actual fixed-N physical operator, transported by the complete proved
physical/exterior equivalence, not postulated from its desired energy. -/
def physicalSectorHamiltonian (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) : PhysicalFermion G theta N :=
  physicalExteriorEquiv G theta N
    (sectorHamiltonian G theta N ((physicalExteriorEquiv G theta N).symm f))

@[simp] theorem physicalSectorHamiltonian_coordinates (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) :
    ((physicalExteriorEquiv G theta N).symm (physicalSectorHamiltonian G theta N f) :
      Space (physicalQ G theta)) =
      physicalHamiltonian G theta ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta)) := by
  rw [physicalSectorHamiltonian, Equiv.symm_apply_apply]
  rfl

/-- Full complex physical operator form in the original N-particle cell metric. -/
theorem physicalSectorHamiltonian_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : PhysicalFermion G theta N) :
    sectorInner G N f.val (physicalSectorHamiltonian G theta N g).val =
      occupationInner (physicalQ G theta)
        ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta))
        (physicalHamiltonian G theta ((physicalExteriorEquiv G theta N).symm g : Space (physicalQ G theta))) := by
  have h := physicalExteriorEquiv_inner G theta N ((physicalExteriorEquiv G theta N).symm f)
    ((physicalExteriorEquiv G theta N).symm (physicalSectorHamiltonian G theta N g))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, physicalSectorHamiltonian_coordinates] at h
  exact h

theorem physicalSectorHamiltonian_actual_energy (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) :
    (sectorInner G N f.val (physicalSectorHamiltonian G theta N f).val).re =
      actualFermionM1Energy G N f.val := by
  rw [physicalSectorHamiltonian_inner]
  exact physicalHamiltonian_actual_energy G theta N f

/-- Its actual physical-sector square, valid for all N with no N≤dimension
hypothesis, is precisely the already proved raw-CAR normal-square form. -/
theorem physicalSectorHamiltonian_square_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : PhysicalFermion G theta N) :
    sectorInner G N f.val (physicalSectorHamiltonian G theta N (physicalSectorHamiltonian G theta N g)).val =
      occupationInner (physicalQ G theta)
        ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta))
        ((matrixFourBody (physicalQ G theta) (contactMatrix G theta) +
          matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) +
          matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta))
          ((physicalExteriorEquiv G theta N).symm g : Space (physicalQ G theta))) := by
  rw [physicalSectorHamiltonian_inner, physicalSectorHamiltonian_coordinates]
  change occupationInner (physicalQ G theta) _
    ((physicalHamiltonian G theta * physicalHamiltonian G theta) _) = _
  rw [physicalHamiltonian_normal_square]

#print axioms rawCreate_mem_exterior
#print axioms rawPairCreate_mem_exterior
#print axioms matrixHamiltonian_mem_exterior
#print axioms physicalSectorHamiltonian_coordinates
#print axioms physicalSectorHamiltonian_inner
#print axioms physicalSectorHamiltonian_actual_energy
#print axioms physicalSectorHamiltonian_square_inner
end TorusLean.Shared.PhysicalFermionNormalSquare
