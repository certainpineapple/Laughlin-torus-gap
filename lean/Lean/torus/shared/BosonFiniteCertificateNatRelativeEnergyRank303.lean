import torus.shared.BosonFiniteCertificateNatRelativeEnergyRankCore
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant
open scoped BigOperators ComplexConjugate

/-- The original H²-H+δH source form, before either Gram inverse. -/
def k303natRelativeEnergyMatrix : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c303sRaw + (delta : ℂ) • complexify c303hRaw

def k303natRelativeEnergyCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k303J) k303natRelativeEnergyMatrix

/-- Coordinates come from the complete true relative kernel, not a supplied vector. -/
theorem k303_nat_relativeSeed_synthesis :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k303natRelativeFamily x = w3RelativeSeed 3 := by
  obtain ⟨x,hx⟩ := (k303_nat_homogeneous_relative_kernel (w3RelativeSeed 3)
    (w3RelativeSeed_bihomogeneous 3).1 (w3RelativeSeed_bihomogeneous 3).2).mp
    (w3RelativeSeed_lower 3)
  exact ⟨x,(k303_nat_family_synthesis x).trans hx⟩

/-- Original Nat H and its actual composition give precisely this old source matrix. -/
theorem k303_nat_relative_energy_form (x y : Fin 1 → ℂ) :
    natRelativeLowEnergyForm (natFamilySynthesis k303natRelativeFamily x)
      (natFamilySynthesis k303natRelativeFamily y) =
      star x ⬝ᵥ (k303natRelativeEnergyMatrix *ᵥ y) := by
  unfold natRelativeLowEnergyForm
  rw [k303_nat_family_synthesis x,k303_nat_family_synthesis y,
    k303_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 3 (by decide) _
      (canonicalBlock_bihomogeneous 3 k303occ k303_particle_degree k303_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9]
  change ip (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x))
      (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ y))) +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ y))) = _
  simp only [k303_actual_common_pair_hamiltonian_square_form,
    k303_actual_common_pair_hamiltonian_form,matrixCross_congruence]
  simp only [k303natRelativeEnergyMatrix,c303sRaw,c303hRaw,planarSingleForm,
    complexify_mul_rect,complexify_transpose_rect,complexify_sub_rect,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_sub,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The exact signed dyad coefficient uses both original relative Gram inverses. -/
theorem k303_nat_relative_energy_coefficient_rank :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k303natRelativeFamily x = w3RelativeSeed 3 ∧
      k303natRelativeEnergyCoefficient =
        Matrix.of (fun i j => natRelativeLowEnergyScalar 3 * (x i * star (x j))) := by
  obtain ⟨x,hx⟩ := k303_nat_relativeSeed_synthesis
  refine ⟨x,hx,?_⟩
  have hF : natFamilyGram k303natRelativeFamily = complexify k303F := by
    rw [k303natRelativeFamily,natFamilyGram_rename,k303_canonical_gram]
  have hs (u : Fin 1 → ℂ) :
      (natFamilySynthesis k303natRelativeFamily u).IsHomogeneous 3 ∧
      (natFamilySynthesis k303natRelativeFamily u).IsWeightedHomogeneous id 3 ∧
      canonicalCOMLowerNat (natFamilySynthesis k303natRelativeFamily u) = 0 := by
    rw [k303_nat_family_synthesis]
    exact ⟨(k303_nat_relative_bihomogeneous u).1,
      (k303_nat_relative_bihomogeneous u).2,k303_nat_relative_vacuum u⟩
  exact natRelativeLowEnergy_coefficient_rank k303natRelativeFamily (complexify k303F)
    (complexify k303J) k303natRelativeEnergyMatrix x hx hF
    k303_inverse_complex_right k303_inverse_complex_left hs k303_nat_relative_energy_form

#print axioms k303_nat_relativeSeed_synthesis
#print axioms k303_nat_relative_energy_form
#print axioms k303_nat_relative_energy_coefficient_rank
end TorusLean.BosonFiniteCertificate
