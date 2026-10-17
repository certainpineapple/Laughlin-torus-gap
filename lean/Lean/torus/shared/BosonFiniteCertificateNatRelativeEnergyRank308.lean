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
def k308natRelativeEnergyMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  complexify c308sRaw + (delta : ℂ) • complexify c308hRaw

def k308natRelativeEnergyCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  inverseGramCoefficient (complexify k308J) k308natRelativeEnergyMatrix

/-- Coordinates come from the complete true relative kernel, not a supplied vector. -/
theorem k308_nat_relativeSeed_synthesis :
    ∃ x : Fin 2 → ℂ, natFamilySynthesis k308natRelativeFamily x = w3RelativeSeed 8 := by
  obtain ⟨x,hx⟩ := (k308_nat_homogeneous_relative_kernel (w3RelativeSeed 8)
    (w3RelativeSeed_bihomogeneous 8).1 (w3RelativeSeed_bihomogeneous 8).2).mp
    (w3RelativeSeed_lower 8)
  exact ⟨x,(k308_nat_family_synthesis x).trans hx⟩

/-- Original Nat H and its actual composition give precisely this old source matrix. -/
theorem k308_nat_relative_energy_form (x y : Fin 2 → ℂ) :
    natRelativeLowEnergyForm (natFamilySynthesis k308natRelativeFamily x)
      (natFamilySynthesis k308natRelativeFamily y) =
      star x ⬝ᵥ (k308natRelativeEnergyMatrix *ᵥ y) := by
  unfold natRelativeLowEnergyForm
  rw [k308_nat_family_synthesis x,k308_nat_family_synthesis y,
    k308_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 8 (by decide) _
      (canonicalBlock_bihomogeneous 8 k308occ k308_particle_degree k308_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9]
  change ip (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))
      (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ y))) +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ y))) = _
  simp only [k308_actual_common_pair_hamiltonian_square_form,
    k308_actual_common_pair_hamiltonian_form,matrixCross_congruence]
  simp only [k308natRelativeEnergyMatrix,c308sRaw,c308hRaw,planarSingleForm,
    complexify_mul_rect,complexify_transpose_rect,complexify_sub_rect,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_sub,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The exact signed dyad coefficient uses both original relative Gram inverses. -/
theorem k308_nat_relative_energy_coefficient_rank :
    ∃ x : Fin 2 → ℂ, natFamilySynthesis k308natRelativeFamily x = w3RelativeSeed 8 ∧
      k308natRelativeEnergyCoefficient =
        Matrix.of (fun i j => natRelativeLowEnergyScalar 8 * (x i * star (x j))) := by
  obtain ⟨x,hx⟩ := k308_nat_relativeSeed_synthesis
  refine ⟨x,hx,?_⟩
  have hF : natFamilyGram k308natRelativeFamily = complexify k308F := by
    rw [k308natRelativeFamily,natFamilyGram_rename,k308_canonical_gram]
  have hs (u : Fin 2 → ℂ) :
      (natFamilySynthesis k308natRelativeFamily u).IsHomogeneous 3 ∧
      (natFamilySynthesis k308natRelativeFamily u).IsWeightedHomogeneous id 8 ∧
      canonicalCOMLowerNat (natFamilySynthesis k308natRelativeFamily u) = 0 := by
    rw [k308_nat_family_synthesis]
    exact ⟨(k308_nat_relative_bihomogeneous u).1,
      (k308_nat_relative_bihomogeneous u).2,k308_nat_relative_vacuum u⟩
  exact natRelativeLowEnergy_coefficient_rank k308natRelativeFamily (complexify k308F)
    (complexify k308J) k308natRelativeEnergyMatrix x hx hF
    k308_inverse_complex_right k308_inverse_complex_left hs k308_nat_relative_energy_form

#print axioms k308_nat_relativeSeed_synthesis
#print axioms k308_nat_relative_energy_form
#print axioms k308_nat_relative_energy_coefficient_rank
end TorusLean.BosonFiniteCertificate
