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
def k301natRelativeEnergyMatrix : Matrix (Fin 0) (Fin 0) ℂ :=
  complexify c301sRaw + (delta : ℂ) • complexify c301hRaw

def k301natRelativeEnergyCoefficient : Matrix (Fin 0) (Fin 0) ℂ :=
  inverseGramCoefficient (complexify k301J) k301natRelativeEnergyMatrix

/-- Coordinates come from the complete true relative kernel, not a supplied vector. -/
theorem k301_nat_relativeSeed_synthesis :
    ∃ x : Fin 0 → ℂ, natFamilySynthesis k301natRelativeFamily x = w3RelativeSeed 1 := by
  obtain ⟨x,hx⟩ := (k301_nat_homogeneous_relative_kernel (w3RelativeSeed 1)
    (w3RelativeSeed_bihomogeneous 1).1 (w3RelativeSeed_bihomogeneous 1).2).mp
    (w3RelativeSeed_lower 1)
  exact ⟨x,(k301_nat_family_synthesis x).trans hx⟩

/-- Original Nat H and its actual composition give precisely this old source matrix. -/
theorem k301_nat_relative_energy_form (x y : Fin 0 → ℂ) :
    natRelativeLowEnergyForm (natFamilySynthesis k301natRelativeFamily x)
      (natFamilySynthesis k301natRelativeFamily y) =
      star x ⬝ᵥ (k301natRelativeEnergyMatrix *ᵥ y) := by
  unfold natRelativeLowEnergyForm
  rw [k301_nat_family_synthesis x,k301_nat_family_synthesis y,
    k301_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 1 (by decide) _
      (canonicalBlock_bihomogeneous 1 k301occ k301_particle_degree k301_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9]
  change ip (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))
      (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) = _
  simp only [k301_actual_common_pair_hamiltonian_square_form,
    k301_actual_common_pair_hamiltonian_form,matrixCross_congruence]
  simp only [k301natRelativeEnergyMatrix,c301sRaw,c301hRaw,planarSingleForm,
    complexify_mul_rect,complexify_transpose_rect,complexify_sub_rect,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_sub,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The exact signed dyad coefficient uses both original relative Gram inverses. -/
theorem k301_nat_relative_energy_coefficient_rank :
    ∃ x : Fin 0 → ℂ, natFamilySynthesis k301natRelativeFamily x = w3RelativeSeed 1 ∧
      k301natRelativeEnergyCoefficient =
        Matrix.of (fun i j => natRelativeLowEnergyScalar 1 * (x i * star (x j))) := by
  obtain ⟨x,hx⟩ := k301_nat_relativeSeed_synthesis
  refine ⟨x,hx,?_⟩
  have hF : natFamilyGram k301natRelativeFamily = complexify k301F := by
    rw [k301natRelativeFamily,natFamilyGram_rename,k301_canonical_gram]
  have hs (u : Fin 0 → ℂ) :
      (natFamilySynthesis k301natRelativeFamily u).IsHomogeneous 3 ∧
      (natFamilySynthesis k301natRelativeFamily u).IsWeightedHomogeneous id 1 ∧
      canonicalCOMLowerNat (natFamilySynthesis k301natRelativeFamily u) = 0 := by
    rw [k301_nat_family_synthesis]
    exact ⟨(k301_nat_relative_bihomogeneous u).1,
      (k301_nat_relative_bihomogeneous u).2,k301_nat_relative_vacuum u⟩
  exact natRelativeLowEnergy_coefficient_rank k301natRelativeFamily (complexify k301F)
    (complexify k301J) k301natRelativeEnergyMatrix x hx hF
    k301_inverse_complex_right k301_inverse_complex_left hs k301_nat_relative_energy_form

#print axioms k301_nat_relativeSeed_synthesis
#print axioms k301_nat_relative_energy_form
#print axioms k301_nat_relative_energy_coefficient_rank
end TorusLean.BosonFiniteCertificate
