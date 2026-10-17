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
def k304natRelativeEnergyMatrix : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c304sRaw + (delta : ℂ) • complexify c304hRaw

def k304natRelativeEnergyCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k304J) k304natRelativeEnergyMatrix

/-- Coordinates come from the complete true relative kernel, not a supplied vector. -/
theorem k304_nat_relativeSeed_synthesis :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k304natRelativeFamily x = w3RelativeSeed 4 := by
  obtain ⟨x,hx⟩ := (k304_nat_homogeneous_relative_kernel (w3RelativeSeed 4)
    (w3RelativeSeed_bihomogeneous 4).1 (w3RelativeSeed_bihomogeneous 4).2).mp
    (w3RelativeSeed_lower 4)
  exact ⟨x,(k304_nat_family_synthesis x).trans hx⟩

/-- Original Nat H and its actual composition give precisely this old source matrix. -/
theorem k304_nat_relative_energy_form (x y : Fin 1 → ℂ) :
    natRelativeLowEnergyForm (natFamilySynthesis k304natRelativeFamily x)
      (natFamilySynthesis k304natRelativeFamily y) =
      star x ⬝ᵥ (k304natRelativeEnergyMatrix *ᵥ y) := by
  unfold natRelativeLowEnergyForm
  rw [k304_nat_family_synthesis x,k304_nat_family_synthesis y,
    k304_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 4 (by decide) _
      (canonicalBlock_bihomogeneous 4 k304occ k304_particle_degree k304_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9]
  change ip (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x))
      (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ y))) +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ y))) = _
  simp only [k304_actual_common_pair_hamiltonian_square_form,
    k304_actual_common_pair_hamiltonian_form,matrixCross_congruence]
  simp only [k304natRelativeEnergyMatrix,c304sRaw,c304hRaw,planarSingleForm,
    complexify_mul_rect,complexify_transpose_rect,complexify_sub_rect,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_sub,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The exact signed dyad coefficient uses both original relative Gram inverses. -/
theorem k304_nat_relative_energy_coefficient_rank :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k304natRelativeFamily x = w3RelativeSeed 4 ∧
      k304natRelativeEnergyCoefficient =
        Matrix.of (fun i j => natRelativeLowEnergyScalar 4 * (x i * star (x j))) := by
  obtain ⟨x,hx⟩ := k304_nat_relativeSeed_synthesis
  refine ⟨x,hx,?_⟩
  have hF : natFamilyGram k304natRelativeFamily = complexify k304F := by
    rw [k304natRelativeFamily,natFamilyGram_rename,k304_canonical_gram]
  have hs (u : Fin 1 → ℂ) :
      (natFamilySynthesis k304natRelativeFamily u).IsHomogeneous 3 ∧
      (natFamilySynthesis k304natRelativeFamily u).IsWeightedHomogeneous id 4 ∧
      canonicalCOMLowerNat (natFamilySynthesis k304natRelativeFamily u) = 0 := by
    rw [k304_nat_family_synthesis]
    exact ⟨(k304_nat_relative_bihomogeneous u).1,
      (k304_nat_relative_bihomogeneous u).2,k304_nat_relative_vacuum u⟩
  exact natRelativeLowEnergy_coefficient_rank k304natRelativeFamily (complexify k304F)
    (complexify k304J) k304natRelativeEnergyMatrix x hx hF
    k304_inverse_complex_right k304_inverse_complex_left hs k304_nat_relative_energy_form

#print axioms k304_nat_relativeSeed_synthesis
#print axioms k304_nat_relative_energy_form
#print axioms k304_nat_relative_energy_coefficient_rank
end TorusLean.BosonFiniteCertificate
