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
def k300natRelativeEnergyMatrix : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c300sRaw + (delta : ℂ) • complexify c300hRaw

def k300natRelativeEnergyCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k300J) k300natRelativeEnergyMatrix

/-- Coordinates come from the complete true relative kernel, not a supplied vector. -/
theorem k300_nat_relativeSeed_synthesis :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k300natRelativeFamily x = w3RelativeSeed 0 := by
  obtain ⟨x,hx⟩ := (k300_nat_homogeneous_relative_kernel (w3RelativeSeed 0)
    (w3RelativeSeed_bihomogeneous 0).1 (w3RelativeSeed_bihomogeneous 0).2).mp
    (w3RelativeSeed_lower 0)
  exact ⟨x,(k300_nat_family_synthesis x).trans hx⟩

/-- Original Nat H and its actual composition give precisely this old source matrix. -/
theorem k300_nat_relative_energy_form (x y : Fin 1 → ℂ) :
    natRelativeLowEnergyForm (natFamilySynthesis k300natRelativeFamily x)
      (natFamilySynthesis k300natRelativeFamily y) =
      star x ⬝ᵥ (k300natRelativeEnergyMatrix *ᵥ y) := by
  unfold natRelativeLowEnergyForm
  rw [k300_nat_family_synthesis x,k300_nat_family_synthesis y,
    k300_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 0 (by decide) _
      (canonicalBlock_bihomogeneous 0 k300occ k300_particle_degree k300_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9]
  change ip (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x))
      (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ y))) +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ y))) = _
  simp only [k300_actual_common_pair_hamiltonian_square_form,
    k300_actual_common_pair_hamiltonian_form,matrixCross_congruence]
  simp only [k300natRelativeEnergyMatrix,c300sRaw,c300hRaw,planarSingleForm,
    complexify_mul_rect,complexify_transpose_rect,complexify_sub_rect,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_sub,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The exact signed dyad coefficient uses both original relative Gram inverses. -/
theorem k300_nat_relative_energy_coefficient_rank :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k300natRelativeFamily x = w3RelativeSeed 0 ∧
      k300natRelativeEnergyCoefficient =
        Matrix.of (fun i j => natRelativeLowEnergyScalar 0 * (x i * star (x j))) := by
  obtain ⟨x,hx⟩ := k300_nat_relativeSeed_synthesis
  refine ⟨x,hx,?_⟩
  have hF : natFamilyGram k300natRelativeFamily = complexify k300F := by
    rw [k300natRelativeFamily,natFamilyGram_rename,k300_canonical_gram]
  have hs (u : Fin 1 → ℂ) :
      (natFamilySynthesis k300natRelativeFamily u).IsHomogeneous 3 ∧
      (natFamilySynthesis k300natRelativeFamily u).IsWeightedHomogeneous id 0 ∧
      canonicalCOMLowerNat (natFamilySynthesis k300natRelativeFamily u) = 0 := by
    rw [k300_nat_family_synthesis]
    exact ⟨(k300_nat_relative_bihomogeneous u).1,
      (k300_nat_relative_bihomogeneous u).2,k300_nat_relative_vacuum u⟩
  exact natRelativeLowEnergy_coefficient_rank k300natRelativeFamily (complexify k300F)
    (complexify k300J) k300natRelativeEnergyMatrix x hx hF
    k300_inverse_complex_right k300_inverse_complex_left hs k300_nat_relative_energy_form

#print axioms k300_nat_relativeSeed_synthesis
#print axioms k300_nat_relative_energy_form
#print axioms k300_nat_relative_energy_coefficient_rank
end TorusLean.BosonFiniteCertificate
