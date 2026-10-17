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
def k306natRelativeEnergyMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  complexify c306sRaw + (delta : ℂ) • complexify c306hRaw

def k306natRelativeEnergyCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  inverseGramCoefficient (complexify k306J) k306natRelativeEnergyMatrix

/-- Coordinates come from the complete true relative kernel, not a supplied vector. -/
theorem k306_nat_relativeSeed_synthesis :
    ∃ x : Fin 2 → ℂ, natFamilySynthesis k306natRelativeFamily x = w3RelativeSeed 6 := by
  obtain ⟨x,hx⟩ := (k306_nat_homogeneous_relative_kernel (w3RelativeSeed 6)
    (w3RelativeSeed_bihomogeneous 6).1 (w3RelativeSeed_bihomogeneous 6).2).mp
    (w3RelativeSeed_lower 6)
  exact ⟨x,(k306_nat_family_synthesis x).trans hx⟩

/-- Original Nat H and its actual composition give precisely this old source matrix. -/
theorem k306_nat_relative_energy_form (x y : Fin 2 → ℂ) :
    natRelativeLowEnergyForm (natFamilySynthesis k306natRelativeFamily x)
      (natFamilySynthesis k306natRelativeFamily y) =
      star x ⬝ᵥ (k306natRelativeEnergyMatrix *ᵥ y) := by
  unfold natRelativeLowEnergyForm
  rw [k306_nat_family_synthesis x,k306_nat_family_synthesis y,
    k306_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 6 (by decide) _
      (canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9]
  change ip (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))
      (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) = _
  simp only [k306_actual_common_pair_hamiltonian_square_form,
    k306_actual_common_pair_hamiltonian_form,matrixCross_congruence]
  simp only [k306natRelativeEnergyMatrix,c306sRaw,c306hRaw,planarSingleForm,
    complexify_mul_rect,complexify_transpose_rect,complexify_sub_rect,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_sub,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The exact signed dyad coefficient uses both original relative Gram inverses. -/
theorem k306_nat_relative_energy_coefficient_rank :
    ∃ x : Fin 2 → ℂ, natFamilySynthesis k306natRelativeFamily x = w3RelativeSeed 6 ∧
      k306natRelativeEnergyCoefficient =
        Matrix.of (fun i j => natRelativeLowEnergyScalar 6 * (x i * star (x j))) := by
  obtain ⟨x,hx⟩ := k306_nat_relativeSeed_synthesis
  refine ⟨x,hx,?_⟩
  have hF : natFamilyGram k306natRelativeFamily = complexify k306F := by
    rw [k306natRelativeFamily,natFamilyGram_rename,k306_canonical_gram]
  have hs (u : Fin 2 → ℂ) :
      (natFamilySynthesis k306natRelativeFamily u).IsHomogeneous 3 ∧
      (natFamilySynthesis k306natRelativeFamily u).IsWeightedHomogeneous id 6 ∧
      canonicalCOMLowerNat (natFamilySynthesis k306natRelativeFamily u) = 0 := by
    rw [k306_nat_family_synthesis]
    exact ⟨(k306_nat_relative_bihomogeneous u).1,
      (k306_nat_relative_bihomogeneous u).2,k306_nat_relative_vacuum u⟩
  exact natRelativeLowEnergy_coefficient_rank k306natRelativeFamily (complexify k306F)
    (complexify k306J) k306natRelativeEnergyMatrix x hx hF
    k306_inverse_complex_right k306_inverse_complex_left hs k306_nat_relative_energy_form

#print axioms k306_nat_relativeSeed_synthesis
#print axioms k306_nat_relative_energy_form
#print axioms k306_nat_relative_energy_coefficient_rank
end TorusLean.BosonFiniteCertificate
