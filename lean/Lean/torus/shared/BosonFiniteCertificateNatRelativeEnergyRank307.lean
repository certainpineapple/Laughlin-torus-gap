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
def k307natRelativeEnergyMatrix : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c307sRaw + (delta : ℂ) • complexify c307hRaw

def k307natRelativeEnergyCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k307J) k307natRelativeEnergyMatrix

/-- Coordinates come from the complete true relative kernel, not a supplied vector. -/
theorem k307_nat_relativeSeed_synthesis :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k307natRelativeFamily x = w3RelativeSeed 7 := by
  obtain ⟨x,hx⟩ := (k307_nat_homogeneous_relative_kernel (w3RelativeSeed 7)
    (w3RelativeSeed_bihomogeneous 7).1 (w3RelativeSeed_bihomogeneous 7).2).mp
    (w3RelativeSeed_lower 7)
  exact ⟨x,(k307_nat_family_synthesis x).trans hx⟩

/-- Original Nat H and its actual composition give precisely this old source matrix. -/
theorem k307_nat_relative_energy_form (x y : Fin 1 → ℂ) :
    natRelativeLowEnergyForm (natFamilySynthesis k307natRelativeFamily x)
      (natFamilySynthesis k307natRelativeFamily y) =
      star x ⬝ᵥ (k307natRelativeEnergyMatrix *ᵥ y) := by
  unfold natRelativeLowEnergyForm
  rw [k307_nat_family_synthesis x,k307_nat_family_synthesis y,
    k307_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 7 (by decide) _
      (canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9]
  change ip (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))
      (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y))) +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y))) = _
  simp only [k307_actual_common_pair_hamiltonian_square_form,
    k307_actual_common_pair_hamiltonian_form,matrixCross_congruence]
  simp only [k307natRelativeEnergyMatrix,c307sRaw,c307hRaw,planarSingleForm,
    complexify_mul_rect,complexify_transpose_rect,complexify_sub_rect,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_sub,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The exact signed dyad coefficient uses both original relative Gram inverses. -/
theorem k307_nat_relative_energy_coefficient_rank :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k307natRelativeFamily x = w3RelativeSeed 7 ∧
      k307natRelativeEnergyCoefficient =
        Matrix.of (fun i j => natRelativeLowEnergyScalar 7 * (x i * star (x j))) := by
  obtain ⟨x,hx⟩ := k307_nat_relativeSeed_synthesis
  refine ⟨x,hx,?_⟩
  have hF : natFamilyGram k307natRelativeFamily = complexify k307F := by
    rw [k307natRelativeFamily,natFamilyGram_rename,k307_canonical_gram]
  have hs (u : Fin 1 → ℂ) :
      (natFamilySynthesis k307natRelativeFamily u).IsHomogeneous 3 ∧
      (natFamilySynthesis k307natRelativeFamily u).IsWeightedHomogeneous id 7 ∧
      canonicalCOMLowerNat (natFamilySynthesis k307natRelativeFamily u) = 0 := by
    rw [k307_nat_family_synthesis]
    exact ⟨(k307_nat_relative_bihomogeneous u).1,
      (k307_nat_relative_bihomogeneous u).2,k307_nat_relative_vacuum u⟩
  exact natRelativeLowEnergy_coefficient_rank k307natRelativeFamily (complexify k307F)
    (complexify k307J) k307natRelativeEnergyMatrix x hx hF
    k307_inverse_complex_right k307_inverse_complex_left hs k307_nat_relative_energy_form

#print axioms k307_nat_relativeSeed_synthesis
#print axioms k307_nat_relative_energy_form
#print axioms k307_nat_relative_energy_coefficient_rank
end TorusLean.BosonFiniteCertificate
