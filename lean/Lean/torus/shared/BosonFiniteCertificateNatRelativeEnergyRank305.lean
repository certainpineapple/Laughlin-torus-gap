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
def k305natRelativeEnergyMatrix : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c305sRaw + (delta : ℂ) • complexify c305hRaw

def k305natRelativeEnergyCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k305J) k305natRelativeEnergyMatrix

/-- Coordinates come from the complete true relative kernel, not a supplied vector. -/
theorem k305_nat_relativeSeed_synthesis :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k305natRelativeFamily x = w3RelativeSeed 5 := by
  obtain ⟨x,hx⟩ := (k305_nat_homogeneous_relative_kernel (w3RelativeSeed 5)
    (w3RelativeSeed_bihomogeneous 5).1 (w3RelativeSeed_bihomogeneous 5).2).mp
    (w3RelativeSeed_lower 5)
  exact ⟨x,(k305_nat_family_synthesis x).trans hx⟩

/-- Original Nat H and its actual composition give precisely this old source matrix. -/
theorem k305_nat_relative_energy_form (x y : Fin 1 → ℂ) :
    natRelativeLowEnergyForm (natFamilySynthesis k305natRelativeFamily x)
      (natFamilySynthesis k305natRelativeFamily y) =
      star x ⬝ᵥ (k305natRelativeEnergyMatrix *ᵥ y) := by
  unfold natRelativeLowEnergyForm
  rw [k305_nat_family_synthesis x,k305_nat_family_synthesis y,
    k305_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 5 (by decide) _
      (canonicalBlock_bihomogeneous 5 k305occ k305_particle_degree k305_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9]
  change ip (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x))
      (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ y))) +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ y))) = _
  simp only [k305_actual_common_pair_hamiltonian_square_form,
    k305_actual_common_pair_hamiltonian_form,matrixCross_congruence]
  simp only [k305natRelativeEnergyMatrix,c305sRaw,c305hRaw,planarSingleForm,
    complexify_mul_rect,complexify_transpose_rect,complexify_sub_rect,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_sub,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The exact signed dyad coefficient uses both original relative Gram inverses. -/
theorem k305_nat_relative_energy_coefficient_rank :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k305natRelativeFamily x = w3RelativeSeed 5 ∧
      k305natRelativeEnergyCoefficient =
        Matrix.of (fun i j => natRelativeLowEnergyScalar 5 * (x i * star (x j))) := by
  obtain ⟨x,hx⟩ := k305_nat_relativeSeed_synthesis
  refine ⟨x,hx,?_⟩
  have hF : natFamilyGram k305natRelativeFamily = complexify k305F := by
    rw [k305natRelativeFamily,natFamilyGram_rename,k305_canonical_gram]
  have hs (u : Fin 1 → ℂ) :
      (natFamilySynthesis k305natRelativeFamily u).IsHomogeneous 3 ∧
      (natFamilySynthesis k305natRelativeFamily u).IsWeightedHomogeneous id 5 ∧
      canonicalCOMLowerNat (natFamilySynthesis k305natRelativeFamily u) = 0 := by
    rw [k305_nat_family_synthesis]
    exact ⟨(k305_nat_relative_bihomogeneous u).1,
      (k305_nat_relative_bihomogeneous u).2,k305_nat_relative_vacuum u⟩
  exact natRelativeLowEnergy_coefficient_rank k305natRelativeFamily (complexify k305F)
    (complexify k305J) k305natRelativeEnergyMatrix x hx hF
    k305_inverse_complex_right k305_inverse_complex_left hs k305_nat_relative_energy_form

#print axioms k305_nat_relativeSeed_synthesis
#print axioms k305_nat_relative_energy_form
#print axioms k305_nat_relative_energy_coefficient_rank
end TorusLean.BosonFiniteCertificate
