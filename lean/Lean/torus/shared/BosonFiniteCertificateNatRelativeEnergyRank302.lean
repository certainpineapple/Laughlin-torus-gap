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
def k302natRelativeEnergyMatrix : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c302sRaw + (delta : ℂ) • complexify c302hRaw

def k302natRelativeEnergyCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  inverseGramCoefficient (complexify k302J) k302natRelativeEnergyMatrix

/-- Coordinates come from the complete true relative kernel, not a supplied vector. -/
theorem k302_nat_relativeSeed_synthesis :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k302natRelativeFamily x = w3RelativeSeed 2 := by
  obtain ⟨x,hx⟩ := (k302_nat_homogeneous_relative_kernel (w3RelativeSeed 2)
    (w3RelativeSeed_bihomogeneous 2).1 (w3RelativeSeed_bihomogeneous 2).2).mp
    (w3RelativeSeed_lower 2)
  exact ⟨x,(k302_nat_family_synthesis x).trans hx⟩

/-- Original Nat H and its actual composition give precisely this old source matrix. -/
theorem k302_nat_relative_energy_form (x y : Fin 1 → ℂ) :
    natRelativeLowEnergyForm (natFamilySynthesis k302natRelativeFamily x)
      (natFamilySynthesis k302natRelativeFamily y) =
      star x ⬝ᵥ (k302natRelativeEnergyMatrix *ᵥ y) := by
  unfold natRelativeLowEnergyForm
  rw [k302_nat_family_synthesis x,k302_nat_family_synthesis y,
    k302_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 2 (by decide) _
      (canonicalBlock_bihomogeneous 2 k302occ k302_particle_degree k302_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9]
  change ip (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x))
      (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ y))) +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ y))) = _
  simp only [k302_actual_common_pair_hamiltonian_square_form,
    k302_actual_common_pair_hamiltonian_form,matrixCross_congruence]
  simp only [k302natRelativeEnergyMatrix,c302sRaw,c302hRaw,planarSingleForm,
    complexify_mul_rect,complexify_transpose_rect,complexify_sub_rect,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_sub,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The exact signed dyad coefficient uses both original relative Gram inverses. -/
theorem k302_nat_relative_energy_coefficient_rank :
    ∃ x : Fin 1 → ℂ, natFamilySynthesis k302natRelativeFamily x = w3RelativeSeed 2 ∧
      k302natRelativeEnergyCoefficient =
        Matrix.of (fun i j => natRelativeLowEnergyScalar 2 * (x i * star (x j))) := by
  obtain ⟨x,hx⟩ := k302_nat_relativeSeed_synthesis
  refine ⟨x,hx,?_⟩
  have hF : natFamilyGram k302natRelativeFamily = complexify k302F := by
    rw [k302natRelativeFamily,natFamilyGram_rename,k302_canonical_gram]
  have hs (u : Fin 1 → ℂ) :
      (natFamilySynthesis k302natRelativeFamily u).IsHomogeneous 3 ∧
      (natFamilySynthesis k302natRelativeFamily u).IsWeightedHomogeneous id 2 ∧
      canonicalCOMLowerNat (natFamilySynthesis k302natRelativeFamily u) = 0 := by
    rw [k302_nat_family_synthesis]
    exact ⟨(k302_nat_relative_bihomogeneous u).1,
      (k302_nat_relative_bihomogeneous u).2,k302_nat_relative_vacuum u⟩
  exact natRelativeLowEnergy_coefficient_rank k302natRelativeFamily (complexify k302F)
    (complexify k302J) k302natRelativeEnergyMatrix x hx hF
    k302_inverse_complex_right k302_inverse_complex_left hs k302_nat_relative_energy_form

#print axioms k302_nat_relativeSeed_synthesis
#print axioms k302_nat_relative_energy_form
#print axioms k302_nat_relative_energy_coefficient_rank
end TorusLean.BosonFiniteCertificate
