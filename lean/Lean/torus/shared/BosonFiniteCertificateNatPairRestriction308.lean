import torus.shared.BosonFiniteCertificateNatPairHamiltonianCompatibility
import torus.shared.BosonFiniteCertificateCanonicalActualHamiltonian308
import torus.shared.BosonFiniteCertificateThreeOccupationNat308
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant

/-- The actual unbounded-label Hamiltonian preserves this complete low-degree
block; the action is inherited from the independently proved genuine H8 action. -/
theorem k308_nat_pair_hamiltonian_action (x : Fin 10 → ℂ) :
    canonicalPairHamiltonianNat
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ x)) =
    MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ
      ((complexify p308Ginv * complexify p308rawHform) *ᵥ x)) := by
  have hh := canonicalBlock_bihomogeneous 8 k308occ k308_particle_degree k308_orbital_degree x
  rw [canonicalPairHamiltonianNat_rename_low_degree 8 (by decide) _ hh.2,
    k308_actual_common_pair_hamiltonian_action]

/-- Actual HNat composed with itself, not the square of a form compression. -/
theorem k308_nat_pair_square_rename (x : Fin 10 → ℂ) :
    canonicalPairHamiltonianNat (canonicalPairHamiltonianNat
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ x))) =
    MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ x))) := by
  rw [k308_nat_pair_hamiltonian_action,k308_nat_pair_hamiltonian_action,
    k308_actual_common_pair_hamiltonian_action,k308_actual_common_pair_hamiltonian_action]

/-- Every Nat-orbital N3 polynomial of this orbital degree has simultaneous
true HNat and HNat squared restrictions, without a selected-span hypothesis. -/
theorem k308_nat_pair_restriction (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3)
    (hd : f.IsWeightedHomogeneous id 8) :
    ∃ g : Core (Fin 9) ℂ, MvPolynomial.rename Fin.val g=f ∧
      canonicalPairHamiltonianNat f=MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 g) ∧
      canonicalPairHamiltonianNat (canonicalPairHamiltonianNat f)=
        MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 g)) := by
  obtain ⟨x,rfl⟩ := k308_nat_homogeneous_block f hN hd
  refine ⟨canonicalBlock (factorialScale 8) k308occ x,rfl,?_,k308_nat_pair_square_rename x⟩
  exact canonicalPairHamiltonianNat_rename_low_degree 8 (by decide) _
    (canonicalBlock_bihomogeneous 8 k308occ k308_particle_degree k308_orbital_degree x).2

#print axioms k308_nat_pair_hamiltonian_action
#print axioms k308_nat_pair_square_rename
#print axioms k308_nat_pair_restriction
end TorusLean.BosonFiniteCertificate
