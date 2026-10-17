import torus.shared.BosonFiniteCertificateNatPairHamiltonianCompatibility
import torus.shared.BosonFiniteCertificateCanonicalActualHamiltonian301
import torus.shared.BosonFiniteCertificateThreeOccupationNat301
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant

/-- The actual unbounded-label Hamiltonian preserves this complete low-degree
block; the action is inherited from the independently proved genuine H8 action. -/
theorem k301_nat_pair_hamiltonian_action (x : Fin 1 → ℂ) :
    canonicalPairHamiltonianNat
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ x)) =
    MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ
      ((complexify p301Ginv * complexify p301rawHform) *ᵥ x)) := by
  have hh := canonicalBlock_bihomogeneous 1 k301occ k301_particle_degree k301_orbital_degree x
  rw [canonicalPairHamiltonianNat_rename_low_degree 1 (by decide) _ hh.2,
    k301_actual_common_pair_hamiltonian_action]

/-- Actual HNat composed with itself, not the square of a form compression. -/
theorem k301_nat_pair_square_rename (x : Fin 1 → ℂ) :
    canonicalPairHamiltonianNat (canonicalPairHamiltonianNat
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ x))) =
    MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ x))) := by
  rw [k301_nat_pair_hamiltonian_action,k301_nat_pair_hamiltonian_action,
    k301_actual_common_pair_hamiltonian_action,k301_actual_common_pair_hamiltonian_action]

/-- Every Nat-orbital N3 polynomial of this orbital degree has simultaneous
true HNat and HNat squared restrictions, without a selected-span hypothesis. -/
theorem k301_nat_pair_restriction (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3)
    (hd : f.IsWeightedHomogeneous id 1) :
    ∃ g : Core (Fin 9) ℂ, MvPolynomial.rename Fin.val g=f ∧
      canonicalPairHamiltonianNat f=MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 g) ∧
      canonicalPairHamiltonianNat (canonicalPairHamiltonianNat f)=
        MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 g)) := by
  obtain ⟨x,rfl⟩ := k301_nat_homogeneous_block f hN hd
  refine ⟨canonicalBlock (factorialScale 8) k301occ x,rfl,?_,k301_nat_pair_square_rename x⟩
  exact canonicalPairHamiltonianNat_rename_low_degree 1 (by decide) _
    (canonicalBlock_bihomogeneous 1 k301occ k301_particle_degree k301_orbital_degree x).2

#print axioms k301_nat_pair_hamiltonian_action
#print axioms k301_nat_pair_square_rename
#print axioms k301_nat_pair_restriction
end TorusLean.BosonFiniteCertificate
