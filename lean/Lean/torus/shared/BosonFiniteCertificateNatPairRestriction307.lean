import torus.shared.BosonFiniteCertificateNatPairHamiltonianCompatibility
import torus.shared.BosonFiniteCertificateCanonicalActualHamiltonian307
import torus.shared.BosonFiniteCertificateThreeOccupationNat307
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant

/-- The actual unbounded-label Hamiltonian preserves this complete low-degree
block; the action is inherited from the independently proved genuine H8 action. -/
theorem k307_nat_pair_hamiltonian_action (x : Fin 8 → ℂ) :
    canonicalPairHamiltonianNat
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ x)) =
    MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ
      ((complexify p307Ginv * complexify p307rawHform) *ᵥ x)) := by
  have hh := canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree x
  rw [canonicalPairHamiltonianNat_rename_low_degree 7 (by decide) _ hh.2,
    k307_actual_common_pair_hamiltonian_action]

/-- Actual HNat composed with itself, not the square of a form compression. -/
theorem k307_nat_pair_square_rename (x : Fin 8 → ℂ) :
    canonicalPairHamiltonianNat (canonicalPairHamiltonianNat
      (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ x))) =
    MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k307occ x))) := by
  rw [k307_nat_pair_hamiltonian_action,k307_nat_pair_hamiltonian_action,
    k307_actual_common_pair_hamiltonian_action,k307_actual_common_pair_hamiltonian_action]

/-- Every Nat-orbital N3 polynomial of this orbital degree has simultaneous
true HNat and HNat squared restrictions, without a selected-span hypothesis. -/
theorem k307_nat_pair_restriction (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3)
    (hd : f.IsWeightedHomogeneous id 7) :
    ∃ g : Core (Fin 9) ℂ, MvPolynomial.rename Fin.val g=f ∧
      canonicalPairHamiltonianNat f=MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 g) ∧
      canonicalPairHamiltonianNat (canonicalPairHamiltonianNat f)=
        MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 g)) := by
  obtain ⟨x,rfl⟩ := k307_nat_homogeneous_block f hN hd
  refine ⟨canonicalBlock (factorialScale 8) k307occ x,rfl,?_,k307_nat_pair_square_rename x⟩
  exact canonicalPairHamiltonianNat_rename_low_degree 7 (by decide) _
    (canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree x).2

#print axioms k307_nat_pair_hamiltonian_action
#print axioms k307_nat_pair_square_rename
#print axioms k307_nat_pair_restriction
end TorusLean.BosonFiniteCertificate
