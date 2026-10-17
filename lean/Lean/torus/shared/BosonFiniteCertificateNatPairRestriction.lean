import torus.shared.BosonFiniteCertificateNatPairRestriction300
import torus.shared.BosonFiniteCertificateNatPairRestriction301
import torus.shared.BosonFiniteCertificateNatPairRestriction302
import torus.shared.BosonFiniteCertificateNatPairRestriction303
import torus.shared.BosonFiniteCertificateNatPairRestriction304
import torus.shared.BosonFiniteCertificateNatPairRestriction305
import torus.shared.BosonFiniteCertificateNatPairRestriction306
import torus.shared.BosonFiniteCertificateNatPairRestriction307
import torus.shared.BosonFiniteCertificateNatPairRestriction308

set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant

/-- True locally finite Nat planar H and its actual square on the entire
low-degree N3 sector, with neither span membership nor invariance assumed. -/
theorem canonicalPairHamiltonianNat_low_degree_restriction (d : ℕ) (hd8 : d≤8)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    ∃ g : Core (Fin 9) ℂ, MvPolynomial.rename Fin.val g=f ∧
      canonicalPairHamiltonianNat f=MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 g) ∧
      canonicalPairHamiltonianNat (canonicalPairHamiltonianNat f)=
        MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 g)) := by
  interval_cases d
  · exact k300_nat_pair_restriction f hN hd
  · exact k301_nat_pair_restriction f hN hd
  · exact k302_nat_pair_restriction f hN hd
  · exact k303_nat_pair_restriction f hN hd
  · exact k304_nat_pair_restriction f hN hd
  · exact k305_nat_pair_restriction f hN hd
  · exact k306_nat_pair_restriction f hN hd
  · exact k307_nat_pair_restriction f hN hd
  · exact k308_nat_pair_restriction f hN hd

#print axioms canonicalPairHamiltonianNat_low_degree_restriction
end TorusLean.BosonFiniteCertificate
