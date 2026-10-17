import torus.shared.BosonFiniteCertificateNatRelativeSeedNorm

/-! Exact relative-sector energy identities for the original locally finite
Nat pair Hamiltonian. These identify its genuine square on the polynomial
common domain at every orbital degree. No high-degree positivity or thermal
payment is assumed or asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion

theorem canonicalPairHamiltonianNat_relative_seed (d : ℕ) :
    canonicalPairHamiltonianNat (w3RelativeSeed d) =
      ((1:ℂ)+2*(-1/2:ℂ)^d) • w3RelativeSeed d := by
  rw [canonicalPairHamiltonianNat_relative_rank_action d (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 (w3RelativeSeed_bihomogeneous d).2
    (w3RelativeSeed_lower d),w3RelativeSeed_natOccupationInner_self]

theorem canonicalPairHamiltonianNat_relative_square_action (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f=0) :
    canonicalPairHamiltonianNat (canonicalPairHamiltonianNat f) =
      (((1:ℂ)+2*(-1/2:ℂ)^d)*natOccupationInner (w3RelativeSeed d) f) • w3RelativeSeed d := by
  rw [canonicalPairHamiltonianNat_relative_rank_action d f hN hd hL,map_smul,
    canonicalPairHamiltonianNat_relative_seed,smul_smul,mul_comm]

/-- The true square-minus-H action, with its signed all-degree coefficient. -/
theorem canonicalPairHamiltonianNat_relative_square_sub_action (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f=0) :
    canonicalPairHamiltonianNat (canonicalPairHamiltonianNat f)-canonicalPairHamiltonianNat f =
      ((2*(-1/2:ℂ)^d)*natOccupationInner (w3RelativeSeed d) f) • w3RelativeSeed d := by
  rw [canonicalPairHamiltonianNat_relative_square_action d f hN hd hL,
    canonicalPairHamiltonianNat_relative_rank_action d f hN hd hL,←sub_smul]
  congr 1
  ring

theorem canonicalPairHamiltonianNat_relative_square_sub_form (d : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 3) (hd : g.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat g=0) :
    natOccupationInner f
      (canonicalPairHamiltonianNat (canonicalPairHamiltonianNat g)-canonicalPairHamiltonianNat g) =
      (2*(-1/2:ℂ)^d)*star (natOccupationInner (w3RelativeSeed d) f)*
        natOccupationInner (w3RelativeSeed d) g := by
  rw [canonicalPairHamiltonianNat_relative_square_sub_action d g hN hd hL,
    natOccupationInner_smul_right,natOccupationInner_conj_symm]
  ring

theorem relative_square_sub_coefficient_odd (d : ℕ) (hd : Odd d) :
    (2*(-1/2:ℂ)^d) = -((2*(1/2:ℝ)^d:ℝ):ℂ) := by
  rw [show (-1/2:ℂ)=-(1/2:ℂ) by ring,hd.neg_pow]
  push_cast
  ring

/-- The genuine odd-degree negative rank term has exactly the coefficient
used by the independently proved thermal relative-tail estimate. -/
theorem canonicalPairHamiltonianNat_relative_odd_square_sub_action
    (d : ℕ) (f : Core ℕ ℂ) (hodd : Odd d)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f=0) :
    canonicalPairHamiltonianNat (canonicalPairHamiltonianNat f)-canonicalPairHamiltonianNat f =
      (-((2*(1/2:ℝ)^d:ℝ):ℂ)*natOccupationInner (w3RelativeSeed d) f) • w3RelativeSeed d := by
  rw [canonicalPairHamiltonianNat_relative_square_sub_action d f hN hd hL,
    relative_square_sub_coefficient_odd d hodd]

#print axioms canonicalPairHamiltonianNat_relative_seed
#print axioms canonicalPairHamiltonianNat_relative_square_action
#print axioms canonicalPairHamiltonianNat_relative_square_sub_action
#print axioms canonicalPairHamiltonianNat_relative_square_sub_form
#print axioms canonicalPairHamiltonianNat_relative_odd_square_sub_action
end TorusLean.BosonFiniteCertificate
