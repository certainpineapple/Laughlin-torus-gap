import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-5 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f405basis : Fin 6 → List ℕ := ![[0,0,0,5], [0,0,1,4], [0,0,2,3], [0,1,1,3], [0,1,2,2], [1,1,1,2]]

theorem f405_basis_enumeration : List.ofFn f405basis = natFourBasis 5 := by
  decide +kernel

theorem f405_occupation_injective :
    Function.Injective (fun a : Fin 6 => wordOccupation (f405basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 6, (f405basis a).Perm (f405basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f405_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 5) :
    ∃ x : Fin 6 → ℂ, natFourWordBlock f405basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 5 f405basis
    f405_basis_enumeration f hN hd

#print axioms f405_basis_enumeration
#print axioms f405_occupation_injective
#print axioms f405_homogeneous_complete
end TorusLean.BosonFiniteCertificate
