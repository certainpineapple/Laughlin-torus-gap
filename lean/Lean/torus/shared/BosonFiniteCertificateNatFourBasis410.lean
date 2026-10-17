import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-10 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f410basis : Fin 23 → List ℕ := ![[0,0,0,10], [0,0,1,9], [0,0,2,8], [0,0,3,7], [0,0,4,6], [0,0,5,5], [0,1,1,8], [0,1,2,7], [0,1,3,6], [0,1,4,5], [0,2,2,6], [0,2,3,5], [0,2,4,4], [0,3,3,4], [1,1,1,7], [1,1,2,6], [1,1,3,5], [1,1,4,4], [1,2,2,5], [1,2,3,4], [1,3,3,3], [2,2,2,4], [2,2,3,3]]

theorem f410_basis_enumeration : List.ofFn f410basis = natFourBasis 10 := by
  decide +kernel

theorem f410_occupation_injective :
    Function.Injective (fun a : Fin 23 => wordOccupation (f410basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 23, (f410basis a).Perm (f410basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f410_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 10) :
    ∃ x : Fin 23 → ℂ, natFourWordBlock f410basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 10 f410basis
    f410_basis_enumeration f hN hd

#print axioms f410_basis_enumeration
#print axioms f410_occupation_injective
#print axioms f410_homogeneous_complete
end TorusLean.BosonFiniteCertificate
