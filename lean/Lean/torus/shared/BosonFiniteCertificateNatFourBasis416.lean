import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-16 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f416basis : Fin 64 → List ℕ := ![[0,0,0,16], [0,0,1,15], [0,0,2,14], [0,0,3,13], [0,0,4,12], [0,0,5,11], [0,0,6,10], [0,0,7,9], [0,0,8,8], [0,1,1,14], [0,1,2,13], [0,1,3,12], [0,1,4,11], [0,1,5,10], [0,1,6,9], [0,1,7,8], [0,2,2,12], [0,2,3,11], [0,2,4,10], [0,2,5,9], [0,2,6,8], [0,2,7,7], [0,3,3,10], [0,3,4,9], [0,3,5,8], [0,3,6,7], [0,4,4,8], [0,4,5,7], [0,4,6,6], [0,5,5,6], [1,1,1,13], [1,1,2,12], [1,1,3,11], [1,1,4,10], [1,1,5,9], [1,1,6,8], [1,1,7,7], [1,2,2,11], [1,2,3,10], [1,2,4,9], [1,2,5,8], [1,2,6,7], [1,3,3,9], [1,3,4,8], [1,3,5,7], [1,3,6,6], [1,4,4,7], [1,4,5,6], [1,5,5,5], [2,2,2,10], [2,2,3,9], [2,2,4,8], [2,2,5,7], [2,2,6,6], [2,3,3,8], [2,3,4,7], [2,3,5,6], [2,4,4,6], [2,4,5,5], [3,3,3,7], [3,3,4,6], [3,3,5,5], [3,4,4,5], [4,4,4,4]]

theorem f416_basis_enumeration : List.ofFn f416basis = natFourBasis 16 := by
  decide +kernel

theorem f416_occupation_injective :
    Function.Injective (fun a : Fin 64 => wordOccupation (f416basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 64, (f416basis a).Perm (f416basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f416_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 16) :
    ∃ x : Fin 64 → ℂ, natFourWordBlock f416basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 16 f416basis
    f416_basis_enumeration f hN hd

#print axioms f416_basis_enumeration
#print axioms f416_occupation_injective
#print axioms f416_homogeneous_complete
end TorusLean.BosonFiniteCertificate
