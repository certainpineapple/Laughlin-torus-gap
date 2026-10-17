import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-15 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f415basis : Fin 54 → List ℕ := ![[0,0,0,15], [0,0,1,14], [0,0,2,13], [0,0,3,12], [0,0,4,11], [0,0,5,10], [0,0,6,9], [0,0,7,8], [0,1,1,13], [0,1,2,12], [0,1,3,11], [0,1,4,10], [0,1,5,9], [0,1,6,8], [0,1,7,7], [0,2,2,11], [0,2,3,10], [0,2,4,9], [0,2,5,8], [0,2,6,7], [0,3,3,9], [0,3,4,8], [0,3,5,7], [0,3,6,6], [0,4,4,7], [0,4,5,6], [0,5,5,5], [1,1,1,12], [1,1,2,11], [1,1,3,10], [1,1,4,9], [1,1,5,8], [1,1,6,7], [1,2,2,10], [1,2,3,9], [1,2,4,8], [1,2,5,7], [1,2,6,6], [1,3,3,8], [1,3,4,7], [1,3,5,6], [1,4,4,6], [1,4,5,5], [2,2,2,9], [2,2,3,8], [2,2,4,7], [2,2,5,6], [2,3,3,7], [2,3,4,6], [2,3,5,5], [2,4,4,5], [3,3,3,6], [3,3,4,5], [3,4,4,4]]

theorem f415_basis_enumeration : List.ofFn f415basis = natFourBasis 15 := by
  decide +kernel

theorem f415_occupation_injective :
    Function.Injective (fun a : Fin 54 => wordOccupation (f415basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 54, (f415basis a).Perm (f415basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f415_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 15) :
    ∃ x : Fin 54 → ℂ, natFourWordBlock f415basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 15 f415basis
    f415_basis_enumeration f hN hd

#print axioms f415_basis_enumeration
#print axioms f415_occupation_injective
#print axioms f415_homogeneous_complete
end TorusLean.BosonFiniteCertificate
