import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-13 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f413basis : Fin 39 → List ℕ := ![[0,0,0,13], [0,0,1,12], [0,0,2,11], [0,0,3,10], [0,0,4,9], [0,0,5,8], [0,0,6,7], [0,1,1,11], [0,1,2,10], [0,1,3,9], [0,1,4,8], [0,1,5,7], [0,1,6,6], [0,2,2,9], [0,2,3,8], [0,2,4,7], [0,2,5,6], [0,3,3,7], [0,3,4,6], [0,3,5,5], [0,4,4,5], [1,1,1,10], [1,1,2,9], [1,1,3,8], [1,1,4,7], [1,1,5,6], [1,2,2,8], [1,2,3,7], [1,2,4,6], [1,2,5,5], [1,3,3,6], [1,3,4,5], [1,4,4,4], [2,2,2,7], [2,2,3,6], [2,2,4,5], [2,3,3,5], [2,3,4,4], [3,3,3,4]]

theorem f413_basis_enumeration : List.ofFn f413basis = natFourBasis 13 := by
  decide +kernel

theorem f413_occupation_injective :
    Function.Injective (fun a : Fin 39 => wordOccupation (f413basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 39, (f413basis a).Perm (f413basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f413_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 13) :
    ∃ x : Fin 39 → ℂ, natFourWordBlock f413basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 13 f413basis
    f413_basis_enumeration f hN hd

#print axioms f413_basis_enumeration
#print axioms f413_occupation_injective
#print axioms f413_homogeneous_complete
end TorusLean.BosonFiniteCertificate
