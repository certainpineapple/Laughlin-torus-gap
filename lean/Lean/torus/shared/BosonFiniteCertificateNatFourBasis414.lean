import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-14 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f414basis : Fin 47 → List ℕ := ![[0,0,0,14], [0,0,1,13], [0,0,2,12], [0,0,3,11], [0,0,4,10], [0,0,5,9], [0,0,6,8], [0,0,7,7], [0,1,1,12], [0,1,2,11], [0,1,3,10], [0,1,4,9], [0,1,5,8], [0,1,6,7], [0,2,2,10], [0,2,3,9], [0,2,4,8], [0,2,5,7], [0,2,6,6], [0,3,3,8], [0,3,4,7], [0,3,5,6], [0,4,4,6], [0,4,5,5], [1,1,1,11], [1,1,2,10], [1,1,3,9], [1,1,4,8], [1,1,5,7], [1,1,6,6], [1,2,2,9], [1,2,3,8], [1,2,4,7], [1,2,5,6], [1,3,3,7], [1,3,4,6], [1,3,5,5], [1,4,4,5], [2,2,2,8], [2,2,3,7], [2,2,4,6], [2,2,5,5], [2,3,3,6], [2,3,4,5], [2,4,4,4], [3,3,3,5], [3,3,4,4]]

theorem f414_basis_enumeration : List.ofFn f414basis = natFourBasis 14 := by
  decide +kernel

theorem f414_occupation_injective :
    Function.Injective (fun a : Fin 47 => wordOccupation (f414basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 47, (f414basis a).Perm (f414basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f414_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 14) :
    ∃ x : Fin 47 → ℂ, natFourWordBlock f414basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 14 f414basis
    f414_basis_enumeration f hN hd

#print axioms f414_basis_enumeration
#print axioms f414_occupation_injective
#print axioms f414_homogeneous_complete
end TorusLean.BosonFiniteCertificate
