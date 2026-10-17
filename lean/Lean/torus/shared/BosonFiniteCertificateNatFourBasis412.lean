import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-12 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f412basis : Fin 34 → List ℕ := ![[0,0,0,12], [0,0,1,11], [0,0,2,10], [0,0,3,9], [0,0,4,8], [0,0,5,7], [0,0,6,6], [0,1,1,10], [0,1,2,9], [0,1,3,8], [0,1,4,7], [0,1,5,6], [0,2,2,8], [0,2,3,7], [0,2,4,6], [0,2,5,5], [0,3,3,6], [0,3,4,5], [0,4,4,4], [1,1,1,9], [1,1,2,8], [1,1,3,7], [1,1,4,6], [1,1,5,5], [1,2,2,7], [1,2,3,6], [1,2,4,5], [1,3,3,5], [1,3,4,4], [2,2,2,6], [2,2,3,5], [2,2,4,4], [2,3,3,4], [3,3,3,3]]

theorem f412_basis_enumeration : List.ofFn f412basis = natFourBasis 12 := by
  decide +kernel

theorem f412_occupation_injective :
    Function.Injective (fun a : Fin 34 => wordOccupation (f412basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 34, (f412basis a).Perm (f412basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f412_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 12) :
    ∃ x : Fin 34 → ℂ, natFourWordBlock f412basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 12 f412basis
    f412_basis_enumeration f hN hd

#print axioms f412_basis_enumeration
#print axioms f412_occupation_injective
#print axioms f412_homogeneous_complete
end TorusLean.BosonFiniteCertificate
