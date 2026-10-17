import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-11 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f411basis : Fin 27 → List ℕ := ![[0,0,0,11], [0,0,1,10], [0,0,2,9], [0,0,3,8], [0,0,4,7], [0,0,5,6], [0,1,1,9], [0,1,2,8], [0,1,3,7], [0,1,4,6], [0,1,5,5], [0,2,2,7], [0,2,3,6], [0,2,4,5], [0,3,3,5], [0,3,4,4], [1,1,1,8], [1,1,2,7], [1,1,3,6], [1,1,4,5], [1,2,2,6], [1,2,3,5], [1,2,4,4], [1,3,3,4], [2,2,2,5], [2,2,3,4], [2,3,3,3]]

theorem f411_basis_enumeration : List.ofFn f411basis = natFourBasis 11 := by
  decide +kernel

theorem f411_occupation_injective :
    Function.Injective (fun a : Fin 27 => wordOccupation (f411basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 27, (f411basis a).Perm (f411basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f411_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 11) :
    ∃ x : Fin 27 → ℂ, natFourWordBlock f411basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 11 f411basis
    f411_basis_enumeration f hN hd

#print axioms f411_basis_enumeration
#print axioms f411_occupation_injective
#print axioms f411_homogeneous_complete
end TorusLean.BosonFiniteCertificate
