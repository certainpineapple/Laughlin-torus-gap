import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-8 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f408basis : Fin 15 → List ℕ := ![[0,0,0,8], [0,0,1,7], [0,0,2,6], [0,0,3,5], [0,0,4,4], [0,1,1,6], [0,1,2,5], [0,1,3,4], [0,2,2,4], [0,2,3,3], [1,1,1,5], [1,1,2,4], [1,1,3,3], [1,2,2,3], [2,2,2,2]]

theorem f408_basis_enumeration : List.ofFn f408basis = natFourBasis 8 := by
  decide +kernel

theorem f408_occupation_injective :
    Function.Injective (fun a : Fin 15 => wordOccupation (f408basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 15, (f408basis a).Perm (f408basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f408_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 8) :
    ∃ x : Fin 15 → ℂ, natFourWordBlock f408basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 8 f408basis
    f408_basis_enumeration f hN hd

#print axioms f408_basis_enumeration
#print axioms f408_occupation_injective
#print axioms f408_homogeneous_complete
end TorusLean.BosonFiniteCertificate
