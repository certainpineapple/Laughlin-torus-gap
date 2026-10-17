import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-7 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f407basis : Fin 11 → List ℕ := ![[0,0,0,7], [0,0,1,6], [0,0,2,5], [0,0,3,4], [0,1,1,5], [0,1,2,4], [0,1,3,3], [0,2,2,3], [1,1,1,4], [1,1,2,3], [1,2,2,2]]

theorem f407_basis_enumeration : List.ofFn f407basis = natFourBasis 7 := by
  decide +kernel

theorem f407_occupation_injective :
    Function.Injective (fun a : Fin 11 => wordOccupation (f407basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 11, (f407basis a).Perm (f407basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f407_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 7) :
    ∃ x : Fin 11 → ℂ, natFourWordBlock f407basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 7 f407basis
    f407_basis_enumeration f hN hd

#print axioms f407_basis_enumeration
#print axioms f407_occupation_injective
#print axioms f407_homogeneous_complete
end TorusLean.BosonFiniteCertificate
