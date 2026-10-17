import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-4 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f404basis : Fin 5 → List ℕ := ![[0,0,0,4], [0,0,1,3], [0,0,2,2], [0,1,1,2], [1,1,1,1]]

theorem f404_basis_enumeration : List.ofFn f404basis = natFourBasis 4 := by
  decide +kernel

theorem f404_occupation_injective :
    Function.Injective (fun a : Fin 5 => wordOccupation (f404basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 5, (f404basis a).Perm (f404basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f404_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 4) :
    ∃ x : Fin 5 → ℂ, natFourWordBlock f404basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 4 f404basis
    f404_basis_enumeration f hN hd

#print axioms f404_basis_enumeration
#print axioms f404_occupation_injective
#print axioms f404_homogeneous_complete
end TorusLean.BosonFiniteCertificate
