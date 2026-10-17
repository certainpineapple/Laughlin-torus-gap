import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-3 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f403basis : Fin 3 → List ℕ := ![[0,0,0,3], [0,0,1,2], [0,1,1,1]]

theorem f403_basis_enumeration : List.ofFn f403basis = natFourBasis 3 := by
  decide +kernel

theorem f403_occupation_injective :
    Function.Injective (fun a : Fin 3 => wordOccupation (f403basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 3, (f403basis a).Perm (f403basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f403_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 3) :
    ∃ x : Fin 3 → ℂ, natFourWordBlock f403basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 3 f403basis
    f403_basis_enumeration f hN hd

#print axioms f403_basis_enumeration
#print axioms f403_occupation_injective
#print axioms f403_homogeneous_complete
end TorusLean.BosonFiniteCertificate
