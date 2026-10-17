import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-6 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f406basis : Fin 9 → List ℕ := ![[0,0,0,6], [0,0,1,5], [0,0,2,4], [0,0,3,3], [0,1,1,4], [0,1,2,3], [0,2,2,2], [1,1,1,3], [1,1,2,2]]

theorem f406_basis_enumeration : List.ofFn f406basis = natFourBasis 6 := by
  decide +kernel

theorem f406_occupation_injective :
    Function.Injective (fun a : Fin 9 => wordOccupation (f406basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 9, (f406basis a).Perm (f406basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f406_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 6) :
    ∃ x : Fin 9 → ℂ, natFourWordBlock f406basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 6 f406basis
    f406_basis_enumeration f hN hd

#print axioms f406_basis_enumeration
#print axioms f406_occupation_injective
#print axioms f406_homogeneous_complete
end TorusLean.BosonFiniteCertificate
