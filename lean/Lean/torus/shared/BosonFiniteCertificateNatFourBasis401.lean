import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-1 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f401basis : Fin 1 → List ℕ := ![[0,0,0,1]]

theorem f401_basis_enumeration : List.ofFn f401basis = natFourBasis 1 := by
  decide +kernel

theorem f401_occupation_injective :
    Function.Injective (fun a : Fin 1 => wordOccupation (f401basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 1, (f401basis a).Perm (f401basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f401_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 1) :
    ∃ x : Fin 1 → ℂ, natFourWordBlock f401basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 1 f401basis
    f401_basis_enumeration f hN hd

#print axioms f401_basis_enumeration
#print axioms f401_occupation_injective
#print axioms f401_homogeneous_complete
end TorusLean.BosonFiniteCertificate
