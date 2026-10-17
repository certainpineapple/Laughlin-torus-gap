import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-2 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f402basis : Fin 2 → List ℕ := ![[0,0,0,2], [0,0,1,1]]

theorem f402_basis_enumeration : List.ofFn f402basis = natFourBasis 2 := by
  decide +kernel

theorem f402_occupation_injective :
    Function.Injective (fun a : Fin 2 => wordOccupation (f402basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 2, (f402basis a).Perm (f402basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f402_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 2) :
    ∃ x : Fin 2 → ℂ, natFourWordBlock f402basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 2 f402basis
    f402_basis_enumeration f hN hd

#print axioms f402_basis_enumeration
#print axioms f402_occupation_injective
#print axioms f402_homogeneous_complete
end TorusLean.BosonFiniteCertificate
