import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-0 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f400basis : Fin 1 → List ℕ := ![[0,0,0,0]]

theorem f400_basis_enumeration : List.ofFn f400basis = natFourBasis 0 := by
  decide +kernel

theorem f400_occupation_injective :
    Function.Injective (fun a : Fin 1 => wordOccupation (f400basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 1, (f400basis a).Perm (f400basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f400_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 0) :
    ∃ x : Fin 1 → ℂ, natFourWordBlock f400basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 0 f400basis
    f400_basis_enumeration f hN hd

#print axioms f400_basis_enumeration
#print axioms f400_occupation_injective
#print axioms f400_homogeneous_complete
end TorusLean.BosonFiniteCertificate
