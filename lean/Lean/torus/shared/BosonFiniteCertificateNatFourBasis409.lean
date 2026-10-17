import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Exact degree-9 original four-particle occupation order. Completeness
follows from arbitrary Nat-label particle and orbital homogeneity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords

def f409basis : Fin 18 → List ℕ := ![[0,0,0,9], [0,0,1,8], [0,0,2,7], [0,0,3,6], [0,0,4,5], [0,1,1,7], [0,1,2,6], [0,1,3,5], [0,1,4,4], [0,2,2,5], [0,2,3,4], [0,3,3,3], [1,1,1,6], [1,1,2,5], [1,1,3,4], [1,2,2,4], [1,2,3,3], [2,2,2,3]]

theorem f409_basis_enumeration : List.ofFn f409basis = natFourBasis 9 := by
  decide +kernel

theorem f409_occupation_injective :
    Function.Injective (fun a : Fin 18 => wordOccupation (f409basis a)) := by
  intro a b h
  have hc : ∀ a b : Fin 18, (f409basis a).Perm (f409basis b) → a=b := by
    decide +kernel
  exact hc a b ((natFourOccupation_eq_iff_perm _ _).mp h)

theorem f409_homogeneous_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 9) :
    ∃ x : Fin 18 → ℂ, natFourWordBlock f409basis x = f :=
  natFour_homogeneous_eq_block_of_enumeration 9 f409basis
    f409_basis_enumeration f hN hd

#print axioms f409_basis_enumeration
#print axioms f409_occupation_injective
#print axioms f409_homogeneous_complete
end TorusLean.BosonFiniteCertificate
