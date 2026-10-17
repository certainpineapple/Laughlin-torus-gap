import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis404
import torus.shared.BosonFiniteCertificate404
import torus.shared.BosonFiniteCertificateNatFourBasis403

/-! Degree-4 actual Nat COM lowering and complete relative kernel.
All basis actions are independently checked in rational polynomials before
transporting the frozen split witness to the real source operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open Matrix
open scoped BigOperators

theorem f404_rational_lower_check : ∀ a : Fin 5,
    natFourRationalLowerWord (f404basis a) =
      ∑ b : Fin 3, b404lower b a • (wordPolynomial (f403basis b) : Core ℕ ℚ) := by
  intro a
  fin_cases a <;>
    norm_num [natFourRationalLowerWord,natFourLoweredWords,f404basis,f403basis,
      b404lower,Fin.sum_univ_succ,wordPolynomial,Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem f404_actual_lower_word (a : Fin 5) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f404basis a)) =
      ∑ b : Fin 3, (b404lower b a : ℂ) • scaledWord factorialRootNat (f403basis b) :=
  natFour_lower_action_of_rational_check (f404basis a) f403basis
    (fun b => b404lower b a) (f404_rational_lower_check a)

theorem f404_actual_lower_block (v : Fin 5 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f404basis v) =
      natFourWordBlock f403basis (complexify b404lower *ᵥ v) :=
  natFourWordBlock_rect_action f404basis f403basis canonicalCOMLowerNat
    (complexify b404lower) f404_actual_lower_word v

theorem f404_actual_relative_kernel (v : Fin 5 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f404basis v)=0 ↔
      ∃ x : Fin 2 → ℂ, complexify b404relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f404basis f403basis
    f403_occupation_injective
    b404lower b404relative b404free b404split
    b404_relative_annihilated b404_relative_complete f404_actual_lower_block v

theorem f404_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 4) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 2 → ℂ, natFourWordBlock f404basis (complexify b404relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 4 f404basis f403basis
    f404_basis_enumeration f404_occupation_injective
    f403_occupation_injective
    b404lower b404relative b404free b404split
    b404_relative_annihilated b404_relative_complete f404_actual_lower_block f hN hd

#print axioms f404_rational_lower_check
#print axioms f404_actual_lower_word
#print axioms f404_actual_lower_block
#print axioms f404_actual_relative_kernel
#print axioms f404_actual_relative_complete
end TorusLean.BosonFiniteCertificate
