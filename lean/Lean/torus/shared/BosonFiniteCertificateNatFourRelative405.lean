import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis405
import torus.shared.BosonFiniteCertificate405
import torus.shared.BosonFiniteCertificateNatFourBasis404

/-! Degree-5 actual Nat COM lowering and complete relative kernel.
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

theorem f405_rational_lower_check : ∀ a : Fin 6,
    natFourRationalLowerWord (f405basis a) =
      ∑ b : Fin 5, b405lower b a • (wordPolynomial (f404basis b) : Core ℕ ℚ) := by
  intro a
  fin_cases a <;>
    norm_num [natFourRationalLowerWord,natFourLoweredWords,f405basis,f404basis,
      b405lower,Fin.sum_univ_succ,wordPolynomial,Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem f405_actual_lower_word (a : Fin 6) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f405basis a)) =
      ∑ b : Fin 5, (b405lower b a : ℂ) • scaledWord factorialRootNat (f404basis b) :=
  natFour_lower_action_of_rational_check (f405basis a) f404basis
    (fun b => b405lower b a) (f405_rational_lower_check a)

theorem f405_actual_lower_block (v : Fin 6 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f405basis v) =
      natFourWordBlock f404basis (complexify b405lower *ᵥ v) :=
  natFourWordBlock_rect_action f405basis f404basis canonicalCOMLowerNat
    (complexify b405lower) f405_actual_lower_word v

theorem f405_actual_relative_kernel (v : Fin 6 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f405basis v)=0 ↔
      ∃ x : Fin 1 → ℂ, complexify b405relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f405basis f404basis
    f404_occupation_injective
    b405lower b405relative b405free b405split
    b405_relative_annihilated b405_relative_complete f405_actual_lower_block v

theorem f405_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 5) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 1 → ℂ, natFourWordBlock f405basis (complexify b405relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 5 f405basis f404basis
    f405_basis_enumeration f405_occupation_injective
    f404_occupation_injective
    b405lower b405relative b405free b405split
    b405_relative_annihilated b405_relative_complete f405_actual_lower_block f hN hd

#print axioms f405_rational_lower_check
#print axioms f405_actual_lower_word
#print axioms f405_actual_lower_block
#print axioms f405_actual_relative_kernel
#print axioms f405_actual_relative_complete
end TorusLean.BosonFiniteCertificate
