import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis407
import torus.shared.BosonFiniteCertificate407
import torus.shared.BosonFiniteCertificateNatFourBasis406

/-! Degree-7 actual Nat COM lowering and complete relative kernel.
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

theorem f407_rational_lower_check : ∀ a : Fin 11,
    natFourRationalLowerWord (f407basis a) =
      ∑ b : Fin 9, b407lower b a • (wordPolynomial (f406basis b) : Core ℕ ℚ) := by
  intro a
  fin_cases a <;>
    norm_num [natFourRationalLowerWord,natFourLoweredWords,f407basis,f406basis,
      b407lower,Fin.sum_univ_succ,wordPolynomial,Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem f407_actual_lower_word (a : Fin 11) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f407basis a)) =
      ∑ b : Fin 9, (b407lower b a : ℂ) • scaledWord factorialRootNat (f406basis b) :=
  natFour_lower_action_of_rational_check (f407basis a) f406basis
    (fun b => b407lower b a) (f407_rational_lower_check a)

theorem f407_actual_lower_block (v : Fin 11 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f407basis v) =
      natFourWordBlock f406basis (complexify b407lower *ᵥ v) :=
  natFourWordBlock_rect_action f407basis f406basis canonicalCOMLowerNat
    (complexify b407lower) f407_actual_lower_word v

theorem f407_actual_relative_kernel (v : Fin 11 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f407basis v)=0 ↔
      ∃ x : Fin 2 → ℂ, complexify b407relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f407basis f406basis
    f406_occupation_injective
    b407lower b407relative b407free b407split
    b407_relative_annihilated b407_relative_complete f407_actual_lower_block v

theorem f407_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 7) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 2 → ℂ, natFourWordBlock f407basis (complexify b407relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 7 f407basis f406basis
    f407_basis_enumeration f407_occupation_injective
    f406_occupation_injective
    b407lower b407relative b407free b407split
    b407_relative_annihilated b407_relative_complete f407_actual_lower_block f hN hd

#print axioms f407_rational_lower_check
#print axioms f407_actual_lower_word
#print axioms f407_actual_lower_block
#print axioms f407_actual_relative_kernel
#print axioms f407_actual_relative_complete
end TorusLean.BosonFiniteCertificate
