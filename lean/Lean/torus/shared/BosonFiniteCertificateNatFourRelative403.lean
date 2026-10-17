import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis403
import torus.shared.BosonFiniteCertificate403
import torus.shared.BosonFiniteCertificateNatFourBasis402

/-! Degree-3 actual Nat COM lowering and complete relative kernel.
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

theorem f403_rational_lower_check : ∀ a : Fin 3,
    natFourRationalLowerWord (f403basis a) =
      ∑ b : Fin 2, b403lower b a • (wordPolynomial (f402basis b) : Core ℕ ℚ) := by
  intro a
  fin_cases a <;>
    norm_num [natFourRationalLowerWord,natFourLoweredWords,f403basis,f402basis,
      b403lower,Fin.sum_univ_succ,wordPolynomial,Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem f403_actual_lower_word (a : Fin 3) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f403basis a)) =
      ∑ b : Fin 2, (b403lower b a : ℂ) • scaledWord factorialRootNat (f402basis b) :=
  natFour_lower_action_of_rational_check (f403basis a) f402basis
    (fun b => b403lower b a) (f403_rational_lower_check a)

theorem f403_actual_lower_block (v : Fin 3 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f403basis v) =
      natFourWordBlock f402basis (complexify b403lower *ᵥ v) :=
  natFourWordBlock_rect_action f403basis f402basis canonicalCOMLowerNat
    (complexify b403lower) f403_actual_lower_word v

theorem f403_actual_relative_kernel (v : Fin 3 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f403basis v)=0 ↔
      ∃ x : Fin 1 → ℂ, complexify b403relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f403basis f402basis
    f402_occupation_injective
    b403lower b403relative b403free b403split
    b403_relative_annihilated b403_relative_complete f403_actual_lower_block v

theorem f403_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 3) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 1 → ℂ, natFourWordBlock f403basis (complexify b403relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 3 f403basis f402basis
    f403_basis_enumeration f403_occupation_injective
    f402_occupation_injective
    b403lower b403relative b403free b403split
    b403_relative_annihilated b403_relative_complete f403_actual_lower_block f hN hd

#print axioms f403_rational_lower_check
#print axioms f403_actual_lower_word
#print axioms f403_actual_lower_block
#print axioms f403_actual_relative_kernel
#print axioms f403_actual_relative_complete
end TorusLean.BosonFiniteCertificate
