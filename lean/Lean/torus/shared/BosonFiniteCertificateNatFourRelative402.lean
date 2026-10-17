import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis402
import torus.shared.BosonFiniteCertificate402
import torus.shared.BosonFiniteCertificateNatFourBasis401

/-! Degree-2 actual Nat COM lowering and complete relative kernel.
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

theorem f402_rational_lower_check : ∀ a : Fin 2,
    natFourRationalLowerWord (f402basis a) =
      ∑ b : Fin 1, b402lower b a • (wordPolynomial (f401basis b) : Core ℕ ℚ) := by
  intro a
  fin_cases a <;>
    norm_num [natFourRationalLowerWord,natFourLoweredWords,f402basis,f401basis,
      b402lower,Fin.sum_univ_succ,wordPolynomial,Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem f402_actual_lower_word (a : Fin 2) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f402basis a)) =
      ∑ b : Fin 1, (b402lower b a : ℂ) • scaledWord factorialRootNat (f401basis b) :=
  natFour_lower_action_of_rational_check (f402basis a) f401basis
    (fun b => b402lower b a) (f402_rational_lower_check a)

theorem f402_actual_lower_block (v : Fin 2 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f402basis v) =
      natFourWordBlock f401basis (complexify b402lower *ᵥ v) :=
  natFourWordBlock_rect_action f402basis f401basis canonicalCOMLowerNat
    (complexify b402lower) f402_actual_lower_word v

theorem f402_actual_relative_kernel (v : Fin 2 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f402basis v)=0 ↔
      ∃ x : Fin 1 → ℂ, complexify b402relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f402basis f401basis
    f401_occupation_injective
    b402lower b402relative b402free b402split
    b402_relative_annihilated b402_relative_complete f402_actual_lower_block v

theorem f402_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 2) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 1 → ℂ, natFourWordBlock f402basis (complexify b402relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 2 f402basis f401basis
    f402_basis_enumeration f402_occupation_injective
    f401_occupation_injective
    b402lower b402relative b402free b402split
    b402_relative_annihilated b402_relative_complete f402_actual_lower_block f hN hd

#print axioms f402_rational_lower_check
#print axioms f402_actual_lower_word
#print axioms f402_actual_lower_block
#print axioms f402_actual_relative_kernel
#print axioms f402_actual_relative_complete
end TorusLean.BosonFiniteCertificate
