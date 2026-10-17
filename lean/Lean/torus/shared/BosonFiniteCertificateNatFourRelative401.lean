import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis401
import torus.shared.BosonFiniteCertificate401
import torus.shared.BosonFiniteCertificateNatFourBasis400

/-! Degree-1 actual Nat COM lowering and complete relative kernel.
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

theorem f401_rational_lower_check : ∀ a : Fin 1,
    natFourRationalLowerWord (f401basis a) =
      ∑ b : Fin 1, b401lower b a • (wordPolynomial (f400basis b) : Core ℕ ℚ) := by
  intro a
  fin_cases a <;>
    norm_num [natFourRationalLowerWord,natFourLoweredWords,f401basis,f400basis,
      b401lower,Fin.sum_univ_succ,wordPolynomial,Algebra.smul_def] <;> ring

theorem f401_actual_lower_word (a : Fin 1) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f401basis a)) =
      ∑ b : Fin 1, (b401lower b a : ℂ) • scaledWord factorialRootNat (f400basis b) :=
  natFour_lower_action_of_rational_check (f401basis a) f400basis
    (fun b => b401lower b a) (f401_rational_lower_check a)

theorem f401_actual_lower_block (v : Fin 1 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f401basis v) =
      natFourWordBlock f400basis (complexify b401lower *ᵥ v) :=
  natFourWordBlock_rect_action f401basis f400basis canonicalCOMLowerNat
    (complexify b401lower) f401_actual_lower_word v

theorem f401_actual_relative_kernel (v : Fin 1 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f401basis v)=0 ↔
      ∃ x : Fin 0 → ℂ, complexify b401relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f401basis f400basis
    f400_occupation_injective
    b401lower b401relative b401free b401split
    b401_relative_annihilated b401_relative_complete f401_actual_lower_block v

theorem f401_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 1) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 0 → ℂ, natFourWordBlock f401basis (complexify b401relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 1 f401basis f400basis
    f401_basis_enumeration f401_occupation_injective
    f400_occupation_injective
    b401lower b401relative b401free b401split
    b401_relative_annihilated b401_relative_complete f401_actual_lower_block f hN hd

#print axioms f401_rational_lower_check
#print axioms f401_actual_lower_word
#print axioms f401_actual_lower_block
#print axioms f401_actual_relative_kernel
#print axioms f401_actual_relative_complete
end TorusLean.BosonFiniteCertificate
