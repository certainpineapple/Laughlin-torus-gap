import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis410
import torus.shared.BosonFiniteCertificate410
import torus.shared.BosonFiniteCertificateNatFourBasis409

/-! Degree-10 actual Nat COM lowering and complete relative kernel.
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

def f410lowerNat : Matrix (Fin 18) (Fin 23) ℕ :=
  !![10, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 9, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 8, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 7, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 6, 10, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 7, 3, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 8, 6, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 2, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 0, 4, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 8, 0, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 0, 6, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 9, 0, 4;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6]

theorem f410_rational_lower_check : ∀ a : Fin 23,
    natFourRationalLowerWord (f410basis a) =
      ∑ b : Fin 18, b410lower b a • (wordPolynomial (f409basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f410lowerNat b a : ℚ)=b410lower b a :=
    natFourRationalEntryCheck_sound (fun b a => (f410lowerNat b a : ℚ))
      b410lower (by decide +kernel)
  have hp : ∀ a : Fin 23, (natFourExpandedWords (natFourLoweredWords (f410basis a))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f410lowerNat b a,f409basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_lower_rational_of_expanded_perm
    (f410basis a) f409basis (fun b => f410lowerNat b a) (hp a)

theorem f410_actual_lower_word (a : Fin 23) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f410basis a)) =
      ∑ b : Fin 18, (b410lower b a : ℂ) • scaledWord factorialRootNat (f409basis b) :=
  natFour_lower_action_of_rational_check (f410basis a) f409basis
    (fun b => b410lower b a) (f410_rational_lower_check a)

theorem f410_actual_lower_block (v : Fin 23 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f410basis v) =
      natFourWordBlock f409basis (complexify b410lower *ᵥ v) :=
  natFourWordBlock_rect_action f410basis f409basis canonicalCOMLowerNat
    (complexify b410lower) f410_actual_lower_word v

theorem f410_actual_relative_kernel (v : Fin 23 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f410basis v)=0 ↔
      ∃ x : Fin 5 → ℂ, complexify b410relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f410basis f409basis
    f409_occupation_injective
    b410lower b410relative b410free b410split
    b410_relative_annihilated b410_relative_complete f410_actual_lower_block v

theorem f410_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 10) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 5 → ℂ, natFourWordBlock f410basis (complexify b410relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 10 f410basis f409basis
    f410_basis_enumeration f410_occupation_injective
    f409_occupation_injective
    b410lower b410relative b410free b410split
    b410_relative_annihilated b410_relative_complete f410_actual_lower_block f hN hd

#print axioms f410_rational_lower_check
#print axioms f410_actual_lower_word
#print axioms f410_actual_lower_block
#print axioms f410_actual_relative_kernel
#print axioms f410_actual_relative_complete
end TorusLean.BosonFiniteCertificate
