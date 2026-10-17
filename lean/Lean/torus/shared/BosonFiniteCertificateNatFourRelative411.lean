import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis411
import torus.shared.BosonFiniteCertificate411
import torus.shared.BosonFiniteCertificateNatFourBasis410

/-! Degree-11 actual Nat COM lowering and complete relative kernel.
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

def f411lowerNat : Matrix (Fin 23) (Fin 27) ℕ :=
  !![11, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 10, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 9, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 8, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 7, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 9, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 8, 3, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 7, 4, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 10, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 3, 0, 4, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 0, 2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 0, 0, 6, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 8, 6, 0, 4, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 9]

private theorem f411_lower_nat_cast : ∀ b a, (f411lowerNat b a : ℚ)=b411lower b a := by
  intro b a
  fin_cases b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 0 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 0 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 1 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 1 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 2 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 2 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 3 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 3 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 4 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 4 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 5 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 5 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 6 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 6 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 7 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 7 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 8 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 8 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 9 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 9 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 10 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 10 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 11 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 11 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 12 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 12 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 13 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 13 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 14 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 14 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 15 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 15 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 16 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 16 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 17 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 17 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 18 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 18 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 19 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 19 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 20 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 20 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 21 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 21 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 27) => (f411lowerNat 22 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 27) => b411lower 22 a)
      (by decide +kernel) 0 a

#print axioms f411_lower_nat_cast

theorem f411_rational_lower_check : ∀ a : Fin 27,
    natFourRationalLowerWord (f411basis a) =
      ∑ b : Fin 23, b411lower b a • (wordPolynomial (f410basis b) : Core ℕ ℚ) := by
  have hc := f411_lower_nat_cast
  have hp : ∀ a : Fin 27, (natFourExpandedWords (natFourLoweredWords (f411basis a))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f411lowerNat b a,f410basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_lower_rational_of_expanded_perm
    (f411basis a) f410basis (fun b => f411lowerNat b a) (hp a)

theorem f411_actual_lower_word (a : Fin 27) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f411basis a)) =
      ∑ b : Fin 23, (b411lower b a : ℂ) • scaledWord factorialRootNat (f410basis b) :=
  natFour_lower_action_of_rational_check (f411basis a) f410basis
    (fun b => b411lower b a) (f411_rational_lower_check a)

theorem f411_actual_lower_block (v : Fin 27 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f411basis v) =
      natFourWordBlock f410basis (complexify b411lower *ᵥ v) :=
  natFourWordBlock_rect_action f411basis f410basis canonicalCOMLowerNat
    (complexify b411lower) f411_actual_lower_word v

theorem f411_actual_relative_kernel (v : Fin 27 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f411basis v)=0 ↔
      ∃ x : Fin 4 → ℂ, complexify b411relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f411basis f410basis
    f410_occupation_injective
    b411lower b411relative b411free b411split
    b411_relative_annihilated b411_relative_complete f411_actual_lower_block v

theorem f411_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 11) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 4 → ℂ, natFourWordBlock f411basis (complexify b411relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 11 f411basis f410basis
    f411_basis_enumeration f411_occupation_injective
    f410_occupation_injective
    b411lower b411relative b411free b411split
    b411_relative_annihilated b411_relative_complete f411_actual_lower_block f hN hd

#print axioms f411_rational_lower_check
#print axioms f411_actual_lower_word
#print axioms f411_actual_lower_block
#print axioms f411_actual_relative_kernel
#print axioms f411_actual_relative_complete
end TorusLean.BosonFiniteCertificate
