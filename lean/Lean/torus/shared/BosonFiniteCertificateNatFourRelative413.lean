import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis413
import torus.shared.BosonFiniteCertificate413
import torus.shared.BosonFiniteCertificateNatFourBasis412

/-! Degree-13 actual Nat COM lowering and complete relative kernel.
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

def f413lowerNat : Matrix (Fin 34) (Fin 39) ℕ :=
  !![13, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 12, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 11, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 10, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 9, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 8, 6, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 10, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 12, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 5, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 10, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 5, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 3, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 4, 0, 6, 0, 0, 0, 4, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 10, 0, 3, 0, 0, 0, 4, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 0, 0, 0, 0, 2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 12, 0, 0, 0, 0, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 3, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 6, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 3, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 8, 9;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]

private theorem f413_lower_nat_cast : ∀ b a, (f413lowerNat b a : ℚ)=b413lower b a := by
  intro b a
  fin_cases b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 0 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 0 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 1 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 1 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 2 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 2 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 3 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 3 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 4 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 4 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 5 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 5 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 6 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 6 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 7 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 7 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 8 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 8 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 9 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 9 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 10 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 10 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 11 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 11 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 12 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 12 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 13 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 13 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 14 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 14 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 15 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 15 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 16 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 16 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 17 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 17 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 18 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 18 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 19 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 19 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 20 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 20 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 21 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 21 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 22 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 22 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 23 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 23 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 24 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 24 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 25 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 25 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 26 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 26 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 27 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 27 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 28 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 28 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 29 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 29 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 30 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 30 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 31 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 31 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 32 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 32 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 39) => (f413lowerNat 33 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 39) => b413lower 33 a)
      (by decide +kernel) 0 a

#print axioms f413_lower_nat_cast

theorem f413_rational_lower_check : ∀ a : Fin 39,
    natFourRationalLowerWord (f413basis a) =
      ∑ b : Fin 34, b413lower b a • (wordPolynomial (f412basis b) : Core ℕ ℚ) := by
  have hc := f413_lower_nat_cast
  have hp : ∀ a : Fin 39, (natFourExpandedWords (natFourLoweredWords (f413basis a))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f413lowerNat b a,f412basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_lower_rational_of_expanded_perm
    (f413basis a) f412basis (fun b => f413lowerNat b a) (hp a)

theorem f413_actual_lower_word (a : Fin 39) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f413basis a)) =
      ∑ b : Fin 34, (b413lower b a : ℂ) • scaledWord factorialRootNat (f412basis b) :=
  natFour_lower_action_of_rational_check (f413basis a) f412basis
    (fun b => b413lower b a) (f413_rational_lower_check a)

theorem f413_actual_lower_block (v : Fin 39 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f413basis v) =
      natFourWordBlock f412basis (complexify b413lower *ᵥ v) :=
  natFourWordBlock_rect_action f413basis f412basis canonicalCOMLowerNat
    (complexify b413lower) f413_actual_lower_word v

theorem f413_actual_relative_kernel (v : Fin 39 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f413basis v)=0 ↔
      ∃ x : Fin 5 → ℂ, complexify b413relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f413basis f412basis
    f412_occupation_injective
    b413lower b413relative b413free b413split
    b413_relative_annihilated b413_relative_complete f413_actual_lower_block v

theorem f413_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 13) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 5 → ℂ, natFourWordBlock f413basis (complexify b413relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 13 f413basis f412basis
    f413_basis_enumeration f413_occupation_injective
    f412_occupation_injective
    b413lower b413relative b413free b413split
    b413_relative_annihilated b413_relative_complete f413_actual_lower_block f hN hd

#print axioms f413_rational_lower_check
#print axioms f413_actual_lower_word
#print axioms f413_actual_lower_block
#print axioms f413_actual_relative_kernel
#print axioms f413_actual_relative_complete
end TorusLean.BosonFiniteCertificate
