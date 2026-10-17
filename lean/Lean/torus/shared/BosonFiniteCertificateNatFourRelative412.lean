import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis412
import torus.shared.BosonFiniteCertificate412
import torus.shared.BosonFiniteCertificateNatFourBasis411

/-! Degree-12 actual Nat COM lowering and complete relative kernel.
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

def f412lowerNat : Matrix (Fin 27) (Fin 34) ℕ :=
  !![12, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 11, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 10, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 9, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 8, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 7, 12, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 9, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 5, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 4, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 10, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 10, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 3, 0, 0, 0, 6, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 6, 0, 0, 4, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 3, 0, 0, 4, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 8, 0, 0, 0, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 3, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 8, 6, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 12]

private theorem f412_lower_nat_cast : ∀ b a, (f412lowerNat b a : ℚ)=b412lower b a := by
  intro b a
  fin_cases b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 0 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 0 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 1 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 1 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 2 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 2 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 3 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 3 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 4 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 4 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 5 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 5 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 6 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 6 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 7 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 7 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 8 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 8 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 9 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 9 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 10 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 10 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 11 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 11 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 12 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 12 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 13 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 13 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 14 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 14 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 15 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 15 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 16 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 16 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 17 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 17 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 18 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 18 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 19 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 19 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 20 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 20 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 21 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 21 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 22 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 22 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 23 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 23 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 24 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 24 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 25 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 25 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412lowerNat 26 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => b412lower 26 a)
      (by decide +kernel) 0 a

#print axioms f412_lower_nat_cast

theorem f412_rational_lower_check : ∀ a : Fin 34,
    natFourRationalLowerWord (f412basis a) =
      ∑ b : Fin 27, b412lower b a • (wordPolynomial (f411basis b) : Core ℕ ℚ) := by
  have hc := f412_lower_nat_cast
  have hp : ∀ a : Fin 34, (natFourExpandedWords (natFourLoweredWords (f412basis a))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f412lowerNat b a,f411basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_lower_rational_of_expanded_perm
    (f412basis a) f411basis (fun b => f412lowerNat b a) (hp a)

theorem f412_actual_lower_word (a : Fin 34) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f412basis a)) =
      ∑ b : Fin 27, (b412lower b a : ℂ) • scaledWord factorialRootNat (f411basis b) :=
  natFour_lower_action_of_rational_check (f412basis a) f411basis
    (fun b => b412lower b a) (f412_rational_lower_check a)

theorem f412_actual_lower_block (v : Fin 34 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f412basis v) =
      natFourWordBlock f411basis (complexify b412lower *ᵥ v) :=
  natFourWordBlock_rect_action f412basis f411basis canonicalCOMLowerNat
    (complexify b412lower) f412_actual_lower_word v

theorem f412_actual_relative_kernel (v : Fin 34 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f412basis v)=0 ↔
      ∃ x : Fin 7 → ℂ, complexify b412relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f412basis f411basis
    f411_occupation_injective
    b412lower b412relative b412free b412split
    b412_relative_annihilated b412_relative_complete f412_actual_lower_block v

theorem f412_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 12) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 7 → ℂ, natFourWordBlock f412basis (complexify b412relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 12 f412basis f411basis
    f412_basis_enumeration f412_occupation_injective
    f411_occupation_injective
    b412lower b412relative b412free b412split
    b412_relative_annihilated b412_relative_complete f412_actual_lower_block f hN hd

#print axioms f412_rational_lower_check
#print axioms f412_actual_lower_word
#print axioms f412_actual_lower_block
#print axioms f412_actual_relative_kernel
#print axioms f412_actual_relative_complete
end TorusLean.BosonFiniteCertificate
