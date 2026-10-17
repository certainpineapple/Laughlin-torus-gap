import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis409
import torus.shared.BosonFiniteCertificate409
import torus.shared.BosonFiniteCertificateNatFourBasis408

/-! Degree-9 actual Nat COM lowering and complete relative kernel.
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

def f409lowerNat : Matrix (Fin 15) (Fin 18) ℕ :=
  !![9, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 8, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 7, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 6, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 7, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 6, 3, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 5, 8, 0, 2, 0, 0, 0, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 9, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 4, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 6;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]

theorem f409_rational_lower_check : ∀ a : Fin 18,
    natFourRationalLowerWord (f409basis a) =
      ∑ b : Fin 15, b409lower b a • (wordPolynomial (f408basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f409lowerNat b a : ℚ)=b409lower b a :=
    natFourRationalEntryCheck_sound (fun b a => (f409lowerNat b a : ℚ))
      b409lower (by decide +kernel)
  have hp : ∀ a : Fin 18, (natFourExpandedWords (natFourLoweredWords (f409basis a))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f409lowerNat b a,f408basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_lower_rational_of_expanded_perm
    (f409basis a) f408basis (fun b => f409lowerNat b a) (hp a)

theorem f409_actual_lower_word (a : Fin 18) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f409basis a)) =
      ∑ b : Fin 15, (b409lower b a : ℂ) • scaledWord factorialRootNat (f408basis b) :=
  natFour_lower_action_of_rational_check (f409basis a) f408basis
    (fun b => b409lower b a) (f409_rational_lower_check a)

theorem f409_actual_lower_block (v : Fin 18 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f409basis v) =
      natFourWordBlock f408basis (complexify b409lower *ᵥ v) :=
  natFourWordBlock_rect_action f409basis f408basis canonicalCOMLowerNat
    (complexify b409lower) f409_actual_lower_word v

theorem f409_actual_relative_kernel (v : Fin 18 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f409basis v)=0 ↔
      ∃ x : Fin 3 → ℂ, complexify b409relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f409basis f408basis
    f408_occupation_injective
    b409lower b409relative b409free b409split
    b409_relative_annihilated b409_relative_complete f409_actual_lower_block v

theorem f409_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 9) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 3 → ℂ, natFourWordBlock f409basis (complexify b409relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 9 f409basis f408basis
    f409_basis_enumeration f409_occupation_injective
    f408_occupation_injective
    b409lower b409relative b409free b409split
    b409_relative_annihilated b409_relative_complete f409_actual_lower_block f hN hd

#print axioms f409_rational_lower_check
#print axioms f409_actual_lower_word
#print axioms f409_actual_lower_block
#print axioms f409_actual_relative_kernel
#print axioms f409_actual_relative_complete
end TorusLean.BosonFiniteCertificate
