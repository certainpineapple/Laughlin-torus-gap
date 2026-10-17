import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis408
import torus.shared.BosonFiniteCertificate408
import torus.shared.BosonFiniteCertificateNatFourBasis407

/-! Degree-8 actual Nat COM lowering and complete relative kernel.
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

def f408lowerNat : Matrix (Fin 11) (Fin 15) ℕ :=
  !![8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 7, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 6, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 5, 8, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 3, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 5, 3, 4, 0, 0, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 4, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 8]

theorem f408_rational_lower_check : ∀ a : Fin 15,
    natFourRationalLowerWord (f408basis a) =
      ∑ b : Fin 11, b408lower b a • (wordPolynomial (f407basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f408lowerNat b a : ℚ)=b408lower b a :=
    natFourRationalEntryCheck_sound (fun b a => (f408lowerNat b a : ℚ))
      b408lower (by decide +kernel)
  have hp : ∀ a : Fin 15, (natFourExpandedWords (natFourLoweredWords (f408basis a))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f408lowerNat b a,f407basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_lower_rational_of_expanded_perm
    (f408basis a) f407basis (fun b => f408lowerNat b a) (hp a)

theorem f408_actual_lower_word (a : Fin 15) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f408basis a)) =
      ∑ b : Fin 11, (b408lower b a : ℂ) • scaledWord factorialRootNat (f407basis b) :=
  natFour_lower_action_of_rational_check (f408basis a) f407basis
    (fun b => b408lower b a) (f408_rational_lower_check a)

theorem f408_actual_lower_block (v : Fin 15 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f408basis v) =
      natFourWordBlock f407basis (complexify b408lower *ᵥ v) :=
  natFourWordBlock_rect_action f408basis f407basis canonicalCOMLowerNat
    (complexify b408lower) f408_actual_lower_word v

theorem f408_actual_relative_kernel (v : Fin 15 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f408basis v)=0 ↔
      ∃ x : Fin 4 → ℂ, complexify b408relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f408basis f407basis
    f407_occupation_injective
    b408lower b408relative b408free b408split
    b408_relative_annihilated b408_relative_complete f408_actual_lower_block v

theorem f408_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 8) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 4 → ℂ, natFourWordBlock f408basis (complexify b408relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 8 f408basis f407basis
    f408_basis_enumeration f408_occupation_injective
    f407_occupation_injective
    b408lower b408relative b408free b408split
    b408_relative_annihilated b408_relative_complete f408_actual_lower_block f hN hd

#print axioms f408_rational_lower_check
#print axioms f408_actual_lower_word
#print axioms f408_actual_lower_block
#print axioms f408_actual_relative_kernel
#print axioms f408_actual_relative_complete
end TorusLean.BosonFiniteCertificate
