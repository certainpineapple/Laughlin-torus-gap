import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis407
import torus.shared.BosonFiniteCertificateNatFourBasis408
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 7 to degree 8.
The target rectangular matrix is checked on the actual rational word action
before the invertible factorial substitution transports it to the source. -/
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

def f407raise : Matrix (Fin 15) (Fin 11) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 1, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 3;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def f407raiseNat : Matrix (Fin 15) (Fin 11) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 2, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 1, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 3;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

theorem f407_rational_raise_check : ∀ a : Fin 11,
    natFourRationalRaiseWord (f407basis a) =
      ∑ b : Fin 15, f407raise b a • (wordPolynomial (f408basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f407raiseNat b a : ℚ)=f407raise b a :=
    natFourRationalEntryCheck_sound (fun b a => (f407raiseNat b a : ℚ))
      f407raise (by decide +kernel)
  have hp : ∀ a : Fin 11, (natFourExpandedWords ((raisedWordsNat (f407basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f407raiseNat b a,f408basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f407basis a) f408basis (fun b => f407raiseNat b a) (hp a)

theorem f407_actual_raise_word (a : Fin 11) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f407basis a)) =
      ∑ b : Fin 15, (f407raise b a : ℂ) • scaledWord factorialRootNat (f408basis b) :=
  natFour_raise_action_of_rational_check (f407basis a) f408basis
    (fun b => f407raise b a) (f407_rational_raise_check a)

theorem f407_actual_raise_block (v : Fin 11 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f407basis v) =
      natFourWordBlock f408basis (complexify f407raise *ᵥ v) :=
  natFourWordBlock_rect_action f407basis f408basis canonicalCOMRaiseNat
    (complexify f407raise) f407_actual_raise_word v

#print axioms f407_rational_raise_check
#print axioms f407_actual_raise_word
#print axioms f407_actual_raise_block
end TorusLean.BosonFiniteCertificate
