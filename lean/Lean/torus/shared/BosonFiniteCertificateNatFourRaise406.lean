import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis406
import torus.shared.BosonFiniteCertificateNatFourBasis407
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 6 to degree 7.
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

def f406raise : Matrix (Fin 11) (Fin 9) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 2, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 2, 0, 2, 1, 0, 0, 0;
    0, 0, 0, 2, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 3, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 3, 2;
    0, 0, 0, 0, 0, 0, 1, 0, 2]

def f406raiseNat : Matrix (Fin 11) (Fin 9) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 2, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 2, 0, 2, 1, 0, 0, 0;
    0, 0, 0, 2, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 3, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 3, 2;
    0, 0, 0, 0, 0, 0, 1, 0, 2]

theorem f406_rational_raise_check : ∀ a : Fin 9,
    natFourRationalRaiseWord (f406basis a) =
      ∑ b : Fin 11, f406raise b a • (wordPolynomial (f407basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f406raiseNat b a : ℚ)=f406raise b a :=
    natFourRationalEntryCheck_sound (fun b a => (f406raiseNat b a : ℚ))
      f406raise (by decide +kernel)
  have hp : ∀ a : Fin 9, (natFourExpandedWords ((raisedWordsNat (f406basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f406raiseNat b a,f407basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f406basis a) f407basis (fun b => f406raiseNat b a) (hp a)

theorem f406_actual_raise_word (a : Fin 9) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f406basis a)) =
      ∑ b : Fin 11, (f406raise b a : ℂ) • scaledWord factorialRootNat (f407basis b) :=
  natFour_raise_action_of_rational_check (f406basis a) f407basis
    (fun b => f406raise b a) (f406_rational_raise_check a)

theorem f406_actual_raise_block (v : Fin 9 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f406basis v) =
      natFourWordBlock f407basis (complexify f406raise *ᵥ v) :=
  natFourWordBlock_rect_action f406basis f407basis canonicalCOMRaiseNat
    (complexify f406raise) f406_actual_raise_word v

#print axioms f406_rational_raise_check
#print axioms f406_actual_raise_word
#print axioms f406_actual_raise_block
end TorusLean.BosonFiniteCertificate
