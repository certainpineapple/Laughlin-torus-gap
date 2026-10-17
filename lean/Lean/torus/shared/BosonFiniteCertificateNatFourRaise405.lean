import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis405
import torus.shared.BosonFiniteCertificateNatFourBasis406
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 5 to degree 6.
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

def f405raise : Matrix (Fin 9) (Fin 6) ℚ :=
  !![1, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 2, 0, 1, 0, 0;
    0, 0, 2, 2, 2, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 1, 3]

def f405raiseNat : Matrix (Fin 9) (Fin 6) ℕ :=
  !![1, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 2, 0, 1, 0, 0;
    0, 0, 2, 2, 2, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 1, 3]

theorem f405_rational_raise_check : ∀ a : Fin 6,
    natFourRationalRaiseWord (f405basis a) =
      ∑ b : Fin 9, f405raise b a • (wordPolynomial (f406basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f405raiseNat b a : ℚ)=f405raise b a :=
    natFourRationalEntryCheck_sound (fun b a => (f405raiseNat b a : ℚ))
      f405raise (by decide +kernel)
  have hp : ∀ a : Fin 6, (natFourExpandedWords ((raisedWordsNat (f405basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f405raiseNat b a,f406basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f405basis a) f406basis (fun b => f405raiseNat b a) (hp a)

theorem f405_actual_raise_word (a : Fin 6) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f405basis a)) =
      ∑ b : Fin 9, (f405raise b a : ℂ) • scaledWord factorialRootNat (f406basis b) :=
  natFour_raise_action_of_rational_check (f405basis a) f406basis
    (fun b => f405raise b a) (f405_rational_raise_check a)

theorem f405_actual_raise_block (v : Fin 6 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f405basis v) =
      natFourWordBlock f406basis (complexify f405raise *ᵥ v) :=
  natFourWordBlock_rect_action f405basis f406basis canonicalCOMRaiseNat
    (complexify f405raise) f405_actual_raise_word v

#print axioms f405_rational_raise_check
#print axioms f405_actual_raise_word
#print axioms f405_actual_raise_block
end TorusLean.BosonFiniteCertificate
