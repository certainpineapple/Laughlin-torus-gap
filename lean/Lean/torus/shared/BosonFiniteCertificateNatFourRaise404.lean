import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis404
import torus.shared.BosonFiniteCertificateNatFourBasis405
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 4 to degree 5.
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

def f404raise : Matrix (Fin 6) (Fin 5) ℚ :=
  !![1, 0, 0, 0, 0;
    3, 1, 0, 0, 0;
    0, 1, 2, 0, 0;
    0, 2, 0, 1, 0;
    0, 0, 2, 2, 0;
    0, 0, 0, 1, 4]

def f404raiseNat : Matrix (Fin 6) (Fin 5) ℕ :=
  !![1, 0, 0, 0, 0;
    3, 1, 0, 0, 0;
    0, 1, 2, 0, 0;
    0, 2, 0, 1, 0;
    0, 0, 2, 2, 0;
    0, 0, 0, 1, 4]

theorem f404_rational_raise_check : ∀ a : Fin 5,
    natFourRationalRaiseWord (f404basis a) =
      ∑ b : Fin 6, f404raise b a • (wordPolynomial (f405basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f404raiseNat b a : ℚ)=f404raise b a :=
    natFourRationalEntryCheck_sound (fun b a => (f404raiseNat b a : ℚ))
      f404raise (by decide +kernel)
  have hp : ∀ a : Fin 5, (natFourExpandedWords ((raisedWordsNat (f404basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f404raiseNat b a,f405basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f404basis a) f405basis (fun b => f404raiseNat b a) (hp a)

theorem f404_actual_raise_word (a : Fin 5) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f404basis a)) =
      ∑ b : Fin 6, (f404raise b a : ℂ) • scaledWord factorialRootNat (f405basis b) :=
  natFour_raise_action_of_rational_check (f404basis a) f405basis
    (fun b => f404raise b a) (f404_rational_raise_check a)

theorem f404_actual_raise_block (v : Fin 5 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f404basis v) =
      natFourWordBlock f405basis (complexify f404raise *ᵥ v) :=
  natFourWordBlock_rect_action f404basis f405basis canonicalCOMRaiseNat
    (complexify f404raise) f404_actual_raise_word v

#print axioms f404_rational_raise_check
#print axioms f404_actual_raise_word
#print axioms f404_actual_raise_block
end TorusLean.BosonFiniteCertificate
