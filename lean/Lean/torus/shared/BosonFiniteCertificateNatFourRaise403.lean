import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis403
import torus.shared.BosonFiniteCertificateNatFourBasis404
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 3 to degree 4.
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

def f403raise : Matrix (Fin 5) (Fin 3) ℚ :=
  !![1, 0, 0;
    3, 1, 0;
    0, 1, 0;
    0, 2, 3;
    0, 0, 1]

def f403raiseNat : Matrix (Fin 5) (Fin 3) ℕ :=
  !![1, 0, 0;
    3, 1, 0;
    0, 1, 0;
    0, 2, 3;
    0, 0, 1]

theorem f403_rational_raise_check : ∀ a : Fin 3,
    natFourRationalRaiseWord (f403basis a) =
      ∑ b : Fin 5, f403raise b a • (wordPolynomial (f404basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f403raiseNat b a : ℚ)=f403raise b a :=
    natFourRationalEntryCheck_sound (fun b a => (f403raiseNat b a : ℚ))
      f403raise (by decide +kernel)
  have hp : ∀ a : Fin 3, (natFourExpandedWords ((raisedWordsNat (f403basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f403raiseNat b a,f404basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f403basis a) f404basis (fun b => f403raiseNat b a) (hp a)

theorem f403_actual_raise_word (a : Fin 3) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f403basis a)) =
      ∑ b : Fin 5, (f403raise b a : ℂ) • scaledWord factorialRootNat (f404basis b) :=
  natFour_raise_action_of_rational_check (f403basis a) f404basis
    (fun b => f403raise b a) (f403_rational_raise_check a)

theorem f403_actual_raise_block (v : Fin 3 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f403basis v) =
      natFourWordBlock f404basis (complexify f403raise *ᵥ v) :=
  natFourWordBlock_rect_action f403basis f404basis canonicalCOMRaiseNat
    (complexify f403raise) f403_actual_raise_word v

#print axioms f403_rational_raise_check
#print axioms f403_actual_raise_word
#print axioms f403_actual_raise_block
end TorusLean.BosonFiniteCertificate
