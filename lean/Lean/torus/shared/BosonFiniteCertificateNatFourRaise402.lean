import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis402
import torus.shared.BosonFiniteCertificateNatFourBasis403
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 2 to degree 3.
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

def f402raise : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1, 0;
    3, 2;
    0, 2]

def f402raiseNat : Matrix (Fin 3) (Fin 2) ℕ :=
  !![1, 0;
    3, 2;
    0, 2]

theorem f402_rational_raise_check : ∀ a : Fin 2,
    natFourRationalRaiseWord (f402basis a) =
      ∑ b : Fin 3, f402raise b a • (wordPolynomial (f403basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f402raiseNat b a : ℚ)=f402raise b a :=
    natFourRationalEntryCheck_sound (fun b a => (f402raiseNat b a : ℚ))
      f402raise (by decide +kernel)
  have hp : ∀ a : Fin 2, (natFourExpandedWords ((raisedWordsNat (f402basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f402raiseNat b a,f403basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f402basis a) f403basis (fun b => f402raiseNat b a) (hp a)

theorem f402_actual_raise_word (a : Fin 2) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f402basis a)) =
      ∑ b : Fin 3, (f402raise b a : ℂ) • scaledWord factorialRootNat (f403basis b) :=
  natFour_raise_action_of_rational_check (f402basis a) f403basis
    (fun b => f402raise b a) (f402_rational_raise_check a)

theorem f402_actual_raise_block (v : Fin 2 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f402basis v) =
      natFourWordBlock f403basis (complexify f402raise *ᵥ v) :=
  natFourWordBlock_rect_action f402basis f403basis canonicalCOMRaiseNat
    (complexify f402raise) f402_actual_raise_word v

#print axioms f402_rational_raise_check
#print axioms f402_actual_raise_word
#print axioms f402_actual_raise_block
end TorusLean.BosonFiniteCertificate
