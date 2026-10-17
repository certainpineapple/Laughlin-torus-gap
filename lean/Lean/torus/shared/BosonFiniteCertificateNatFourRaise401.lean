import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis401
import torus.shared.BosonFiniteCertificateNatFourBasis402
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 1 to degree 2.
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

def f401raise : Matrix (Fin 2) (Fin 1) ℚ :=
  !![1;
    3]

def f401raiseNat : Matrix (Fin 2) (Fin 1) ℕ :=
  !![1;
    3]

theorem f401_rational_raise_check : ∀ a : Fin 1,
    natFourRationalRaiseWord (f401basis a) =
      ∑ b : Fin 2, f401raise b a • (wordPolynomial (f402basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f401raiseNat b a : ℚ)=f401raise b a :=
    natFourRationalEntryCheck_sound (fun b a => (f401raiseNat b a : ℚ))
      f401raise (by decide +kernel)
  have hp : ∀ a : Fin 1, (natFourExpandedWords ((raisedWordsNat (f401basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f401raiseNat b a,f402basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f401basis a) f402basis (fun b => f401raiseNat b a) (hp a)

theorem f401_actual_raise_word (a : Fin 1) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f401basis a)) =
      ∑ b : Fin 2, (f401raise b a : ℂ) • scaledWord factorialRootNat (f402basis b) :=
  natFour_raise_action_of_rational_check (f401basis a) f402basis
    (fun b => f401raise b a) (f401_rational_raise_check a)

theorem f401_actual_raise_block (v : Fin 1 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f401basis v) =
      natFourWordBlock f402basis (complexify f401raise *ᵥ v) :=
  natFourWordBlock_rect_action f401basis f402basis canonicalCOMRaiseNat
    (complexify f401raise) f401_actual_raise_word v

#print axioms f401_rational_raise_check
#print axioms f401_actual_raise_word
#print axioms f401_actual_raise_block
end TorusLean.BosonFiniteCertificate
