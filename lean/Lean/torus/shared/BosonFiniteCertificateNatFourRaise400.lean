import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis400
import torus.shared.BosonFiniteCertificateNatFourBasis401
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 0 to degree 1.
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

def f400raise : Matrix (Fin 1) (Fin 1) ℚ :=
  !![4]

def f400raiseNat : Matrix (Fin 1) (Fin 1) ℕ :=
  !![4]

theorem f400_rational_raise_check : ∀ a : Fin 1,
    natFourRationalRaiseWord (f400basis a) =
      ∑ b : Fin 1, f400raise b a • (wordPolynomial (f401basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f400raiseNat b a : ℚ)=f400raise b a :=
    natFourRationalEntryCheck_sound (fun b a => (f400raiseNat b a : ℚ))
      f400raise (by decide +kernel)
  have hp : ∀ a : Fin 1, (natFourExpandedWords ((raisedWordsNat (f400basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f400raiseNat b a,f401basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f400basis a) f401basis (fun b => f400raiseNat b a) (hp a)

theorem f400_actual_raise_word (a : Fin 1) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f400basis a)) =
      ∑ b : Fin 1, (f400raise b a : ℂ) • scaledWord factorialRootNat (f401basis b) :=
  natFour_raise_action_of_rational_check (f400basis a) f401basis
    (fun b => f400raise b a) (f400_rational_raise_check a)

theorem f400_actual_raise_block (v : Fin 1 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f400basis v) =
      natFourWordBlock f401basis (complexify f400raise *ᵥ v) :=
  natFourWordBlock_rect_action f400basis f401basis canonicalCOMRaiseNat
    (complexify f400raise) f400_actual_raise_word v

#print axioms f400_rational_raise_check
#print axioms f400_actual_raise_word
#print axioms f400_actual_raise_block
end TorusLean.BosonFiniteCertificate
