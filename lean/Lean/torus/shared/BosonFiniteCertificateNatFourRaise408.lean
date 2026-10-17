import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis408
import torus.shared.BosonFiniteCertificateNatFourBasis409
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 8 to degree 9.
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

def f408raise : Matrix (Fin 18) (Fin 15) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4]

def f408raiseNat : Matrix (Fin 18) (Fin 15) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4]

theorem f408_rational_raise_check : ∀ a : Fin 15,
    natFourRationalRaiseWord (f408basis a) =
      ∑ b : Fin 18, f408raise b a • (wordPolynomial (f409basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f408raiseNat b a : ℚ)=f408raise b a :=
    natFourRationalEntryCheck_sound (fun b a => (f408raiseNat b a : ℚ))
      f408raise (by decide +kernel)
  have hp : ∀ a : Fin 15, (natFourExpandedWords ((raisedWordsNat (f408basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f408raiseNat b a,f409basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f408basis a) f409basis (fun b => f408raiseNat b a) (hp a)

theorem f408_actual_raise_word (a : Fin 15) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f408basis a)) =
      ∑ b : Fin 18, (f408raise b a : ℂ) • scaledWord factorialRootNat (f409basis b) :=
  natFour_raise_action_of_rational_check (f408basis a) f409basis
    (fun b => f408raise b a) (f408_rational_raise_check a)

theorem f408_actual_raise_block (v : Fin 15 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f408basis v) =
      natFourWordBlock f409basis (complexify f408raise *ᵥ v) :=
  natFourWordBlock_rect_action f408basis f409basis canonicalCOMRaiseNat
    (complexify f408raise) f408_actual_raise_word v

#print axioms f408_rational_raise_check
#print axioms f408_actual_raise_word
#print axioms f408_actual_raise_block
end TorusLean.BosonFiniteCertificate
