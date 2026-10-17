import torus.shared.BosonFiniteCertificateNatFourRaise415Cast0
import torus.shared.BosonFiniteCertificateNatFourRaise415Cast1
import torus.shared.BosonFiniteCertificateNatFourRaise415Cast2
import torus.shared.BosonFiniteCertificateNatFourRaise415Cast3

/-! True Nat COM raising from degree 15 to degree 16.
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

private theorem f415_raise_nat_cast : ∀ b a, (f415raiseNat b a : ℚ)=f415raise b a := by
  intro b a
  by_cases h0 : b.val < 16
  · simpa only [Nat.add_zero] using f415_raise_nat_cast_chunk0 ⟨b.val,h0⟩ a
  · by_cases h1 : b.val < 32
    · have h : b.val - 16 < 16 := by omega
      simpa only [Nat.sub_add_cancel (show 16 ≤ b.val by omega)] using
        f415_raise_nat_cast_chunk1 ⟨b.val-16,h⟩ a
    · by_cases h2 : b.val < 48
      · have h : b.val - 32 < 16 := by omega
        simpa only [Nat.sub_add_cancel (show 32 ≤ b.val by omega)] using
          f415_raise_nat_cast_chunk2 ⟨b.val-32,h⟩ a
      · have h : b.val - 48 < 16 := by omega
        simpa only [Nat.sub_add_cancel (show 48 ≤ b.val by omega)] using
          f415_raise_nat_cast_chunk3 ⟨b.val-48,h⟩ a

#print axioms f415_raise_nat_cast

theorem f415_rational_raise_check : ∀ a : Fin 54,
    natFourRationalRaiseWord (f415basis a) =
      ∑ b : Fin 64, f415raise b a • (wordPolynomial (f416basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f415raiseNat b a : ℚ)=f415raise b a :=
    f415_raise_nat_cast
  have hp : ∀ a : Fin 54, (natFourExpandedWords ((raisedWordsNat (f415basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f415raiseNat b a,f416basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f415basis a) f416basis (fun b => f415raiseNat b a) (hp a)

theorem f415_actual_raise_word (a : Fin 54) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f415basis a)) =
      ∑ b : Fin 64, (f415raise b a : ℂ) • scaledWord factorialRootNat (f416basis b) :=
  natFour_raise_action_of_rational_check (f415basis a) f416basis
    (fun b => f415raise b a) (f415_rational_raise_check a)

theorem f415_actual_raise_block (v : Fin 54 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f415basis v) =
      natFourWordBlock f416basis (complexify f415raise *ᵥ v) :=
  natFourWordBlock_rect_action f415basis f416basis canonicalCOMRaiseNat
    (complexify f415raise) f415_actual_raise_word v

#print axioms f415_rational_raise_check
#print axioms f415_actual_raise_word
#print axioms f415_actual_raise_block
end TorusLean.BosonFiniteCertificate
