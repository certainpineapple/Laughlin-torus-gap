import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis400
import torus.shared.BosonFiniteCertificate400

/-! Degree-0 actual relative-family factorial Gram and its two-sided inverse.
The metric is checked on the independently defined Nat occupation words;
F is checked as Uᵀ G U. J is used on both sides of every rank coefficient. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

def f400wordMetric : Fin 1 → ℕ := ![24]

def f400relativeGram : Matrix (Fin 1) (Fin 1) ℚ :=
  !![24]

def f400relativeGramInverse : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/24)]

def f400relativeFamily : Fin 1 → Core ℕ ℂ :=
  natFourColumnFamily f400basis b400relative

theorem f400_word_metric_check : ∀ a,
    natFourWordMetric (f400basis a)=f400wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f400basis a)=f400wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

theorem f400_relative_gram_check :
    b400relativeᵀ*natFourWordGram f400basis*b400relative=f400relativeGram := by
  have hG : natFourWordGram f400basis=Matrix.diagonal (fun a => (f400wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f400_word_metric_check]
  rw [hG]
  ext i j
  rw [natFour_diagonal_compression_entry]
  have h : ∀ i j : Fin 1, (∑ a : Fin 1, b400relative a i*(f400wordMetric a : ℚ)*b400relative a j)=
      f400relativeGram i j := by
    intro i
    fin_cases i <;> intro j <;> fin_cases j <;> decide +kernel
  exact h i j

theorem f400_actual_relative_gram :
    natFamilyGram f400relativeFamily=complexify f400relativeGram := by
  rw [f400relativeFamily,natFourColumnFamily_gram f400basis f400_occupation_injective,
    f400_relative_gram_check]

theorem f400_relative_gram_inverse_right :
    f400relativeGram*f400relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f400_relative_gram_inverse_left :
    f400relativeGramInverse*f400relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f400_relative_gram_inverse_symmetric :
    f400relativeGramInverseᵀ=f400relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f400_word_metric_check
#print axioms f400_relative_gram_check
#print axioms f400_actual_relative_gram
#print axioms f400_relative_gram_inverse_right
#print axioms f400_relative_gram_inverse_left
#print axioms f400_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
