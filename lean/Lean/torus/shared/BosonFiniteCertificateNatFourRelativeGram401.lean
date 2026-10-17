import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis401
import torus.shared.BosonFiniteCertificate401

/-! Degree-1 actual relative-family factorial Gram and its two-sided inverse.
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

def f401wordMetric : Fin 1 → ℕ := ![6]

def f401relativeGram : Matrix (Fin 0) (Fin 0) ℚ :=
  fun i => Fin.elim0 i

def f401relativeGramInverse : Matrix (Fin 0) (Fin 0) ℚ :=
  fun i => Fin.elim0 i

def f401relativeFamily : Fin 0 → Core ℕ ℂ :=
  natFourColumnFamily f401basis b401relative

theorem f401_word_metric_check : ∀ a,
    natFourWordMetric (f401basis a)=f401wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f401basis a)=f401wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f401GramIntegerCoordinates : Matrix (Fin 1) (Fin 0) ℤ :=
  fun _ i => Fin.elim0 i

private def f401GramIntegerForm : Matrix (Fin 0) (Fin 0) ℤ :=
  fun i => Fin.elim0 i

theorem f401_relative_gram_check :
    b401relativeᵀ*natFourWordGram f401basis*b401relative=f401relativeGram := by
  have hG : natFourWordGram f401basis=Matrix.diagonal (fun a => (f401wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f401_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 1 f401GramIntegerCoordinates=b401relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 1, f401GramIntegerCoordinates a i*(f401wordMetric a : ℤ)*
      f401GramIntegerCoordinates a j)=f401GramIntegerForm i j := by
    intro i j
    exact Fin.elim0 i
  have hF : natFourIntegerMatrix (1*1) f401GramIntegerForm=f401relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 1 f401wordMetric
    f401GramIntegerCoordinates f401GramIntegerForm b401relative f401relativeGram hU hY hF

theorem f401_actual_relative_gram :
    natFamilyGram f401relativeFamily=complexify f401relativeGram := by
  rw [f401relativeFamily,natFourColumnFamily_gram f401basis f401_occupation_injective,
    f401_relative_gram_check]

theorem f401_relative_gram_inverse_right :
    f401relativeGram*f401relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f401_relative_gram_inverse_left :
    f401relativeGramInverse*f401relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f401_relative_gram_inverse_symmetric :
    f401relativeGramInverseᵀ=f401relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f401_word_metric_check
#print axioms f401_relative_gram_check
#print axioms f401_actual_relative_gram
#print axioms f401_relative_gram_inverse_right
#print axioms f401_relative_gram_inverse_left
#print axioms f401_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
