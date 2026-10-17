import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis406
import torus.shared.BosonFiniteCertificate406

/-! Degree-6 actual relative-family factorial Gram and its two-sided inverse.
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

def f406wordMetric : Fin 9 → ℕ := ![4320, 240, 96, 144, 48, 12, 48, 36, 16]

def f406relativeGram : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(2448/5), (-1008/5), (-768/5);
    (-1008/5), (1488/5), (1088/5);
    (-768/5), (1088/5), (4544/15)]

def f406relativeGramInverse : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(209/73728), (15/8192), (1/8192);
    (15/8192), (203/24576), (-41/8192);
    (1/8192), (-41/8192), (57/8192)]

def f406relativeFamily : Fin 3 → Core ℕ ℂ :=
  natFourColumnFamily f406basis b406relative

theorem f406_word_metric_check : ∀ a,
    natFourWordMetric (f406basis a)=f406wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f406basis a)=f406wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f406GramIntegerCoordinates : Matrix (Fin 9) (Fin 3) ℤ :=
  !![-3, 3, 3;
    18, -18, -18;
    -45, 15, 5;
    30, 0, 0;
    0, 30, 40;
    0, -60, -20;
    0, 30, 0;
    0, 0, -40;
    0, 0, 30]

private def f406GramIntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![440640, -181440, -138240;
    -181440, 267840, 195840;
    -138240, 195840, 272640]

theorem f406_relative_gram_check :
    b406relativeᵀ*natFourWordGram f406basis*b406relative=f406relativeGram := by
  have hG : natFourWordGram f406basis=Matrix.diagonal (fun a => (f406wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f406_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 30 f406GramIntegerCoordinates=b406relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 9, f406GramIntegerCoordinates a i*(f406wordMetric a : ℤ)*
      f406GramIntegerCoordinates a j)=f406GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => ∑ a : Fin 9, f406GramIntegerCoordinates a 0*
          (f406wordMetric a : ℤ)*f406GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 3) => f406GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => ∑ a : Fin 9, f406GramIntegerCoordinates a 1*
          (f406wordMetric a : ℤ)*f406GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 3) => f406GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => ∑ a : Fin 9, f406GramIntegerCoordinates a 2*
          (f406wordMetric a : ℤ)*f406GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 3) => f406GramIntegerForm 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (30*30) f406GramIntegerForm=f406relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 30 f406wordMetric
    f406GramIntegerCoordinates f406GramIntegerForm b406relative f406relativeGram hU hY hF

theorem f406_actual_relative_gram :
    natFamilyGram f406relativeFamily=complexify f406relativeGram := by
  rw [f406relativeFamily,natFourColumnFamily_gram f406basis f406_occupation_injective,
    f406_relative_gram_check]

theorem f406_relative_gram_inverse_right :
    f406relativeGram*f406relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f406_relative_gram_inverse_left :
    f406relativeGramInverse*f406relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f406_relative_gram_inverse_symmetric :
    f406relativeGramInverseᵀ=f406relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f406_word_metric_check
#print axioms f406_relative_gram_check
#print axioms f406_actual_relative_gram
#print axioms f406_relative_gram_inverse_right
#print axioms f406_relative_gram_inverse_left
#print axioms f406_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
