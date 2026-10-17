import torus.shared.BosonFiniteCertificateNatFourIntegerMatrix
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourHWordsSparse
import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import torus.shared.BosonFiniteCertificateNatFourBasis407
import torus.shared.BosonFiniteCertificate407

/-! Independently checked genuine H/S4 source word forms and their original
relative compressions. Repeated-particle factorials and pair halves are part
of the source evaluator, not assumptions on these numerical tables. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f407rawHForm : Matrix (Fin 11) (Fin 11) ℚ :=
  !![(184275/2), (945/2), (945/2), (945/2), 0, 0, 0, 0, 0, 0, 0;
    (945/2), (9135/2), (315/2), (315/2), 90, 45, 45, 0, 0, 0, 0;
    (945/2), (315/2), (2355/2), (315/2), 240, 30, 0, 60, 0, 0, 0;
    (945/2), (315/2), (315/2), (1323/2), 0, 72, 72, 36, 0, 0, 0;
    0, 90, 240, 0, 705, 45, 45, 0, 45, 15, 0;
    0, 45, 30, 72, 45, (303/2), (45/2), 30, 72, 12, 18;
    0, 45, 0, 72, 45, (45/2), (405/2), 36, 0, 36, 0;
    0, 0, 60, 36, 0, 30, 36, 138, 0, 24, 36;
    0, 0, 0, 0, 45, 72, 0, 0, 351, 45, 0;
    0, 0, 0, 0, 15, 12, 36, 24, 45, 87, 36;
    0, 0, 0, 0, 0, 18, 0, 36, 0, 36, 162]

def f407rawS4Form : Matrix (Fin 11) (Fin 11) ℚ :=
  !![2835, 945, 945, 945, 0, 0, 0, 0, 0, 0, 0;
    945, 495, 315, 315, 180, 90, 90, 0, 0, 0, 0;
    945, 315, 375, 315, 30, 30, 0, 60, 90, 30, 0;
    945, 315, 315, 351, 0, 18, 36, 18, 0, 36, 54;
    0, 180, 30, 0, 195, 105, 90, 30, 45, 15, 0;
    0, 90, 30, 18, 105, 69, 63, 39, 45, 33, 27;
    0, 90, 0, 36, 90, 63, 81, 18, 0, 36, 54;
    0, 0, 60, 18, 30, 39, 18, 69, 90, 48, 27;
    0, 0, 90, 0, 45, 45, 0, 90, 135, 45, 0;
    0, 0, 30, 36, 15, 33, 36, 48, 45, 51, 54;
    0, 0, 0, 54, 0, 27, 54, 27, 0, 54, 81]

private theorem f407hs_shape (a : Fin 11) :
    (f407basis a).length=4 ∧ (f407basis a).sum=7 := by
  apply natFourBasis_shape 7
  rw [← f407_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

private theorem f407_H_source_row_0 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 0) (f407basis b)=f407rawHForm 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 0) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 0 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_1 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 1) (f407basis b)=f407rawHForm 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 1) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 1 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_2 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 2) (f407basis b)=f407rawHForm 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 2) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 2 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_3 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 3) (f407basis b)=f407rawHForm 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 3) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 3 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_4 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 4) (f407basis b)=f407rawHForm 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 4) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 4 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_5 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 5) (f407basis b)=f407rawHForm 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 5) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 5 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_6 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 6) (f407basis b)=f407rawHForm 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 6) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 6 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_7 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 7) (f407basis b)=f407rawHForm 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 7) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 7 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_8 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 8) (f407basis b)=f407rawHForm 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 8) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 8 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_9 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 9) (f407basis b)=f407rawHForm 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 9) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 9 b) (by decide +kernel)
  exact h 0

private theorem f407_H_source_row_10 : ∀ b : Fin 11,
    natFourHWordFormSparse 7 (f407basis 10) (f407basis b)=f407rawHForm 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) => natFourHWordFormSparse 7 (f407basis 10) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawHForm 10 b) (by decide +kernel)
  exact h 0

theorem f407_raw_H_matrix_check : ∀ a b : Fin 11,
    natFourHWordForm 7 (f407basis a) (f407basis b)=f407rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f407_H_source_row_0 b
  · exact f407_H_source_row_1 b
  · exact f407_H_source_row_2 b
  · exact f407_H_source_row_3 b
  · exact f407_H_source_row_4 b
  · exact f407_H_source_row_5 b
  · exact f407_H_source_row_6 b
  · exact f407_H_source_row_7 b
  · exact f407_H_source_row_8 b
  · exact f407_H_source_row_9 b
  · exact f407_H_source_row_10 b


theorem f407_actual_raw_H_matrix (x y : Fin 11 → ℂ) :
    natOccupationInner (natFourWordBlock f407basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f407basis y))=
      star x ⬝ᵥ (complexify f407rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 7 f407basis (fun a => (f407hs_shape a).2)
    f407rawHForm f407_raw_H_matrix_check x y

private def f407HCompressionInteger : Matrix (Fin 11) (Fin 11) ℤ :=
  !![184275, 945, 945, 945, 0, 0, 0, 0, 0, 0, 0;
    945, 9135, 315, 315, 180, 90, 90, 0, 0, 0, 0;
    945, 315, 2355, 315, 480, 60, 0, 120, 0, 0, 0;
    945, 315, 315, 1323, 0, 144, 144, 72, 0, 0, 0;
    0, 180, 480, 0, 1410, 90, 90, 0, 90, 30, 0;
    0, 90, 60, 144, 90, 303, 45, 60, 144, 24, 36;
    0, 90, 0, 144, 90, 45, 405, 72, 0, 72, 0;
    0, 0, 120, 72, 0, 60, 72, 276, 0, 48, 72;
    0, 0, 0, 0, 90, 144, 0, 0, 702, 90, 0;
    0, 0, 0, 0, 30, 24, 72, 48, 90, 174, 72;
    0, 0, 0, 0, 0, 36, 0, 72, 0, 72, 324]

private def f407HCompressionCoordinates : Matrix (Fin 11) (Fin 2) ℤ :=
  !![3, (-4);
    (-21), 28;
    27, (-16);
    (-15), 0;
    36, (-68);
    (-90), 80;
    60, 0;
    0, (-20);
    0, 60;
    0, (-120);
    0, 60]

private def f407HCompressionLeftProduct : Matrix (Fin 2) (Fin 11) ℤ :=
  !![544320, (-181440), 66960, (-19440), 57240, (-23760), 19440, 1080, (-9720), 3240, (-3240);
    (-725760), 241920, (-62880), 10080, (-89520), 26400, (-10080), (-4080), 36720, (-12240), 12240]

private def f407HCompressionResult : Matrix (Fin 2) (Fin 2) ℤ :=
  !![12908160, (-15310080);
    (-15310080), 23370240]

theorem f407_relative_H_compression :
    b407relativeᵀ*f407rawHForm*b407relative=b407h := by
  have hM : natFourIntegerMatrix 2 f407HCompressionInteger=f407rawHForm := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f407HCompressionInteger) (f407rawHForm) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 60 f407HCompressionCoordinates=b407relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407HCompressionCoordinates) (b407relative) (by decide +kernel) a b
  have hV : f407HCompressionCoordinatesᵀ*f407HCompressionInteger=f407HCompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f407HCompressionCoordinatesᵀ*f407HCompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f407HCompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f407HCompressionCoordinatesᵀ*f407HCompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f407HCompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f407HCompressionLeftProduct*f407HCompressionCoordinates=f407HCompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407HCompressionLeftProduct*f407HCompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407HCompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407HCompressionLeftProduct*f407HCompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407HCompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*2*60) f407HCompressionResult=b407h := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*2*60) f407HCompressionResult) (b407h) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 2 60
    f407HCompressionInteger f407HCompressionCoordinates f407HCompressionLeftProduct f407HCompressionResult
    f407rawHForm b407relative b407h hM hD hV hY hF

theorem f407_actual_relative_H_form (x y : Fin 2 → ℂ) :
    natOccupationInner (natFourWordBlock f407basis (complexify b407relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f407basis (complexify b407relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b407h *ᵥ y) :=
  natFour_operator_relative_matrix_form f407basis b407relative canonicalPairHamiltonianNat
    f407rawHForm b407h f407_actual_raw_H_matrix
    f407_relative_H_compression x y

def f407S4Amplitudes : Matrix (Fin 8) (Fin 11) ℚ :=
  !![12, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0;
    0, 8, 0, 0, 8, 4, 4, 0, 0, 0, 0;
    0, 0, 8, 0, 4, 4, 0, 8, 12, 4, 0;
    0, 0, 0, 8, 0, 4, 8, 4, 0, 8, 12;
    0, 0, 0, 8, 0, 4, 8, 4, 0, 8, 12;
    0, 0, 8, 0, 4, 4, 0, 8, 12, 4, 0;
    0, 8, 0, 0, 8, 4, 4, 0, 0, 0, 0;
    12, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0]

private theorem f407_S4_amplitude_row_0 : ∀ a : Fin 11,
    (natFourDoublePairRemoval 0 (7-0) (f407basis a) : ℚ)=f407S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 11) => (natFourDoublePairRemoval 0 (7-0) (f407basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 11) => f407S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f407_S4_amplitude_row_1 : ∀ a : Fin 11,
    (natFourDoublePairRemoval 1 (7-1) (f407basis a) : ℚ)=f407S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 11) => (natFourDoublePairRemoval 1 (7-1) (f407basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 11) => f407S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f407_S4_amplitude_row_2 : ∀ a : Fin 11,
    (natFourDoublePairRemoval 2 (7-2) (f407basis a) : ℚ)=f407S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 11) => (natFourDoublePairRemoval 2 (7-2) (f407basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 11) => f407S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f407_S4_amplitude_row_3 : ∀ a : Fin 11,
    (natFourDoublePairRemoval 3 (7-3) (f407basis a) : ℚ)=f407S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 11) => (natFourDoublePairRemoval 3 (7-3) (f407basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 11) => f407S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f407_S4_amplitude_row_4 : ∀ a : Fin 11,
    (natFourDoublePairRemoval 4 (7-4) (f407basis a) : ℚ)=f407S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 11) => (natFourDoublePairRemoval 4 (7-4) (f407basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 11) => f407S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f407_S4_amplitude_row_5 : ∀ a : Fin 11,
    (natFourDoublePairRemoval 5 (7-5) (f407basis a) : ℚ)=f407S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 11) => (natFourDoublePairRemoval 5 (7-5) (f407basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 11) => f407S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f407_S4_amplitude_row_6 : ∀ a : Fin 11,
    (natFourDoublePairRemoval 6 (7-6) (f407basis a) : ℚ)=f407S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 11) => (natFourDoublePairRemoval 6 (7-6) (f407basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 11) => f407S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f407_S4_amplitude_row_7 : ∀ a : Fin 11,
    (natFourDoublePairRemoval 7 (7-7) (f407basis a) : ℚ)=f407S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 11) => (natFourDoublePairRemoval 7 (7-7) (f407basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 11) => f407S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

theorem f407_S4_amplitudes_check : ∀ p : Fin 8, ∀ a : Fin 11,
    (natFourDoublePairRemoval p.val (7-p.val) (f407basis a) : ℚ)=f407S4Amplitudes p a := by
  intro p
  fin_cases p
  · exact f407_S4_amplitude_row_0
  · exact f407_S4_amplitude_row_1
  · exact f407_S4_amplitude_row_2
  · exact f407_S4_amplitude_row_3
  · exact f407_S4_amplitude_row_4
  · exact f407_S4_amplitude_row_5
  · exact f407_S4_amplitude_row_6
  · exact f407_S4_amplitude_row_7


theorem f407_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 7 f407S4Amplitudes=f407rawS4Form := by
  ext a b
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 0 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 1 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 2 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 3 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 4 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 5 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 6 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 7 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 8 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 9 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 11) => (natFourS4AmplitudeGram 7 f407S4Amplitudes) 10 j)
      (fun (_ : Fin 1) (j : Fin 11) => (f407rawS4Form) 10 j) (by decide +kernel)
    exact h 0 b

theorem f407_actual_raw_S4_matrix (x y : Fin 11 → ℂ) :
    natOccupationInner (natFourWordBlock f407basis x)
      (canonicalNatFourS4 (natFourWordBlock f407basis y))=
      star x ⬝ᵥ (complexify f407rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 7 f407basis
    (fun a => (f407hs_shape a).1) (fun a => (f407hs_shape a).2)
    f407S4Amplitudes f407_S4_amplitudes_check f407rawS4Form f407_S4_amplitude_gram_check x y

private def f407S4CompressionInteger : Matrix (Fin 11) (Fin 11) ℤ :=
  !![2835, 945, 945, 945, 0, 0, 0, 0, 0, 0, 0;
    945, 495, 315, 315, 180, 90, 90, 0, 0, 0, 0;
    945, 315, 375, 315, 30, 30, 0, 60, 90, 30, 0;
    945, 315, 315, 351, 0, 18, 36, 18, 0, 36, 54;
    0, 180, 30, 0, 195, 105, 90, 30, 45, 15, 0;
    0, 90, 30, 18, 105, 69, 63, 39, 45, 33, 27;
    0, 90, 0, 36, 90, 63, 81, 18, 0, 36, 54;
    0, 0, 60, 18, 30, 39, 18, 69, 90, 48, 27;
    0, 0, 90, 0, 45, 45, 0, 90, 135, 45, 0;
    0, 0, 30, 36, 15, 33, 36, 48, 45, 51, 54;
    0, 0, 0, 54, 0, 27, 54, 27, 0, 54, 81]

private def f407S4CompressionCoordinates : Matrix (Fin 11) (Fin 2) ℤ :=
  !![3, (-4);
    (-21), 28;
    27, (-16);
    (-15), 0;
    36, (-68);
    (-90), 80;
    60, 0;
    0, (-20);
    0, 60;
    0, (-120);
    0, 60]

private def f407S4CompressionLeftProduct : Matrix (Fin 2) (Fin 11) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def f407S4CompressionResult : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 0;
    0, 0]

theorem f407_relative_S4_compression :
    b407relativeᵀ*f407rawS4Form*b407relative=b407s := by
  have hM : natFourIntegerMatrix 1 f407S4CompressionInteger=f407rawS4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f407S4CompressionInteger) (f407rawS4Form) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 60 f407S4CompressionCoordinates=b407relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407S4CompressionCoordinates) (b407relative) (by decide +kernel) a b
  have hV : f407S4CompressionCoordinatesᵀ*f407S4CompressionInteger=f407S4CompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f407S4CompressionCoordinatesᵀ*f407S4CompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f407S4CompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f407S4CompressionCoordinatesᵀ*f407S4CompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f407S4CompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f407S4CompressionLeftProduct*f407S4CompressionCoordinates=f407S4CompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407S4CompressionLeftProduct*f407S4CompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407S4CompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407S4CompressionLeftProduct*f407S4CompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407S4CompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1*60) f407S4CompressionResult=b407s := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1*60) f407S4CompressionResult) (b407s) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1 60
    f407S4CompressionInteger f407S4CompressionCoordinates f407S4CompressionLeftProduct f407S4CompressionResult
    f407rawS4Form b407relative b407s hM hD hV hY hF

theorem f407_actual_relative_S4_form (x y : Fin 2 → ℂ) :
    natOccupationInner (natFourWordBlock f407basis (complexify b407relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f407basis (complexify b407relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b407s *ᵥ y) :=
  natFour_operator_relative_matrix_form f407basis b407relative canonicalNatFourS4
    f407rawS4Form b407s f407_actual_raw_S4_matrix
    f407_relative_S4_compression x y

#print axioms f407_raw_H_matrix_check
#print axioms f407_actual_raw_H_matrix
#print axioms f407_relative_H_compression
#print axioms f407_actual_relative_H_form
#print axioms f407_S4_amplitudes_check
#print axioms f407_S4_amplitude_gram_check
#print axioms f407_actual_raw_S4_matrix
#print axioms f407_relative_S4_compression
#print axioms f407_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
