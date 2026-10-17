import torus.shared.BosonFiniteCertificateNatFourIntegerMatrix
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourHWordsSparse
import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import torus.shared.BosonFiniteCertificateNatFourBasis406
import torus.shared.BosonFiniteCertificate406

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

def f406rawHForm : Matrix (Fin 9) (Fin 9) ℚ :=
  !![13365, 135, 135, 135, 0, 0, 0, 0, 0;
    135, 795, 45, 45, 30, 15, 0, 0, 0;
    135, 45, 261, 45, 48, 12, 36, 0, 0;
    135, 45, 45, 333, 0, 36, 0, 0, 0;
    0, 30, 48, 0, 156, 15, 0, 18, 6;
    0, 15, 12, 36, 15, (87/2), 18, 18, 12;
    0, 0, 36, 0, 0, 18, 126, 0, 24;
    0, 0, 0, 0, 18, 18, 0, 108, 18;
    0, 0, 0, 0, 6, 12, 24, 18, 62]

def f406rawS4Form : Matrix (Fin 9) (Fin 9) ℚ :=
  !![810, 270, 270, 270, 0, 0, 0, 0, 0;
    270, 150, 90, 90, 60, 30, 0, 0, 0;
    270, 90, 114, 90, 12, 12, 36, 36, 12;
    270, 90, 90, 126, 0, 18, 0, 0, 36;
    0, 60, 12, 0, 66, 36, 18, 18, 6;
    0, 30, 12, 18, 36, 30, 18, 18, 24;
    0, 0, 36, 0, 18, 18, 54, 54, 18;
    0, 0, 36, 0, 18, 18, 54, 54, 18;
    0, 0, 12, 36, 6, 24, 18, 18, 42]

private theorem f406hs_shape (a : Fin 9) :
    (f406basis a).length=4 ∧ (f406basis a).sum=6 := by
  apply natFourBasis_shape 6
  rw [← f406_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

private theorem f406_H_source_row_0 : ∀ b : Fin 9,
    natFourHWordFormSparse 6 (f406basis 0) (f406basis b)=f406rawHForm 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) => natFourHWordFormSparse 6 (f406basis 0) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawHForm 0 b) (by decide +kernel)
  exact h 0

private theorem f406_H_source_row_1 : ∀ b : Fin 9,
    natFourHWordFormSparse 6 (f406basis 1) (f406basis b)=f406rawHForm 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) => natFourHWordFormSparse 6 (f406basis 1) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawHForm 1 b) (by decide +kernel)
  exact h 0

private theorem f406_H_source_row_2 : ∀ b : Fin 9,
    natFourHWordFormSparse 6 (f406basis 2) (f406basis b)=f406rawHForm 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) => natFourHWordFormSparse 6 (f406basis 2) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawHForm 2 b) (by decide +kernel)
  exact h 0

private theorem f406_H_source_row_3 : ∀ b : Fin 9,
    natFourHWordFormSparse 6 (f406basis 3) (f406basis b)=f406rawHForm 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) => natFourHWordFormSparse 6 (f406basis 3) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawHForm 3 b) (by decide +kernel)
  exact h 0

private theorem f406_H_source_row_4 : ∀ b : Fin 9,
    natFourHWordFormSparse 6 (f406basis 4) (f406basis b)=f406rawHForm 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) => natFourHWordFormSparse 6 (f406basis 4) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawHForm 4 b) (by decide +kernel)
  exact h 0

private theorem f406_H_source_row_5 : ∀ b : Fin 9,
    natFourHWordFormSparse 6 (f406basis 5) (f406basis b)=f406rawHForm 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) => natFourHWordFormSparse 6 (f406basis 5) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawHForm 5 b) (by decide +kernel)
  exact h 0

private theorem f406_H_source_row_6 : ∀ b : Fin 9,
    natFourHWordFormSparse 6 (f406basis 6) (f406basis b)=f406rawHForm 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) => natFourHWordFormSparse 6 (f406basis 6) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawHForm 6 b) (by decide +kernel)
  exact h 0

private theorem f406_H_source_row_7 : ∀ b : Fin 9,
    natFourHWordFormSparse 6 (f406basis 7) (f406basis b)=f406rawHForm 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) => natFourHWordFormSparse 6 (f406basis 7) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawHForm 7 b) (by decide +kernel)
  exact h 0

private theorem f406_H_source_row_8 : ∀ b : Fin 9,
    natFourHWordFormSparse 6 (f406basis 8) (f406basis b)=f406rawHForm 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) => natFourHWordFormSparse 6 (f406basis 8) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawHForm 8 b) (by decide +kernel)
  exact h 0

theorem f406_raw_H_matrix_check : ∀ a b : Fin 9,
    natFourHWordForm 6 (f406basis a) (f406basis b)=f406rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f406_H_source_row_0 b
  · exact f406_H_source_row_1 b
  · exact f406_H_source_row_2 b
  · exact f406_H_source_row_3 b
  · exact f406_H_source_row_4 b
  · exact f406_H_source_row_5 b
  · exact f406_H_source_row_6 b
  · exact f406_H_source_row_7 b
  · exact f406_H_source_row_8 b


theorem f406_actual_raw_H_matrix (x y : Fin 9 → ℂ) :
    natOccupationInner (natFourWordBlock f406basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f406basis y))=
      star x ⬝ᵥ (complexify f406rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 6 f406basis (fun a => (f406hs_shape a).2)
    f406rawHForm f406_raw_H_matrix_check x y

private def f406HCompressionInteger : Matrix (Fin 9) (Fin 9) ℤ :=
  !![26730, 270, 270, 270, 0, 0, 0, 0, 0;
    270, 1590, 90, 90, 60, 30, 0, 0, 0;
    270, 90, 522, 90, 96, 24, 72, 0, 0;
    270, 90, 90, 666, 0, 72, 0, 0, 0;
    0, 60, 96, 0, 312, 30, 0, 36, 12;
    0, 30, 24, 72, 30, 87, 36, 36, 24;
    0, 0, 72, 0, 0, 36, 252, 0, 48;
    0, 0, 0, 0, 36, 36, 0, 216, 36;
    0, 0, 0, 0, 12, 24, 48, 36, 124]

private def f406HCompressionCoordinates : Matrix (Fin 9) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    18, (-18), (-18);
    (-45), 15, 5;
    30, 0, 0;
    0, 30, 40;
    0, (-60), (-20);
    0, 30, 0;
    0, 0, (-40);
    0, 0, 30]

private def f406HCompressionLeftProduct : Matrix (Fin 3) (Fin 9) ℤ :=
  !![(-79380), 26460, (-19980), 16740, (-3240), 1620, (-3240), 0, 0;
    79380, (-26460), 10620, (-3780), 7920, (-3420), 6480, (-1080), 360;
    76680, (-25560), 5160, (-1800), 10200, (-1680), 1080, (-6840), 2280]

private def f406HCompressionResult : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2115720, (-1305720), (-976320);
    (-1305720), 1510920, 1206720;
    (-976320), 1206720, 1499520]

theorem f406_relative_H_compression :
    b406relativeᵀ*f406rawHForm*b406relative=b406h := by
  have hM : natFourIntegerMatrix 2 f406HCompressionInteger=f406rawHForm := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f406HCompressionInteger) (f406rawHForm) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 30 f406HCompressionCoordinates=b406relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406HCompressionCoordinates) (b406relative) (by decide +kernel) a b
  have hV : f406HCompressionCoordinatesᵀ*f406HCompressionInteger=f406HCompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f406HCompressionCoordinatesᵀ*f406HCompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f406HCompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f406HCompressionCoordinatesᵀ*f406HCompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f406HCompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f406HCompressionCoordinatesᵀ*f406HCompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f406HCompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406HCompressionLeftProduct*f406HCompressionCoordinates=f406HCompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406HCompressionLeftProduct*f406HCompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406HCompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406HCompressionLeftProduct*f406HCompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406HCompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406HCompressionLeftProduct*f406HCompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406HCompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*2*30) f406HCompressionResult=b406h := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*2*30) f406HCompressionResult) (b406h) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 2 30
    f406HCompressionInteger f406HCompressionCoordinates f406HCompressionLeftProduct f406HCompressionResult
    f406rawHForm b406relative b406h hM hD hV hY hF

theorem f406_actual_relative_H_form (x y : Fin 3 → ℂ) :
    natOccupationInner (natFourWordBlock f406basis (complexify b406relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f406basis (complexify b406relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b406h *ᵥ y) :=
  natFour_operator_relative_matrix_form f406basis b406relative canonicalPairHamiltonianNat
    f406rawHForm b406h f406_actual_raw_H_matrix
    f406_relative_H_compression x y

def f406S4Amplitudes : Matrix (Fin 7) (Fin 9) ℚ :=
  !![12, 4, 4, 4, 0, 0, 0, 0, 0;
    0, 8, 0, 0, 8, 4, 0, 0, 0;
    0, 0, 8, 0, 4, 4, 12, 12, 4;
    0, 0, 0, 16, 0, 8, 0, 0, 16;
    0, 0, 8, 0, 4, 4, 12, 12, 4;
    0, 8, 0, 0, 8, 4, 0, 0, 0;
    12, 4, 4, 4, 0, 0, 0, 0, 0]

private theorem f406_S4_amplitude_row_0 : ∀ a : Fin 9,
    (natFourDoublePairRemoval 0 (6-0) (f406basis a) : ℚ)=f406S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 9) => (natFourDoublePairRemoval 0 (6-0) (f406basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 9) => f406S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f406_S4_amplitude_row_1 : ∀ a : Fin 9,
    (natFourDoublePairRemoval 1 (6-1) (f406basis a) : ℚ)=f406S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 9) => (natFourDoublePairRemoval 1 (6-1) (f406basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 9) => f406S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f406_S4_amplitude_row_2 : ∀ a : Fin 9,
    (natFourDoublePairRemoval 2 (6-2) (f406basis a) : ℚ)=f406S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 9) => (natFourDoublePairRemoval 2 (6-2) (f406basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 9) => f406S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f406_S4_amplitude_row_3 : ∀ a : Fin 9,
    (natFourDoublePairRemoval 3 (6-3) (f406basis a) : ℚ)=f406S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 9) => (natFourDoublePairRemoval 3 (6-3) (f406basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 9) => f406S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f406_S4_amplitude_row_4 : ∀ a : Fin 9,
    (natFourDoublePairRemoval 4 (6-4) (f406basis a) : ℚ)=f406S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 9) => (natFourDoublePairRemoval 4 (6-4) (f406basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 9) => f406S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f406_S4_amplitude_row_5 : ∀ a : Fin 9,
    (natFourDoublePairRemoval 5 (6-5) (f406basis a) : ℚ)=f406S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 9) => (natFourDoublePairRemoval 5 (6-5) (f406basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 9) => f406S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f406_S4_amplitude_row_6 : ∀ a : Fin 9,
    (natFourDoublePairRemoval 6 (6-6) (f406basis a) : ℚ)=f406S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 9) => (natFourDoublePairRemoval 6 (6-6) (f406basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 9) => f406S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

theorem f406_S4_amplitudes_check : ∀ p : Fin 7, ∀ a : Fin 9,
    (natFourDoublePairRemoval p.val (6-p.val) (f406basis a) : ℚ)=f406S4Amplitudes p a := by
  intro p
  fin_cases p
  · exact f406_S4_amplitude_row_0
  · exact f406_S4_amplitude_row_1
  · exact f406_S4_amplitude_row_2
  · exact f406_S4_amplitude_row_3
  · exact f406_S4_amplitude_row_4
  · exact f406_S4_amplitude_row_5
  · exact f406_S4_amplitude_row_6


theorem f406_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 6 f406S4Amplitudes=f406rawS4Form := by
  ext a b
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 9) => (natFourS4AmplitudeGram 6 f406S4Amplitudes) 0 j)
      (fun (_ : Fin 1) (j : Fin 9) => (f406rawS4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 9) => (natFourS4AmplitudeGram 6 f406S4Amplitudes) 1 j)
      (fun (_ : Fin 1) (j : Fin 9) => (f406rawS4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 9) => (natFourS4AmplitudeGram 6 f406S4Amplitudes) 2 j)
      (fun (_ : Fin 1) (j : Fin 9) => (f406rawS4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 9) => (natFourS4AmplitudeGram 6 f406S4Amplitudes) 3 j)
      (fun (_ : Fin 1) (j : Fin 9) => (f406rawS4Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 9) => (natFourS4AmplitudeGram 6 f406S4Amplitudes) 4 j)
      (fun (_ : Fin 1) (j : Fin 9) => (f406rawS4Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 9) => (natFourS4AmplitudeGram 6 f406S4Amplitudes) 5 j)
      (fun (_ : Fin 1) (j : Fin 9) => (f406rawS4Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 9) => (natFourS4AmplitudeGram 6 f406S4Amplitudes) 6 j)
      (fun (_ : Fin 1) (j : Fin 9) => (f406rawS4Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 9) => (natFourS4AmplitudeGram 6 f406S4Amplitudes) 7 j)
      (fun (_ : Fin 1) (j : Fin 9) => (f406rawS4Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 9) => (natFourS4AmplitudeGram 6 f406S4Amplitudes) 8 j)
      (fun (_ : Fin 1) (j : Fin 9) => (f406rawS4Form) 8 j) (by decide +kernel)
    exact h 0 b

theorem f406_actual_raw_S4_matrix (x y : Fin 9 → ℂ) :
    natOccupationInner (natFourWordBlock f406basis x)
      (canonicalNatFourS4 (natFourWordBlock f406basis y))=
      star x ⬝ᵥ (complexify f406rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 6 f406basis
    (fun a => (f406hs_shape a).1) (fun a => (f406hs_shape a).2)
    f406S4Amplitudes f406_S4_amplitudes_check f406rawS4Form f406_S4_amplitude_gram_check x y

private def f406S4CompressionInteger : Matrix (Fin 9) (Fin 9) ℤ :=
  !![810, 270, 270, 270, 0, 0, 0, 0, 0;
    270, 150, 90, 90, 60, 30, 0, 0, 0;
    270, 90, 114, 90, 12, 12, 36, 36, 12;
    270, 90, 90, 126, 0, 18, 0, 0, 36;
    0, 60, 12, 0, 66, 36, 18, 18, 6;
    0, 30, 12, 18, 36, 30, 18, 18, 24;
    0, 0, 36, 0, 18, 18, 54, 54, 18;
    0, 0, 36, 0, 18, 18, 54, 54, 18;
    0, 0, 12, 36, 6, 24, 18, 18, 42]

private def f406S4CompressionCoordinates : Matrix (Fin 9) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    18, (-18), (-18);
    (-45), 15, 5;
    30, 0, 0;
    0, 30, 40;
    0, (-60), (-20);
    0, 30, 0;
    0, 0, (-40);
    0, 0, 30]

private def f406S4CompressionLeftProduct : Matrix (Fin 3) (Fin 9) ℤ :=
  !![(-1620), 540, (-1620), 540, 540, 540, (-1620), (-1620), 540;
    1620, (-540), 1620, (-540), (-540), (-540), 1620, 1620, (-540);
    (-1080), 360, (-1080), 360, 360, 360, (-1080), (-1080), 360]

private def f406S4CompressionResult : Matrix (Fin 3) (Fin 3) ℤ :=
  !![103680, (-103680), 69120;
    (-103680), 103680, (-69120);
    69120, (-69120), 46080]

theorem f406_relative_S4_compression :
    b406relativeᵀ*f406rawS4Form*b406relative=b406s := by
  have hM : natFourIntegerMatrix 1 f406S4CompressionInteger=f406rawS4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f406S4CompressionInteger) (f406rawS4Form) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 30 f406S4CompressionCoordinates=b406relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406S4CompressionCoordinates) (b406relative) (by decide +kernel) a b
  have hV : f406S4CompressionCoordinatesᵀ*f406S4CompressionInteger=f406S4CompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f406S4CompressionCoordinatesᵀ*f406S4CompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f406S4CompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f406S4CompressionCoordinatesᵀ*f406S4CompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f406S4CompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f406S4CompressionCoordinatesᵀ*f406S4CompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f406S4CompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406S4CompressionLeftProduct*f406S4CompressionCoordinates=f406S4CompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406S4CompressionLeftProduct*f406S4CompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406S4CompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406S4CompressionLeftProduct*f406S4CompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406S4CompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406S4CompressionLeftProduct*f406S4CompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406S4CompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1*30) f406S4CompressionResult=b406s := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1*30) f406S4CompressionResult) (b406s) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1 30
    f406S4CompressionInteger f406S4CompressionCoordinates f406S4CompressionLeftProduct f406S4CompressionResult
    f406rawS4Form b406relative b406s hM hD hV hY hF

theorem f406_actual_relative_S4_form (x y : Fin 3 → ℂ) :
    natOccupationInner (natFourWordBlock f406basis (complexify b406relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f406basis (complexify b406relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b406s *ᵥ y) :=
  natFour_operator_relative_matrix_form f406basis b406relative canonicalNatFourS4
    f406rawS4Form b406s f406_actual_raw_S4_matrix
    f406_relative_S4_compression x y

#print axioms f406_raw_H_matrix_check
#print axioms f406_actual_raw_H_matrix
#print axioms f406_relative_H_compression
#print axioms f406_actual_relative_H_form
#print axioms f406_S4_amplitudes_check
#print axioms f406_S4_amplitude_gram_check
#print axioms f406_actual_raw_S4_matrix
#print axioms f406_relative_S4_compression
#print axioms f406_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
