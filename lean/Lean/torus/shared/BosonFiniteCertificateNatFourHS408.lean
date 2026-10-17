import torus.shared.BosonFiniteCertificateNatFourIntegerMatrix
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourHWordsSparse
import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import torus.shared.BosonFiniteCertificateNatFourBasis408
import torus.shared.BosonFiniteCertificate408

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

def f408rawHForm : Matrix (Fin 15) (Fin 15) ℚ :=
  !![731430, 1890, 1890, 1890, 1890, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1890, 31185, 630, 630, 630, 315, (315/2), (315/2), 0, 0, 0, 0, 0, 0, 0;
    1890, 630, 6570, 630, 630, 1440, 90, 0, 180, 90, 0, 0, 0, 0, 0;
    1890, 630, 630, 2970, 630, 0, 360, 90, 0, 180, 0, 0, 0, 0, 0;
    1890, 630, 630, 630, 4086, 0, 0, 288, 288, 0, 0, 0, 0, 0, 0;
    0, 315, 1440, 0, 0, 3960, (315/2), (315/2), 0, 0, 135, 45, 45, 0, 0;
    0, (315/2), 90, 360, 0, (315/2), (2715/4), (315/4), 90, 45, 360, 30, 0, 30, 0;
    0, (315/2), 0, 90, 288, (315/2), (315/4), (1575/4), 72, 90, 0, 72, 72, 18, 0;
    0, 0, 180, 0, 288, 0, 90, 72, 468, 90, 0, 96, 0, 24, 144;
    0, 0, 90, 180, 0, 0, 45, 90, 90, 369, 0, 0, 72, 72, 0;
    0, 0, 0, 0, 0, 135, 360, 0, 0, 0, 1485, 135, 135, 0, 0;
    0, 0, 0, 0, 0, 45, 30, 72, 96, 0, 135, 297, 45, 60, 0;
    0, 0, 0, 0, 0, 45, 0, 72, 0, 72, 135, 45, 405, 72, 0;
    0, 0, 0, 0, 0, 0, 30, 18, 24, 72, 0, 60, 72, 174, 144;
    0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 144, 864]

def f408rawS4Form : Matrix (Fin 15) (Fin 15) ℚ :=
  !![11340, 3780, 3780, 3780, 3780, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3780, 1890, 1260, 1260, 1260, 630, 315, 315, 0, 0, 0, 0, 0, 0, 0;
    3780, 1260, 1440, 1260, 1260, 90, 90, 0, 180, 90, 270, 90, 90, 0, 0;
    3780, 1260, 1260, 1350, 1260, 0, 45, 45, 0, 90, 0, 90, 0, 90, 0;
    3780, 1260, 1260, 1260, 1404, 0, 0, 72, 72, 0, 0, 0, 144, 72, 216;
    0, 630, 90, 0, 0, 675, 360, 315, 90, 45, 135, 45, 45, 0, 0;
    0, 315, 90, 45, 0, 360, 225, 180, 90, 90, 135, 90, 45, 45, 0;
    0, 315, 0, 45, 72, 315, 180, 216, 36, 45, 0, 45, 72, 81, 108;
    0, 0, 180, 0, 72, 90, 90, 36, 216, 90, 270, 90, 162, 36, 108;
    0, 0, 90, 90, 0, 45, 90, 45, 90, 135, 135, 135, 45, 90, 0;
    0, 0, 270, 0, 0, 135, 135, 0, 270, 135, 405, 135, 135, 0, 0;
    0, 0, 90, 90, 0, 45, 90, 45, 90, 135, 135, 135, 45, 90, 0;
    0, 0, 90, 0, 144, 45, 45, 72, 162, 45, 135, 45, 189, 72, 216;
    0, 0, 0, 90, 72, 0, 45, 81, 36, 90, 0, 90, 72, 126, 108;
    0, 0, 0, 0, 216, 0, 0, 108, 108, 0, 0, 0, 216, 108, 324]

private theorem f408hs_shape (a : Fin 15) :
    (f408basis a).length=4 ∧ (f408basis a).sum=8 := by
  apply natFourBasis_shape 8
  rw [← f408_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

private theorem f408_H_source_row_0 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 0) (f408basis b)=f408rawHForm 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 0) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 0 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_1 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 1) (f408basis b)=f408rawHForm 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 1) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 1 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_2 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 2) (f408basis b)=f408rawHForm 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 2) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 2 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_3 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 3) (f408basis b)=f408rawHForm 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 3) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 3 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_4 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 4) (f408basis b)=f408rawHForm 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 4) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 4 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_5 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 5) (f408basis b)=f408rawHForm 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 5) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 5 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_6 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 6) (f408basis b)=f408rawHForm 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 6) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 6 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_7 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 7) (f408basis b)=f408rawHForm 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 7) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 7 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_8 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 8) (f408basis b)=f408rawHForm 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 8) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 8 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_9 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 9) (f408basis b)=f408rawHForm 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 9) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 9 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_10 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 10) (f408basis b)=f408rawHForm 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 10) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 10 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_11 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 11) (f408basis b)=f408rawHForm 11 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 11) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 11 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_12 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 12) (f408basis b)=f408rawHForm 12 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 12) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 12 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_13 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 13) (f408basis b)=f408rawHForm 13 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 13) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 13 b) (by decide +kernel)
  exact h 0

private theorem f408_H_source_row_14 : ∀ b : Fin 15,
    natFourHWordFormSparse 8 (f408basis 14) (f408basis b)=f408rawHForm 14 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 15) => natFourHWordFormSparse 8 (f408basis 14) (f408basis b))
    (fun (_ : Fin 1) (b : Fin 15) => f408rawHForm 14 b) (by decide +kernel)
  exact h 0

theorem f408_raw_H_matrix_check : ∀ a b : Fin 15,
    natFourHWordForm 8 (f408basis a) (f408basis b)=f408rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f408_H_source_row_0 b
  · exact f408_H_source_row_1 b
  · exact f408_H_source_row_2 b
  · exact f408_H_source_row_3 b
  · exact f408_H_source_row_4 b
  · exact f408_H_source_row_5 b
  · exact f408_H_source_row_6 b
  · exact f408_H_source_row_7 b
  · exact f408_H_source_row_8 b
  · exact f408_H_source_row_9 b
  · exact f408_H_source_row_10 b
  · exact f408_H_source_row_11 b
  · exact f408_H_source_row_12 b
  · exact f408_H_source_row_13 b
  · exact f408_H_source_row_14 b


theorem f408_actual_raw_H_matrix (x y : Fin 15 → ℂ) :
    natOccupationInner (natFourWordBlock f408basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f408basis y))=
      star x ⬝ᵥ (complexify f408rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 8 f408basis (fun a => (f408hs_shape a).2)
    f408rawHForm f408_raw_H_matrix_check x y

private def f408HCompressionInteger : Matrix (Fin 15) (Fin 15) ℤ :=
  !![2925720, 7560, 7560, 7560, 7560, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    7560, 124740, 2520, 2520, 2520, 1260, 630, 630, 0, 0, 0, 0, 0, 0, 0;
    7560, 2520, 26280, 2520, 2520, 5760, 360, 0, 720, 360, 0, 0, 0, 0, 0;
    7560, 2520, 2520, 11880, 2520, 0, 1440, 360, 0, 720, 0, 0, 0, 0, 0;
    7560, 2520, 2520, 2520, 16344, 0, 0, 1152, 1152, 0, 0, 0, 0, 0, 0;
    0, 1260, 5760, 0, 0, 15840, 630, 630, 0, 0, 540, 180, 180, 0, 0;
    0, 630, 360, 1440, 0, 630, 2715, 315, 360, 180, 1440, 120, 0, 120, 0;
    0, 630, 0, 360, 1152, 630, 315, 1575, 288, 360, 0, 288, 288, 72, 0;
    0, 0, 720, 0, 1152, 0, 360, 288, 1872, 360, 0, 384, 0, 96, 576;
    0, 0, 360, 720, 0, 0, 180, 360, 360, 1476, 0, 0, 288, 288, 0;
    0, 0, 0, 0, 0, 540, 1440, 0, 0, 0, 5940, 540, 540, 0, 0;
    0, 0, 0, 0, 0, 180, 120, 288, 384, 0, 540, 1188, 180, 240, 0;
    0, 0, 0, 0, 0, 180, 0, 288, 0, 288, 540, 180, 1620, 288, 0;
    0, 0, 0, 0, 0, 0, 120, 72, 96, 288, 0, 240, 288, 696, 576;
    0, 0, 0, 0, 0, 0, 0, 0, 576, 0, 0, 0, 0, 576, 3456]

private def f408HCompressionCoordinates : Matrix (Fin 15) (Fin 4) ℤ :=
  !![6, (-6), (-6), 10;
    (-48), 48, 48, (-80);
    168, (-63), (-42), 56;
    (-336), 21, 21, 0;
    210, 0, 0, 0;
    0, (-105), (-126), 224;
    0, 315, 189, (-336);
    0, (-105), (-105), 0;
    0, (-315), 0, 140;
    0, 210, 0, 0;
    0, 0, 126, (-224);
    0, 0, (-315), 560;
    0, 0, 210, 0;
    0, 0, 0, (-560);
    0, 0, 0, 210]

private def f408HCompressionLeftProduct : Matrix (Fin 4) (Fin 15) ℤ :=
  !![17508960, (-5836320), 4021920, (-3114720), 2933280, 907200, (-453600), 90720, 362880, (-181440), 0, 0, 0, 0, 0;
    (-17508960), 5836320, (-2169720), 733320, (-514080), (-1833300), 718200, (-109620), (-476280), 207900, 396900, (-132300), 11340, 60480, (-181440);
    (-17350200), 5783400, (-1632960), 453600, (-98280), (-2075220), 589680, (-177660), (-113400), 56700, 895860, (-298620), 298620, 0, 0;
    29075760, (-9691920), 2615760, (-468720), 176400, 3538080, (-1073520), 146160, 463680, (-151200), (-1391040), 463680, (-141120), (-161280), 483840]

private def f408HCompressionResult : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2723414400, (-1104062400), (-829090080), 1273648320;
    (-1104062400), 1161216000, 964036080, (-1717117920);
    (-829090080), 964036080, 1121049720, (-1774377360);
    1273648320, (-1717117920), (-1774377360), 3193918560]

theorem f408_relative_H_compression :
    b408relativeᵀ*f408rawHForm*b408relative=b408h := by
  have hM : natFourIntegerMatrix 4 f408HCompressionInteger=f408rawHForm := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 4 f408HCompressionInteger) (f408rawHForm) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 210 f408HCompressionCoordinates=b408relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 210 f408HCompressionCoordinates) (b408relative) (by decide +kernel) a b
  have hV : f408HCompressionCoordinatesᵀ*f408HCompressionInteger=f408HCompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408HCompressionCoordinatesᵀ*f408HCompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408HCompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408HCompressionCoordinatesᵀ*f408HCompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408HCompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408HCompressionCoordinatesᵀ*f408HCompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408HCompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408HCompressionCoordinatesᵀ*f408HCompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408HCompressionLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f408HCompressionLeftProduct*f408HCompressionCoordinates=f408HCompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408HCompressionLeftProduct*f408HCompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408HCompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408HCompressionLeftProduct*f408HCompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408HCompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408HCompressionLeftProduct*f408HCompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408HCompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408HCompressionLeftProduct*f408HCompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408HCompressionResult) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (210*4*210) f408HCompressionResult=b408h := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (210*4*210) f408HCompressionResult) (b408h) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 4 210
    f408HCompressionInteger f408HCompressionCoordinates f408HCompressionLeftProduct f408HCompressionResult
    f408rawHForm b408relative b408h hM hD hV hY hF

theorem f408_actual_relative_H_form (x y : Fin 4 → ℂ) :
    natOccupationInner (natFourWordBlock f408basis (complexify b408relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f408basis (complexify b408relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b408h *ᵥ y) :=
  natFour_operator_relative_matrix_form f408basis b408relative canonicalPairHamiltonianNat
    f408rawHForm b408h f408_actual_raw_H_matrix
    f408_relative_H_compression x y

def f408S4Amplitudes : Matrix (Fin 9) (Fin 15) ℚ :=
  !![12, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 8, 0, 0, 0, 8, 4, 4, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 8, 0, 0, 4, 4, 0, 8, 4, 12, 4, 4, 0, 0;
    0, 0, 0, 8, 0, 0, 4, 4, 0, 8, 0, 8, 0, 8, 0;
    0, 0, 0, 0, 16, 0, 0, 8, 8, 0, 0, 0, 16, 8, 24;
    0, 0, 0, 8, 0, 0, 4, 4, 0, 8, 0, 8, 0, 8, 0;
    0, 0, 8, 0, 0, 4, 4, 0, 8, 4, 12, 4, 4, 0, 0;
    0, 8, 0, 0, 0, 8, 4, 4, 0, 0, 0, 0, 0, 0, 0;
    12, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem f408_S4_amplitude_row_0 : ∀ a : Fin 15,
    (natFourDoublePairRemoval 0 (8-0) (f408basis a) : ℚ)=f408S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 15) => (natFourDoublePairRemoval 0 (8-0) (f408basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 15) => f408S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f408_S4_amplitude_row_1 : ∀ a : Fin 15,
    (natFourDoublePairRemoval 1 (8-1) (f408basis a) : ℚ)=f408S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 15) => (natFourDoublePairRemoval 1 (8-1) (f408basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 15) => f408S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f408_S4_amplitude_row_2 : ∀ a : Fin 15,
    (natFourDoublePairRemoval 2 (8-2) (f408basis a) : ℚ)=f408S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 15) => (natFourDoublePairRemoval 2 (8-2) (f408basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 15) => f408S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f408_S4_amplitude_row_3 : ∀ a : Fin 15,
    (natFourDoublePairRemoval 3 (8-3) (f408basis a) : ℚ)=f408S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 15) => (natFourDoublePairRemoval 3 (8-3) (f408basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 15) => f408S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f408_S4_amplitude_row_4 : ∀ a : Fin 15,
    (natFourDoublePairRemoval 4 (8-4) (f408basis a) : ℚ)=f408S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 15) => (natFourDoublePairRemoval 4 (8-4) (f408basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 15) => f408S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f408_S4_amplitude_row_5 : ∀ a : Fin 15,
    (natFourDoublePairRemoval 5 (8-5) (f408basis a) : ℚ)=f408S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 15) => (natFourDoublePairRemoval 5 (8-5) (f408basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 15) => f408S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f408_S4_amplitude_row_6 : ∀ a : Fin 15,
    (natFourDoublePairRemoval 6 (8-6) (f408basis a) : ℚ)=f408S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 15) => (natFourDoublePairRemoval 6 (8-6) (f408basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 15) => f408S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f408_S4_amplitude_row_7 : ∀ a : Fin 15,
    (natFourDoublePairRemoval 7 (8-7) (f408basis a) : ℚ)=f408S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 15) => (natFourDoublePairRemoval 7 (8-7) (f408basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 15) => f408S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

private theorem f408_S4_amplitude_row_8 : ∀ a : Fin 15,
    (natFourDoublePairRemoval 8 (8-8) (f408basis a) : ℚ)=f408S4Amplitudes 8 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 15) => (natFourDoublePairRemoval 8 (8-8) (f408basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 15) => f408S4Amplitudes 8 a) (by decide +kernel)
  exact h 0

theorem f408_S4_amplitudes_check : ∀ p : Fin 9, ∀ a : Fin 15,
    (natFourDoublePairRemoval p.val (8-p.val) (f408basis a) : ℚ)=f408S4Amplitudes p a := by
  intro p
  fin_cases p
  · exact f408_S4_amplitude_row_0
  · exact f408_S4_amplitude_row_1
  · exact f408_S4_amplitude_row_2
  · exact f408_S4_amplitude_row_3
  · exact f408_S4_amplitude_row_4
  · exact f408_S4_amplitude_row_5
  · exact f408_S4_amplitude_row_6
  · exact f408_S4_amplitude_row_7
  · exact f408_S4_amplitude_row_8


theorem f408_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 8 f408S4Amplitudes=f408rawS4Form := by
  ext a b
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 0 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 1 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 2 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 3 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 4 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 5 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 6 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 7 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 8 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 9 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 10 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 11 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 12 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 13 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 15) => (natFourS4AmplitudeGram 8 f408S4Amplitudes) 14 j)
      (fun (_ : Fin 1) (j : Fin 15) => (f408rawS4Form) 14 j) (by decide +kernel)
    exact h 0 b

theorem f408_actual_raw_S4_matrix (x y : Fin 15 → ℂ) :
    natOccupationInner (natFourWordBlock f408basis x)
      (canonicalNatFourS4 (natFourWordBlock f408basis y))=
      star x ⬝ᵥ (complexify f408rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 8 f408basis
    (fun a => (f408hs_shape a).1) (fun a => (f408hs_shape a).2)
    f408S4Amplitudes f408_S4_amplitudes_check f408rawS4Form f408_S4_amplitude_gram_check x y

private def f408S4CompressionInteger : Matrix (Fin 15) (Fin 15) ℤ :=
  !![11340, 3780, 3780, 3780, 3780, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3780, 1890, 1260, 1260, 1260, 630, 315, 315, 0, 0, 0, 0, 0, 0, 0;
    3780, 1260, 1440, 1260, 1260, 90, 90, 0, 180, 90, 270, 90, 90, 0, 0;
    3780, 1260, 1260, 1350, 1260, 0, 45, 45, 0, 90, 0, 90, 0, 90, 0;
    3780, 1260, 1260, 1260, 1404, 0, 0, 72, 72, 0, 0, 0, 144, 72, 216;
    0, 630, 90, 0, 0, 675, 360, 315, 90, 45, 135, 45, 45, 0, 0;
    0, 315, 90, 45, 0, 360, 225, 180, 90, 90, 135, 90, 45, 45, 0;
    0, 315, 0, 45, 72, 315, 180, 216, 36, 45, 0, 45, 72, 81, 108;
    0, 0, 180, 0, 72, 90, 90, 36, 216, 90, 270, 90, 162, 36, 108;
    0, 0, 90, 90, 0, 45, 90, 45, 90, 135, 135, 135, 45, 90, 0;
    0, 0, 270, 0, 0, 135, 135, 0, 270, 135, 405, 135, 135, 0, 0;
    0, 0, 90, 90, 0, 45, 90, 45, 90, 135, 135, 135, 45, 90, 0;
    0, 0, 90, 0, 144, 45, 45, 72, 162, 45, 135, 45, 189, 72, 216;
    0, 0, 0, 90, 72, 0, 45, 81, 36, 90, 0, 90, 72, 126, 108;
    0, 0, 0, 0, 216, 0, 0, 108, 108, 0, 0, 0, 216, 108, 324]

private def f408S4CompressionCoordinates : Matrix (Fin 15) (Fin 4) ℤ :=
  !![6, (-6), (-6), 10;
    (-48), 48, 48, (-80);
    168, (-63), (-42), 56;
    (-336), 21, 21, 0;
    210, 0, 0, 0;
    0, (-105), (-126), 224;
    0, 315, 189, (-336);
    0, (-105), (-105), 0;
    0, (-315), 0, 140;
    0, 210, 0, 0;
    0, 0, 126, (-224);
    0, 0, (-315), 560;
    0, 0, 210, 0;
    0, 0, 0, (-560);
    0, 0, 0, 210]

private def f408S4CompressionLeftProduct : Matrix (Fin 4) (Fin 15) ℤ :=
  !![45360, (-15120), 45360, (-15120), 45360, (-15120), (-15120), (-15120), 45360, (-15120), 45360, (-15120), 45360, (-15120), 45360;
    (-45360), 15120, (-45360), 15120, (-45360), 15120, 15120, 15120, (-45360), 15120, (-45360), 15120, (-45360), 15120, (-45360);
    34020, (-11340), 34020, (-11340), 34020, (-11340), (-11340), (-11340), 34020, (-11340), 34020, (-11340), 34020, (-11340), 34020;
    22680, (-7560), 22680, (-7560), 22680, (-7560), (-7560), (-7560), 22680, (-7560), 22680, (-7560), 22680, (-7560), 22680]

private def f408S4CompressionResult : Matrix (Fin 4) (Fin 4) ℤ :=
  !![23224320, (-23224320), 17418240, 11612160;
    (-23224320), 23224320, (-17418240), (-11612160);
    17418240, (-17418240), 13063680, 8709120;
    11612160, (-11612160), 8709120, 5806080]

theorem f408_relative_S4_compression :
    b408relativeᵀ*f408rawS4Form*b408relative=b408s := by
  have hM : natFourIntegerMatrix 1 f408S4CompressionInteger=f408rawS4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f408S4CompressionInteger) (f408rawS4Form) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 210 f408S4CompressionCoordinates=b408relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 210 f408S4CompressionCoordinates) (b408relative) (by decide +kernel) a b
  have hV : f408S4CompressionCoordinatesᵀ*f408S4CompressionInteger=f408S4CompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408S4CompressionCoordinatesᵀ*f408S4CompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408S4CompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408S4CompressionCoordinatesᵀ*f408S4CompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408S4CompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408S4CompressionCoordinatesᵀ*f408S4CompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408S4CompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408S4CompressionCoordinatesᵀ*f408S4CompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408S4CompressionLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f408S4CompressionLeftProduct*f408S4CompressionCoordinates=f408S4CompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408S4CompressionLeftProduct*f408S4CompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408S4CompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408S4CompressionLeftProduct*f408S4CompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408S4CompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408S4CompressionLeftProduct*f408S4CompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408S4CompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408S4CompressionLeftProduct*f408S4CompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408S4CompressionResult) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (210*1*210) f408S4CompressionResult=b408s := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (210*1*210) f408S4CompressionResult) (b408s) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1 210
    f408S4CompressionInteger f408S4CompressionCoordinates f408S4CompressionLeftProduct f408S4CompressionResult
    f408rawS4Form b408relative b408s hM hD hV hY hF

theorem f408_actual_relative_S4_form (x y : Fin 4 → ℂ) :
    natOccupationInner (natFourWordBlock f408basis (complexify b408relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f408basis (complexify b408relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b408s *ᵥ y) :=
  natFour_operator_relative_matrix_form f408basis b408relative canonicalNatFourS4
    f408rawS4Form b408s f408_actual_raw_S4_matrix
    f408_relative_S4_compression x y

#print axioms f408_raw_H_matrix_check
#print axioms f408_actual_raw_H_matrix
#print axioms f408_relative_H_compression
#print axioms f408_actual_relative_H_form
#print axioms f408_S4_amplitudes_check
#print axioms f408_S4_amplitude_gram_check
#print axioms f408_actual_raw_S4_matrix
#print axioms f408_relative_S4_compression
#print axioms f408_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
