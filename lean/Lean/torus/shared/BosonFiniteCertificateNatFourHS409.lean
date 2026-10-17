import torus.shared.BosonFiniteCertificateNatFourIntegerMatrix
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourHWordsSparse
import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import torus.shared.BosonFiniteCertificateNatFourBasis409
import torus.shared.BosonFiniteCertificate409

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

def f409rawHForm : Matrix (Fin 18) (Fin 18) ℚ :=
  !![6557355, 8505, 8505, 8505, 8505, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    8505, 246015, 2835, 2835, 2835, 1260, 630, 630, 630, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    8505, 2835, 43785, 2835, 2835, 10080, 315, 0, 0, 630, 315, 0, 0, 0, 0, 0, 0, 0;
    8505, 2835, 2835, 16335, 2835, 0, 2160, 270, 0, 0, 270, 810, 0, 0, 0, 0, 0, 0;
    8505, 2835, 2835, 2835, 10755, 0, 0, 720, 720, 720, 360, 0, 0, 0, 0, 0, 0, 0;
    0, 1260, 10080, 0, 0, (53235/2), 630, 630, 630, 0, 0, 0, (945/2), (315/2), (315/2), 0, 0, 0;
    0, 630, 315, 2160, 0, 630, (7515/2), 315, 315, 315, (315/2), 0, 2160, 90, 0, 90, 45, 0;
    0, 630, 0, 270, 720, 630, 315, 1755, 315, 360, 135, 405, 0, 360, 90, 0, 90, 0;
    0, 630, 0, 0, 720, 630, 315, 315, 2475, 0, 360, 0, 0, 0, 288, 144, 0, 0;
    0, 0, 630, 0, 720, 0, 315, 360, 0, 2010, 315, 0, 0, 480, 0, 60, 0, 180;
    0, 0, 315, 270, 360, 0, (315/2), 135, 360, 315, (1449/2), 405, 0, 0, 144, 144, 72, 108;
    0, 0, 0, 810, 0, 0, 0, 405, 0, 0, 405, 2187, 0, 0, 0, 0, 324, 0;
    0, 0, 0, 0, 0, (945/2), 2160, 0, 0, 0, 0, 0, (15795/2), (945/2), (945/2), 0, 0, 0;
    0, 0, 0, 0, 0, (315/2), 90, 360, 0, 480, 0, 0, (945/2), (2595/2), (315/2), 180, 90, 0;
    0, 0, 0, 0, 0, (315/2), 0, 90, 288, 0, 144, 0, (945/2), (315/2), (1539/2), 144, 180, 0;
    0, 0, 0, 0, 0, 0, 90, 0, 144, 60, 144, 0, 0, 180, 144, 600, 90, 180;
    0, 0, 0, 0, 0, 0, 45, 90, 0, 0, 72, 324, 0, 90, 180, 90, 477, 216;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 108, 0, 0, 0, 0, 180, 216, 864]

def f409rawS4Form : Matrix (Fin 18) (Fin 18) ℚ :=
  !![51030, 17010, 17010, 17010, 17010, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    17010, 8190, 5670, 5670, 5670, 2520, 1260, 1260, 1260, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    17010, 5670, 6300, 5670, 5670, 315, 315, 0, 0, 630, 315, 0, 945, 315, 315, 0, 0, 0;
    17010, 5670, 5670, 5940, 5670, 0, 135, 135, 0, 0, 135, 405, 0, 270, 0, 270, 135, 0;
    17010, 5670, 5670, 5670, 5850, 0, 0, 90, 180, 90, 90, 0, 0, 0, 180, 90, 180, 270;
    0, 2520, 315, 0, 0, (5355/2), (2835/2), 1260, 1260, 315, (315/2), 0, (945/2), (315/2), (315/2), 0, 0, 0;
    0, 1260, 315, 135, 0, (2835/2), 855, (1395/2), 630, 315, 225, (405/2), (945/2), (585/2), (315/2), 135, (135/2), 0;
    0, 1260, 0, 135, 90, 1260, (1395/2), (1485/2), 720, 45, (225/2), (405/2), 0, 135, 90, 180, (315/2), 135;
    0, 1260, 0, 0, 180, 1260, 630, 720, 810, 90, 90, 0, 0, 0, 180, 90, 180, 270;
    0, 0, 630, 0, 90, 315, 315, 45, 90, 675, 360, 0, 945, 315, 405, 45, 90, 135;
    0, 0, 315, 135, 90, (315/2), 225, (225/2), 90, 360, 270, (405/2), (945/2), (585/2), (495/2), 180, (315/2), 135;
    0, 0, 0, 405, 0, 0, (405/2), (405/2), 0, 0, (405/2), (1215/2), 0, 405, 0, 405, (405/2), 0;
    0, 0, 945, 0, 0, (945/2), (945/2), 0, 0, 945, (945/2), 0, (2835/2), (945/2), (945/2), 0, 0, 0;
    0, 0, 315, 270, 0, (315/2), (585/2), 135, 0, 315, (585/2), 405, (945/2), (855/2), (315/2), 270, 135, 0;
    0, 0, 315, 0, 180, (315/2), (315/2), 90, 180, 405, (495/2), 0, (945/2), (315/2), (675/2), 90, 180, 270;
    0, 0, 0, 270, 90, 0, 135, 180, 90, 45, 180, 405, 0, 270, 90, 315, 225, 135;
    0, 0, 0, 135, 180, 0, (135/2), (315/2), 180, 90, (315/2), (405/2), 0, 135, 180, 225, (495/2), 270;
    0, 0, 0, 0, 270, 0, 0, 135, 270, 135, 135, 0, 0, 0, 270, 135, 270, 405]

private theorem f409hs_shape (a : Fin 18) :
    (f409basis a).length=4 ∧ (f409basis a).sum=9 := by
  apply natFourBasis_shape 9
  rw [← f409_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

private theorem f409_H_source_row_0 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 0) (f409basis b)=f409rawHForm 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 0) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 0 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_1 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 1) (f409basis b)=f409rawHForm 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 1) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 1 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_2 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 2) (f409basis b)=f409rawHForm 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 2) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 2 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_3 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 3) (f409basis b)=f409rawHForm 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 3) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 3 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_4 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 4) (f409basis b)=f409rawHForm 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 4) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 4 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_5 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 5) (f409basis b)=f409rawHForm 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 5) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 5 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_6 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 6) (f409basis b)=f409rawHForm 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 6) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 6 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_7 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 7) (f409basis b)=f409rawHForm 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 7) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 7 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_8 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 8) (f409basis b)=f409rawHForm 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 8) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 8 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_9 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 9) (f409basis b)=f409rawHForm 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 9) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 9 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_10 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 10) (f409basis b)=f409rawHForm 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 10) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 10 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_11 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 11) (f409basis b)=f409rawHForm 11 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 11) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 11 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_12 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 12) (f409basis b)=f409rawHForm 12 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 12) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 12 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_13 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 13) (f409basis b)=f409rawHForm 13 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 13) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 13 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_14 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 14) (f409basis b)=f409rawHForm 14 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 14) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 14 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_15 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 15) (f409basis b)=f409rawHForm 15 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 15) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 15 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_16 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 16) (f409basis b)=f409rawHForm 16 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 16) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 16 b) (by decide +kernel)
  exact h 0

private theorem f409_H_source_row_17 : ∀ b : Fin 18,
    natFourHWordFormSparse 9 (f409basis 17) (f409basis b)=f409rawHForm 17 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 18) => natFourHWordFormSparse 9 (f409basis 17) (f409basis b))
    (fun (_ : Fin 1) (b : Fin 18) => f409rawHForm 17 b) (by decide +kernel)
  exact h 0

theorem f409_raw_H_matrix_check : ∀ a b : Fin 18,
    natFourHWordForm 9 (f409basis a) (f409basis b)=f409rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f409_H_source_row_0 b
  · exact f409_H_source_row_1 b
  · exact f409_H_source_row_2 b
  · exact f409_H_source_row_3 b
  · exact f409_H_source_row_4 b
  · exact f409_H_source_row_5 b
  · exact f409_H_source_row_6 b
  · exact f409_H_source_row_7 b
  · exact f409_H_source_row_8 b
  · exact f409_H_source_row_9 b
  · exact f409_H_source_row_10 b
  · exact f409_H_source_row_11 b
  · exact f409_H_source_row_12 b
  · exact f409_H_source_row_13 b
  · exact f409_H_source_row_14 b
  · exact f409_H_source_row_15 b
  · exact f409_H_source_row_16 b
  · exact f409_H_source_row_17 b


theorem f409_actual_raw_H_matrix (x y : Fin 18 → ℂ) :
    natOccupationInner (natFourWordBlock f409basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f409basis y))=
      star x ⬝ᵥ (complexify f409rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 9 f409basis (fun a => (f409hs_shape a).2)
    f409rawHForm f409_raw_H_matrix_check x y

#print axioms f409_actual_raw_H_matrix

private def f409HCompressionInteger : Matrix (Fin 18) (Fin 18) ℤ :=
  !![13114710, 17010, 17010, 17010, 17010, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    17010, 492030, 5670, 5670, 5670, 2520, 1260, 1260, 1260, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    17010, 5670, 87570, 5670, 5670, 20160, 630, 0, 0, 1260, 630, 0, 0, 0, 0, 0, 0, 0;
    17010, 5670, 5670, 32670, 5670, 0, 4320, 540, 0, 0, 540, 1620, 0, 0, 0, 0, 0, 0;
    17010, 5670, 5670, 5670, 21510, 0, 0, 1440, 1440, 1440, 720, 0, 0, 0, 0, 0, 0, 0;
    0, 2520, 20160, 0, 0, 53235, 1260, 1260, 1260, 0, 0, 0, 945, 315, 315, 0, 0, 0;
    0, 1260, 630, 4320, 0, 1260, 7515, 630, 630, 630, 315, 0, 4320, 180, 0, 180, 90, 0;
    0, 1260, 0, 540, 1440, 1260, 630, 3510, 630, 720, 270, 810, 0, 720, 180, 0, 180, 0;
    0, 1260, 0, 0, 1440, 1260, 630, 630, 4950, 0, 720, 0, 0, 0, 576, 288, 0, 0;
    0, 0, 1260, 0, 1440, 0, 630, 720, 0, 4020, 630, 0, 0, 960, 0, 120, 0, 360;
    0, 0, 630, 540, 720, 0, 315, 270, 720, 630, 1449, 810, 0, 0, 288, 288, 144, 216;
    0, 0, 0, 1620, 0, 0, 0, 810, 0, 0, 810, 4374, 0, 0, 0, 0, 648, 0;
    0, 0, 0, 0, 0, 945, 4320, 0, 0, 0, 0, 0, 15795, 945, 945, 0, 0, 0;
    0, 0, 0, 0, 0, 315, 180, 720, 0, 960, 0, 0, 945, 2595, 315, 360, 180, 0;
    0, 0, 0, 0, 0, 315, 0, 180, 576, 0, 288, 0, 945, 315, 1539, 288, 360, 0;
    0, 0, 0, 0, 0, 0, 180, 0, 288, 120, 288, 0, 0, 360, 288, 1200, 180, 360;
    0, 0, 0, 0, 0, 0, 90, 180, 0, 0, 144, 648, 0, 180, 360, 180, 954, 432;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 360, 216, 0, 0, 0, 0, 360, 432, 1728]

private def f409HCompressionCoordinates : Matrix (Fin 18) (Fin 3) ℤ :=
  !![(-4), 5, 5;
    36, (-45), (-45);
    (-80), 72, 44;
    112, (-42), (-14);
    (-56), 0, 0;
    (-64), 108, 136;
    224, (-378), (-266);
    (-448), 252, 84;
    280, 0, 0;
    0, 378, 126;
    0, (-630), (-70);
    0, 280, 0;
    0, 0, (-140);
    0, 0, 420;
    0, 0, (-140);
    0, 0, (-420);
    0, 0, 280;
    0, 0, 0]

private def f409HCompressionLeftProduct : Matrix (Fin 3) (Fin 18) ℤ :=
  !![(-52254720), 17418240, (-7701120), 3749760, (-1128960), (-4858560), 1975680, (-1310400), 1128960, (-362880), 120960, (-181440), 907200, (-302400), 60480, 120960, (-60480), 0;
    65318400, (-21772800), 7915320, (-2517480), 453600, 6928740, (-2698920), 1031940, (-453600), 1156680, (-476280), 850500, (-1530900), 510300, (-102060), (-204120), 102060, 0;
    65318400, (-21772800), 6292440, (-1519560), 252000, 7740180, (-2386440), 633780, (-252000), 763560, (-183960), 170100, (-2967300), 989100, (-197820), (-395640), 197820, 0]

private def f409HCompressionResult : Matrix (Fin 3) (Fin 3) ℤ :=
  !![3592028160, (-3622993920), (-3117219840);
    (-3622993920), 4985971200, 4173120000;
    (-3117219840), 4173120000, 4534387200]

theorem f409_relative_H_compression :
    b409relativeᵀ*f409rawHForm*b409relative=b409h := by
  have hM : natFourIntegerMatrix 2 f409HCompressionInteger=f409rawHForm := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f409HCompressionInteger) (f409rawHForm) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 280 f409HCompressionCoordinates=b409relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409HCompressionCoordinates) (b409relative) (by decide +kernel) a b
  have hV : f409HCompressionCoordinatesᵀ*f409HCompressionInteger=f409HCompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f409HCompressionCoordinatesᵀ*f409HCompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f409HCompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f409HCompressionCoordinatesᵀ*f409HCompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f409HCompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f409HCompressionCoordinatesᵀ*f409HCompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f409HCompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f409HCompressionLeftProduct*f409HCompressionCoordinates=f409HCompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409HCompressionLeftProduct*f409HCompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409HCompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409HCompressionLeftProduct*f409HCompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409HCompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409HCompressionLeftProduct*f409HCompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409HCompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*2*280) f409HCompressionResult=b409h := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*2*280) f409HCompressionResult) (b409h) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 2 280
    f409HCompressionInteger f409HCompressionCoordinates f409HCompressionLeftProduct f409HCompressionResult
    f409rawHForm b409relative b409h hM hD hV hY hF

theorem f409_actual_relative_H_form (x y : Fin 3 → ℂ) :
    natOccupationInner (natFourWordBlock f409basis (complexify b409relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f409basis (complexify b409relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b409h *ᵥ y) :=
  natFour_operator_relative_matrix_form f409basis b409relative canonicalPairHamiltonianNat
    f409rawHForm b409h f409_actual_raw_H_matrix
    f409_relative_H_compression x y

#print axioms f409_actual_relative_H_form

def f409S4Amplitudes : Matrix (Fin 10) (Fin 18) ℚ :=
  !![12, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 8, 0, 0, 0, 8, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 8, 0, 0, 4, 4, 0, 0, 8, 4, 0, 12, 4, 4, 0, 0, 0;
    0, 0, 0, 8, 0, 0, 4, 4, 0, 0, 4, 12, 0, 8, 0, 8, 4, 0;
    0, 0, 0, 0, 8, 0, 0, 4, 8, 4, 4, 0, 0, 0, 8, 4, 8, 12;
    0, 0, 0, 0, 8, 0, 0, 4, 8, 4, 4, 0, 0, 0, 8, 4, 8, 12;
    0, 0, 0, 8, 0, 0, 4, 4, 0, 0, 4, 12, 0, 8, 0, 8, 4, 0;
    0, 0, 8, 0, 0, 4, 4, 0, 0, 8, 4, 0, 12, 4, 4, 0, 0, 0;
    0, 8, 0, 0, 0, 8, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    12, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem f409_S4_amplitude_row_0 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 0 (9-0) (f409basis a) : ℚ)=f409S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 0 (9-0) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f409_S4_amplitude_row_1 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 1 (9-1) (f409basis a) : ℚ)=f409S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 1 (9-1) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f409_S4_amplitude_row_2 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 2 (9-2) (f409basis a) : ℚ)=f409S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 2 (9-2) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f409_S4_amplitude_row_3 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 3 (9-3) (f409basis a) : ℚ)=f409S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 3 (9-3) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f409_S4_amplitude_row_4 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 4 (9-4) (f409basis a) : ℚ)=f409S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 4 (9-4) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f409_S4_amplitude_row_5 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 5 (9-5) (f409basis a) : ℚ)=f409S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 5 (9-5) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f409_S4_amplitude_row_6 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 6 (9-6) (f409basis a) : ℚ)=f409S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 6 (9-6) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f409_S4_amplitude_row_7 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 7 (9-7) (f409basis a) : ℚ)=f409S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 7 (9-7) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

private theorem f409_S4_amplitude_row_8 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 8 (9-8) (f409basis a) : ℚ)=f409S4Amplitudes 8 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 8 (9-8) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 8 a) (by decide +kernel)
  exact h 0

private theorem f409_S4_amplitude_row_9 : ∀ a : Fin 18,
    (natFourDoublePairRemoval 9 (9-9) (f409basis a) : ℚ)=f409S4Amplitudes 9 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 18) => (natFourDoublePairRemoval 9 (9-9) (f409basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 18) => f409S4Amplitudes 9 a) (by decide +kernel)
  exact h 0

theorem f409_S4_amplitudes_check : ∀ p : Fin 10, ∀ a : Fin 18,
    (natFourDoublePairRemoval p.val (9-p.val) (f409basis a) : ℚ)=f409S4Amplitudes p a := by
  intro p
  fin_cases p
  · exact f409_S4_amplitude_row_0
  · exact f409_S4_amplitude_row_1
  · exact f409_S4_amplitude_row_2
  · exact f409_S4_amplitude_row_3
  · exact f409_S4_amplitude_row_4
  · exact f409_S4_amplitude_row_5
  · exact f409_S4_amplitude_row_6
  · exact f409_S4_amplitude_row_7
  · exact f409_S4_amplitude_row_8
  · exact f409_S4_amplitude_row_9


#print axioms f409_S4_amplitudes_check

theorem f409_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 9 f409S4Amplitudes=f409rawS4Form := by
  ext a b
  rw [natFourS4AmplitudeGram_apply]
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 0 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 1 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 2 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 3 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 4 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 5 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 6 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 7 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 8 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 9 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 10 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 11 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 12 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 13 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 14 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 15 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 16 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 18) => (∑ p : Fin 10, natFourPairWeight p.val (9-p.val) * f409S4Amplitudes p 17 * f409S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 18) => (f409rawS4Form) 17 j) (by decide +kernel)
    exact h 0 b

theorem f409_actual_raw_S4_matrix (x y : Fin 18 → ℂ) :
    natOccupationInner (natFourWordBlock f409basis x)
      (canonicalNatFourS4 (natFourWordBlock f409basis y))=
      star x ⬝ᵥ (complexify f409rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 9 f409basis
    (fun a => (f409hs_shape a).1) (fun a => (f409hs_shape a).2)
    f409S4Amplitudes f409_S4_amplitudes_check f409rawS4Form f409_S4_amplitude_gram_check x y

#print axioms f409_actual_raw_S4_matrix

private def f409S4CompressionInteger : Matrix (Fin 18) (Fin 18) ℤ :=
  !![102060, 34020, 34020, 34020, 34020, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    34020, 16380, 11340, 11340, 11340, 5040, 2520, 2520, 2520, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    34020, 11340, 12600, 11340, 11340, 630, 630, 0, 0, 1260, 630, 0, 1890, 630, 630, 0, 0, 0;
    34020, 11340, 11340, 11880, 11340, 0, 270, 270, 0, 0, 270, 810, 0, 540, 0, 540, 270, 0;
    34020, 11340, 11340, 11340, 11700, 0, 0, 180, 360, 180, 180, 0, 0, 0, 360, 180, 360, 540;
    0, 5040, 630, 0, 0, 5355, 2835, 2520, 2520, 630, 315, 0, 945, 315, 315, 0, 0, 0;
    0, 2520, 630, 270, 0, 2835, 1710, 1395, 1260, 630, 450, 405, 945, 585, 315, 270, 135, 0;
    0, 2520, 0, 270, 180, 2520, 1395, 1485, 1440, 90, 225, 405, 0, 270, 180, 360, 315, 270;
    0, 2520, 0, 0, 360, 2520, 1260, 1440, 1620, 180, 180, 0, 0, 0, 360, 180, 360, 540;
    0, 0, 1260, 0, 180, 630, 630, 90, 180, 1350, 720, 0, 1890, 630, 810, 90, 180, 270;
    0, 0, 630, 270, 180, 315, 450, 225, 180, 720, 540, 405, 945, 585, 495, 360, 315, 270;
    0, 0, 0, 810, 0, 0, 405, 405, 0, 0, 405, 1215, 0, 810, 0, 810, 405, 0;
    0, 0, 1890, 0, 0, 945, 945, 0, 0, 1890, 945, 0, 2835, 945, 945, 0, 0, 0;
    0, 0, 630, 540, 0, 315, 585, 270, 0, 630, 585, 810, 945, 855, 315, 540, 270, 0;
    0, 0, 630, 0, 360, 315, 315, 180, 360, 810, 495, 0, 945, 315, 675, 180, 360, 540;
    0, 0, 0, 540, 180, 0, 270, 360, 180, 90, 360, 810, 0, 540, 180, 630, 450, 270;
    0, 0, 0, 270, 360, 0, 135, 315, 360, 180, 315, 405, 0, 270, 360, 450, 495, 540;
    0, 0, 0, 0, 540, 0, 0, 270, 540, 270, 270, 0, 0, 0, 540, 270, 540, 810]

private def f409S4CompressionCoordinates : Matrix (Fin 18) (Fin 3) ℤ :=
  !![(-4), 5, 5;
    36, (-45), (-45);
    (-80), 72, 44;
    112, (-42), (-14);
    (-56), 0, 0;
    (-64), 108, 136;
    224, (-378), (-266);
    (-448), 252, 84;
    280, 0, 0;
    0, 378, 126;
    0, (-630), (-70);
    0, 280, 0;
    0, 0, (-140);
    0, 0, 420;
    0, 0, (-140);
    0, 0, (-420);
    0, 0, 280;
    0, 0, 0]

private def f409S4CompressionLeftProduct : Matrix (Fin 3) (Fin 18) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def f409S4CompressionResult : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, 0]

theorem f409_relative_S4_compression :
    b409relativeᵀ*f409rawS4Form*b409relative=b409s := by
  have hM : natFourIntegerMatrix 2 f409S4CompressionInteger=f409rawS4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f409S4CompressionInteger) (f409rawS4Form) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 280 f409S4CompressionCoordinates=b409relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409S4CompressionCoordinates) (b409relative) (by decide +kernel) a b
  have hV : f409S4CompressionCoordinatesᵀ*f409S4CompressionInteger=f409S4CompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f409S4CompressionCoordinatesᵀ*f409S4CompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f409S4CompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f409S4CompressionCoordinatesᵀ*f409S4CompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f409S4CompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f409S4CompressionCoordinatesᵀ*f409S4CompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f409S4CompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f409S4CompressionLeftProduct*f409S4CompressionCoordinates=f409S4CompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409S4CompressionLeftProduct*f409S4CompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409S4CompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409S4CompressionLeftProduct*f409S4CompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409S4CompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409S4CompressionLeftProduct*f409S4CompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409S4CompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*2*280) f409S4CompressionResult=b409s := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*2*280) f409S4CompressionResult) (b409s) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 2 280
    f409S4CompressionInteger f409S4CompressionCoordinates f409S4CompressionLeftProduct f409S4CompressionResult
    f409rawS4Form b409relative b409s hM hD hV hY hF

theorem f409_actual_relative_S4_form (x y : Fin 3 → ℂ) :
    natOccupationInner (natFourWordBlock f409basis (complexify b409relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f409basis (complexify b409relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b409s *ᵥ y) :=
  natFour_operator_relative_matrix_form f409basis b409relative canonicalNatFourS4
    f409rawS4Form b409s f409_actual_raw_S4_matrix
    f409_relative_S4_compression x y

#print axioms f409_raw_H_matrix_check
#print axioms f409_actual_raw_H_matrix
#print axioms f409_relative_H_compression
#print axioms f409_actual_relative_H_form
#print axioms f409_S4_amplitudes_check
#print axioms f409_S4_amplitude_gram_check
#print axioms f409_actual_raw_S4_matrix
#print axioms f409_relative_S4_compression
#print axioms f409_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
