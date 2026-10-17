import torus.shared.BosonFiniteCertificateNatFourHS410Data
import torus.shared.BosonFiniteCertificateNatFourHS410HRows0
import torus.shared.BosonFiniteCertificateNatFourHS410HRows1
import torus.shared.BosonFiniteCertificateNatFourHS410HRows2
import torus.shared.BosonFiniteCertificateNatFourHS410HRows3

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



private theorem f410hs_shape (a : Fin 23) :
    (f410basis a).length=4 ∧ (f410basis a).sum=10 := by
  apply natFourBasis_shape 10
  rw [← f410_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f410_raw_H_matrix_check : ∀ a b : Fin 23,
    natFourHWordForm 10 (f410basis a) (f410basis b)=f410rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f410_H_rows_0 0 b (by decide) (by decide)
  · exact f410_H_rows_0 1 b (by decide) (by decide)
  · exact f410_H_rows_0 2 b (by decide) (by decide)
  · exact f410_H_rows_0 3 b (by decide) (by decide)
  · exact f410_H_rows_0 4 b (by decide) (by decide)
  · exact f410_H_rows_0 5 b (by decide) (by decide)
  · exact f410_H_rows_1 6 b (by decide) (by decide)
  · exact f410_H_rows_1 7 b (by decide) (by decide)
  · exact f410_H_rows_1 8 b (by decide) (by decide)
  · exact f410_H_rows_1 9 b (by decide) (by decide)
  · exact f410_H_rows_1 10 b (by decide) (by decide)
  · exact f410_H_rows_1 11 b (by decide) (by decide)
  · exact f410_H_rows_2 12 b (by decide) (by decide)
  · exact f410_H_rows_2 13 b (by decide) (by decide)
  · exact f410_H_rows_2 14 b (by decide) (by decide)
  · exact f410_H_rows_2 15 b (by decide) (by decide)
  · exact f410_H_rows_2 16 b (by decide) (by decide)
  · exact f410_H_rows_2 17 b (by decide) (by decide)
  · exact f410_H_rows_3 18 b (by decide) (by decide)
  · exact f410_H_rows_3 19 b (by decide) (by decide)
  · exact f410_H_rows_3 20 b (by decide) (by decide)
  · exact f410_H_rows_3 21 b (by decide) (by decide)
  · exact f410_H_rows_3 22 b (by decide) (by decide)


theorem f410_actual_raw_H_matrix (x y : Fin 23 → ℂ) :
    natOccupationInner (natFourWordBlock f410basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f410basis y))=
      star x ⬝ᵥ (complexify f410rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 10 f410basis (fun a => (f410hs_shape a).2)
    f410rawHForm f410_raw_H_matrix_check x y

#print axioms f410_actual_raw_H_matrix

private def f410HCompressionInteger : Matrix (Fin 23) (Fin 23) ℤ :=
  !![130891950, 85050, 85050, 85050, 85050, 85050, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    85050, 4394250, 28350, 28350, 28350, 28350, 11340, 5670, 5670, 5670, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    85050, 28350, 678510, 28350, 28350, 28350, 161280, 2520, 0, 0, 5040, 2520, 2520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    85050, 28350, 28350, 213570, 28350, 28350, 0, 30240, 1890, 0, 0, 1890, 0, 3780, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    85050, 28350, 28350, 28350, 119070, 28350, 0, 0, 8640, 2160, 8640, 0, 4320, 2160, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    85050, 28350, 28350, 28350, 28350, 172350, 0, 0, 0, 7200, 0, 7200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 11340, 161280, 0, 0, 0, 415800, 5670, 5670, 5670, 0, 0, 0, 0, 3780, 1260, 1260, 1260, 0, 0, 0, 0, 0;
    0, 5670, 2520, 30240, 0, 0, 5670, 49770, 2835, 2835, 2520, 1260, 1260, 0, 30240, 630, 0, 0, 630, 315, 0, 0, 0;
    0, 5670, 0, 1890, 8640, 0, 5670, 2835, 19170, 2835, 4320, 945, 0, 1890, 0, 4320, 540, 0, 0, 270, 810, 0, 0;
    0, 5670, 0, 0, 2160, 7200, 5670, 2835, 2835, 12555, 0, 1800, 2160, 1080, 0, 0, 1440, 1440, 720, 360, 0, 0, 0;
    0, 0, 5040, 0, 8640, 0, 0, 2520, 4320, 0, 21240, 2520, 2520, 0, 0, 5760, 0, 0, 360, 0, 0, 1080, 360;
    0, 0, 2520, 1890, 0, 7200, 0, 1260, 945, 1800, 2520, 6345, 1260, 1890, 0, 0, 1440, 0, 1440, 180, 0, 0, 720;
    0, 0, 2520, 0, 4320, 0, 0, 1260, 0, 2160, 2520, 1260, 9036, 2160, 0, 0, 0, 2304, 0, 576, 0, 1728, 0;
    0, 0, 0, 3780, 2160, 0, 0, 0, 1890, 1080, 0, 1890, 2160, 7020, 0, 0, 0, 0, 0, 864, 1296, 0, 432;
    0, 0, 0, 0, 0, 0, 3780, 30240, 0, 0, 0, 0, 0, 0, 102060, 3780, 3780, 3780, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1260, 630, 4320, 0, 5760, 0, 0, 0, 3780, 14040, 1260, 1260, 1260, 630, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1260, 0, 540, 1440, 0, 1440, 0, 0, 3780, 1260, 6660, 1260, 1440, 540, 1620, 0, 0;
    0, 0, 0, 0, 0, 0, 1260, 0, 0, 1440, 0, 0, 2304, 0, 3780, 1260, 1260, 9324, 0, 1440, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 630, 0, 720, 360, 1440, 0, 0, 0, 1260, 1440, 0, 5220, 630, 0, 1080, 360;
    0, 0, 0, 0, 0, 0, 0, 315, 270, 360, 0, 180, 576, 864, 0, 630, 540, 1440, 630, 1845, 810, 864, 720;
    0, 0, 0, 0, 0, 0, 0, 0, 810, 0, 0, 0, 0, 1296, 0, 0, 1620, 0, 0, 810, 6318, 0, 1296;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1080, 0, 1728, 0, 0, 0, 0, 0, 1080, 864, 0, 5832, 1080;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 360, 720, 0, 432, 0, 0, 0, 0, 360, 720, 1296, 1080, 3672]

private def f410HCompressionCoordinates : Matrix (Fin 23) (Fin 5) ℤ :=
  !![(-10), 10, 10, (-15), (-15);
    100, (-100), (-100), 150, 150;
    (-450), 198, 162, (-189), (-153);
    1200, (-192), (-192), 99, 36;
    (-2100), 84, 84, 0, 0;
    1260, 0, 0, 0, 0;
    0, 252, 288, (-486), (-522);
    0, (-1008), (-720), 1215, 1116;
    0, 1008, 1008, (-693), (-252);
    0, (-504), (-504), 0, 0;
    0, 1008, 0, (-756), (-630);
    0, (-2016), 0, 945, 252;
    0, 1260, 0, 0, 0;
    0, 0, 0, (-315), 0;
    0, 0, (-288), 486, 648;
    0, 0, 1008, (-1701), (-2268);
    0, 0, (-2016), 1134, 504;
    0, 0, 1260, 0, 0;
    0, 0, 0, 1701, 3024;
    0, 0, 0, (-2835), (-1260);
    0, 0, 0, 1260, 0;
    0, 0, 0, 0, (-1890);
    0, 0, 0, 0, 1260]

private def f410HCompressionLeftProduct : Matrix (Fin 5) (Fin 23) ℤ :=
  !![(-1308069000), 436023000, (-293139000), 221697000, (-191079000), 180873000, (-71442000), 35721000, (-15309000), 5103000, (-20412000), 10206000, (-10206000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1308069000, (-436023000), 170576280, (-67382280), 29960280, (-17577000), 132723360, (-51597000), 18711000, (-6191640), 23042880, (-9752400), 9888480, (-272160), (-29529360), 9843120, (-2766960), 2494800, (-3538080), 136080, 816480, 3265920, (-1088640);
    1305007200, (-435002400), 149506560, (-55883520), 14787360, (-4082400), 142747920, (-46811520), 20548080, (-5352480), 9888480, (-3719520), 1678320, 816480, (-49124880), 16374960, (-11476080), 9026640, (-2449440), 1224720, (-2449440), 0, 0;
    (-1958276250), 652758750, (-199204110), 54789210, (-12774510), 7229250, (-226777320), 72207450, (-21007350), 2772630, (-23745960), 7654500, (-1973160), (-2177280), 82362420, (-27454140), 10580220, (-3572100), 8436960, (-3504060), 6531840, (-1428840), 476280;
    (-1960572600), 653524200, (-183730680), 40075560, (-7960680), 1474200, (-234896760), 71827560, (-16057440), 3243240, (-25356240), 6622560, (-4241160), (-408240), 91241640, (-30413880), 6191640, (-2245320), 12111120, (-1973160), 1224720, (-8164800), 2721600]

private def f410HCompressionResult : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1083797820000, (-299364660000), (-227085768000), 276182865000, 234302544000;
    (-299364660000), 268696038240, 224273810880, (-330253028280), (-323370714240);
    (-227085768000), 224273810880, 256131227520, (-345821056560), (-332518556160);
    276182865000, (-330253028280), (-345821056560), 539977874310, 535080984480;
    234302544000, (-323370714240), (-332518556160), 535080984480, 570650935680]

theorem f410_relative_H_compression :
    b410relativeᵀ*f410rawHForm*b410relative=b410h := by
  have hM : natFourIntegerMatrix 2 f410HCompressionInteger=f410rawHForm := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f410HCompressionInteger) (f410rawHForm) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 1260 f410HCompressionCoordinates=b410relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1260 f410HCompressionCoordinates) (b410relative) (by decide +kernel) a b
  have hV : f410HCompressionCoordinatesᵀ*f410HCompressionInteger=f410HCompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionCoordinatesᵀ*f410HCompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionCoordinatesᵀ*f410HCompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionCoordinatesᵀ*f410HCompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionCoordinatesᵀ*f410HCompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionCoordinatesᵀ*f410HCompressionInteger) 4 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410HCompressionLeftProduct) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f410HCompressionLeftProduct*f410HCompressionCoordinates=f410HCompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionLeftProduct*f410HCompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionLeftProduct*f410HCompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionLeftProduct*f410HCompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionLeftProduct*f410HCompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionResult) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionLeftProduct*f410HCompressionCoordinates) 4 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410HCompressionResult) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1260*2*1260) f410HCompressionResult=b410h := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1260*2*1260) f410HCompressionResult) (b410h) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 2 1260
    f410HCompressionInteger f410HCompressionCoordinates f410HCompressionLeftProduct f410HCompressionResult
    f410rawHForm b410relative b410h hM hD hV hY hF

theorem f410_actual_relative_H_form (x y : Fin 5 → ℂ) :
    natOccupationInner (natFourWordBlock f410basis (complexify b410relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f410basis (complexify b410relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b410h *ᵥ y) :=
  natFour_operator_relative_matrix_form f410basis b410relative canonicalPairHamiltonianNat
    f410rawHForm b410h f410_actual_raw_H_matrix
    f410_relative_H_compression x y

#print axioms f410_actual_relative_H_form


private theorem f410_S4_amplitude_row_0 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 0 (10-0) (f410basis a) : ℚ)=f410S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 0 (10-0) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_1 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 1 (10-1) (f410basis a) : ℚ)=f410S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 1 (10-1) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_2 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 2 (10-2) (f410basis a) : ℚ)=f410S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 2 (10-2) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_3 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 3 (10-3) (f410basis a) : ℚ)=f410S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 3 (10-3) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_4 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 4 (10-4) (f410basis a) : ℚ)=f410S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 4 (10-4) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_5 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 5 (10-5) (f410basis a) : ℚ)=f410S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 5 (10-5) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_6 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 6 (10-6) (f410basis a) : ℚ)=f410S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 6 (10-6) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_7 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 7 (10-7) (f410basis a) : ℚ)=f410S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 7 (10-7) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_8 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 8 (10-8) (f410basis a) : ℚ)=f410S4Amplitudes 8 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 8 (10-8) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 8 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_9 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 9 (10-9) (f410basis a) : ℚ)=f410S4Amplitudes 9 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 9 (10-9) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 9 a) (by decide +kernel)
  exact h 0

private theorem f410_S4_amplitude_row_10 : ∀ a : Fin 23,
    (natFourDoublePairRemoval 10 (10-10) (f410basis a) : ℚ)=f410S4Amplitudes 10 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 23) => (natFourDoublePairRemoval 10 (10-10) (f410basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 23) => f410S4Amplitudes 10 a) (by decide +kernel)
  exact h 0

theorem f410_S4_amplitudes_check : ∀ p : Fin 11, ∀ a : Fin 23,
    (natFourDoublePairRemoval p.val (10-p.val) (f410basis a) : ℚ)=f410S4Amplitudes p a := by
  intro p
  fin_cases p
  · exact f410_S4_amplitude_row_0
  · exact f410_S4_amplitude_row_1
  · exact f410_S4_amplitude_row_2
  · exact f410_S4_amplitude_row_3
  · exact f410_S4_amplitude_row_4
  · exact f410_S4_amplitude_row_5
  · exact f410_S4_amplitude_row_6
  · exact f410_S4_amplitude_row_7
  · exact f410_S4_amplitude_row_8
  · exact f410_S4_amplitude_row_9
  · exact f410_S4_amplitude_row_10


#print axioms f410_S4_amplitudes_check

theorem f410_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 10 f410S4Amplitudes=f410rawS4Form := by
  ext a b
  rw [natFourS4AmplitudeGram_apply]
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 0 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 1 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 2 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 3 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 4 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 5 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 6 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 7 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 8 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 9 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 10 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 11 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 12 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 13 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 14 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 15 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 16 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 17 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 18 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 19 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 20 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 21 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 23) => (∑ p : Fin 11, natFourPairWeight p.val (10-p.val) * f410S4Amplitudes p 22 * f410S4Amplitudes p j))
      (fun (_ : Fin 1) (j : Fin 23) => (f410rawS4Form) 22 j) (by decide +kernel)
    exact h 0 b

theorem f410_actual_raw_S4_matrix (x y : Fin 23 → ℂ) :
    natOccupationInner (natFourWordBlock f410basis x)
      (canonicalNatFourS4 (natFourWordBlock f410basis y))=
      star x ⬝ᵥ (complexify f410rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 10 f410basis
    (fun a => (f410hs_shape a).1) (fun a => (f410hs_shape a).2)
    f410S4Amplitudes f410_S4_amplitudes_check f410rawS4Form f410_S4_amplitude_gram_check x y

#print axioms f410_actual_raw_S4_matrix

private def f410S4CompressionInteger : Matrix (Fin 23) (Fin 23) ℤ :=
  !![1020600, 340200, 340200, 340200, 340200, 340200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    340200, 158760, 113400, 113400, 113400, 113400, 45360, 22680, 22680, 22680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    340200, 113400, 123480, 113400, 113400, 113400, 5040, 5040, 0, 0, 10080, 5040, 5040, 0, 15120, 5040, 5040, 5040, 0, 0, 0, 0, 0;
    340200, 113400, 113400, 117180, 113400, 113400, 0, 1890, 1890, 0, 0, 1890, 0, 3780, 0, 3780, 0, 0, 3780, 1890, 0, 0, 0;
    340200, 113400, 113400, 113400, 115560, 113400, 0, 0, 1080, 1080, 1080, 0, 2160, 1080, 0, 0, 2160, 0, 1080, 1080, 3240, 3240, 1080;
    340200, 113400, 113400, 113400, 113400, 117000, 0, 0, 0, 1800, 0, 1800, 0, 0, 0, 0, 0, 3600, 0, 1800, 0, 0, 3600;
    0, 45360, 5040, 0, 0, 0, 47880, 25200, 22680, 22680, 5040, 2520, 2520, 0, 7560, 2520, 2520, 2520, 0, 0, 0, 0, 0;
    0, 22680, 5040, 1890, 0, 0, 25200, 14805, 12285, 11340, 5040, 3465, 2520, 1890, 7560, 4410, 2520, 2520, 1890, 945, 0, 0, 0;
    0, 22680, 0, 1890, 1080, 0, 22680, 12285, 12825, 11880, 540, 945, 1080, 2430, 0, 1890, 1080, 0, 2430, 1485, 1620, 1620, 540;
    0, 22680, 0, 0, 1080, 1800, 22680, 11340, 11880, 12780, 540, 900, 1080, 540, 0, 0, 1080, 1800, 540, 1440, 1620, 1620, 2340;
    0, 0, 10080, 0, 1080, 0, 5040, 5040, 540, 540, 10620, 5040, 6120, 540, 15120, 5040, 6120, 5040, 540, 540, 1620, 1620, 540;
    0, 0, 5040, 1890, 0, 1800, 2520, 3465, 945, 900, 5040, 4365, 2520, 1890, 7560, 4410, 2520, 4320, 1890, 1845, 0, 0, 1800;
    0, 0, 5040, 0, 2160, 0, 2520, 2520, 1080, 1080, 6120, 2520, 4680, 1080, 7560, 2520, 4680, 2520, 1080, 1080, 3240, 3240, 1080;
    0, 0, 0, 3780, 1080, 0, 0, 1890, 2430, 540, 540, 1890, 1080, 4320, 0, 3780, 1080, 0, 4320, 2430, 1620, 1620, 540;
    0, 0, 15120, 0, 0, 0, 7560, 7560, 0, 0, 15120, 7560, 7560, 0, 22680, 7560, 7560, 7560, 0, 0, 0, 0, 0;
    0, 0, 5040, 3780, 0, 0, 2520, 4410, 1890, 0, 5040, 4410, 2520, 3780, 7560, 6300, 2520, 2520, 3780, 1890, 0, 0, 0;
    0, 0, 5040, 0, 2160, 0, 2520, 2520, 1080, 1080, 6120, 2520, 4680, 1080, 7560, 2520, 4680, 2520, 1080, 1080, 3240, 3240, 1080;
    0, 0, 5040, 0, 0, 3600, 2520, 2520, 0, 1800, 5040, 4320, 2520, 0, 7560, 2520, 2520, 6120, 0, 1800, 0, 0, 3600;
    0, 0, 0, 3780, 1080, 0, 0, 1890, 2430, 540, 540, 1890, 1080, 4320, 0, 3780, 1080, 0, 4320, 2430, 1620, 1620, 540;
    0, 0, 0, 1890, 1080, 1800, 0, 945, 1485, 1440, 540, 1845, 1080, 2430, 0, 1890, 1080, 1800, 2430, 2385, 1620, 1620, 2340;
    0, 0, 0, 0, 3240, 0, 0, 0, 1620, 1620, 1620, 0, 3240, 1620, 0, 0, 3240, 0, 1620, 1620, 4860, 4860, 1620;
    0, 0, 0, 0, 3240, 0, 0, 0, 1620, 1620, 1620, 0, 3240, 1620, 0, 0, 3240, 0, 1620, 1620, 4860, 4860, 1620;
    0, 0, 0, 0, 1080, 3600, 0, 0, 540, 2340, 540, 1800, 1080, 540, 0, 0, 1080, 3600, 540, 2340, 1620, 1620, 4140]

private def f410S4CompressionCoordinates : Matrix (Fin 23) (Fin 5) ℤ :=
  !![(-10), 10, 10, (-15), (-15);
    100, (-100), (-100), 150, 150;
    (-450), 198, 162, (-189), (-153);
    1200, (-192), (-192), 99, 36;
    (-2100), 84, 84, 0, 0;
    1260, 0, 0, 0, 0;
    0, 252, 288, (-486), (-522);
    0, (-1008), (-720), 1215, 1116;
    0, 1008, 1008, (-693), (-252);
    0, (-504), (-504), 0, 0;
    0, 1008, 0, (-756), (-630);
    0, (-2016), 0, 945, 252;
    0, 1260, 0, 0, 0;
    0, 0, 0, (-315), 0;
    0, 0, (-288), 486, 648;
    0, 0, 1008, (-1701), (-2268);
    0, 0, (-2016), 1134, 504;
    0, 0, 1260, 0, 0;
    0, 0, 0, 1701, 3024;
    0, 0, 0, (-2835), (-1260);
    0, 0, 0, 1260, 0;
    0, 0, 0, 0, (-1890);
    0, 0, 0, 0, 1260]

private def f410S4CompressionLeftProduct : Matrix (Fin 5) (Fin 23) ℤ :=
  !![(-6804000), 2268000, (-6804000), 2268000, (-6804000), 2268000, 2268000, 2268000, 2268000, 2268000, (-6804000), 2268000, (-6804000), 2268000, (-6804000), 2268000, (-6804000), 2268000, 2268000, 2268000, (-6804000), (-6804000), 2268000;
    6804000, (-2268000), 6804000, (-2268000), 6804000, (-2268000), (-2268000), (-2268000), (-2268000), (-2268000), 6804000, (-2268000), 6804000, (-2268000), 6804000, (-2268000), 6804000, (-2268000), (-2268000), (-2268000), 6804000, 6804000, (-2268000);
    (-5443200), 1814400, (-5443200), 1814400, (-5443200), 1814400, 1814400, 1814400, 1814400, 1814400, (-5443200), 1814400, (-5443200), 1814400, (-5443200), 1814400, (-5443200), 1814400, 1814400, 1814400, (-5443200), (-5443200), 1814400;
    5103000, (-1701000), 5103000, (-1701000), 5103000, (-1701000), (-1701000), (-1701000), (-1701000), (-1701000), 5103000, (-1701000), 5103000, (-1701000), 5103000, (-1701000), 5103000, (-1701000), (-1701000), (-1701000), 5103000, 5103000, (-1701000);
    (-4082400), 1360800, (-4082400), 1360800, (-4082400), 1360800, 1360800, 1360800, 1360800, 1360800, (-4082400), 1360800, (-4082400), 1360800, (-4082400), 1360800, (-4082400), 1360800, 1360800, 1360800, (-4082400), (-4082400), 1360800]

private def f410S4CompressionResult : Matrix (Fin 5) (Fin 5) ℤ :=
  !![23224320000, (-23224320000), 18579456000, (-17418240000), 13934592000;
    (-23224320000), 23224320000, (-18579456000), 17418240000, (-13934592000);
    18579456000, (-18579456000), 14863564800, (-13934592000), 11147673600;
    (-17418240000), 17418240000, (-13934592000), 13063680000, (-10450944000);
    13934592000, (-13934592000), 11147673600, (-10450944000), 8360755200]

theorem f410_relative_S4_compression :
    b410relativeᵀ*f410rawS4Form*b410relative=b410s := by
  have hM : natFourIntegerMatrix 4 f410S4CompressionInteger=f410rawS4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 4 f410S4CompressionInteger) (f410rawS4Form) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 1260 f410S4CompressionCoordinates=b410relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1260 f410S4CompressionCoordinates) (b410relative) (by decide +kernel) a b
  have hV : f410S4CompressionCoordinatesᵀ*f410S4CompressionInteger=f410S4CompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionCoordinatesᵀ*f410S4CompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionCoordinatesᵀ*f410S4CompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionCoordinatesᵀ*f410S4CompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionCoordinatesᵀ*f410S4CompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionCoordinatesᵀ*f410S4CompressionInteger) 4 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f410S4CompressionLeftProduct) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f410S4CompressionLeftProduct*f410S4CompressionCoordinates=f410S4CompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionLeftProduct*f410S4CompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionLeftProduct*f410S4CompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionLeftProduct*f410S4CompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionLeftProduct*f410S4CompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionResult) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionLeftProduct*f410S4CompressionCoordinates) 4 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410S4CompressionResult) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1260*4*1260) f410S4CompressionResult=b410s := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1260*4*1260) f410S4CompressionResult) (b410s) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 4 1260
    f410S4CompressionInteger f410S4CompressionCoordinates f410S4CompressionLeftProduct f410S4CompressionResult
    f410rawS4Form b410relative b410s hM hD hV hY hF

theorem f410_actual_relative_S4_form (x y : Fin 5 → ℂ) :
    natOccupationInner (natFourWordBlock f410basis (complexify b410relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f410basis (complexify b410relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b410s *ᵥ y) :=
  natFour_operator_relative_matrix_form f410basis b410relative canonicalNatFourS4
    f410rawS4Form b410s f410_actual_raw_S4_matrix
    f410_relative_S4_compression x y

#print axioms f410_raw_H_matrix_check
#print axioms f410_actual_raw_H_matrix
#print axioms f410_relative_H_compression
#print axioms f410_actual_relative_H_form
#print axioms f410_S4_amplitudes_check
#print axioms f410_S4_amplitude_gram_check
#print axioms f410_actual_raw_S4_matrix
#print axioms f410_relative_S4_compression
#print axioms f410_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
