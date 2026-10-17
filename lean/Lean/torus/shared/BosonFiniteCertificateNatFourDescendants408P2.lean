import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger410
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate408

/-! Genuine Nat COM descendants of the original relative basis, with every
step checked against independently verified raising actions and every form
checked against independently reconstructed raw source M4 matrices. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f408desc2Form : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(-56932673107389063484592553/68359375000000000000000), (2702036920715715603372972927/1093750000000000000000000), (1856057551087540075777585233/1093750000000000000000000), (-520108079492705190931672873/136718750000000000000000);
    (2702036920715715603372972927/1093750000000000000000000), (-69751664519739557959755459/78125000000000000000000), (-828811924158031845015328059/546875000000000000000000), (1941761680479152666340613713/1093750000000000000000000);
    (1856057551087540075777585233/1093750000000000000000000), (-828811924158031845015328059/546875000000000000000000), (-4246979099475647155320911049/2734375000000000000000000), (1984381069214157658929786721/781250000000000000000000);
    (-520108079492705190931672873/136718750000000000000000), (1941761680479152666340613713/1093750000000000000000000), (1984381069214157658929786721/781250000000000000000000), (-414835837969474668288634763/128173828125000000000000)]

private def f408desc2IntegerCoordinates : Matrix (Fin 23) (Fin 4) ℤ :=
  !![6, (-6), (-6), 10;
    (-12), 12, 12, (-20);
    90, 15, 36, (-74);
    (-48), (-57), (-15), 32;
    (-84), (-21), 0, 56;
    84, 21, 21, 0;
    (-156), 51, 30, (-36);
    384, (-69), (-195), 304;
    (-672), 147, (-63), 0;
    336, 84, (-42), (-336);
    336, (-21), 42, 28;
    (-672), (-63), 399, (-448);
    420, (-420), (-210), 280;
    0, 315, (-105), 280;
    (-96), (-114), (-30), 64;
    336, (-21), 105, (-224);
    (-672), 462, 378, (-224);
    420, (-210), (-105), 560;
    0, 315, 63, (-392);
    0, (-735), (-525), 560;
    0, 420, 420, (-1120);
    0, (-315), (-630), 980;
    0, 210, 420, (-280)]

private def f408desc2IntegerLeftProduct : Matrix (Fin 4) (Fin 23) ℤ :=
  !![0, 0, 14640085021576795759395002880, 117424463609359554370064471808, (-176673319640076949400434505472), 762892483347803078936839641600, 3061180551628370458517852160, 209300313917738032539391376640, 105678921129051911016207147264, 191047375399599951180200037504, (-20924084910023141768573460480), 103017293853097969223229916800, (-9773354626640869377079217664), 49209165576310611202730827776, 73167125888101310604766886400, 68784801559360100622220976640, 120010879372672640927005862400, (-94000099515776103139960891392), (-4583573591050880759147420160), 26731191526202797498261661184, 20602058582119080693567596544, (-21047241031021443887756305920), 24979238155543946592267919872;
    0, 0, 90923843642174226770357718720, (-241746371264701749541588149888), (-135500668624581697605966098688), (-213671848034839379857905830400), (-149754587741017723539855360), 4468761222193234695189101760, (-5045757608834949610944350784), (-19080751973963592447019577664), (-6512400103163985464800504320), (-64270380447210980330376638400), 32767522170992691101233591104, (-35808765485656696327305426816), (-4417963795103425676696160000), (-3339685246389875018529661440), (-55413614635273508919288960960), 13577918181420179297130083712, (-9572644202508471446874541440), (-34075003962240843364296218304), (-28262781493625735012850251904), 22293970382738954244863966400, (-21983393328212286061298790912);
    0, 0, 95376577742229419877233563200, 939177142978998076259460480, (-173753040871350640404169118208), (-158970848362003135690031243520), (-2390389746838833583268490240), (-20744479880817064358731536960), (-4212340560094037718535051392), (-67611570682147972456854124224), (-20387241103015629020347263360), (-53212963894401141393929397504), 41219799164988111805949292096, (-26730690678290557188525612672), (-6340373824859117083865784960), (-8600725058452198344951258240), (-55519076590968275228854327680), 26872697736370593993248493696, (-12119755259694310947174326400), (-25771913299353397727395753920), (-39691610182681379985387612672), 14837012283254000047056598464, (-23679572101224536768060740608);
    0, 0, (-98517776757026630186678584320), 301001330542684006148467131648, 273786681787672167449563127040, 259314775059872764412262266880, 3356129325333091407997317120, 17602863313717290994219457280, 3618878358156525668206973952, 43405734258186207150536568960, 19518767648800110980907932160, 88084225269001892956657424256, (-72890042517905796863933342208), 30127729541185171663765899264, 12357384844718049854446794240, 4953479105853220638906124800, 95903324914615508472551297280, (-34302515136177913215447361536), 4879922730632815008531459840, 40444254667298804252210525184, 55850318169048116212499384832, (-22026233607562774724952070656), 36890306019483207257574633984]

private def f408desc2IntegerForm : Matrix (Fin 4) (Fin 4) ℤ :=
  !![(-36728406075038832635180347791360), 108946128643257653127998268416640, 74836240459849615855352236594560, (-167766062121166986386920401914880);
    108946128643257653127998268416640, (-39373419588102585677122761496320), (-66835393564103687982036054677760), 78291830956919435506853544908160;
    74836240459849615855352236594560, (-66835393564103687982036054677760), (-68495278916343237321015653398272), 112014342595000771531268600827008;
    (-167766062121166986386920401914880), 78291830956919435506853544908160, 112014342595000771531268600827008, (-142730077755129332270060831096832)]

theorem f408desc2_compression_check :
    f408desc2ᵀ*f410rawM4Form*f408desc2=f408desc2Form := by
  have hD : natFourIntegerMatrix 210 f408desc2IntegerCoordinates=f408desc2 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 210 f408desc2IntegerCoordinates) (f408desc2) (by decide +kernel) a b
  have hV : f408desc2IntegerCoordinatesᵀ*f410rawInteger=f408desc2IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f408desc2IntegerCoordinatesᵀ*f410rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f408desc2IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f408desc2IntegerCoordinatesᵀ*f410rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f408desc2IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f408desc2IntegerCoordinatesᵀ*f410rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f408desc2IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f408desc2IntegerCoordinatesᵀ*f410rawInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f408desc2IntegerLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f408desc2IntegerLeftProduct*f408desc2IntegerCoordinates=f408desc2IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc2IntegerLeftProduct*f408desc2IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc2IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc2IntegerLeftProduct*f408desc2IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc2IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc2IntegerLeftProduct*f408desc2IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc2IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc2IntegerLeftProduct*f408desc2IntegerCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc2IntegerForm) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc2IntegerForm=f408desc2Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc2IntegerForm) (f408desc2Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 210
    f410rawInteger f408desc2IntegerCoordinates f408desc2IntegerLeftProduct f408desc2IntegerForm
    f410rawM4Form f408desc2 f408desc2Form f410_raw_integer_check hD hV hY hF

theorem f408desc2_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f408basis (complexify b408relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f408basis (complexify b408relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f408desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f408basis b408relative
    f410basis f408desc2 f410rawM4Form f408desc2Form
    f408desc2_actual f410_actual_raw_M4_matrix f408desc2_compression_check x y


#print axioms f408desc2_compression_check
#print axioms f408desc2_source_form
end TorusLean.BosonFiniteCertificate
