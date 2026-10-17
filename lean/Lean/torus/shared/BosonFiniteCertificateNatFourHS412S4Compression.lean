import torus.shared.BosonFiniteCertificateNatFourHS412S4Gram

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private def f412S4CompressionInteger : Matrix (Fin 34) (Fin 34) ℤ :=
  !![33679800, 11226600, 11226600, 11226600, 11226600, 11226600, 11226600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    11226600, 4989600, 3742200, 3742200, 3742200, 3742200, 3742200, 1247400, 623700, 623700, 623700, 623700, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    11226600, 3742200, 3969000, 3742200, 3742200, 3742200, 3742200, 113400, 113400, 0, 0, 0, 226800, 113400, 113400, 113400, 0, 0, 0, 340200, 113400, 113400, 113400, 113400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    11226600, 3742200, 3742200, 3810240, 3742200, 3742200, 3742200, 0, 34020, 34020, 0, 0, 0, 34020, 0, 0, 68040, 34020, 0, 0, 68040, 0, 0, 0, 68040, 34020, 34020, 0, 0, 0, 0, 0, 0, 0;
    11226600, 3742200, 3742200, 3742200, 3772440, 3742200, 3742200, 0, 0, 15120, 15120, 0, 15120, 0, 15120, 0, 0, 15120, 45360, 0, 0, 30240, 0, 0, 15120, 15120, 0, 30240, 15120, 45360, 15120, 15120, 0, 0;
    11226600, 3742200, 3742200, 3742200, 3742200, 3761100, 3742200, 0, 0, 0, 9450, 9450, 0, 9450, 0, 18900, 0, 9450, 0, 0, 0, 0, 18900, 0, 0, 9450, 9450, 0, 18900, 0, 18900, 0, 18900, 0;
    11226600, 3742200, 3742200, 3742200, 3742200, 3742200, 3774600, 0, 0, 0, 0, 16200, 0, 0, 16200, 0, 16200, 0, 0, 0, 0, 0, 0, 32400, 0, 0, 16200, 16200, 0, 0, 0, 32400, 16200, 48600;
    0, 1247400, 113400, 0, 0, 0, 0, 1304100, 680400, 623700, 623700, 623700, 113400, 56700, 56700, 56700, 0, 0, 0, 170100, 56700, 56700, 56700, 56700, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 623700, 113400, 34020, 0, 0, 0, 680400, 385560, 328860, 311850, 311850, 113400, 73710, 56700, 56700, 34020, 17010, 0, 170100, 90720, 56700, 56700, 56700, 34020, 17010, 17010, 0, 0, 0, 0, 0, 0, 0;
    0, 623700, 0, 34020, 15120, 0, 0, 623700, 328860, 336420, 319410, 311850, 7560, 17010, 7560, 0, 34020, 24570, 22680, 0, 34020, 15120, 0, 0, 41580, 24570, 17010, 15120, 7560, 22680, 7560, 7560, 0, 0;
    0, 623700, 0, 0, 15120, 9450, 0, 623700, 311850, 319410, 324135, 316575, 7560, 4725, 7560, 9450, 0, 12285, 22680, 0, 0, 15120, 9450, 0, 7560, 12285, 4725, 15120, 17010, 22680, 17010, 7560, 9450, 0;
    0, 623700, 0, 0, 0, 9450, 16200, 623700, 311850, 311850, 316575, 324675, 0, 4725, 8100, 9450, 8100, 4725, 0, 0, 0, 0, 9450, 16200, 0, 4725, 12825, 8100, 9450, 0, 9450, 16200, 17550, 24300;
    0, 0, 226800, 0, 15120, 0, 0, 113400, 113400, 7560, 7560, 0, 234360, 113400, 120960, 113400, 0, 7560, 22680, 340200, 113400, 128520, 113400, 113400, 7560, 7560, 0, 15120, 7560, 22680, 7560, 7560, 0, 0;
    0, 0, 113400, 34020, 0, 9450, 0, 56700, 73710, 17010, 4725, 4725, 113400, 78435, 56700, 66150, 34020, 21735, 0, 170100, 90720, 56700, 66150, 56700, 34020, 21735, 21735, 0, 9450, 0, 9450, 0, 9450, 0;
    0, 0, 113400, 0, 15120, 0, 16200, 56700, 56700, 7560, 7560, 8100, 120960, 56700, 72360, 56700, 8100, 7560, 22680, 170100, 56700, 71820, 56700, 72900, 7560, 7560, 8100, 23220, 7560, 22680, 7560, 23760, 8100, 24300;
    0, 0, 113400, 0, 0, 18900, 0, 56700, 56700, 0, 9450, 9450, 113400, 66150, 56700, 75600, 0, 9450, 0, 170100, 56700, 56700, 75600, 56700, 0, 9450, 9450, 0, 18900, 0, 18900, 0, 18900, 0;
    0, 0, 0, 68040, 0, 0, 16200, 0, 34020, 34020, 0, 8100, 0, 34020, 8100, 0, 76140, 34020, 0, 0, 68040, 0, 0, 16200, 68040, 34020, 42120, 8100, 0, 0, 0, 16200, 8100, 24300;
    0, 0, 0, 34020, 15120, 9450, 0, 0, 17010, 24570, 12285, 4725, 7560, 21735, 7560, 9450, 34020, 29295, 22680, 0, 34020, 15120, 9450, 0, 41580, 29295, 21735, 15120, 17010, 22680, 17010, 7560, 9450, 0;
    0, 0, 0, 0, 45360, 0, 0, 0, 0, 22680, 22680, 0, 22680, 0, 22680, 0, 0, 22680, 68040, 0, 0, 45360, 0, 0, 22680, 22680, 0, 45360, 22680, 68040, 22680, 22680, 0, 0;
    0, 0, 340200, 0, 0, 0, 0, 170100, 170100, 0, 0, 0, 340200, 170100, 170100, 170100, 0, 0, 0, 510300, 170100, 170100, 170100, 170100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 113400, 68040, 0, 0, 0, 56700, 90720, 34020, 0, 0, 113400, 90720, 56700, 56700, 68040, 34020, 0, 170100, 124740, 56700, 56700, 56700, 68040, 34020, 34020, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 113400, 0, 30240, 0, 0, 56700, 56700, 15120, 15120, 0, 128520, 56700, 71820, 56700, 0, 15120, 45360, 170100, 56700, 86940, 56700, 56700, 15120, 15120, 0, 30240, 15120, 45360, 15120, 15120, 0, 0;
    0, 0, 113400, 0, 0, 18900, 0, 56700, 56700, 0, 9450, 9450, 113400, 66150, 56700, 75600, 0, 9450, 0, 170100, 56700, 56700, 75600, 56700, 0, 9450, 9450, 0, 18900, 0, 18900, 0, 18900, 0;
    0, 0, 113400, 0, 0, 0, 32400, 56700, 56700, 0, 0, 16200, 113400, 56700, 72900, 56700, 16200, 0, 0, 170100, 56700, 56700, 56700, 89100, 0, 0, 16200, 16200, 0, 0, 0, 32400, 16200, 48600;
    0, 0, 0, 68040, 15120, 0, 0, 0, 34020, 41580, 7560, 0, 7560, 34020, 7560, 0, 68040, 41580, 22680, 0, 68040, 15120, 0, 0, 75600, 41580, 34020, 15120, 7560, 22680, 7560, 7560, 0, 0;
    0, 0, 0, 34020, 15120, 9450, 0, 0, 17010, 24570, 12285, 4725, 7560, 21735, 7560, 9450, 34020, 29295, 22680, 0, 34020, 15120, 9450, 0, 41580, 29295, 21735, 15120, 17010, 22680, 17010, 7560, 9450, 0;
    0, 0, 0, 34020, 0, 9450, 16200, 0, 17010, 17010, 4725, 12825, 0, 21735, 8100, 9450, 42120, 21735, 0, 0, 34020, 0, 9450, 16200, 34020, 21735, 29835, 8100, 9450, 0, 9450, 16200, 17550, 24300;
    0, 0, 0, 0, 30240, 0, 16200, 0, 0, 15120, 15120, 8100, 15120, 0, 23220, 0, 8100, 15120, 45360, 0, 0, 30240, 0, 16200, 15120, 15120, 8100, 38340, 15120, 45360, 15120, 31320, 8100, 24300;
    0, 0, 0, 0, 15120, 18900, 0, 0, 0, 7560, 17010, 9450, 7560, 9450, 7560, 18900, 0, 17010, 22680, 0, 0, 15120, 18900, 0, 7560, 17010, 9450, 15120, 26460, 22680, 26460, 7560, 18900, 0;
    0, 0, 0, 0, 45360, 0, 0, 0, 0, 22680, 22680, 0, 22680, 0, 22680, 0, 0, 22680, 68040, 0, 0, 45360, 0, 0, 22680, 22680, 0, 45360, 22680, 68040, 22680, 22680, 0, 0;
    0, 0, 0, 0, 15120, 18900, 0, 0, 0, 7560, 17010, 9450, 7560, 9450, 7560, 18900, 0, 17010, 22680, 0, 0, 15120, 18900, 0, 7560, 17010, 9450, 15120, 26460, 22680, 26460, 7560, 18900, 0;
    0, 0, 0, 0, 15120, 0, 32400, 0, 0, 7560, 7560, 16200, 7560, 0, 23760, 0, 16200, 7560, 22680, 0, 0, 15120, 0, 32400, 7560, 7560, 16200, 31320, 7560, 22680, 7560, 39960, 16200, 48600;
    0, 0, 0, 0, 0, 18900, 16200, 0, 0, 0, 9450, 17550, 0, 9450, 8100, 18900, 8100, 9450, 0, 0, 0, 0, 18900, 16200, 0, 9450, 17550, 8100, 18900, 0, 18900, 16200, 27000, 24300;
    0, 0, 0, 0, 0, 0, 48600, 0, 0, 0, 0, 24300, 0, 0, 24300, 0, 24300, 0, 0, 0, 0, 0, 0, 48600, 0, 0, 24300, 24300, 0, 0, 0, 48600, 24300, 72900]

private def f412S4CompressionCoordinates : Matrix (Fin 34) (Fin 7) ℤ :=
  !![15, (-15), 21, (-15), 21, 21, (-42);
    (-180), 180, (-252), 180, (-252), (-252), 504;
    990, (-495), 594, (-440), 429, 374, (-693);
    (-3300), 825, (-660), 825, (-363), (-264), 330;
    7425, (-825), 297, (-825), 99, 99, 0;
    (-11880), 330, 0, 330, 0, 0, 0;
    6930, 0, 0, 0, 0, 0, 0;
    0, (-495), 792, (-550), 957, 1012, (-2079);
    0, 2475, (-3960), 1925, (-3201), (-2948), 5940;
    0, (-4125), 4752, (-4125), 2871, 1980, (-2970);
    0, 4950, (-2376), 4950, (-792), (-792), 0;
    0, (-2310), 0, (-2310), 0, 0, 0;
    0, (-2475), 5346, 0, 2673, 1980, (-4455);
    0, 6600, (-14256), 0, (-5148), (-2112), 4752;
    0, (-11550), 8316, 0, 1386, 924, 0;
    0, 6930, 0, 0, 0, 0, 0;
    0, 0, 11088, 0, 2772, 0, (-1386);
    0, 0, (-16632), 0, (-1386), 0, 0;
    0, 0, 6930, 0, 0, 0, 0;
    0, 0, 0, 550, (-1056), (-1408), 2970;
    0, 0, 0, (-2475), 4752, 6336, (-13365);
    0, 0, 0, 6600, (-4752), (-4224), 7128;
    0, 0, 0, (-11550), 1386, 1848, 0;
    0, 0, 0, 6930, 0, 0, 0;
    0, 0, 0, 0, (-5940), (-9504), 21384;
    0, 0, 0, 0, 13860, 11088, (-24948);
    0, 0, 0, 0, (-4158), (-5544), 0;
    0, 0, 0, 0, (-11088), 0, 8316;
    0, 0, 0, 0, 6930, 0, 0;
    0, 0, 0, 0, 0, 5544, (-12474);
    0, 0, 0, 0, 0, (-11088), 24948;
    0, 0, 0, 0, 0, 6930, 0;
    0, 0, 0, 0, 0, 0, (-20790);
    0, 0, 0, 0, 0, 0, 6930]

private def f412S4CompressionLeftProduct : Matrix (Fin 7) (Fin 34) ℤ :=
  !![336798000, (-112266000), 336798000, (-112266000), 336798000, (-112266000), 336798000, (-112266000), (-112266000), (-112266000), (-112266000), (-112266000), 336798000, (-112266000), 336798000, (-112266000), (-112266000), (-112266000), 336798000, 336798000, (-112266000), 336798000, (-112266000), 336798000, (-112266000), (-112266000), (-112266000), 336798000, (-112266000), 336798000, (-112266000), 336798000, (-112266000), 336798000;
    (-336798000), 112266000, (-336798000), 112266000, (-336798000), 112266000, (-336798000), 112266000, 112266000, 112266000, 112266000, 112266000, (-336798000), 112266000, (-336798000), 112266000, 112266000, 112266000, (-336798000), (-336798000), 112266000, (-336798000), 112266000, (-336798000), 112266000, 112266000, 112266000, (-336798000), 112266000, (-336798000), 112266000, (-336798000), 112266000, (-336798000);
    471517200, (-157172400), 471517200, (-157172400), 471517200, (-157172400), 471517200, (-157172400), (-157172400), (-157172400), (-157172400), (-157172400), 471517200, (-157172400), 471517200, (-157172400), (-157172400), (-157172400), 471517200, 471517200, (-157172400), 471517200, (-157172400), 471517200, (-157172400), (-157172400), (-157172400), 471517200, (-157172400), 471517200, (-157172400), 471517200, (-157172400), 471517200;
    280665000, (-93555000), 280665000, (-93555000), 280665000, (-93555000), 280665000, (-93555000), (-93555000), (-93555000), (-93555000), (-93555000), 280665000, (-93555000), 280665000, (-93555000), (-93555000), (-93555000), 280665000, 280665000, (-93555000), 280665000, (-93555000), 280665000, (-93555000), (-93555000), (-93555000), 280665000, (-93555000), 280665000, (-93555000), 280665000, (-93555000), 280665000;
    (-269438400), 89812800, (-269438400), 89812800, (-269438400), 89812800, (-269438400), 89812800, 89812800, 89812800, 89812800, 89812800, (-269438400), 89812800, (-269438400), 89812800, 89812800, 89812800, (-269438400), (-269438400), 89812800, (-269438400), 89812800, (-269438400), 89812800, 89812800, 89812800, (-269438400), 89812800, (-269438400), 89812800, (-269438400), 89812800, (-269438400);
    224532000, (-74844000), 224532000, (-74844000), 224532000, (-74844000), 224532000, (-74844000), (-74844000), (-74844000), (-74844000), (-74844000), 224532000, (-74844000), 224532000, (-74844000), (-74844000), (-74844000), 224532000, 224532000, (-74844000), 224532000, (-74844000), 224532000, (-74844000), (-74844000), (-74844000), 224532000, (-74844000), 224532000, (-74844000), 224532000, (-74844000), 224532000;
    168399000, (-56133000), 168399000, (-56133000), 168399000, (-56133000), 168399000, (-56133000), (-56133000), (-56133000), (-56133000), (-56133000), 168399000, (-56133000), 168399000, (-56133000), (-56133000), (-56133000), 168399000, 168399000, (-56133000), 168399000, (-56133000), 168399000, (-56133000), (-56133000), (-56133000), 168399000, (-56133000), 168399000, (-56133000), 168399000, (-56133000), 168399000]

private def f412S4CompressionResult : Matrix (Fin 7) (Fin 7) ℤ :=
  !![6897623040000, (-6897623040000), 9656672256000, 5748019200000, (-5518098432000), 4598415360000, 3448811520000;
    (-6897623040000), 6897623040000, (-9656672256000), (-5748019200000), 5518098432000, (-4598415360000), (-3448811520000);
    9656672256000, (-9656672256000), 13519341158400, 8047226880000, (-7725337804800), 6437781504000, 4828336128000;
    5748019200000, (-5748019200000), 8047226880000, 4790016000000, (-4598415360000), 3832012800000, 2874009600000;
    (-5518098432000), 5518098432000, (-7725337804800), (-4598415360000), 4414478745600, (-3678732288000), (-2759049216000);
    4598415360000, (-4598415360000), 6437781504000, 3832012800000, (-3678732288000), 3065610240000, 2299207680000;
    3448811520000, (-3448811520000), 4828336128000, 2874009600000, (-2759049216000), 2299207680000, 1724405760000]

theorem f412_relative_S4_compression :
    b412relativeᵀ*f412rawS4Form*b412relative=b412s := by
  have hM : natFourIntegerMatrix 4 f412S4CompressionInteger=f412rawS4Form := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 4 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 5 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 6 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 7 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 8 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 9 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 10 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 11 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 12 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 12 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 13 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 13 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 14 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 14 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 15 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 15 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 16 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 16 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 17 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 17 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 18 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 18 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 19 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 19 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 20 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 20 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 21 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 21 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 22 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 22 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 23 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 23 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 24 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 24 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 25 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 25 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 26 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 26 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 27 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 27 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 28 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 28 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 29 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 29 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 30 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 30 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 31 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 31 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 32 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 32 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 4 f412S4CompressionInteger) 33 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 33 j) (by decide +kernel)
      exact h 0 b
  have hD : natFourIntegerMatrix 6930 f412S4CompressionCoordinates=b412relative := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 4 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 5 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 6 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 7 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 8 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 9 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 10 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 11 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 12 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 12 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 13 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 13 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 14 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 14 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 15 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 15 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 16 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 16 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 17 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 17 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 18 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 18 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 19 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 19 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 20 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 20 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 21 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 21 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 22 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 22 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 23 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 23 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 24 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 24 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 25 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 25 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 26 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 26 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 27 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 27 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 28 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 28 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 29 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 29 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 30 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 30 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 31 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 31 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 32 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 32 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 6930 f412S4CompressionCoordinates) 33 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412relative) 33 j) (by decide +kernel)
      exact h 0 b
  have hV : f412S4CompressionCoordinatesᵀ*f412S4CompressionInteger=f412S4CompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionCoordinatesᵀ*f412S4CompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionCoordinatesᵀ*f412S4CompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionCoordinatesᵀ*f412S4CompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionCoordinatesᵀ*f412S4CompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionCoordinatesᵀ*f412S4CompressionInteger) 4 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionLeftProduct) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionCoordinatesᵀ*f412S4CompressionInteger) 5 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionLeftProduct) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionCoordinatesᵀ*f412S4CompressionInteger) 6 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4CompressionLeftProduct) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f412S4CompressionLeftProduct*f412S4CompressionCoordinates=f412S4CompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionLeftProduct*f412S4CompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionLeftProduct*f412S4CompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionLeftProduct*f412S4CompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionLeftProduct*f412S4CompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionResult) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionLeftProduct*f412S4CompressionCoordinates) 4 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionResult) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionLeftProduct*f412S4CompressionCoordinates) 5 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionResult) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionLeftProduct*f412S4CompressionCoordinates) 6 j)
        (fun (_ : Fin 1) (j : Fin 7) => (f412S4CompressionResult) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6930*4*6930) f412S4CompressionResult=b412s := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412S4CompressionResult) 0 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412s) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412S4CompressionResult) 1 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412s) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412S4CompressionResult) 2 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412s) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412S4CompressionResult) 3 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412s) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412S4CompressionResult) 4 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412s) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412S4CompressionResult) 5 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412s) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (6930*4*6930) f412S4CompressionResult) 6 j)
        (fun (_ : Fin 1) (j : Fin 7) => (b412s) 6 j) (by decide +kernel)
      exact h 0 b
  exact natFourIntegerMatrix_compression_check_staged 4 6930
    f412S4CompressionInteger f412S4CompressionCoordinates f412S4CompressionLeftProduct f412S4CompressionResult
    f412rawS4Form b412relative b412s hM hD hV hY hF

theorem f412_actual_relative_S4_form (x y : Fin 7 → ℂ) :
    natOccupationInner (natFourWordBlock f412basis (complexify b412relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f412basis (complexify b412relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b412s *ᵥ y) :=
  natFour_operator_relative_matrix_form f412basis b412relative canonicalNatFourS4
    f412rawS4Form b412s f412_actual_raw_S4_matrix
    f412_relative_S4_compression x y

#print axioms f412_relative_S4_compression
#print axioms f412_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
