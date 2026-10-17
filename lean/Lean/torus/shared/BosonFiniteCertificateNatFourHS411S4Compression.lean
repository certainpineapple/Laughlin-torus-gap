import torus.shared.BosonFiniteCertificateNatFourHS411S4Gram

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private def f411S4CompressionInteger : Matrix (Fin 27) (Fin 27) ℤ :=
  !![2806650, 935550, 935550, 935550, 935550, 935550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    935550, 425250, 311850, 311850, 311850, 311850, 113400, 56700, 56700, 56700, 56700, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    935550, 311850, 334530, 311850, 311850, 311850, 11340, 11340, 0, 0, 0, 22680, 11340, 11340, 0, 0, 34020, 11340, 11340, 11340, 0, 0, 0, 0, 0, 0, 0;
    935550, 311850, 311850, 319410, 311850, 311850, 0, 3780, 3780, 0, 0, 0, 3780, 0, 7560, 3780, 0, 7560, 0, 0, 7560, 3780, 3780, 0, 0, 0, 0;
    935550, 311850, 311850, 311850, 315630, 311850, 0, 0, 1890, 1890, 0, 1890, 0, 1890, 0, 3780, 0, 0, 3780, 0, 1890, 1890, 0, 3780, 5670, 1890, 0;
    935550, 311850, 311850, 311850, 311850, 314550, 0, 0, 0, 1350, 2700, 0, 1350, 1350, 1350, 0, 0, 0, 0, 2700, 0, 1350, 2700, 1350, 0, 2700, 4050;
    0, 113400, 11340, 0, 0, 0, 119070, 62370, 56700, 56700, 56700, 11340, 5670, 5670, 0, 0, 17010, 5670, 5670, 5670, 0, 0, 0, 0, 0, 0, 0;
    0, 56700, 11340, 3780, 0, 0, 62370, 35910, 30240, 28350, 28350, 11340, 7560, 5670, 3780, 1890, 17010, 9450, 5670, 5670, 3780, 1890, 1890, 0, 0, 0, 0;
    0, 56700, 0, 3780, 1890, 0, 56700, 30240, 31185, 29295, 28350, 945, 1890, 945, 3780, 3780, 0, 3780, 1890, 0, 4725, 2835, 1890, 1890, 2835, 945, 0;
    0, 56700, 0, 0, 1890, 1350, 56700, 28350, 29295, 29970, 29700, 945, 675, 1620, 675, 1890, 0, 0, 1890, 1350, 945, 1620, 1350, 2565, 2835, 2295, 2025;
    0, 56700, 0, 0, 0, 2700, 56700, 28350, 28350, 29700, 31050, 0, 1350, 1350, 1350, 0, 0, 0, 0, 2700, 0, 1350, 2700, 1350, 0, 2700, 4050;
    0, 0, 22680, 0, 1890, 0, 11340, 11340, 945, 945, 0, 23625, 11340, 12285, 0, 1890, 34020, 11340, 13230, 11340, 945, 945, 0, 1890, 2835, 945, 0;
    0, 0, 11340, 3780, 0, 1350, 5670, 7560, 1890, 675, 1350, 11340, 8235, 6345, 4455, 1890, 17010, 9450, 5670, 7020, 3780, 2565, 3240, 675, 0, 1350, 2025;
    0, 0, 11340, 0, 1890, 1350, 5670, 5670, 945, 1620, 1350, 12285, 6345, 7290, 675, 1890, 17010, 5670, 7560, 7020, 945, 1620, 1350, 2565, 2835, 2295, 2025;
    0, 0, 0, 7560, 0, 1350, 0, 3780, 3780, 675, 1350, 0, 4455, 675, 8235, 3780, 0, 7560, 0, 1350, 7560, 4455, 5130, 675, 0, 1350, 2025;
    0, 0, 0, 3780, 3780, 0, 0, 1890, 3780, 1890, 0, 1890, 1890, 1890, 3780, 5670, 0, 3780, 3780, 0, 5670, 3780, 1890, 3780, 5670, 1890, 0;
    0, 0, 34020, 0, 0, 0, 17010, 17010, 0, 0, 0, 34020, 17010, 17010, 0, 0, 51030, 17010, 17010, 17010, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 11340, 7560, 0, 0, 5670, 9450, 3780, 0, 0, 11340, 9450, 5670, 7560, 3780, 17010, 13230, 5670, 5670, 7560, 3780, 3780, 0, 0, 0, 0;
    0, 0, 11340, 0, 3780, 0, 5670, 5670, 1890, 1890, 0, 13230, 5670, 7560, 0, 3780, 17010, 5670, 9450, 5670, 1890, 1890, 0, 3780, 5670, 1890, 0;
    0, 0, 11340, 0, 0, 2700, 5670, 5670, 0, 1350, 2700, 11340, 7020, 7020, 1350, 0, 17010, 5670, 5670, 8370, 0, 1350, 2700, 1350, 0, 2700, 4050;
    0, 0, 0, 7560, 1890, 0, 0, 3780, 4725, 945, 0, 945, 3780, 945, 7560, 5670, 0, 7560, 1890, 0, 8505, 4725, 3780, 1890, 2835, 945, 0;
    0, 0, 0, 3780, 1890, 1350, 0, 1890, 2835, 1620, 1350, 945, 2565, 1620, 4455, 3780, 0, 3780, 1890, 1350, 4725, 3510, 3240, 2565, 2835, 2295, 2025;
    0, 0, 0, 3780, 0, 2700, 0, 1890, 1890, 1350, 2700, 0, 3240, 1350, 5130, 1890, 0, 3780, 0, 2700, 3780, 3240, 4590, 1350, 0, 2700, 4050;
    0, 0, 0, 0, 3780, 1350, 0, 0, 1890, 2565, 1350, 1890, 675, 2565, 675, 3780, 0, 0, 3780, 1350, 1890, 2565, 1350, 4455, 5670, 3240, 2025;
    0, 0, 0, 0, 5670, 0, 0, 0, 2835, 2835, 0, 2835, 0, 2835, 0, 5670, 0, 0, 5670, 0, 2835, 2835, 0, 5670, 8505, 2835, 0;
    0, 0, 0, 0, 1890, 2700, 0, 0, 945, 2295, 2700, 945, 1350, 2295, 1350, 1890, 0, 0, 1890, 2700, 945, 2295, 2700, 3240, 2835, 3645, 4050;
    0, 0, 0, 0, 0, 4050, 0, 0, 0, 2025, 4050, 0, 2025, 2025, 2025, 0, 0, 0, 0, 4050, 0, 2025, 4050, 2025, 0, 4050, 6075]

private def f411S4CompressionCoordinates : Matrix (Fin 27) (Fin 4) ℤ :=
  !![10, (-12), (-12), 21;
    (-110), 132, 132, (-231);
    350, (-276), (-204), 285;
    (-750), 252, 180, (-117);
    900, (-72), (-72), 0;
    (-420), 0, 0, 0;
    200, (-384), (-456), 870;
    (-900), 1728, 1296, (-2214);
    2400, (-1728), (-1152), 936;
    (-4200), 504, 504, 0;
    2520, 0, 0, 0;
    0, (-2160), (-720), 1458;
    0, 5040, 1008, (-1260);
    0, (-1512), (-504), 0;
    0, (-4032), 0, 252;
    0, 2520, 0, 0;
    0, 0, 504, (-1134);
    0, 0, (-2016), 4536;
    0, 0, 2016, (-2016);
    0, 0, (-1008), 0;
    0, 0, 2016, (-6426);
    0, 0, (-4032), 6048;
    0, 0, 2520, 0;
    0, 0, 0, (-1260);
    0, 0, 0, 3402;
    0, 0, 0, (-5670);
    0, 0, 0, 2520]

private def f411S4CompressionLeftProduct : Matrix (Fin 4) (Fin 27) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def f411S4CompressionResult : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

theorem f411_relative_S4_compression :
    b411relativeᵀ*f411rawS4Form*b411relative=b411s := by
  have hM : natFourIntegerMatrix 2 f411S4CompressionInteger=f411rawS4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f411S4CompressionInteger) (f411rawS4Form) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 2520 f411S4CompressionCoordinates=b411relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2520 f411S4CompressionCoordinates) (b411relative) (by decide +kernel) a b
  have hV : f411S4CompressionCoordinatesᵀ*f411S4CompressionInteger=f411S4CompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4CompressionCoordinatesᵀ*f411S4CompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4CompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4CompressionCoordinatesᵀ*f411S4CompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4CompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4CompressionCoordinatesᵀ*f411S4CompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4CompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4CompressionCoordinatesᵀ*f411S4CompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4CompressionLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f411S4CompressionLeftProduct*f411S4CompressionCoordinates=f411S4CompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f411S4CompressionLeftProduct*f411S4CompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f411S4CompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f411S4CompressionLeftProduct*f411S4CompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f411S4CompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f411S4CompressionLeftProduct*f411S4CompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f411S4CompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f411S4CompressionLeftProduct*f411S4CompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f411S4CompressionResult) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2520*2*2520) f411S4CompressionResult=b411s := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2520*2*2520) f411S4CompressionResult) (b411s) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 2 2520
    f411S4CompressionInteger f411S4CompressionCoordinates f411S4CompressionLeftProduct f411S4CompressionResult
    f411rawS4Form b411relative b411s hM hD hV hY hF

theorem f411_actual_relative_S4_form (x y : Fin 4 → ℂ) :
    natOccupationInner (natFourWordBlock f411basis (complexify b411relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f411basis (complexify b411relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b411s *ᵥ y) :=
  natFour_operator_relative_matrix_form f411basis b411relative canonicalNatFourS4
    f411rawS4Form b411s f411_actual_raw_S4_matrix
    f411_relative_S4_compression x y

#print axioms f411_relative_S4_compression
#print axioms f411_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
