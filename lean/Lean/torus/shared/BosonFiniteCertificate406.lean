/- Generated from frozen integer rows, with exact finite arithmetic witnesses.
    Provenance and semantic-boundary notes: checks/boson-finite/README.md.
    This module does not identify the plane comparison with a torus operator. -/
import torus.shared.BosonFiniteCertificateCore
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def b406h : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(5877/5), (-3627/5), (-2712/5);
    (-3627/5), (4197/5), (3352/5);
    (-2712/5), (3352/5), (12496/15)]

def b406s : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(576/5), (-576/5), (384/5);
    (-576/5), (576/5), (-384/5);
    (384/5), (-384/5), (256/5)]

def b406average : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(-2062801641819433761414805420904931/45875200000000000000000000000000), (829478175343377880152381920542191/45875200000000000000000000000000), (-169651772996955697146064593092069/45875200000000000000000000000000);
    (829478175343377880152381920542191/45875200000000000000000000000000), (90696770007754248022605599179509/45875200000000000000000000000000), (-478501600622685758834746007573511/45875200000000000000000000000000);
    (-169651772996955697146064593092069/45875200000000000000000000000000), (-478501600622685758834746007573511/45875200000000000000000000000000), (-1827551724756639709222109602390073/137625600000000000000000000000000)]

def b406E : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(92445728261686519117761231407660710760417/658258978406400000000000000000000000000), (-74748588323763692670723674006341288235237/658258978406400000000000000000000000000), (132993892672683491650327138786812821555749/1974776935219200000000000000000000000000);
    (-74748588323763692670723674006341288235237/658258978406400000000000000000000000000), (61545158650713753748428698359693949053337/658258978406400000000000000000000000000), (-105092762461822317717087403506119184992569/1974776935219200000000000000000000000000);
    (132993892672683491650327138786812821555749/1974776935219200000000000000000000000000), (-105092762461822317717087403506119184992569/1974776935219200000000000000000000000000), (330059067075860099885045279085506405600633/5924330805657600000000000000000000000000)]

def b406L : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0;
    (-74748588323763692670723674006341288235237/92445728261686519117761231407660710760417), 1, 0;
    (132993892672683491650327138786812821555749/277337184785059557353283694222982132281251), (1560657365456279227194364557242292807920446093051704662922423519020104/2120527286477854125260800053908606877049129076188989877092335289504143), 1]

def b406pivots : Fin 3 → ℚ := ![(92445728261686519117761231407660710760417/658258978406400000000000000000000000000), (6361581859433562375782400161725820631147387228566969631277005868512429/3786577029598679823063500038457782712746680320000000000000000000000000), (146618461298391243270572225695752254707371928753287766917337058888785008241467935115412686189600349/6514259824059967872801177765607240326294924522052576902427654009356727296000000000000000000000000)]

def b406hL : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0;
    (-403/653), 1, 0;
    (-904/1959), (13699/15987), 1]

def b406hPivots : Fin 3 → ℚ := ![(5877/5), (255792/653), (1572864/5329)]

def b406lower : Matrix (Fin 6) (Fin 9) ℚ :=
  !![6, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 5, 2, 0, 2, 0, 0, 0, 0;
    0, 0, 4, 6, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 4, 2, 0, 3, 0;
    0, 0, 0, 0, 0, 3, 6, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 3, 4]

def b406relative : Matrix (Fin 9) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (3/5), (-3/5), (-3/5);
    (-3/2), (1/2), (1/6);
    1, 0, 0;
    0, 1, (4/3);
    0, -2, (-2/3);
    0, 1, 0;
    0, 0, (-4/3);
    0, 0, 1]

def b406free : Matrix (Fin 3) (Fin 9) ℚ :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

def b406split : Matrix (Fin 9) (Fin 6) ℚ :=
  !![(1/6), (-1/30), (1/60), (1/60), (-1/60), (-1/60);
    0, (1/5), (-1/10), (-1/10), (1/10), (1/10);
    0, 0, (1/4), 0, (-1/12), 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, (1/4), (-1/6), (-1/4);
    0, 0, 0, 0, (1/3), 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, (1/3);
    0, 0, 0, 0, 0, 0]

def b406null : Matrix (Fin 3) (Fin 0) ℚ :=
  fun _ _ => 0

def b406nullFree : Matrix (Fin 0) (Fin 3) ℚ :=
  fun _ _ => 0

def b406nullSplit : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(8675/4718592), (8357/4718592), (-359/1572864);
    (8357/4718592), (71353/14155776), (-13699/4718592);
    (-359/1572864), (-13699/4718592), (5329/1572864)]

def b406comparison : Matrix (Fin 3) (Fin 3) ℚ :=
  (alpha) • b406s - b406average + delta • b406h

theorem b406_comparison_reconstruction :
    b406comparison = b406E := by decide +kernel

theorem b406_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b406E b406L b406pivots = true := by decide +kernel

theorem b406_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b406h b406hL b406hPivots = true := by decide +kernel

theorem b406_relative_annihilated :
    b406lower * b406relative = 0 := by decide +kernel

theorem b406_relative_left_inverse :
    b406free * b406relative = 1 := by decide +kernel

theorem b406_relative_complete :
    b406relative * b406free + b406split * b406lower = 1 := by decide +kernel

theorem b406_kernel_annihilated :
    b406h * b406null = 0 := by decide +kernel

theorem b406_kernel_left_inverse :
    b406nullFree * b406null = 1 := by decide +kernel

theorem b406_kernel_complete :
    b406null * b406nullFree + b406nullSplit * b406h = 1 := by decide +kernel

theorem b406_kernel_preserved :
    b406E * b406null = 0 := by decide +kernel

theorem b406_comparison_positive :
    (TorusLean.M2.complexify b406comparison).PosSemidef := by
  rw [b406_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b406_factor_acceptance

theorem b406_relative_exact (v : Fin 9 → ℚ) :
    b406lower *ᵥ v = 0 ↔ ∃ x : Fin 3 → ℚ, b406relative *ᵥ x = v :=
  kernel_from_split b406lower b406relative b406free b406split
    b406_relative_annihilated b406_relative_complete v

theorem b406_zero_kernel_preserved (v : Fin 3 → ℚ)
    (hv : b406h *ᵥ v = 0) : b406comparison *ᵥ v = 0 := by
  rw [b406_comparison_reconstruction]
  exact kernel_preserved_from_split b406h b406E b406null
    b406nullFree b406nullSplit b406_kernel_complete
    b406_kernel_preserved v hv

#print axioms b406_comparison_reconstruction
#print axioms b406_factor_acceptance
#print axioms b406_hamiltonian_factor_acceptance
#print axioms b406_relative_annihilated
#print axioms b406_relative_left_inverse
#print axioms b406_relative_complete
#print axioms b406_kernel_annihilated
#print axioms b406_kernel_left_inverse
#print axioms b406_kernel_complete
#print axioms b406_kernel_preserved
#print axioms b406_comparison_positive
#print axioms b406_relative_exact
#print axioms b406_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
