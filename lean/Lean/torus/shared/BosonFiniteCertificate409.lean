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

def b409h : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(801792/35), (-808704/35), (-695808/35);
    (-808704/35), (222588/7), (186300/7);
    (-695808/35), (186300/7), (202428/7)]

def b409s : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, 0;
    0, 0, 0;
    0, 0, 0]

def b409average : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(-101388340195732121544316992236907/627200000000000000000000000000), (69163618899725953761911502136311/501760000000000000000000000000), (8099655165195303099513167180643/100352000000000000000000000000);
    (69163618899725953761911502136311/501760000000000000000000000000), (-1233291416880166422561796813695963/10035200000000000000000000000000), (-788683947446598060618400690735731/10035200000000000000000000000000);
    (8099655165195303099513167180643/100352000000000000000000000000), (-788683947446598060618400690735731/10035200000000000000000000000000), (-601755481876250633646359496569547/10035200000000000000000000000000)]

def b409E : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(101402708308372121544316992236907/627200000000000000000000000000), (-69175212480269953761911502136311/501760000000000000000000000000), (-8101650185892903099513167180643/100352000000000000000000000000);
    (-69175212480269953761911502136311/501760000000000000000000000000), (1233610519036966422561796813695963/10035200000000000000000000000000), (788951027126598060618400690735731/10035200000000000000000000000000);
    (-8101650185892903099513167180643/100352000000000000000000000000), (788951027126598060618400690735731/10035200000000000000000000000000), (602045682657050633646359496569547/10035200000000000000000000000000)]

def b409L : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0;
    (-115292020800449922936519170227185/135203611077829495392422656315876), 1, 0;
    (-67513751549107525829276393172025/135203611077829495392422656315876), (78322619378810677528739705267431653075954828354715599513049/42998843268003913656241167974563171831665203011979895163677), 1]

def b409pivots : Fin 3 → ℚ := ![(101402708308372121544316992236907/627200000000000000000000000000), (1160968768236105668718511535313205639454960481323457169419279/216325777724527192627876250105401600000000000000000000000000), (34372124339943292050939014020467064911280411193276857981326932018279563366402600359/18346173127681669826662898335813619981510486618444755269835520000000000000000000000)]

def b409hL : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0;
    (-117/116), 1, 0;
    (-151/174), (979/1267), 1]

def b409hPivots : Fin 3 → ℚ := ![(801792/35), (1231524/145), (8355840/1267)]

def b409lower : Matrix (Fin 15) (Fin 18) ℚ :=
  !![9, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 8, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 7, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 6, 4, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 7, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 6, 3, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 5, 8, 0, 2, 0, 0, 0, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 9, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 4, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 6;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]

def b409relative : Matrix (Fin 18) (Fin 3) ℚ :=
  !![(-1/70), (1/56), (1/56);
    (9/70), (-9/56), (-9/56);
    (-2/7), (9/35), (11/70);
    (2/5), (-3/20), (-1/20);
    (-1/5), 0, 0;
    (-8/35), (27/70), (17/35);
    (4/5), (-27/20), (-19/20);
    (-8/5), (9/10), (3/10);
    1, 0, 0;
    0, (27/20), (9/20);
    0, (-9/4), (-1/4);
    0, 1, 0;
    0, 0, (-1/2);
    0, 0, (3/2);
    0, 0, (-1/2);
    0, 0, (-3/2);
    0, 0, 1;
    0, 0, 0]

def b409free : Matrix (Fin 3) (Fin 18) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

def b409split : Matrix (Fin 18) (Fin 15) ℚ :=
  !![(1/9), (-1/72), (1/252), (-1/504), (1/630), (1/252), (-1/504), (1/630), (1/630), (-1/504), (-1/504), (1/630), (-1/504), (-1/504), (1/252);
    0, (1/8), (-1/28), (1/56), (-1/70), (-1/28), (1/56), (-1/70), (-1/70), (1/56), (1/56), (-1/70), (1/56), (1/56), (-1/28);
    0, 0, (1/7), (-1/14), (2/35), 0, (-1/42), (1/35), (2/105), (-1/35), 0, (1/105), (-3/140), (-1/70), (1/35);
    0, 0, 0, (1/6), (-2/15), 0, 0, (-1/30), 0, (1/60), 0, 0, (1/60), 0, 0;
    0, 0, 0, 0, (1/5), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, (1/7), (-1/21), (1/35), (4/105), (-3/70), (-1/14), (1/21), (-1/20), (-2/35), (4/35);
    0, 0, 0, 0, 0, 0, (1/6), (-1/10), (-2/15), (3/20), 0, (-1/15), (1/10), (1/10), (-1/5);
    0, 0, 0, 0, 0, 0, 0, (1/5), 0, (-1/10), 0, 0, (-1/10), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (1/5), (-3/20), 0, 0, 0, (-1/20), (1/10);
    0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/6), (-1/15), (1/20), (1/15), (-2/15);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/5), (-3/20), (-1/5), (2/5);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), (-1/2);
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/3)]

def b409null : Matrix (Fin 3) (Fin 0) ℚ :=
  fun _ _ => 0

def b409nullFree : Matrix (Fin 0) (Fin 3) ℚ :=
  fun _ _ => 0

def b409nullSplit : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(13205/80216064), (6521/60162048), (269/20054016);
    (6521/60162048), (140963/676823040), (-979/8355840);
    (269/20054016), (-979/8355840), (1267/8355840)]

def b409comparison : Matrix (Fin 3) (Fin 3) ℚ :=
  (alpha) • b409s - b409average + delta • b409h

theorem b409_comparison_reconstruction :
    b409comparison = b409E := by decide +kernel

theorem b409_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b409E b409L b409pivots = true := by decide +kernel

theorem b409_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b409h b409hL b409hPivots = true := by decide +kernel

theorem b409_relative_annihilated :
    b409lower * b409relative = 0 := by decide +kernel

theorem b409_relative_left_inverse :
    b409free * b409relative = 1 := by decide +kernel

theorem b409_relative_complete :
    b409relative * b409free + b409split * b409lower = 1 := by decide +kernel

theorem b409_kernel_annihilated :
    b409h * b409null = 0 := by decide +kernel

theorem b409_kernel_left_inverse :
    b409nullFree * b409null = 1 := by decide +kernel

theorem b409_kernel_complete :
    b409null * b409nullFree + b409nullSplit * b409h = 1 := by decide +kernel

theorem b409_kernel_preserved :
    b409E * b409null = 0 := by decide +kernel

theorem b409_comparison_positive :
    (TorusLean.M2.complexify b409comparison).PosSemidef := by
  rw [b409_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b409_factor_acceptance

theorem b409_relative_exact (v : Fin 18 → ℚ) :
    b409lower *ᵥ v = 0 ↔ ∃ x : Fin 3 → ℚ, b409relative *ᵥ x = v :=
  kernel_from_split b409lower b409relative b409free b409split
    b409_relative_annihilated b409_relative_complete v

theorem b409_zero_kernel_preserved (v : Fin 3 → ℚ)
    (hv : b409h *ᵥ v = 0) : b409comparison *ᵥ v = 0 := by
  rw [b409_comparison_reconstruction]
  exact kernel_preserved_from_split b409h b409E b409null
    b409nullFree b409nullSplit b409_kernel_complete
    b409_kernel_preserved v hv

#print axioms b409_comparison_reconstruction
#print axioms b409_factor_acceptance
#print axioms b409_hamiltonian_factor_acceptance
#print axioms b409_relative_annihilated
#print axioms b409_relative_left_inverse
#print axioms b409_relative_complete
#print axioms b409_kernel_annihilated
#print axioms b409_kernel_left_inverse
#print axioms b409_kernel_complete
#print axioms b409_kernel_preserved
#print axioms b409_comparison_positive
#print axioms b409_relative_exact
#print axioms b409_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
