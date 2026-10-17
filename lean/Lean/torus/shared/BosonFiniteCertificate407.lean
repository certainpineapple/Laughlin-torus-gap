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

def b407h : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(8964/5), (-10632/5);
    (-10632/5), (48688/15)]

def b407s : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 0;
    0, 0]

def b407average : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(-112620667695195148963588259563893/6553600000000000000000000000000), (33781366509005724669156573495981/1638400000000000000000000000000);
    (33781366509005724669156573495981/1638400000000000000000000000000), (-94544730386965115046590640442493/3686400000000000000000000000000)]

def b407E : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(112632416989275148963588259563893/6553600000000000000000000000000), (-33784850402765724669156573495981/1638400000000000000000000000000);
    (-33784850402765724669156573495981/1638400000000000000000000000000), (94556695949845115046590640442493/3686400000000000000000000000000)]

def b407L : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0;
    (-45046467203687632892208764661308/37544138996425049654529419854631), 1]

def b407pivots : Fin 2 → ℚ := ![(112632416989275148963588259563893/6553600000000000000000000000000), (62900692785954244867260701573616059206064327045993348452889/69201356998210651523228626676055859200000000000000000000000)]

def b407hL : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0;
    (-886/747), 1]

def b407hPivots : Fin 2 → ℚ := ![(8964/5), (180224/249)]

def b407lower : Matrix (Fin 9) (Fin 11) ℚ :=
  !![7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 6, 2, 0, 2, 0, 0, 0, 0, 0, 0;
    0, 0, 5, 3, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 5, 2, 0, 0, 3, 0, 0;
    0, 0, 0, 0, 0, 4, 6, 4, 0, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6]

def b407relative : Matrix (Fin 11) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (-7/20), (7/15);
    (9/20), (-4/15);
    (-1/4), 0;
    (3/5), (-17/15);
    (-3/2), (4/3);
    1, 0;
    0, (-1/3);
    0, 1;
    0, -2;
    0, 1]

def b407free : Matrix (Fin 2) (Fin 11) ℚ :=
  !![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def b407split : Matrix (Fin 11) (Fin 9) ℚ :=
  !![(1/7), (-1/42), (1/105), (-1/140), (1/105), (-1/140), (1/105), (-1/140), (1/105);
    0, (1/6), (-1/15), (1/20), (-1/15), (1/20), (-1/15), (1/20), (-1/15);
    0, 0, (1/5), (-3/20), 0, (-1/20), (1/15), 0, (1/30);
    0, 0, 0, (1/4), 0, 0, 0, 0, 0;
    0, 0, 0, 0, (1/5), (-1/10), (2/15), (-3/20), (1/6);
    0, 0, 0, 0, 0, (1/4), (-1/3), 0, (-1/6);
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, (1/3), 0, 0;
    0, 0, 0, 0, 0, 0, 0, (1/4), (-1/6);
    0, 0, 0, 0, 0, 0, 0, 0, (1/3);
    0, 0, 0, 0, 0, 0, 0, 0, 0]

def b407null : Matrix (Fin 2) (Fin 0) ℚ :=
  fun _ _ => 0

def b407nullFree : Matrix (Fin 0) (Fin 2) ℚ :=
  fun _ _ => 0

def b407nullSplit : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(3043/1216512), (443/270336);
    (443/270336), (249/180224)]

def b407comparison : Matrix (Fin 2) (Fin 2) ℚ :=
  (alpha) • b407s - b407average + delta • b407h

theorem b407_comparison_reconstruction :
    b407comparison = b407E := by decide +kernel

theorem b407_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b407E b407L b407pivots = true := by decide +kernel

theorem b407_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b407h b407hL b407hPivots = true := by decide +kernel

theorem b407_relative_annihilated :
    b407lower * b407relative = 0 := by decide +kernel

theorem b407_relative_left_inverse :
    b407free * b407relative = 1 := by decide +kernel

theorem b407_relative_complete :
    b407relative * b407free + b407split * b407lower = 1 := by decide +kernel

theorem b407_kernel_annihilated :
    b407h * b407null = 0 := by decide +kernel

theorem b407_kernel_left_inverse :
    b407nullFree * b407null = 1 := by decide +kernel

theorem b407_kernel_complete :
    b407null * b407nullFree + b407nullSplit * b407h = 1 := by decide +kernel

theorem b407_kernel_preserved :
    b407E * b407null = 0 := by decide +kernel

theorem b407_comparison_positive :
    (TorusLean.M2.complexify b407comparison).PosSemidef := by
  rw [b407_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b407_factor_acceptance

theorem b407_relative_exact (v : Fin 11 → ℚ) :
    b407lower *ᵥ v = 0 ↔ ∃ x : Fin 2 → ℚ, b407relative *ᵥ x = v :=
  kernel_from_split b407lower b407relative b407free b407split
    b407_relative_annihilated b407_relative_complete v

theorem b407_zero_kernel_preserved (v : Fin 2 → ℚ)
    (hv : b407h *ᵥ v = 0) : b407comparison *ᵥ v = 0 := by
  rw [b407_comparison_reconstruction]
  exact kernel_preserved_from_split b407h b407E b407null
    b407nullFree b407nullSplit b407_kernel_complete
    b407_kernel_preserved v hv

#print axioms b407_comparison_reconstruction
#print axioms b407_factor_acceptance
#print axioms b407_hamiltonian_factor_acceptance
#print axioms b407_relative_annihilated
#print axioms b407_relative_left_inverse
#print axioms b407_relative_complete
#print axioms b407_kernel_annihilated
#print axioms b407_kernel_left_inverse
#print axioms b407_kernel_complete
#print axioms b407_kernel_preserved
#print axioms b407_comparison_positive
#print axioms b407_relative_exact
#print axioms b407_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
