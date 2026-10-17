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

def b307h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(137781/320)]

def b307s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-137781/20480)]

def b307average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-42049748776223490863806537/6250000000000000000000000)]

def b307E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(5015494973490863806537/6250000000000000000000000)]

def b307L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b307pivots : Fin 1 → ℚ := ![(5015494973490863806537/6250000000000000000000000)]

def b307hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b307hPivots : Fin 1 → ℚ := ![(137781/320)]

def b307lower : Matrix (Fin 7) (Fin 8) ℚ :=
  !![7, 1, 0, 0, 0, 0, 0, 0;
    0, 6, 2, 0, 2, 0, 0, 0;
    0, 0, 5, 3, 0, 1, 0, 0;
    0, 0, 0, 4, 0, 0, 1, 0;
    0, 0, 0, 0, 5, 2, 0, 0;
    0, 0, 0, 0, 0, 4, 6, 4;
    0, 0, 0, 0, 0, 0, 0, 3]

def b307relative : Matrix (Fin 8) (Fin 1) ℚ :=
  !![(1/20);
    (-7/20);
    (9/20);
    (-1/4);
    (3/5);
    (-3/2);
    1;
    0]

def b307free : Matrix (Fin 1) (Fin 8) ℚ :=
  !![0, 0, 0, 0, 0, 0, 1, 0]

def b307split : Matrix (Fin 8) (Fin 7) ℚ :=
  !![(1/7), (-1/42), (1/105), (-1/140), (1/105), (-1/140), (1/105);
    0, (1/6), (-1/15), (1/20), (-1/15), (1/20), (-1/15);
    0, 0, (1/5), (-3/20), 0, (-1/20), (1/15);
    0, 0, 0, (1/4), 0, 0, 0;
    0, 0, 0, 0, (1/5), (-1/10), (2/15);
    0, 0, 0, 0, 0, (1/4), (-1/3);
    0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, (1/3)]

def b307null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b307nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b307nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(320/137781)]

def b307comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (1) • b307s - b307average + delta • b307h

theorem b307_comparison_reconstruction :
    b307comparison = b307E := by decide +kernel

theorem b307_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b307E b307L b307pivots = true := by decide +kernel

theorem b307_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b307h b307hL b307hPivots = true := by decide +kernel

theorem b307_relative_annihilated :
    b307lower * b307relative = 0 := by decide +kernel

theorem b307_relative_left_inverse :
    b307free * b307relative = 1 := by decide +kernel

theorem b307_relative_complete :
    b307relative * b307free + b307split * b307lower = 1 := by decide +kernel

theorem b307_kernel_annihilated :
    b307h * b307null = 0 := by decide +kernel

theorem b307_kernel_left_inverse :
    b307nullFree * b307null = 1 := by decide +kernel

theorem b307_kernel_complete :
    b307null * b307nullFree + b307nullSplit * b307h = 1 := by decide +kernel

theorem b307_kernel_preserved :
    b307E * b307null = 0 := by decide +kernel

theorem b307_comparison_positive :
    (TorusLean.M2.complexify b307comparison).PosSemidef := by
  rw [b307_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b307_factor_acceptance

theorem b307_relative_exact (v : Fin 8 → ℚ) :
    b307lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b307relative *ᵥ x = v :=
  kernel_from_split b307lower b307relative b307free b307split
    b307_relative_annihilated b307_relative_complete v

theorem b307_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b307h *ᵥ v = 0) : b307comparison *ᵥ v = 0 := by
  rw [b307_comparison_reconstruction]
  exact kernel_preserved_from_split b307h b307E b307null
    b307nullFree b307nullSplit b307_kernel_complete
    b307_kernel_preserved v hv

#print axioms b307_comparison_reconstruction
#print axioms b307_factor_acceptance
#print axioms b307_hamiltonian_factor_acceptance
#print axioms b307_relative_annihilated
#print axioms b307_relative_left_inverse
#print axioms b307_relative_complete
#print axioms b307_kernel_annihilated
#print axioms b307_kernel_left_inverse
#print axioms b307_kernel_complete
#print axioms b307_kernel_preserved
#print axioms b307_comparison_positive
#print axioms b307_relative_exact
#print axioms b307_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
