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

def b405h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![256]

def b405s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![0]

def b405average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-297942667950031777633181877225579/73400320000000000000000000000000)]

def b405E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(297961458431951777633181877225579/73400320000000000000000000000000)]

def b405L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b405pivots : Fin 1 → ℚ := ![(297961458431951777633181877225579/73400320000000000000000000000000)]

def b405hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b405hPivots : Fin 1 → ℚ := ![256]

def b405lower : Matrix (Fin 5) (Fin 6) ℚ :=
  !![5, 1, 0, 0, 0, 0;
    0, 4, 2, 2, 0, 0;
    0, 0, 3, 0, 1, 0;
    0, 0, 0, 3, 4, 3;
    0, 0, 0, 0, 0, 2]

def b405relative : Matrix (Fin 6) (Fin 1) ℚ :=
  !![(-1/6);
    (5/6);
    (-1/3);
    (-4/3);
    1;
    0]

def b405free : Matrix (Fin 1) (Fin 6) ℚ :=
  !![0, 0, 0, 0, 1, 0]

def b405split : Matrix (Fin 6) (Fin 5) ℚ :=
  !![(1/5), (-1/20), (1/30), (1/30), (-1/20);
    0, (1/4), (-1/6), (-1/6), (1/4);
    0, 0, (1/3), 0, 0;
    0, 0, 0, (1/3), (-1/2);
    0, 0, 0, 0, 0;
    0, 0, 0, 0, (1/2)]

def b405null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b405nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b405nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/256)]

def b405comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (alpha) • b405s - b405average + delta • b405h

theorem b405_comparison_reconstruction :
    b405comparison = b405E := by decide +kernel

theorem b405_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b405E b405L b405pivots = true := by decide +kernel

theorem b405_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b405h b405hL b405hPivots = true := by decide +kernel

theorem b405_relative_annihilated :
    b405lower * b405relative = 0 := by decide +kernel

theorem b405_relative_left_inverse :
    b405free * b405relative = 1 := by decide +kernel

theorem b405_relative_complete :
    b405relative * b405free + b405split * b405lower = 1 := by decide +kernel

theorem b405_kernel_annihilated :
    b405h * b405null = 0 := by decide +kernel

theorem b405_kernel_left_inverse :
    b405nullFree * b405null = 1 := by decide +kernel

theorem b405_kernel_complete :
    b405null * b405nullFree + b405nullSplit * b405h = 1 := by decide +kernel

theorem b405_kernel_preserved :
    b405E * b405null = 0 := by decide +kernel

theorem b405_comparison_positive :
    (TorusLean.M2.complexify b405comparison).PosSemidef := by
  rw [b405_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b405_factor_acceptance

theorem b405_relative_exact (v : Fin 6 → ℚ) :
    b405lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b405relative *ᵥ x = v :=
  kernel_from_split b405lower b405relative b405free b405split
    b405_relative_annihilated b405_relative_complete v

theorem b405_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b405h *ᵥ v = 0) : b405comparison *ᵥ v = 0 := by
  rw [b405_comparison_reconstruction]
  exact kernel_preserved_from_split b405h b405E b405null
    b405nullFree b405nullSplit b405_kernel_complete
    b405_kernel_preserved v hv

#print axioms b405_comparison_reconstruction
#print axioms b405_factor_acceptance
#print axioms b405_hamiltonian_factor_acceptance
#print axioms b405_relative_annihilated
#print axioms b405_relative_left_inverse
#print axioms b405_relative_complete
#print axioms b405_kernel_annihilated
#print axioms b405_kernel_left_inverse
#print axioms b405_kernel_complete
#print axioms b405_kernel_preserved
#print axioms b405_comparison_positive
#print axioms b405_relative_exact
#print axioms b405_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
