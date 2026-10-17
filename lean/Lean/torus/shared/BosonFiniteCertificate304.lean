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

def b304h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![27]

def b304s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(27/8)]

def b304average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(153772843022517932953529749/45562500000000000000000000)]

def b304E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1824664982067046470251/45562500000000000000000000)]

def b304L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b304pivots : Fin 1 → ℚ := ![(1824664982067046470251/45562500000000000000000000)]

def b304hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b304hPivots : Fin 1 → ℚ := ![27]

def b304lower : Matrix (Fin 3) (Fin 4) ℚ :=
  !![4, 1, 0, 0;
    0, 3, 4, 2;
    0, 0, 0, 2]

def b304relative : Matrix (Fin 4) (Fin 1) ℚ :=
  !![(1/3);
    (-4/3);
    1;
    0]

def b304free : Matrix (Fin 1) (Fin 4) ℚ :=
  !![0, 0, 1, 0]

def b304split : Matrix (Fin 4) (Fin 3) ℚ :=
  !![(1/4), (-1/12), (1/12);
    0, (1/3), (-1/3);
    0, 0, 0;
    0, 0, (1/2)]

def b304null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b304nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b304nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/27)]

def b304comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (1) • b304s - b304average + delta • b304h

theorem b304_comparison_reconstruction :
    b304comparison = b304E := by decide +kernel

theorem b304_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b304E b304L b304pivots = true := by decide +kernel

theorem b304_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b304h b304hL b304hPivots = true := by decide +kernel

theorem b304_relative_annihilated :
    b304lower * b304relative = 0 := by decide +kernel

theorem b304_relative_left_inverse :
    b304free * b304relative = 1 := by decide +kernel

theorem b304_relative_complete :
    b304relative * b304free + b304split * b304lower = 1 := by decide +kernel

theorem b304_kernel_annihilated :
    b304h * b304null = 0 := by decide +kernel

theorem b304_kernel_left_inverse :
    b304nullFree * b304null = 1 := by decide +kernel

theorem b304_kernel_complete :
    b304null * b304nullFree + b304nullSplit * b304h = 1 := by decide +kernel

theorem b304_kernel_preserved :
    b304E * b304null = 0 := by decide +kernel

theorem b304_comparison_positive :
    (TorusLean.M2.complexify b304comparison).PosSemidef := by
  rw [b304_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b304_factor_acceptance

theorem b304_relative_exact (v : Fin 4 → ℚ) :
    b304lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b304relative *ᵥ x = v :=
  kernel_from_split b304lower b304relative b304free b304split
    b304_relative_annihilated b304_relative_complete v

theorem b304_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b304h *ᵥ v = 0) : b304comparison *ᵥ v = 0 := by
  rw [b304_comparison_reconstruction]
  exact kernel_preserved_from_split b304h b304E b304null
    b304nullFree b304nullSplit b304_kernel_complete
    b304_kernel_preserved v hv

#print axioms b304_comparison_reconstruction
#print axioms b304_factor_acceptance
#print axioms b304_hamiltonian_factor_acceptance
#print axioms b304_relative_annihilated
#print axioms b304_relative_left_inverse
#print axioms b304_relative_complete
#print axioms b304_kernel_annihilated
#print axioms b304_kernel_left_inverse
#print axioms b304_kernel_complete
#print axioms b304_kernel_preserved
#print axioms b304_comparison_positive
#print axioms b304_relative_exact
#print axioms b304_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
