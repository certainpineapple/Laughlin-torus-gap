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

def b301h : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b301s : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b301average : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b301E : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b301L : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b301pivots : Fin 0 → ℚ := fun _ => 0

def b301hL : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b301hPivots : Fin 0 → ℚ := fun _ => 0

def b301lower : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b301relative : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b301free : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b301split : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b301null : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b301nullFree : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b301nullSplit : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b301comparison : Matrix (Fin 0) (Fin 0) ℚ :=
  (1) • b301s - b301average + delta • b301h

theorem b301_comparison_reconstruction :
    b301comparison = b301E := by decide +kernel

theorem b301_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b301E b301L b301pivots = true := by decide +kernel

theorem b301_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b301h b301hL b301hPivots = true := by decide +kernel

theorem b301_relative_annihilated :
    b301lower * b301relative = 0 := by decide +kernel

theorem b301_relative_left_inverse :
    b301free * b301relative = 1 := by decide +kernel

theorem b301_relative_complete :
    b301relative * b301free + b301split * b301lower = 1 := by decide +kernel

theorem b301_kernel_annihilated :
    b301h * b301null = 0 := by decide +kernel

theorem b301_kernel_left_inverse :
    b301nullFree * b301null = 1 := by decide +kernel

theorem b301_kernel_complete :
    b301null * b301nullFree + b301nullSplit * b301h = 1 := by decide +kernel

theorem b301_kernel_preserved :
    b301E * b301null = 0 := by decide +kernel

theorem b301_comparison_positive :
    (TorusLean.M2.complexify b301comparison).PosSemidef := by
  rw [b301_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b301_factor_acceptance

theorem b301_relative_exact (v : Fin 1 → ℚ) :
    b301lower *ᵥ v = 0 ↔ ∃ x : Fin 0 → ℚ, b301relative *ᵥ x = v :=
  kernel_from_split b301lower b301relative b301free b301split
    b301_relative_annihilated b301_relative_complete v

theorem b301_zero_kernel_preserved (v : Fin 0 → ℚ)
    (hv : b301h *ᵥ v = 0) : b301comparison *ᵥ v = 0 := by
  rw [b301_comparison_reconstruction]
  exact kernel_preserved_from_split b301h b301E b301null
    b301nullFree b301nullSplit b301_kernel_complete
    b301_kernel_preserved v hv

#print axioms b301_comparison_reconstruction
#print axioms b301_factor_acceptance
#print axioms b301_hamiltonian_factor_acceptance
#print axioms b301_relative_annihilated
#print axioms b301_relative_left_inverse
#print axioms b301_relative_complete
#print axioms b301_kernel_annihilated
#print axioms b301_kernel_left_inverse
#print axioms b301_kernel_complete
#print axioms b301_kernel_preserved
#print axioms b301_comparison_positive
#print axioms b301_relative_exact
#print axioms b301_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
