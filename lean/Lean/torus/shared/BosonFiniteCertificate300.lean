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

def b300h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![18]

def b300s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![36]

def b300average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(107289555978763849934821288829/3189375000000000000000000000)]

def b300E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(7528001429986150065178711171/3189375000000000000000000000)]

def b300L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b300pivots : Fin 1 → ℚ := ![(7528001429986150065178711171/3189375000000000000000000000)]

def b300hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b300hPivots : Fin 1 → ℚ := ![18]

def b300lower : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b300relative : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b300free : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b300split : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b300null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b300nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b300nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/18)]

def b300comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (1) • b300s - b300average + delta • b300h

theorem b300_comparison_reconstruction :
    b300comparison = b300E := by decide +kernel

theorem b300_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b300E b300L b300pivots = true := by decide +kernel

theorem b300_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b300h b300hL b300hPivots = true := by decide +kernel

theorem b300_relative_annihilated :
    b300lower * b300relative = 0 := by decide +kernel

theorem b300_relative_left_inverse :
    b300free * b300relative = 1 := by decide +kernel

theorem b300_relative_complete :
    b300relative * b300free + b300split * b300lower = 1 := by decide +kernel

theorem b300_kernel_annihilated :
    b300h * b300null = 0 := by decide +kernel

theorem b300_kernel_left_inverse :
    b300nullFree * b300null = 1 := by decide +kernel

theorem b300_kernel_complete :
    b300null * b300nullFree + b300nullSplit * b300h = 1 := by decide +kernel

theorem b300_kernel_preserved :
    b300E * b300null = 0 := by decide +kernel

theorem b300_comparison_positive :
    (TorusLean.M2.complexify b300comparison).PosSemidef := by
  rw [b300_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b300_factor_acceptance

theorem b300_relative_exact (v : Fin 1 → ℚ) :
    b300lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b300relative *ᵥ x = v :=
  kernel_from_split b300lower b300relative b300free b300split
    b300_relative_annihilated b300_relative_complete v

theorem b300_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b300h *ᵥ v = 0) : b300comparison *ᵥ v = 0 := by
  rw [b300_comparison_reconstruction]
  exact kernel_preserved_from_split b300h b300E b300null
    b300nullFree b300nullSplit b300_kernel_complete
    b300_kernel_preserved v hv

#print axioms b300_comparison_reconstruction
#print axioms b300_factor_acceptance
#print axioms b300_hamiltonian_factor_acceptance
#print axioms b300_relative_annihilated
#print axioms b300_relative_left_inverse
#print axioms b300_relative_complete
#print axioms b300_kernel_annihilated
#print axioms b300_kernel_left_inverse
#print axioms b300_kernel_complete
#print axioms b300_kernel_preserved
#print axioms b300_comparison_positive
#print axioms b300_relative_exact
#print axioms b300_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
