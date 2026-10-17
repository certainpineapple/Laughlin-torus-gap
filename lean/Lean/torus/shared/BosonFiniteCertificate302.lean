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

def b302h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![9]

def b302s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(9/2)]

def b302average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(6003769324190846185192312511/1366875000000000000000000000)]

def b302E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(147180477684153814807687489/1366875000000000000000000000)]

def b302L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b302pivots : Fin 1 → ℚ := ![(147180477684153814807687489/1366875000000000000000000000)]

def b302hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b302hPivots : Fin 1 → ℚ := ![9]

def b302lower : Matrix (Fin 1) (Fin 2) ℚ :=
  !![2, 2]

def b302relative : Matrix (Fin 2) (Fin 1) ℚ :=
  !![-1;
    1]

def b302free : Matrix (Fin 1) (Fin 2) ℚ :=
  !![0, 1]

def b302split : Matrix (Fin 2) (Fin 1) ℚ :=
  !![(1/2);
    0]

def b302null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b302nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b302nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/9)]

def b302comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (1) • b302s - b302average + delta • b302h

theorem b302_comparison_reconstruction :
    b302comparison = b302E := by decide +kernel

theorem b302_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b302E b302L b302pivots = true := by decide +kernel

theorem b302_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b302h b302hL b302hPivots = true := by decide +kernel

theorem b302_relative_annihilated :
    b302lower * b302relative = 0 := by decide +kernel

theorem b302_relative_left_inverse :
    b302free * b302relative = 1 := by decide +kernel

theorem b302_relative_complete :
    b302relative * b302free + b302split * b302lower = 1 := by decide +kernel

theorem b302_kernel_annihilated :
    b302h * b302null = 0 := by decide +kernel

theorem b302_kernel_left_inverse :
    b302nullFree * b302null = 1 := by decide +kernel

theorem b302_kernel_complete :
    b302null * b302nullFree + b302nullSplit * b302h = 1 := by decide +kernel

theorem b302_kernel_preserved :
    b302E * b302null = 0 := by decide +kernel

theorem b302_comparison_positive :
    (TorusLean.M2.complexify b302comparison).PosSemidef := by
  rw [b302_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b302_factor_acceptance

theorem b302_relative_exact (v : Fin 2 → ℚ) :
    b302lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b302relative *ᵥ x = v :=
  kernel_from_split b302lower b302relative b302free b302split
    b302_relative_annihilated b302_relative_complete v

theorem b302_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b302h *ᵥ v = 0) : b302comparison *ᵥ v = 0 := by
  rw [b302_comparison_reconstruction]
  exact kernel_preserved_from_split b302h b302E b302null
    b302nullFree b302nullSplit b302_kernel_complete
    b302_kernel_preserved v hv

#print axioms b302_comparison_reconstruction
#print axioms b302_factor_acceptance
#print axioms b302_hamiltonian_factor_acceptance
#print axioms b302_relative_annihilated
#print axioms b302_relative_left_inverse
#print axioms b302_relative_complete
#print axioms b302_kernel_annihilated
#print axioms b302_kernel_left_inverse
#print axioms b302_kernel_complete
#print axioms b302_kernel_preserved
#print axioms b302_comparison_positive
#print axioms b302_relative_exact
#print axioms b302_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
