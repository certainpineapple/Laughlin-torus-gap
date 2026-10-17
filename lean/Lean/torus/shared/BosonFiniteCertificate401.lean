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

def b401h : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b401s : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b401average : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b401E : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b401L : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b401pivots : Fin 0 → ℚ := fun _ => 0

def b401hL : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b401hPivots : Fin 0 → ℚ := fun _ => 0

def b401lower : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b401relative : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b401free : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b401split : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b401null : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b401nullFree : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b401nullSplit : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def b401comparison : Matrix (Fin 0) (Fin 0) ℚ :=
  (alpha) • b401s - b401average + delta • b401h

theorem b401_comparison_reconstruction :
    b401comparison = b401E := by decide +kernel

theorem b401_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b401E b401L b401pivots = true := by decide +kernel

theorem b401_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b401h b401hL b401hPivots = true := by decide +kernel

theorem b401_relative_annihilated :
    b401lower * b401relative = 0 := by decide +kernel

theorem b401_relative_left_inverse :
    b401free * b401relative = 1 := by decide +kernel

theorem b401_relative_complete :
    b401relative * b401free + b401split * b401lower = 1 := by decide +kernel

theorem b401_kernel_annihilated :
    b401h * b401null = 0 := by decide +kernel

theorem b401_kernel_left_inverse :
    b401nullFree * b401null = 1 := by decide +kernel

theorem b401_kernel_complete :
    b401null * b401nullFree + b401nullSplit * b401h = 1 := by decide +kernel

theorem b401_kernel_preserved :
    b401E * b401null = 0 := by decide +kernel

theorem b401_comparison_positive :
    (TorusLean.M2.complexify b401comparison).PosSemidef := by
  rw [b401_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b401_factor_acceptance

theorem b401_relative_exact (v : Fin 1 → ℚ) :
    b401lower *ᵥ v = 0 ↔ ∃ x : Fin 0 → ℚ, b401relative *ᵥ x = v :=
  kernel_from_split b401lower b401relative b401free b401split
    b401_relative_annihilated b401_relative_complete v

theorem b401_zero_kernel_preserved (v : Fin 0 → ℚ)
    (hv : b401h *ᵥ v = 0) : b401comparison *ᵥ v = 0 := by
  rw [b401_comparison_reconstruction]
  exact kernel_preserved_from_split b401h b401E b401null
    b401nullFree b401nullSplit b401_kernel_complete
    b401_kernel_preserved v hv

#print axioms b401_comparison_reconstruction
#print axioms b401_factor_acceptance
#print axioms b401_hamiltonian_factor_acceptance
#print axioms b401_relative_annihilated
#print axioms b401_relative_left_inverse
#print axioms b401_relative_complete
#print axioms b401_kernel_annihilated
#print axioms b401_kernel_left_inverse
#print axioms b401_kernel_complete
#print axioms b401_kernel_preserved
#print axioms b401_comparison_positive
#print axioms b401_relative_exact
#print axioms b401_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
