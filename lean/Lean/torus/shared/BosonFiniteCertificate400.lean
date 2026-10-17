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

def b400h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![144]

def b400s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![144]

def b400average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1088232871132987271798731360797712569/9395240960000000000000000000000000)]

def b400E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(473644590916212189999960985930176534687917/134811438777630720000000000000000000000000)]

def b400L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b400pivots : Fin 1 → ℚ := ![(473644590916212189999960985930176534687917/134811438777630720000000000000000000000000)]

def b400hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b400hPivots : Fin 1 → ℚ := ![144]

def b400lower : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b400relative : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b400free : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b400split : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b400null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b400nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b400nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/144)]

def b400comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (alpha) • b400s - b400average + delta • b400h

theorem b400_comparison_reconstruction :
    b400comparison = b400E := by decide +kernel

theorem b400_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b400E b400L b400pivots = true := by decide +kernel

theorem b400_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b400h b400hL b400hPivots = true := by decide +kernel

theorem b400_relative_annihilated :
    b400lower * b400relative = 0 := by decide +kernel

theorem b400_relative_left_inverse :
    b400free * b400relative = 1 := by decide +kernel

theorem b400_relative_complete :
    b400relative * b400free + b400split * b400lower = 1 := by decide +kernel

theorem b400_kernel_annihilated :
    b400h * b400null = 0 := by decide +kernel

theorem b400_kernel_left_inverse :
    b400nullFree * b400null = 1 := by decide +kernel

theorem b400_kernel_complete :
    b400null * b400nullFree + b400nullSplit * b400h = 1 := by decide +kernel

theorem b400_kernel_preserved :
    b400E * b400null = 0 := by decide +kernel

theorem b400_comparison_positive :
    (TorusLean.M2.complexify b400comparison).PosSemidef := by
  rw [b400_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b400_factor_acceptance

theorem b400_relative_exact (v : Fin 1 → ℚ) :
    b400lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b400relative *ᵥ x = v :=
  kernel_from_split b400lower b400relative b400free b400split
    b400_relative_annihilated b400_relative_complete v

theorem b400_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b400h *ᵥ v = 0) : b400comparison *ᵥ v = 0 := by
  rw [b400_comparison_reconstruction]
  exact kernel_preserved_from_split b400h b400E b400null
    b400nullFree b400nullSplit b400_kernel_complete
    b400_kernel_preserved v hv

#print axioms b400_comparison_reconstruction
#print axioms b400_factor_acceptance
#print axioms b400_hamiltonian_factor_acceptance
#print axioms b400_relative_annihilated
#print axioms b400_relative_left_inverse
#print axioms b400_relative_complete
#print axioms b400_kernel_annihilated
#print axioms b400_kernel_left_inverse
#print axioms b400_kernel_complete
#print axioms b400_kernel_preserved
#print axioms b400_comparison_positive
#print axioms b400_relative_exact
#print axioms b400_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
