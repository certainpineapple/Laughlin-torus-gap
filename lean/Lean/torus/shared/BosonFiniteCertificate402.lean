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

def b402h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![64]

def b402s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![32]

def b402average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(97220331602677048370792349551241593/4697620480000000000000000000000000)]

def b402E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(3533566795909849901084351539799683827600341/606651474499338240000000000000000000000000)]

def b402L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b402pivots : Fin 1 → ℚ := ![(3533566795909849901084351539799683827600341/606651474499338240000000000000000000000000)]

def b402hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b402hPivots : Fin 1 → ℚ := ![64]

def b402lower : Matrix (Fin 1) (Fin 2) ℚ :=
  !![2, 2]

def b402relative : Matrix (Fin 2) (Fin 1) ℚ :=
  !![-1;
    1]

def b402free : Matrix (Fin 1) (Fin 2) ℚ :=
  !![0, 1]

def b402split : Matrix (Fin 2) (Fin 1) ℚ :=
  !![(1/2);
    0]

def b402null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b402nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b402nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/64)]

def b402comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (alpha) • b402s - b402average + delta • b402h

theorem b402_comparison_reconstruction :
    b402comparison = b402E := by decide +kernel

theorem b402_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b402E b402L b402pivots = true := by decide +kernel

theorem b402_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b402h b402hL b402hPivots = true := by decide +kernel

theorem b402_relative_annihilated :
    b402lower * b402relative = 0 := by decide +kernel

theorem b402_relative_left_inverse :
    b402free * b402relative = 1 := by decide +kernel

theorem b402_relative_complete :
    b402relative * b402free + b402split * b402lower = 1 := by decide +kernel

theorem b402_kernel_annihilated :
    b402h * b402null = 0 := by decide +kernel

theorem b402_kernel_left_inverse :
    b402nullFree * b402null = 1 := by decide +kernel

theorem b402_kernel_complete :
    b402null * b402nullFree + b402nullSplit * b402h = 1 := by decide +kernel

theorem b402_kernel_preserved :
    b402E * b402null = 0 := by decide +kernel

theorem b402_comparison_positive :
    (TorusLean.M2.complexify b402comparison).PosSemidef := by
  rw [b402_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b402_factor_acceptance

theorem b402_relative_exact (v : Fin 2 → ℚ) :
    b402lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b402relative *ᵥ x = v :=
  kernel_from_split b402lower b402relative b402free b402split
    b402_relative_annihilated b402_relative_complete v

theorem b402_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b402h *ᵥ v = 0) : b402comparison *ᵥ v = 0 := by
  rw [b402_comparison_reconstruction]
  exact kernel_preserved_from_split b402h b402E b402null
    b402nullFree b402nullSplit b402_kernel_complete
    b402_kernel_preserved v hv

#print axioms b402_comparison_reconstruction
#print axioms b402_factor_acceptance
#print axioms b402_hamiltonian_factor_acceptance
#print axioms b402_relative_annihilated
#print axioms b402_relative_left_inverse
#print axioms b402_relative_complete
#print axioms b402_kernel_annihilated
#print axioms b402_kernel_left_inverse
#print axioms b402_kernel_complete
#print axioms b402_kernel_preserved
#print axioms b402_comparison_positive
#print axioms b402_relative_exact
#print axioms b402_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
