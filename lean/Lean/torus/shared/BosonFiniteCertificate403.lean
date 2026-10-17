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

def b403h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![72]

def b403s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![0]

def b403average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-9582477567299087481442642956689811/4697620480000000000000000000000000)]

def b403E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(9582815795973647481442642956689811/4697620480000000000000000000000000)]

def b403L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b403pivots : Fin 1 → ℚ := ![(9582815795973647481442642956689811/4697620480000000000000000000000000)]

def b403hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b403hPivots : Fin 1 → ℚ := ![72]

def b403lower : Matrix (Fin 2) (Fin 3) ℚ :=
  !![3, 1, 0;
    0, 2, 3]

def b403relative : Matrix (Fin 3) (Fin 1) ℚ :=
  !![(1/2);
    (-3/2);
    1]

def b403free : Matrix (Fin 1) (Fin 3) ℚ :=
  !![0, 0, 1]

def b403split : Matrix (Fin 3) (Fin 2) ℚ :=
  !![(1/3), (-1/6);
    0, (1/2);
    0, 0]

def b403null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b403nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b403nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/72)]

def b403comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (alpha) • b403s - b403average + delta • b403h

theorem b403_comparison_reconstruction :
    b403comparison = b403E := by decide +kernel

theorem b403_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b403E b403L b403pivots = true := by decide +kernel

theorem b403_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b403h b403hL b403hPivots = true := by decide +kernel

theorem b403_relative_annihilated :
    b403lower * b403relative = 0 := by decide +kernel

theorem b403_relative_left_inverse :
    b403free * b403relative = 1 := by decide +kernel

theorem b403_relative_complete :
    b403relative * b403free + b403split * b403lower = 1 := by decide +kernel

theorem b403_kernel_annihilated :
    b403h * b403null = 0 := by decide +kernel

theorem b403_kernel_left_inverse :
    b403nullFree * b403null = 1 := by decide +kernel

theorem b403_kernel_complete :
    b403null * b403nullFree + b403nullSplit * b403h = 1 := by decide +kernel

theorem b403_kernel_preserved :
    b403E * b403null = 0 := by decide +kernel

theorem b403_comparison_positive :
    (TorusLean.M2.complexify b403comparison).PosSemidef := by
  rw [b403_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b403_factor_acceptance

theorem b403_relative_exact (v : Fin 3 → ℚ) :
    b403lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b403relative *ᵥ x = v :=
  kernel_from_split b403lower b403relative b403free b403split
    b403_relative_annihilated b403_relative_complete v

theorem b403_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b403h *ᵥ v = 0) : b403comparison *ᵥ v = 0 := by
  rw [b403_comparison_reconstruction]
  exact kernel_preserved_from_split b403h b403E b403null
    b403nullFree b403nullSplit b403_kernel_complete
    b403_kernel_preserved v hv

#print axioms b403_comparison_reconstruction
#print axioms b403_factor_acceptance
#print axioms b403_hamiltonian_factor_acceptance
#print axioms b403_relative_annihilated
#print axioms b403_relative_left_inverse
#print axioms b403_relative_complete
#print axioms b403_kernel_annihilated
#print axioms b403_kernel_left_inverse
#print axioms b403_kernel_complete
#print axioms b403_kernel_preserved
#print axioms b403_comparison_positive
#print axioms b403_relative_exact
#print axioms b403_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
