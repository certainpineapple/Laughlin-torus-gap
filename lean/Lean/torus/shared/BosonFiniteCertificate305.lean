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

def b305h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(405/8)]

def b305s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-405/128)]

def b305average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-192567057796353844300252699/60750000000000000000000000)]

def b305E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(353336390103844300252699/60750000000000000000000000)]

def b305L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b305pivots : Fin 1 → ℚ := ![(353336390103844300252699/60750000000000000000000000)]

def b305hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b305hPivots : Fin 1 → ℚ := ![(405/8)]

def b305lower : Matrix (Fin 4) (Fin 5) ℚ :=
  !![5, 1, 0, 0, 0;
    0, 4, 2, 2, 0;
    0, 0, 3, 0, 1;
    0, 0, 0, 3, 4]

def b305relative : Matrix (Fin 5) (Fin 1) ℚ :=
  !![(-1/6);
    (5/6);
    (-1/3);
    (-4/3);
    1]

def b305free : Matrix (Fin 1) (Fin 5) ℚ :=
  !![0, 0, 0, 0, 1]

def b305split : Matrix (Fin 5) (Fin 4) ℚ :=
  !![(1/5), (-1/20), (1/30), (1/30);
    0, (1/4), (-1/6), (-1/6);
    0, 0, (1/3), 0;
    0, 0, 0, (1/3);
    0, 0, 0, 0]

def b305null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b305nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b305nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(8/405)]

def b305comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (1) • b305s - b305average + delta • b305h

theorem b305_comparison_reconstruction :
    b305comparison = b305E := by decide +kernel

theorem b305_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b305E b305L b305pivots = true := by decide +kernel

theorem b305_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b305h b305hL b305hPivots = true := by decide +kernel

theorem b305_relative_annihilated :
    b305lower * b305relative = 0 := by decide +kernel

theorem b305_relative_left_inverse :
    b305free * b305relative = 1 := by decide +kernel

theorem b305_relative_complete :
    b305relative * b305free + b305split * b305lower = 1 := by decide +kernel

theorem b305_kernel_annihilated :
    b305h * b305null = 0 := by decide +kernel

theorem b305_kernel_left_inverse :
    b305nullFree * b305null = 1 := by decide +kernel

theorem b305_kernel_complete :
    b305null * b305nullFree + b305nullSplit * b305h = 1 := by decide +kernel

theorem b305_kernel_preserved :
    b305E * b305null = 0 := by decide +kernel

theorem b305_comparison_positive :
    (TorusLean.M2.complexify b305comparison).PosSemidef := by
  rw [b305_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b305_factor_acceptance

theorem b305_relative_exact (v : Fin 5 → ℚ) :
    b305lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b305relative *ᵥ x = v :=
  kernel_from_split b305lower b305relative b305free b305split
    b305_relative_annihilated b305_relative_complete v

theorem b305_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b305h *ᵥ v = 0) : b305comparison *ᵥ v = 0 := by
  rw [b305_comparison_reconstruction]
  exact kernel_preserved_from_split b305h b305E b305null
    b305nullFree b305nullSplit b305_kernel_complete
    b305_kernel_preserved v hv

#print axioms b305_comparison_reconstruction
#print axioms b305_factor_acceptance
#print axioms b305_hamiltonian_factor_acceptance
#print axioms b305_relative_annihilated
#print axioms b305_relative_left_inverse
#print axioms b305_relative_complete
#print axioms b305_kernel_annihilated
#print axioms b305_kernel_left_inverse
#print axioms b305_kernel_complete
#print axioms b305_kernel_preserved
#print axioms b305_comparison_positive
#print axioms b305_relative_exact
#print axioms b305_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
