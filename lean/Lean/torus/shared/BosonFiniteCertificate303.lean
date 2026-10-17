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

def b303h : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(81/8)]

def b303s : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-81/32)]

def b303average : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-12885025163279851361639099/5062500000000000000000000)]

def b303E : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(70623296092351361639099/5062500000000000000000000)]

def b303L : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b303pivots : Fin 1 → ℚ := ![(70623296092351361639099/5062500000000000000000000)]

def b303hL : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

def b303hPivots : Fin 1 → ℚ := ![(81/8)]

def b303lower : Matrix (Fin 2) (Fin 3) ℚ :=
  !![3, 1, 0;
    0, 2, 3]

def b303relative : Matrix (Fin 3) (Fin 1) ℚ :=
  !![(1/2);
    (-3/2);
    1]

def b303free : Matrix (Fin 1) (Fin 3) ℚ :=
  !![0, 0, 1]

def b303split : Matrix (Fin 3) (Fin 2) ℚ :=
  !![(1/3), (-1/6);
    0, (1/2);
    0, 0]

def b303null : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

def b303nullFree : Matrix (Fin 0) (Fin 1) ℚ :=
  fun _ _ => 0

def b303nullSplit : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(8/81)]

def b303comparison : Matrix (Fin 1) (Fin 1) ℚ :=
  (1) • b303s - b303average + delta • b303h

theorem b303_comparison_reconstruction :
    b303comparison = b303E := by decide +kernel

theorem b303_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b303E b303L b303pivots = true := by decide +kernel

theorem b303_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b303h b303hL b303hPivots = true := by decide +kernel

theorem b303_relative_annihilated :
    b303lower * b303relative = 0 := by decide +kernel

theorem b303_relative_left_inverse :
    b303free * b303relative = 1 := by decide +kernel

theorem b303_relative_complete :
    b303relative * b303free + b303split * b303lower = 1 := by decide +kernel

theorem b303_kernel_annihilated :
    b303h * b303null = 0 := by decide +kernel

theorem b303_kernel_left_inverse :
    b303nullFree * b303null = 1 := by decide +kernel

theorem b303_kernel_complete :
    b303null * b303nullFree + b303nullSplit * b303h = 1 := by decide +kernel

theorem b303_kernel_preserved :
    b303E * b303null = 0 := by decide +kernel

theorem b303_comparison_positive :
    (TorusLean.M2.complexify b303comparison).PosSemidef := by
  rw [b303_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b303_factor_acceptance

theorem b303_relative_exact (v : Fin 3 → ℚ) :
    b303lower *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b303relative *ᵥ x = v :=
  kernel_from_split b303lower b303relative b303free b303split
    b303_relative_annihilated b303_relative_complete v

theorem b303_zero_kernel_preserved (v : Fin 1 → ℚ)
    (hv : b303h *ᵥ v = 0) : b303comparison *ᵥ v = 0 := by
  rw [b303_comparison_reconstruction]
  exact kernel_preserved_from_split b303h b303E b303null
    b303nullFree b303nullSplit b303_kernel_complete
    b303_kernel_preserved v hv

#print axioms b303_comparison_reconstruction
#print axioms b303_factor_acceptance
#print axioms b303_hamiltonian_factor_acceptance
#print axioms b303_relative_annihilated
#print axioms b303_relative_left_inverse
#print axioms b303_relative_complete
#print axioms b303_kernel_annihilated
#print axioms b303_kernel_left_inverse
#print axioms b303_kernel_complete
#print axioms b303_kernel_preserved
#print axioms b303_comparison_positive
#print axioms b303_relative_exact
#print axioms b303_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
