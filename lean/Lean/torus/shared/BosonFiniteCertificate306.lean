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

def b306h : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(6561/40), (-6561/40);
    (-6561/40), (6561/40)]

def b306s : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(6561/1280), (-6561/1280);
    (-6561/1280), (6561/1280)]

def b306average : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1279271266181869704132993/250000000000000000000000), (-1279271266181869704132993/250000000000000000000000);
    (-1279271266181869704132993/250000000000000000000000), (1279271266181869704132993/250000000000000000000000)]

def b306E : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(2215052568130295867007/250000000000000000000000), (-2215052568130295867007/250000000000000000000000);
    (-2215052568130295867007/250000000000000000000000), (2215052568130295867007/250000000000000000000000)]

def b306L : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0;
    -1, 0]

def b306pivots : Fin 2 → ℚ := ![(2215052568130295867007/250000000000000000000000), 0]

def b306hL : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0;
    -1, 0]

def b306hPivots : Fin 2 → ℚ := ![(6561/40), 0]

def b306lower : Matrix (Fin 5) (Fin 7) ℚ :=
  !![6, 1, 0, 0, 0, 0, 0;
    0, 5, 2, 0, 2, 0, 0;
    0, 0, 4, 6, 0, 1, 0;
    0, 0, 0, 0, 4, 2, 0;
    0, 0, 0, 0, 0, 3, 6]

def b306relative : Matrix (Fin 7) (Fin 2) ℚ :=
  !![(-1/10), (1/10);
    (3/5), (-3/5);
    (-3/2), (1/2);
    1, 0;
    0, 1;
    0, -2;
    0, 1]

def b306free : Matrix (Fin 2) (Fin 7) ℚ :=
  !![0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1]

def b306split : Matrix (Fin 7) (Fin 5) ℚ :=
  !![(1/6), (-1/30), (1/60), (1/60), (-1/60);
    0, (1/5), (-1/10), (-1/10), (1/10);
    0, 0, (1/4), 0, (-1/12);
    0, 0, 0, 0, 0;
    0, 0, 0, (1/4), (-1/6);
    0, 0, 0, 0, (1/3);
    0, 0, 0, 0, 0]

def b306null : Matrix (Fin 2) (Fin 1) ℚ :=
  !![1;
    1]

def b306nullFree : Matrix (Fin 1) (Fin 2) ℚ :=
  !![0, 1]

def b306nullSplit : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(40/6561), 0;
    0, 0]

def b306comparison : Matrix (Fin 2) (Fin 2) ℚ :=
  (1) • b306s - b306average + delta • b306h

theorem b306_comparison_reconstruction :
    b306comparison = b306E := by decide +kernel

theorem b306_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b306E b306L b306pivots = true := by decide +kernel

theorem b306_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b306h b306hL b306hPivots = true := by decide +kernel

theorem b306_relative_annihilated :
    b306lower * b306relative = 0 := by decide +kernel

theorem b306_relative_left_inverse :
    b306free * b306relative = 1 := by decide +kernel

theorem b306_relative_complete :
    b306relative * b306free + b306split * b306lower = 1 := by decide +kernel

theorem b306_kernel_annihilated :
    b306h * b306null = 0 := by decide +kernel

theorem b306_kernel_left_inverse :
    b306nullFree * b306null = 1 := by decide +kernel

theorem b306_kernel_complete :
    b306null * b306nullFree + b306nullSplit * b306h = 1 := by decide +kernel

theorem b306_kernel_preserved :
    b306E * b306null = 0 := by decide +kernel

theorem b306_comparison_positive :
    (TorusLean.M2.complexify b306comparison).PosSemidef := by
  rw [b306_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b306_factor_acceptance

theorem b306_relative_exact (v : Fin 7 → ℚ) :
    b306lower *ᵥ v = 0 ↔ ∃ x : Fin 2 → ℚ, b306relative *ᵥ x = v :=
  kernel_from_split b306lower b306relative b306free b306split
    b306_relative_annihilated b306_relative_complete v

theorem b306_zero_kernel_preserved (v : Fin 2 → ℚ)
    (hv : b306h *ᵥ v = 0) : b306comparison *ᵥ v = 0 := by
  rw [b306_comparison_reconstruction]
  exact kernel_preserved_from_split b306h b306E b306null
    b306nullFree b306nullSplit b306_kernel_complete
    b306_kernel_preserved v hv

#print axioms b306_comparison_reconstruction
#print axioms b306_factor_acceptance
#print axioms b306_hamiltonian_factor_acceptance
#print axioms b306_relative_annihilated
#print axioms b306_relative_left_inverse
#print axioms b306_relative_complete
#print axioms b306_kernel_annihilated
#print axioms b306_kernel_left_inverse
#print axioms b306_kernel_complete
#print axioms b306_kernel_preserved
#print axioms b306_comparison_positive
#print axioms b306_relative_exact
#print axioms b306_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
