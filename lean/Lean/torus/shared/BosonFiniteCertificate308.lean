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

def b308h : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(59049/35), (-59049/35);
    (-59049/35), (59049/35)]

def b308s : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(59049/4480), (-59049/4480);
    (-59049/4480), (59049/4480)]

def b308average : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(24539885076590598328130721/1914062500000000000000000), (-24539885076590598328130721/1914062500000000000000000);
    (-24539885076590598328130721/1914062500000000000000000), (24539885076590598328130721/1914062500000000000000000)]

def b308E : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(691798755440651671869279/1914062500000000000000000), (-691798755440651671869279/1914062500000000000000000);
    (-691798755440651671869279/1914062500000000000000000), (691798755440651671869279/1914062500000000000000000)]

def b308L : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0;
    -1, 0]

def b308pivots : Fin 2 → ℚ := ![(691798755440651671869279/1914062500000000000000000), 0]

def b308hL : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0;
    -1, 0]

def b308hPivots : Fin 2 → ℚ := ![(59049/35), 0]

def b308lower : Matrix (Fin 8) (Fin 10) ℚ :=
  !![8, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 7, 2, 0, 0, 2, 0, 0, 0, 0;
    0, 0, 6, 3, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 5, 8, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 6, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 5, 3, 4, 0;
    0, 0, 0, 0, 0, 0, 0, 4, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 4, 6]

def b308relative : Matrix (Fin 10) (Fin 2) ℚ :=
  !![(1/35), (-1/35);
    (-8/35), (8/35);
    (4/5), (-3/10);
    (-8/5), (1/10);
    1, 0;
    0, (-1/2);
    0, (3/2);
    0, (-1/2);
    0, (-3/2);
    0, 1]

def b308free : Matrix (Fin 2) (Fin 10) ℚ :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def b308split : Matrix (Fin 10) (Fin 8) ℚ :=
  !![(1/8), (-1/56), (1/168), (-1/280), (1/168), (-1/280), (1/280), (1/280);
    0, (1/7), (-1/21), (1/35), (-1/21), (1/35), (-1/35), (-1/35);
    0, 0, (1/6), (-1/10), 0, (-1/30), (1/20), (1/30);
    0, 0, 0, (1/5), 0, 0, (-1/20), 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, (1/6), (-1/15), (1/20), (1/15);
    0, 0, 0, 0, 0, (1/5), (-3/20), (-1/5);
    0, 0, 0, 0, 0, 0, (1/4), 0;
    0, 0, 0, 0, 0, 0, 0, (1/4);
    0, 0, 0, 0, 0, 0, 0, 0]

def b308null : Matrix (Fin 2) (Fin 1) ℚ :=
  !![1;
    1]

def b308nullFree : Matrix (Fin 1) (Fin 2) ℚ :=
  !![0, 1]

def b308nullSplit : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(35/59049), 0;
    0, 0]

def b308comparison : Matrix (Fin 2) (Fin 2) ℚ :=
  (1) • b308s - b308average + delta • b308h

theorem b308_comparison_reconstruction :
    b308comparison = b308E := by decide +kernel

theorem b308_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b308E b308L b308pivots = true := by decide +kernel

theorem b308_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b308h b308hL b308hPivots = true := by decide +kernel

theorem b308_relative_annihilated :
    b308lower * b308relative = 0 := by decide +kernel

theorem b308_relative_left_inverse :
    b308free * b308relative = 1 := by decide +kernel

theorem b308_relative_complete :
    b308relative * b308free + b308split * b308lower = 1 := by decide +kernel

theorem b308_kernel_annihilated :
    b308h * b308null = 0 := by decide +kernel

theorem b308_kernel_left_inverse :
    b308nullFree * b308null = 1 := by decide +kernel

theorem b308_kernel_complete :
    b308null * b308nullFree + b308nullSplit * b308h = 1 := by decide +kernel

theorem b308_kernel_preserved :
    b308E * b308null = 0 := by decide +kernel

theorem b308_comparison_positive :
    (TorusLean.M2.complexify b308comparison).PosSemidef := by
  rw [b308_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b308_factor_acceptance

theorem b308_relative_exact (v : Fin 10 → ℚ) :
    b308lower *ᵥ v = 0 ↔ ∃ x : Fin 2 → ℚ, b308relative *ᵥ x = v :=
  kernel_from_split b308lower b308relative b308free b308split
    b308_relative_annihilated b308_relative_complete v

theorem b308_zero_kernel_preserved (v : Fin 2 → ℚ)
    (hv : b308h *ᵥ v = 0) : b308comparison *ᵥ v = 0 := by
  rw [b308_comparison_reconstruction]
  exact kernel_preserved_from_split b308h b308E b308null
    b308nullFree b308nullSplit b308_kernel_complete
    b308_kernel_preserved v hv

#print axioms b308_comparison_reconstruction
#print axioms b308_factor_acceptance
#print axioms b308_hamiltonian_factor_acceptance
#print axioms b308_relative_annihilated
#print axioms b308_relative_left_inverse
#print axioms b308_relative_complete
#print axioms b308_kernel_annihilated
#print axioms b308_kernel_left_inverse
#print axioms b308_kernel_complete
#print axioms b308_kernel_preserved
#print axioms b308_comparison_positive
#print axioms b308_relative_exact
#print axioms b308_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
