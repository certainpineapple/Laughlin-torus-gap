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

def b404h : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(520/3), (-364/3);
    (-364/3), (562/3)]

def b404s : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(128/3), (64/3);
    (64/3), (32/3)]

def b404average : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1614656475841088260269634498723363/132120576000000000000000000000000), (5773649968705491896270508249501661/660602880000000000000000000000000);
    (5773649968705491896270508249501661/660602880000000000000000000000000), (-3266687634841854271159674072837769/660602880000000000000000000000000)]

def b404E : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(131602536986012084828437658961480536757277/5687357573431296000000000000000000000000), (254227895324566219387242490855503609896419/28436787867156480000000000000000000000000);
    (254227895324566219387242490855503609896419/28436787867156480000000000000000000000000), (392009540874123364847188836264381120405449/28436787867156480000000000000000000000000)]

def b404L : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0;
    (254227895324566219387242490855503609896419/658012684930060424142188294807402683786385), 1]

def b404pivots : Fin 2 → ℚ := ![(131602536986012084828437658961480536757277/5687357573431296000000000000000000000000), (13365560061198747861390999149418306083328501531920930937287156492878971509/1293705579587293198697473562654938268538735820800000000000000000000000000)]

def b404hL : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0;
    (-7/10), 1]

def b404hPivots : Fin 2 → ℚ := ![(520/3), (512/5)]

def b404lower : Matrix (Fin 3) (Fin 5) ℚ :=
  !![4, 1, 0, 0, 0;
    0, 3, 4, 2, 0;
    0, 0, 0, 2, 4]

def b404relative : Matrix (Fin 5) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (-4/3), (4/3);
    1, 0;
    0, -2;
    0, 1]

def b404free : Matrix (Fin 2) (Fin 5) ℚ :=
  !![0, 0, 1, 0, 0;
    0, 0, 0, 0, 1]

def b404split : Matrix (Fin 5) (Fin 3) ℚ :=
  !![(1/4), (-1/12), (1/12);
    0, (1/3), (-1/3);
    0, 0, 0;
    0, 0, (1/2);
    0, 0, 0]

def b404null : Matrix (Fin 2) (Fin 0) ℚ :=
  fun _ _ => 0

def b404nullFree : Matrix (Fin 0) (Fin 2) ℚ :=
  fun _ _ => 0

def b404nullSplit : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(281/26624), (7/1024);
    (7/1024), (5/512)]

def b404comparison : Matrix (Fin 2) (Fin 2) ℚ :=
  (alpha) • b404s - b404average + delta • b404h

theorem b404_comparison_reconstruction :
    b404comparison = b404E := by decide +kernel

theorem b404_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b404E b404L b404pivots = true := by decide +kernel

theorem b404_hamiltonian_factor_acceptance :
    TorusLean.M2.rationalPSDCheck b404h b404hL b404hPivots = true := by decide +kernel

theorem b404_relative_annihilated :
    b404lower * b404relative = 0 := by decide +kernel

theorem b404_relative_left_inverse :
    b404free * b404relative = 1 := by decide +kernel

theorem b404_relative_complete :
    b404relative * b404free + b404split * b404lower = 1 := by decide +kernel

theorem b404_kernel_annihilated :
    b404h * b404null = 0 := by decide +kernel

theorem b404_kernel_left_inverse :
    b404nullFree * b404null = 1 := by decide +kernel

theorem b404_kernel_complete :
    b404null * b404nullFree + b404nullSplit * b404h = 1 := by decide +kernel

theorem b404_kernel_preserved :
    b404E * b404null = 0 := by decide +kernel

theorem b404_comparison_positive :
    (TorusLean.M2.complexify b404comparison).PosSemidef := by
  rw [b404_comparison_reconstruction]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ b404_factor_acceptance

theorem b404_relative_exact (v : Fin 5 → ℚ) :
    b404lower *ᵥ v = 0 ↔ ∃ x : Fin 2 → ℚ, b404relative *ᵥ x = v :=
  kernel_from_split b404lower b404relative b404free b404split
    b404_relative_annihilated b404_relative_complete v

theorem b404_zero_kernel_preserved (v : Fin 2 → ℚ)
    (hv : b404h *ᵥ v = 0) : b404comparison *ᵥ v = 0 := by
  rw [b404_comparison_reconstruction]
  exact kernel_preserved_from_split b404h b404E b404null
    b404nullFree b404nullSplit b404_kernel_complete
    b404_kernel_preserved v hv

#print axioms b404_comparison_reconstruction
#print axioms b404_factor_acceptance
#print axioms b404_hamiltonian_factor_acceptance
#print axioms b404_relative_annihilated
#print axioms b404_relative_left_inverse
#print axioms b404_relative_complete
#print axioms b404_kernel_annihilated
#print axioms b404_kernel_left_inverse
#print axioms b404_kernel_complete
#print axioms b404_kernel_preserved
#print axioms b404_comparison_positive
#print axioms b404_relative_exact
#print axioms b404_zero_kernel_preserved

end TorusLean.BosonFiniteCertificate
