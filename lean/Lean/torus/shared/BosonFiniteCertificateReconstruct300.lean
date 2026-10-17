/- Reconstruct the anchored planar N=3 matrix from all original integer rows.
No finite torus h projection is assumed. -/
import torus.shared.BosonFiniteCertificatePlanar
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
namespace TorusLean.BosonFiniteCertificate

def p300basis : Fin 1 → List ℕ := ![[0, 0, 0]]

theorem p300_basis_enumerated :
    (List.finRange 1).map p300basis = threeBasis 0 := by decide +kernel

def p300action0 : Matrix (Fin 31) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    -553112028;
    -812156844;
    -263222226;
    -328077474;
    -633087342;
    -915682842;
    -334427376;
    -970062444;
    -360771864;
    -1217162334;
    3711532932;
    1104414090;
    -22359647748;
    62618565168;
    -47829818346;
    18682091892;
    -24695498736;
    188893126764;
    -168484101372;
    -122955430680;
    -176753539206;
    375997742820;
    830591424576;
    -684705956616;
    -3775043805414]

def p300action0Raw : Matrix (Fin 31) (Fin 1) ℤ := fun r i => threeRowAction 0 ((frozenRows 0)[r.val]?.getD []) (p300basis i)

theorem p300action0_reconstructed : p300action0Raw = p300action0 := by decide +kernel

def p300pair0 : Matrix (Fin 31) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    -553322676;
    -812344110;
    -263351886;
    -327701040;
    -632772378;
    -916650654;
    -334709292;
    -968844870;
    -360225462;
    -1214963682;
    3777601260;
    1235556882;
    -21751510128;
    60824093520;
    -51375716742;
    6949629828;
    -3075428370;
    315471575574;
    -450768253632;
    119776626996;
    -10718502288;
    16190352816;
    390720532422;
    -917598801540;
    -2372284537722]

def p300pair0Raw : Matrix (Fin 31) (Fin 1) ℤ := fun r i => rowInteger ((frozenRows 0)[r.val]?.getD []) 0 * (pairRemoval (p300basis i) 0 : ℤ)

theorem p300pair0_reconstructed : p300pair0Raw = p300pair0 := by decide +kernel

def p300action1 : Matrix (Fin 37) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0]

def p300action1Raw : Matrix (Fin 37) (Fin 1) ℤ := fun r i => threeRowAction 1 ((frozenRows 1)[r.val]?.getD []) (p300basis i)

theorem p300action1_reconstructed : p300action1Raw = p300action1 := by decide +kernel

def p300pair1 : Matrix (Fin 37) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0]

def p300pair1Raw : Matrix (Fin 37) (Fin 1) ℤ := fun r i => rowInteger ((frozenRows 1)[r.val]?.getD []) 0 * (pairRemoval (p300basis i) 1 : ℤ)

theorem p300pair1_reconstructed : p300pair1Raw = p300pair1 := by decide +kernel

def p300action2 : Matrix (Fin 36) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0]

def p300action2Raw : Matrix (Fin 36) (Fin 1) ℤ := fun r i => threeRowAction 2 ((frozenRows 2)[r.val]?.getD []) (p300basis i)

theorem p300action2_reconstructed : p300action2Raw = p300action2 := by decide +kernel

def p300pair2 : Matrix (Fin 36) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0]

def p300pair2Raw : Matrix (Fin 36) (Fin 1) ℤ := fun r i => rowInteger ((frozenRows 2)[r.val]?.getD []) 0 * (pairRemoval (p300basis i) 2 : ℤ)

theorem p300pair2_reconstructed : p300pair2Raw = p300pair2 := by decide +kernel

def p300action3 : Matrix (Fin 34) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0]

def p300action3Raw : Matrix (Fin 34) (Fin 1) ℤ := fun r i => threeRowAction 3 ((frozenRows 3)[r.val]?.getD []) (p300basis i)

theorem p300action3_reconstructed : p300action3Raw = p300action3 := by decide +kernel

def p300pair3 : Matrix (Fin 34) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0]

def p300pair3Raw : Matrix (Fin 34) (Fin 1) ℤ := fun r i => rowInteger ((frozenRows 3)[r.val]?.getD []) 0 * (pairRemoval (p300basis i) 3 : ℤ)

theorem p300pair3_reconstructed : p300pair3Raw = p300pair3 := by decide +kernel

def p300rawNumerator : Matrix (Fin 1) (Fin 1) ℤ :=
  (1 : ℤ) • ((p300action0Raw)ᵀ * p300action0Raw - (p300pair0Raw)ᵀ * p300pair0Raw)

def p300numerator : Matrix (Fin 1) (Fin 1) ℤ :=
  !![8722436848062034142133792]

theorem p300_numerator_reconstructed :
    p300rawNumerator = p300numerator := by
  unfold p300rawNumerator
  simp only [p300action0_reconstructed, p300pair0_reconstructed, p300action1_reconstructed, p300pair1_reconstructed, p300action2_reconstructed, p300pair2_reconstructed, p300action3_reconstructed, p300pair3_reconstructed]
  decide +kernel

def p300Mform : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(272576151501938566941681/31250000000000000000000)]

def p300rawMform : Matrix (Fin 1) (Fin 1) ℚ :=
  integerForm p300rawNumerator

theorem p300_Mform_reconstructed : p300rawMform = p300Mform := by
  unfold p300rawMform
  rw [p300_numerator_reconstructed]
  decide +kernel

def p300Hform : Matrix (Fin 1) (Fin 1) ℚ :=
  !![18]

def p300Sform : Matrix (Fin 1) (Fin 1) ℚ :=
  !![36]

def p300Ginv : Matrix (Fin 1) (Fin 1) ℚ :=
  Matrix.diagonal ![(1/6)]

def p300rawHform : Matrix (Fin 1) (Fin 1) ℚ := fun i j => planarHForm 0 (p300basis i) (p300basis j)

theorem p300_Hform_reconstructed :
    p300rawHform = p300Hform := by decide +kernel

theorem p300_Sform_reconstructed :
    planarSingleForm p300Ginv p300Hform = p300Sform := by decide +kernel

#print axioms p300action0_reconstructed
#print axioms p300pair0_reconstructed
#print axioms p300action1_reconstructed
#print axioms p300pair1_reconstructed
#print axioms p300action2_reconstructed
#print axioms p300pair2_reconstructed
#print axioms p300action3_reconstructed
#print axioms p300pair3_reconstructed
#print axioms p300_basis_enumerated
#print axioms p300_numerator_reconstructed
#print axioms p300_Mform_reconstructed
#print axioms p300_Hform_reconstructed
#print axioms p300_Sform_reconstructed

end TorusLean.BosonFiniteCertificate
