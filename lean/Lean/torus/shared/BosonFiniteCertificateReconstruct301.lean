/- Reconstruct the anchored planar N=3 matrix from all original integer rows.
No finite torus h projection is assumed. -/
import torus.shared.BosonFiniteCertificatePlanar
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
namespace TorusLean.BosonFiniteCertificate

def p301basis : Fin 1 → List ℕ := ![[0, 0, 1]]

theorem p301_basis_enumerated :
    (List.finRange 1).map p301basis = threeBasis 1 := by decide +kernel

def p301action0 : Matrix (Fin 31) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    -184263952;
    -270786542;
    -87858446;
    -109617512;
    -211098756;
    -304440872;
    -111264376;
    -324219246;
    -119483410;
    -404313440;
    1239846124;
    -57922998;
    -7589415482;
    19406422870;
    -12094600312;
    8647733760;
    4522072844;
    67012598064;
    -53298373244;
    5672452304;
    -21954681308;
    -353583884872;
    355854402664;
    -1059017230288;
    -601429971114]

def p301action0Raw : Matrix (Fin 31) (Fin 1) ℤ := fun r i => threeRowAction 0 ((frozenRows 0)[r.val]?.getD []) (p301basis i)

theorem p301action0_reconstructed : p301action0Raw = p301action0 := by decide +kernel

def p301pair0 : Matrix (Fin 31) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    -184440892;
    -270781370;
    -87783962;
    -109233680;
    -210924126;
    -305550218;
    -111569764;
    -322948290;
    -120075154;
    -404987894;
    1259200420;
    411852294;
    -7250503376;
    20274697840;
    -17125238914;
    2316543276;
    -1025142790;
    105157191858;
    -150256084544;
    39925542332;
    -3572834096;
    5396784272;
    130240177474;
    -305866267180;
    -790761512574]

def p301pair0Raw : Matrix (Fin 31) (Fin 1) ℤ := fun r i => rowInteger ((frozenRows 0)[r.val]?.getD []) 0 * (pairRemoval (p301basis i) 0 : ℤ)

theorem p301pair0_reconstructed : p301pair0Raw = p301pair0 := by decide +kernel

def p301action1 : Matrix (Fin 37) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    -69998558;
    -242484978;
    -606583250;
    -93233976;
    -643372820;
    -280770820;
    -307045330;
    -816788272;
    -108130998;
    -427397132;
    1845672414;
    442933544;
    -5194769430;
    5613732252;
    -10603716662;
    69648000700;
    -65894442840;
    38894086712;
    -40435411812;
    167912426344;
    -164298892976;
    81534795602;
    174444674532;
    -226076260336;
    -526313006322;
    67079637256;
    -39208975886;
    -706343641864]

def p301action1Raw : Matrix (Fin 37) (Fin 1) ℤ := fun r i => threeRowAction 1 ((frozenRows 1)[r.val]?.getD []) (p301basis i)

theorem p301action1_reconstructed : p301action1Raw = p301action1 := by decide +kernel

def p301pair1 : Matrix (Fin 37) (Fin 1) ℤ :=
  !![0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    0;
    -69931640;
    -242488596;
    -606731888;
    -92917128;
    -642109256;
    -277988776;
    -306664492;
    -818060716;
    -108239244;
    -425919464;
    1848199056;
    455529944;
    -5233054824;
    5633650440;
    -10651465640;
    76824848200;
    -78783015408;
    48114198320;
    -71596185240;
    86159473288;
    -132144103868;
    74736798764;
    141477828348;
    -120391457056;
    73950695916;
    -57747617192;
    -50186440304;
    -203983191856]

def p301pair1Raw : Matrix (Fin 37) (Fin 1) ℤ := fun r i => rowInteger ((frozenRows 1)[r.val]?.getD []) 0 * (pairRemoval (p301basis i) 1 : ℤ)

theorem p301pair1_reconstructed : p301pair1Raw = p301pair1 := by decide +kernel

def p301action2 : Matrix (Fin 36) (Fin 1) ℤ :=
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

def p301action2Raw : Matrix (Fin 36) (Fin 1) ℤ := fun r i => threeRowAction 2 ((frozenRows 2)[r.val]?.getD []) (p301basis i)

theorem p301action2_reconstructed : p301action2Raw = p301action2 := by decide +kernel

def p301pair2 : Matrix (Fin 36) (Fin 1) ℤ :=
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

def p301pair2Raw : Matrix (Fin 36) (Fin 1) ℤ := fun r i => rowInteger ((frozenRows 2)[r.val]?.getD []) 0 * (pairRemoval (p301basis i) 2 : ℤ)

theorem p301pair2_reconstructed : p301pair2Raw = p301pair2 := by decide +kernel

def p301action3 : Matrix (Fin 34) (Fin 1) ℤ :=
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

def p301action3Raw : Matrix (Fin 34) (Fin 1) ℤ := fun r i => threeRowAction 3 ((frozenRows 3)[r.val]?.getD []) (p301basis i)

theorem p301action3_reconstructed : p301action3Raw = p301action3 := by decide +kernel

def p301pair3 : Matrix (Fin 34) (Fin 1) ℤ :=
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

def p301pair3Raw : Matrix (Fin 34) (Fin 1) ℤ := fun r i => rowInteger ((frozenRows 3)[r.val]?.getD []) 0 * (pairRemoval (p301basis i) 3 : ℤ)

theorem p301pair3_reconstructed : p301pair3Raw = p301pair3 := by decide +kernel

def p301rawNumerator : Matrix (Fin 1) (Fin 1) ℤ :=
  (1 : ℤ) • ((p301action0Raw)ᵀ * p301action0Raw - (p301pair0Raw)ᵀ * p301pair0Raw) +
    (1 : ℤ) • ((p301action1Raw)ᵀ * p301action1Raw - (p301pair1Raw)ᵀ * p301pair1Raw)

def p301numerator : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1771774402581369756291096]

theorem p301_numerator_reconstructed :
    p301rawNumerator = p301numerator := by
  unfold p301rawNumerator
  simp only [p301action0_reconstructed, p301pair0_reconstructed, p301action1_reconstructed, p301pair1_reconstructed, p301action2_reconstructed, p301pair2_reconstructed, p301action3_reconstructed, p301pair3_reconstructed]
  decide +kernel

def p301Mform : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(221471800322671219536387/125000000000000000000000)]

def p301rawMform : Matrix (Fin 1) (Fin 1) ℚ :=
  integerForm p301rawNumerator

theorem p301_Mform_reconstructed : p301rawMform = p301Mform := by
  unfold p301rawMform
  rw [p301_numerator_reconstructed]
  decide +kernel

def p301Hform : Matrix (Fin 1) (Fin 1) ℚ :=
  !![6]

def p301Sform : Matrix (Fin 1) (Fin 1) ℚ :=
  !![12]

def p301Ginv : Matrix (Fin 1) (Fin 1) ℚ :=
  Matrix.diagonal ![(1/2)]

def p301rawHform : Matrix (Fin 1) (Fin 1) ℚ := fun i j => planarHForm 1 (p301basis i) (p301basis j)

theorem p301_Hform_reconstructed :
    p301rawHform = p301Hform := by decide +kernel

theorem p301_Sform_reconstructed :
    planarSingleForm p301Ginv p301Hform = p301Sform := by decide +kernel

#print axioms p301action0_reconstructed
#print axioms p301pair0_reconstructed
#print axioms p301action1_reconstructed
#print axioms p301pair1_reconstructed
#print axioms p301action2_reconstructed
#print axioms p301pair2_reconstructed
#print axioms p301action3_reconstructed
#print axioms p301pair3_reconstructed
#print axioms p301_basis_enumerated
#print axioms p301_numerator_reconstructed
#print axioms p301_Mform_reconstructed
#print axioms p301_Hform_reconstructed
#print axioms p301_Sform_reconstructed

end TorusLean.BosonFiniteCertificate
