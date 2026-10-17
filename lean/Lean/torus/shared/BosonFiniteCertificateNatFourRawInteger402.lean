import torus.shared.BosonFiniteCertificateNatFourIntegerMatrix
import torus.shared.BosonFiniteCertificateNatFourRaw402

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f402rawInteger : Matrix (Fin 2) (Fin 2) ℤ :=
  !![7479984651226258862873412, (-830445774503580501270384);
    (-830445774503580501270384), 3615566503792874812471504]

theorem f402_raw_integer_check :
    natFourIntegerMatrix 1000000000000000000000000 f402rawInteger=f402rawM4Form := by
  ext a b
  exact natFourRationalEntryCheck_sound
    (natFourIntegerMatrix 1000000000000000000000000 f402rawInteger)
    f402rawM4Form (by decide +kernel) a b

#print axioms f402_raw_integer_check
end TorusLean.BosonFiniteCertificate
