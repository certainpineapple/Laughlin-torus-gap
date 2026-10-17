import torus.shared.BosonFiniteCertificateNatFourIntegerMatrix
import torus.shared.BosonFiniteCertificateNatFourRaw401

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f401rawInteger : Matrix (Fin 1) (Fin 1) ℤ :=
  !![3282838723754635739190372]

theorem f401_raw_integer_check :
    natFourIntegerMatrix 1000000000000000000000000 f401rawInteger=f401rawM4Form := by
  ext a b
  exact natFourRationalEntryCheck_sound
    (natFourIntegerMatrix 1000000000000000000000000 f401rawInteger)
    f401rawM4Form (by decide +kernel) a b

#print axioms f401_raw_integer_check
end TorusLean.BosonFiniteCertificate
