import torus.shared.BosonFiniteCertificateNatFourIntegerMatrix
import torus.shared.BosonFiniteCertificateNatFourRaw403

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f403rawInteger : Matrix (Fin 3) (Fin 3) ℤ :=
  !![4163217277647931433710596, 5192203281705604375754760, (-961351792703437755921660);
    5192203281705604375754760, 712241096989685877968508, 2914862553904057041208056;
    (-961351792703437755921660), 2914862553904057041208056, 4555547476493802749849952]

theorem f403_raw_integer_check :
    natFourIntegerMatrix 1000000000000000000000000 f403rawInteger=f403rawM4Form := by
  ext a b
  exact natFourRationalEntryCheck_sound
    (natFourIntegerMatrix 1000000000000000000000000 f403rawInteger)
    f403rawM4Form (by decide +kernel) a b

#print axioms f403_raw_integer_check
end TorusLean.BosonFiniteCertificate
