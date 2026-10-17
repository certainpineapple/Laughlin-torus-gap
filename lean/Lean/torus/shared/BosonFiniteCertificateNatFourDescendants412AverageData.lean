import torus.shared.BosonFiniteCertificateNatFourDescendants412P0Data
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1Data
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2Data
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3Data
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

def f412descForms : ℕ → Matrix (Fin 7) (Fin 7) ℚ
  | 0 => f412desc0Form
  | 1 => f412desc1Form
  | 2 => f412desc2Form
  | 3 => f412desc3Form
  | 4 => f412desc4Form
  | _ => 0

end TorusLean.BosonFiniteCertificate
