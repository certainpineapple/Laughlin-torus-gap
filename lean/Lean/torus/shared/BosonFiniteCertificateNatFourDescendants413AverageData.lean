import torus.shared.BosonFiniteCertificateNatFourDescendants413P0Data
import torus.shared.BosonFiniteCertificateNatFourDescendants413P1Data
import torus.shared.BosonFiniteCertificateNatFourDescendants413P2Data
import torus.shared.BosonFiniteCertificateNatFourDescendants413P3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

def f413descForms : ℕ → Matrix (Fin 5) (Fin 5) ℚ
  | 0 => f413desc0Form
  | 1 => f413desc1Form
  | 2 => f413desc2Form
  | 3 => f413desc3Form
  | _ => 0

end TorusLean.BosonFiniteCertificate
