import torus.shared.BosonFiniteCertificateNatFourDescendants414P0Data
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1Data
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

def f414descForms : ℕ → Matrix (Fin 8) (Fin 8) ℚ
  | 0 => f414desc0Form
  | 1 => f414desc1Form
  | 2 => f414desc2Form
  | _ => 0

end TorusLean.BosonFiniteCertificate
