import torus.shared.BosonFiniteCertificateNatFourDescendants411P0Data
import torus.shared.BosonFiniteCertificateNatFourDescendants411P1Data
import torus.shared.BosonFiniteCertificateNatFourDescendants411P2Data
import torus.shared.BosonFiniteCertificateNatFourDescendants411P3Data
import torus.shared.BosonFiniteCertificateNatFourDescendants411P4Data
import torus.shared.BosonFiniteCertificateNatFourDescendants411P5Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

def f411descForms : ℕ → Matrix (Fin 4) (Fin 4) ℚ
  | 0 => f411desc0Form
  | 1 => f411desc1Form
  | 2 => f411desc2Form
  | 3 => f411desc3Form
  | 4 => f411desc4Form
  | 5 => f411desc5Form
  | _ => 0

end TorusLean.BosonFiniteCertificate
