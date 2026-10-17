import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants410P0
import torus.shared.BosonFiniteCertificateNatFourDescendants410P1
import torus.shared.BosonFiniteCertificateNatFourDescendants410P2
import torus.shared.BosonFiniteCertificateNatFourDescendants410P3
import torus.shared.BosonFiniteCertificateNatFourDescendants410P4
import torus.shared.BosonFiniteCertificateNatFourDescendants410P5
import torus.shared.BosonFiniteCertificateNatFourDescendants410P6

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

def f410descForms : ℕ → Matrix (Fin 5) (Fin 5) ℚ
  | 0 => f410desc0Form
  | 1 => f410desc1Form
  | 2 => f410desc2Form
  | 3 => f410desc3Form
  | 4 => f410desc4Form
  | 5 => f410desc5Form
  | 6 => f410desc6Form
  | _ => 0

end TorusLean.BosonFiniteCertificate
