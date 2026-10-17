import torus.shared.BosonFiniteCertificateNatFourDescendants415P0Data
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

def f415descForms : ℕ → Matrix (Fin 7) (Fin 7) ℚ
  | 0 => f415desc0Form
  | 1 => f415desc1Form
  | _ => 0

end TorusLean.BosonFiniteCertificate
