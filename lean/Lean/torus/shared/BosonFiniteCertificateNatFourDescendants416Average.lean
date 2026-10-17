import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f416descForms : ℕ → Matrix (Fin 10) (Fin 10) ℚ
  | 0 => f416desc0Form
  | _ => 0

theorem f416_COM_average_check :
    (∑ k ∈ Finset.range 1, natFourOriginalCOMWeight k • f416descForms k)=b416average := by
  decide +kernel


#print axioms f416_COM_average_check

end TorusLean.BosonFiniteCertificate
