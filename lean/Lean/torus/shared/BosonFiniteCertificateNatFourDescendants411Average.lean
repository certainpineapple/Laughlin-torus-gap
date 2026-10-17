import torus.shared.BosonFiniteCertificateNatFourDescendants411AverageRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411_COM_average_check :
    (∑ k ∈ Finset.range 6, natFourOriginalCOMWeight k • f411descForms k)=b411average := by
  ext a b
  exact f411_bounded_average a b

#print axioms f411_COM_average_check

end TorusLean.BosonFiniteCertificate
