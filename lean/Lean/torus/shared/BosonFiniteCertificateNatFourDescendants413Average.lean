import torus.shared.BosonFiniteCertificateNatFourDescendants413AverageRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_COM_average_check :
    (∑ k ∈ Finset.range 4, natFourOriginalCOMWeight k • f413descForms k)=b413average := by
  ext a b
  exact f413_bounded_average a b

#print axioms f413_COM_average_check

end TorusLean.BosonFiniteCertificate
