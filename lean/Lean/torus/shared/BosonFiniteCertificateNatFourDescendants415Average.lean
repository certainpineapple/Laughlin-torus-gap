import torus.shared.BosonFiniteCertificateNatFourDescendants415AverageRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_COM_average_check :
    (∑ k ∈ Finset.range 2, natFourOriginalCOMWeight k • f415descForms k)=b415average := by
  ext a b
  exact f415_bounded_average a b

#print axioms f415_COM_average_check

end TorusLean.BosonFiniteCertificate
