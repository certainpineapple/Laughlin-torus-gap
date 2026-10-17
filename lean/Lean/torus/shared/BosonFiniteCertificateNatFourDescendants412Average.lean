import torus.shared.BosonFiniteCertificateNatFourDescendants412AverageRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412_COM_average_check :
    (∑ k ∈ Finset.range 5, natFourOriginalCOMWeight k • f412descForms k)=b412average := by
  ext a b
  exact f412_bounded_average a b

#print axioms f412_COM_average_check

end TorusLean.BosonFiniteCertificate
