import torus.shared.BosonFiniteCertificateNatFourDescendants413P1Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc1_bounded_product (a : Fin 5) (b : Fin 5) :
    (f413desc1IntegerLeftProductShared*f413desc1IntegerCoordinatesShared) a b=(f413desc1IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerLeftProductShared*f413desc1IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerLeftProductShared*f413desc1IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerLeftProductShared*f413desc1IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerLeftProductShared*f413desc1IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerLeftProductShared*f413desc1IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1IntegerFormShared) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f413desc1_bounded_product

end TorusLean.BosonFiniteCertificate
