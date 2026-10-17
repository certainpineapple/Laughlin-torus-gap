import torus.shared.BosonFiniteCertificateNatFourDescendants413P3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc3_bounded_product (a : Fin 5) (b : Fin 5) :
    (f413desc3IntegerLeftProductShared*f413desc3IntegerCoordinatesShared) a b=(f413desc3IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerLeftProductShared*f413desc3IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerLeftProductShared*f413desc3IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerLeftProductShared*f413desc3IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerLeftProductShared*f413desc3IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerLeftProductShared*f413desc3IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3IntegerFormShared) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f413desc3_bounded_product

end TorusLean.BosonFiniteCertificate
