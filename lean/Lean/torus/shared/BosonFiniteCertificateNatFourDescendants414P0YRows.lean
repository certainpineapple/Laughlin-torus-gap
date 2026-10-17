import torus.shared.BosonFiniteCertificateNatFourDescendants414P0Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414desc0_bounded_product (a : Fin 8) (b : Fin 8) :
    (f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared) a b=(f414desc0IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerFormShared) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerFormShared) 5 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerFormShared) 6 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerLeftProductShared*f414desc0IntegerCoordinatesShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc0IntegerFormShared) 7 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f414desc0_bounded_product

end TorusLean.BosonFiniteCertificate
