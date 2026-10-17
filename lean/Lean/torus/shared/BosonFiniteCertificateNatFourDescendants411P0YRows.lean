import torus.shared.BosonFiniteCertificateNatFourDescendants411P0Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc0_bounded_product (a : Fin 4) (b : Fin 4) :
    (f411desc0IntegerLeftProductShared*f411desc0IntegerCoordinatesShared) a b=(f411desc0IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0IntegerLeftProductShared*f411desc0IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0IntegerLeftProductShared*f411desc0IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0IntegerLeftProductShared*f411desc0IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0IntegerLeftProductShared*f411desc0IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f411desc0_bounded_product

end TorusLean.BosonFiniteCertificate
