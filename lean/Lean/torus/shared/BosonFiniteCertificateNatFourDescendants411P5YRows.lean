import torus.shared.BosonFiniteCertificateNatFourDescendants411P5Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc5_bounded_product (a : Fin 4) (b : Fin 4) :
    (f411desc5IntegerLeftProductShared*f411desc5IntegerCoordinatesShared) a b=(f411desc5IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5IntegerLeftProductShared*f411desc5IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5IntegerLeftProductShared*f411desc5IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5IntegerLeftProductShared*f411desc5IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5IntegerLeftProductShared*f411desc5IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f411desc5_bounded_product

end TorusLean.BosonFiniteCertificate
