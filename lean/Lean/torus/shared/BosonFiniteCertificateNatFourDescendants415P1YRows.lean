import torus.shared.BosonFiniteCertificateNatFourDescendants415P1Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415desc1_bounded_product (a : Fin 7) (b : Fin 7) :
    (f415desc1IntegerLeftProductShared*f415desc1IntegerCoordinatesShared) a b=(f415desc1IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerLeftProductShared*f415desc1IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerLeftProductShared*f415desc1IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerLeftProductShared*f415desc1IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerLeftProductShared*f415desc1IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerLeftProductShared*f415desc1IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerFormShared) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerLeftProductShared*f415desc1IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerFormShared) 5 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerLeftProductShared*f415desc1IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1IntegerFormShared) 6 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f415desc1_bounded_product

end TorusLean.BosonFiniteCertificate
