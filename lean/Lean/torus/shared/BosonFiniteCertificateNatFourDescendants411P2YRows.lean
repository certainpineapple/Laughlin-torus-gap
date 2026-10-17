import torus.shared.BosonFiniteCertificateNatFourDescendants411P2Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc2_bounded_product (a : Fin 4) (b : Fin 4) :
    (f411desc2IntegerLeftProductShared*f411desc2IntegerCoordinatesShared) a b=(f411desc2IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc2IntegerLeftProductShared*f411desc2IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc2IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc2IntegerLeftProductShared*f411desc2IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc2IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc2IntegerLeftProductShared*f411desc2IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc2IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc2IntegerLeftProductShared*f411desc2IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc2IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f411desc2_bounded_product

end TorusLean.BosonFiniteCertificate
