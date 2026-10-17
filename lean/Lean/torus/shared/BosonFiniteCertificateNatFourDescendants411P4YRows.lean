import torus.shared.BosonFiniteCertificateNatFourDescendants411P4Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc4_bounded_product (a : Fin 4) (b : Fin 4) :
    (f411desc4IntegerLeftProductShared*f411desc4IntegerCoordinatesShared) a b=(f411desc4IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4IntegerLeftProductShared*f411desc4IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4IntegerLeftProductShared*f411desc4IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4IntegerLeftProductShared*f411desc4IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4IntegerLeftProductShared*f411desc4IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f411desc4_bounded_product

end TorusLean.BosonFiniteCertificate
