import torus.shared.BosonFiniteCertificateNatFourDescendants412P4Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412desc4_bounded_product (a : Fin 7) (b : Fin 7) :
    (f412desc4IntegerLeftProductShared*f412desc4IntegerCoordinatesShared) a b=(f412desc4IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerLeftProductShared*f412desc4IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerLeftProductShared*f412desc4IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerLeftProductShared*f412desc4IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerLeftProductShared*f412desc4IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerLeftProductShared*f412desc4IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerFormShared) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerLeftProductShared*f412desc4IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerFormShared) 5 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerLeftProductShared*f412desc4IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc4IntegerFormShared) 6 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f412desc4_bounded_product

end TorusLean.BosonFiniteCertificate
