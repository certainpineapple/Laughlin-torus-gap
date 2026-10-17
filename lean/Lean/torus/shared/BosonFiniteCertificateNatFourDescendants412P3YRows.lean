import torus.shared.BosonFiniteCertificateNatFourDescendants412P3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412desc3_bounded_product (a : Fin 7) (b : Fin 7) :
    (f412desc3IntegerLeftProductShared*f412desc3IntegerCoordinatesShared) a b=(f412desc3IntegerFormShared) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerLeftProductShared*f412desc3IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerFormShared) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerLeftProductShared*f412desc3IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerFormShared) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerLeftProductShared*f412desc3IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerFormShared) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerLeftProductShared*f412desc3IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerFormShared) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerLeftProductShared*f412desc3IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerFormShared) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerLeftProductShared*f412desc3IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerFormShared) 5 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerLeftProductShared*f412desc3IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f412desc3IntegerFormShared) 6 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f412desc3_bounded_product

end TorusLean.BosonFiniteCertificate
