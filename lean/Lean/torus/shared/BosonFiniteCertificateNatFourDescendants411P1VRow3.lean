import torus.shared.BosonFiniteCertificateNatFourDescendants411P1Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

private theorem f411desc1_bounded_v_row3_columns0 (j : Fin 8) :
    (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 34)=(f411desc1IntegerLeftProductShared) 3 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 34) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 34))
    (fun (_ : Fin 1) (j : Fin 8) => (f411desc1IntegerLeftProductShared) 3 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 34)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f411desc1_bounded_v_row3_columns0

private theorem f411desc1_bounded_v_row3_columns1 (j : Fin 8) :
    (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 34)=(f411desc1IntegerLeftProductShared) 3 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 34) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 34))
    (fun (_ : Fin 1) (j : Fin 8) => (f411desc1IntegerLeftProductShared) 3 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 34)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f411desc1_bounded_v_row3_columns1

private theorem f411desc1_bounded_v_row3_columns2 (j : Fin 8) :
    (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 34)=(f411desc1IntegerLeftProductShared) 3 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 34) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 34))
    (fun (_ : Fin 1) (j : Fin 8) => (f411desc1IntegerLeftProductShared) 3 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 34)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f411desc1_bounded_v_row3_columns2

private theorem f411desc1_bounded_v_row3_columns3 (j : Fin 8) :
    (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 34)=(f411desc1IntegerLeftProductShared) 3 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 34) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 34))
    (fun (_ : Fin 1) (j : Fin 8) => (f411desc1IntegerLeftProductShared) 3 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 34)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f411desc1_bounded_v_row3_columns3

private theorem f411desc1_bounded_v_row3_columns4 (j : Fin 2) :
    (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 34)=(f411desc1IntegerLeftProductShared) 3 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 34) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 2) => (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 34))
    (fun (_ : Fin 1) (j : Fin 2) => (f411desc1IntegerLeftProductShared) 3 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 34)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f411desc1_bounded_v_row3_columns4

theorem f411desc1_bounded_v_row3 (b : Fin 34) :
    (f411desc1IntegerCoordinatesSharedᵀ*f412rawInteger) 3 b=(f411desc1IntegerLeftProductShared) 3 b := by
  fin_cases b
  · exact f411desc1_bounded_v_row3_columns0 0
  · exact f411desc1_bounded_v_row3_columns0 1
  · exact f411desc1_bounded_v_row3_columns0 2
  · exact f411desc1_bounded_v_row3_columns0 3
  · exact f411desc1_bounded_v_row3_columns0 4
  · exact f411desc1_bounded_v_row3_columns0 5
  · exact f411desc1_bounded_v_row3_columns0 6
  · exact f411desc1_bounded_v_row3_columns0 7
  · exact f411desc1_bounded_v_row3_columns1 0
  · exact f411desc1_bounded_v_row3_columns1 1
  · exact f411desc1_bounded_v_row3_columns1 2
  · exact f411desc1_bounded_v_row3_columns1 3
  · exact f411desc1_bounded_v_row3_columns1 4
  · exact f411desc1_bounded_v_row3_columns1 5
  · exact f411desc1_bounded_v_row3_columns1 6
  · exact f411desc1_bounded_v_row3_columns1 7
  · exact f411desc1_bounded_v_row3_columns2 0
  · exact f411desc1_bounded_v_row3_columns2 1
  · exact f411desc1_bounded_v_row3_columns2 2
  · exact f411desc1_bounded_v_row3_columns2 3
  · exact f411desc1_bounded_v_row3_columns2 4
  · exact f411desc1_bounded_v_row3_columns2 5
  · exact f411desc1_bounded_v_row3_columns2 6
  · exact f411desc1_bounded_v_row3_columns2 7
  · exact f411desc1_bounded_v_row3_columns3 0
  · exact f411desc1_bounded_v_row3_columns3 1
  · exact f411desc1_bounded_v_row3_columns3 2
  · exact f411desc1_bounded_v_row3_columns3 3
  · exact f411desc1_bounded_v_row3_columns3 4
  · exact f411desc1_bounded_v_row3_columns3 5
  · exact f411desc1_bounded_v_row3_columns3 6
  · exact f411desc1_bounded_v_row3_columns3 7
  · exact f411desc1_bounded_v_row3_columns4 0
  · exact f411desc1_bounded_v_row3_columns4 1

#print axioms f411desc1_bounded_v_row3

end TorusLean.BosonFiniteCertificate
