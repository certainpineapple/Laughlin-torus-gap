import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

private theorem f415_S4Compression_hV_rows_3_row6_columns0 (j : Fin 8) :
    (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 54)=(f415S4CompressionLeftProduct) 6 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 54) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 54))
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionLeftProduct) 6 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 54)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f415_S4Compression_hV_rows_3_row6_columns0

private theorem f415_S4Compression_hV_rows_3_row6_columns1 (j : Fin 8) :
    (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 54)=(f415S4CompressionLeftProduct) 6 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 54) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 54))
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionLeftProduct) 6 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 54)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f415_S4Compression_hV_rows_3_row6_columns1

private theorem f415_S4Compression_hV_rows_3_row6_columns2 (j : Fin 8) :
    (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 54)=(f415S4CompressionLeftProduct) 6 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 54) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 54))
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionLeftProduct) 6 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 54)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f415_S4Compression_hV_rows_3_row6_columns2

private theorem f415_S4Compression_hV_rows_3_row6_columns3 (j : Fin 8) :
    (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 54)=(f415S4CompressionLeftProduct) 6 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 54) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 54))
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionLeftProduct) 6 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 54)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f415_S4Compression_hV_rows_3_row6_columns3

private theorem f415_S4Compression_hV_rows_3_row6_columns4 (j : Fin 8) :
    (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 54)=(f415S4CompressionLeftProduct) 6 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 54) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 54))
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionLeftProduct) 6 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 54)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f415_S4Compression_hV_rows_3_row6_columns4

private theorem f415_S4Compression_hV_rows_3_row6_columns5 (j : Fin 8) :
    (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 54)=(f415S4CompressionLeftProduct) 6 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 54) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 54))
    (fun (_ : Fin 1) (j : Fin 8) => (f415S4CompressionLeftProduct) 6 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 54)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f415_S4Compression_hV_rows_3_row6_columns5

private theorem f415_S4Compression_hV_rows_3_row6_columns6 (j : Fin 6) :
    (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 48, by have hj := j.isLt; omega⟩ : Fin 54)=(f415S4CompressionLeftProduct) 6 (⟨j.val + 48, by have hj := j.isLt; omega⟩ : Fin 54) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 6) => (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) 6 (⟨j.val + 48, by have hj := j.isLt; omega⟩ : Fin 54))
    (fun (_ : Fin 1) (j : Fin 6) => (f415S4CompressionLeftProduct) 6 (⟨j.val + 48, by have hj := j.isLt; omega⟩ : Fin 54)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f415_S4Compression_hV_rows_3_row6_columns6

theorem f415_S4Compression_hV_rows_3 (a : Fin 7) (hlo : 6 ≤ a.val) (hhi : a.val < 7) (b : Fin 54) :
    (f415S4CompressionCoordinatesᵀ*f415S4CompressionInteger) a b=(f415S4CompressionLeftProduct) a b := by
  fin_cases a
  · change 6 ≤ (0 : ℕ) at hlo
    omega
  · change 6 ≤ (1 : ℕ) at hlo
    omega
  · change 6 ≤ (2 : ℕ) at hlo
    omega
  · change 6 ≤ (3 : ℕ) at hlo
    omega
  · change 6 ≤ (4 : ℕ) at hlo
    omega
  · change 6 ≤ (5 : ℕ) at hlo
    omega
  · fin_cases b
    · exact f415_S4Compression_hV_rows_3_row6_columns0 0
    · exact f415_S4Compression_hV_rows_3_row6_columns0 1
    · exact f415_S4Compression_hV_rows_3_row6_columns0 2
    · exact f415_S4Compression_hV_rows_3_row6_columns0 3
    · exact f415_S4Compression_hV_rows_3_row6_columns0 4
    · exact f415_S4Compression_hV_rows_3_row6_columns0 5
    · exact f415_S4Compression_hV_rows_3_row6_columns0 6
    · exact f415_S4Compression_hV_rows_3_row6_columns0 7
    · exact f415_S4Compression_hV_rows_3_row6_columns1 0
    · exact f415_S4Compression_hV_rows_3_row6_columns1 1
    · exact f415_S4Compression_hV_rows_3_row6_columns1 2
    · exact f415_S4Compression_hV_rows_3_row6_columns1 3
    · exact f415_S4Compression_hV_rows_3_row6_columns1 4
    · exact f415_S4Compression_hV_rows_3_row6_columns1 5
    · exact f415_S4Compression_hV_rows_3_row6_columns1 6
    · exact f415_S4Compression_hV_rows_3_row6_columns1 7
    · exact f415_S4Compression_hV_rows_3_row6_columns2 0
    · exact f415_S4Compression_hV_rows_3_row6_columns2 1
    · exact f415_S4Compression_hV_rows_3_row6_columns2 2
    · exact f415_S4Compression_hV_rows_3_row6_columns2 3
    · exact f415_S4Compression_hV_rows_3_row6_columns2 4
    · exact f415_S4Compression_hV_rows_3_row6_columns2 5
    · exact f415_S4Compression_hV_rows_3_row6_columns2 6
    · exact f415_S4Compression_hV_rows_3_row6_columns2 7
    · exact f415_S4Compression_hV_rows_3_row6_columns3 0
    · exact f415_S4Compression_hV_rows_3_row6_columns3 1
    · exact f415_S4Compression_hV_rows_3_row6_columns3 2
    · exact f415_S4Compression_hV_rows_3_row6_columns3 3
    · exact f415_S4Compression_hV_rows_3_row6_columns3 4
    · exact f415_S4Compression_hV_rows_3_row6_columns3 5
    · exact f415_S4Compression_hV_rows_3_row6_columns3 6
    · exact f415_S4Compression_hV_rows_3_row6_columns3 7
    · exact f415_S4Compression_hV_rows_3_row6_columns4 0
    · exact f415_S4Compression_hV_rows_3_row6_columns4 1
    · exact f415_S4Compression_hV_rows_3_row6_columns4 2
    · exact f415_S4Compression_hV_rows_3_row6_columns4 3
    · exact f415_S4Compression_hV_rows_3_row6_columns4 4
    · exact f415_S4Compression_hV_rows_3_row6_columns4 5
    · exact f415_S4Compression_hV_rows_3_row6_columns4 6
    · exact f415_S4Compression_hV_rows_3_row6_columns4 7
    · exact f415_S4Compression_hV_rows_3_row6_columns5 0
    · exact f415_S4Compression_hV_rows_3_row6_columns5 1
    · exact f415_S4Compression_hV_rows_3_row6_columns5 2
    · exact f415_S4Compression_hV_rows_3_row6_columns5 3
    · exact f415_S4Compression_hV_rows_3_row6_columns5 4
    · exact f415_S4Compression_hV_rows_3_row6_columns5 5
    · exact f415_S4Compression_hV_rows_3_row6_columns5 6
    · exact f415_S4Compression_hV_rows_3_row6_columns5 7
    · exact f415_S4Compression_hV_rows_3_row6_columns6 0
    · exact f415_S4Compression_hV_rows_3_row6_columns6 1
    · exact f415_S4Compression_hV_rows_3_row6_columns6 2
    · exact f415_S4Compression_hV_rows_3_row6_columns6 3
    · exact f415_S4Compression_hV_rows_3_row6_columns6 4
    · exact f415_S4Compression_hV_rows_3_row6_columns6 5

#print axioms f415_S4Compression_hV_rows_3
end TorusLean.BosonFiniteCertificate
