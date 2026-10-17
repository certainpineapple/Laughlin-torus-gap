import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

private theorem f416_S4Compression_hV_rows_0_row0_columns0 (j : Fin 8) :
    (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 64)=(f416S4CompressionLeftProduct) 0 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 64) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 64))
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionLeftProduct) 0 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 64)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f416_S4Compression_hV_rows_0_row0_columns0

private theorem f416_S4Compression_hV_rows_0_row0_columns1 (j : Fin 8) :
    (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 64)=(f416S4CompressionLeftProduct) 0 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 64) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 64))
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionLeftProduct) 0 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 64)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f416_S4Compression_hV_rows_0_row0_columns1

private theorem f416_S4Compression_hV_rows_0_row0_columns2 (j : Fin 8) :
    (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 64)=(f416S4CompressionLeftProduct) 0 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 64) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 64))
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionLeftProduct) 0 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 64)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f416_S4Compression_hV_rows_0_row0_columns2

private theorem f416_S4Compression_hV_rows_0_row0_columns3 (j : Fin 8) :
    (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 64)=(f416S4CompressionLeftProduct) 0 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 64) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 64))
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionLeftProduct) 0 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 64)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f416_S4Compression_hV_rows_0_row0_columns3

private theorem f416_S4Compression_hV_rows_0_row0_columns4 (j : Fin 8) :
    (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 64)=(f416S4CompressionLeftProduct) 0 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 64) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 64))
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionLeftProduct) 0 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 64)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f416_S4Compression_hV_rows_0_row0_columns4

private theorem f416_S4Compression_hV_rows_0_row0_columns5 (j : Fin 8) :
    (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 64)=(f416S4CompressionLeftProduct) 0 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 64) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 64))
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionLeftProduct) 0 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 64)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f416_S4Compression_hV_rows_0_row0_columns5

private theorem f416_S4Compression_hV_rows_0_row0_columns6 (j : Fin 8) :
    (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 48, by have hj := j.isLt; omega⟩ : Fin 64)=(f416S4CompressionLeftProduct) 0 (⟨j.val + 48, by have hj := j.isLt; omega⟩ : Fin 64) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 48, by have hj := j.isLt; omega⟩ : Fin 64))
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionLeftProduct) 0 (⟨j.val + 48, by have hj := j.isLt; omega⟩ : Fin 64)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f416_S4Compression_hV_rows_0_row0_columns6

private theorem f416_S4Compression_hV_rows_0_row0_columns7 (j : Fin 8) :
    (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 56, by have hj := j.isLt; omega⟩ : Fin 64)=(f416S4CompressionLeftProduct) 0 (⟨j.val + 56, by have hj := j.isLt; omega⟩ : Fin 64) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) 0 (⟨j.val + 56, by have hj := j.isLt; omega⟩ : Fin 64))
    (fun (_ : Fin 1) (j : Fin 8) => (f416S4CompressionLeftProduct) 0 (⟨j.val + 56, by have hj := j.isLt; omega⟩ : Fin 64)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f416_S4Compression_hV_rows_0_row0_columns7

theorem f416_S4Compression_hV_rows_0 (a : Fin 10) (hlo : 0 ≤ a.val) (hhi : a.val < 1) (b : Fin 64) :
    (f416S4CompressionCoordinatesᵀ*f416S4CompressionInteger) a b=(f416S4CompressionLeftProduct) a b := by
  fin_cases a
  · fin_cases b
    · exact f416_S4Compression_hV_rows_0_row0_columns0 0
    · exact f416_S4Compression_hV_rows_0_row0_columns0 1
    · exact f416_S4Compression_hV_rows_0_row0_columns0 2
    · exact f416_S4Compression_hV_rows_0_row0_columns0 3
    · exact f416_S4Compression_hV_rows_0_row0_columns0 4
    · exact f416_S4Compression_hV_rows_0_row0_columns0 5
    · exact f416_S4Compression_hV_rows_0_row0_columns0 6
    · exact f416_S4Compression_hV_rows_0_row0_columns0 7
    · exact f416_S4Compression_hV_rows_0_row0_columns1 0
    · exact f416_S4Compression_hV_rows_0_row0_columns1 1
    · exact f416_S4Compression_hV_rows_0_row0_columns1 2
    · exact f416_S4Compression_hV_rows_0_row0_columns1 3
    · exact f416_S4Compression_hV_rows_0_row0_columns1 4
    · exact f416_S4Compression_hV_rows_0_row0_columns1 5
    · exact f416_S4Compression_hV_rows_0_row0_columns1 6
    · exact f416_S4Compression_hV_rows_0_row0_columns1 7
    · exact f416_S4Compression_hV_rows_0_row0_columns2 0
    · exact f416_S4Compression_hV_rows_0_row0_columns2 1
    · exact f416_S4Compression_hV_rows_0_row0_columns2 2
    · exact f416_S4Compression_hV_rows_0_row0_columns2 3
    · exact f416_S4Compression_hV_rows_0_row0_columns2 4
    · exact f416_S4Compression_hV_rows_0_row0_columns2 5
    · exact f416_S4Compression_hV_rows_0_row0_columns2 6
    · exact f416_S4Compression_hV_rows_0_row0_columns2 7
    · exact f416_S4Compression_hV_rows_0_row0_columns3 0
    · exact f416_S4Compression_hV_rows_0_row0_columns3 1
    · exact f416_S4Compression_hV_rows_0_row0_columns3 2
    · exact f416_S4Compression_hV_rows_0_row0_columns3 3
    · exact f416_S4Compression_hV_rows_0_row0_columns3 4
    · exact f416_S4Compression_hV_rows_0_row0_columns3 5
    · exact f416_S4Compression_hV_rows_0_row0_columns3 6
    · exact f416_S4Compression_hV_rows_0_row0_columns3 7
    · exact f416_S4Compression_hV_rows_0_row0_columns4 0
    · exact f416_S4Compression_hV_rows_0_row0_columns4 1
    · exact f416_S4Compression_hV_rows_0_row0_columns4 2
    · exact f416_S4Compression_hV_rows_0_row0_columns4 3
    · exact f416_S4Compression_hV_rows_0_row0_columns4 4
    · exact f416_S4Compression_hV_rows_0_row0_columns4 5
    · exact f416_S4Compression_hV_rows_0_row0_columns4 6
    · exact f416_S4Compression_hV_rows_0_row0_columns4 7
    · exact f416_S4Compression_hV_rows_0_row0_columns5 0
    · exact f416_S4Compression_hV_rows_0_row0_columns5 1
    · exact f416_S4Compression_hV_rows_0_row0_columns5 2
    · exact f416_S4Compression_hV_rows_0_row0_columns5 3
    · exact f416_S4Compression_hV_rows_0_row0_columns5 4
    · exact f416_S4Compression_hV_rows_0_row0_columns5 5
    · exact f416_S4Compression_hV_rows_0_row0_columns5 6
    · exact f416_S4Compression_hV_rows_0_row0_columns5 7
    · exact f416_S4Compression_hV_rows_0_row0_columns6 0
    · exact f416_S4Compression_hV_rows_0_row0_columns6 1
    · exact f416_S4Compression_hV_rows_0_row0_columns6 2
    · exact f416_S4Compression_hV_rows_0_row0_columns6 3
    · exact f416_S4Compression_hV_rows_0_row0_columns6 4
    · exact f416_S4Compression_hV_rows_0_row0_columns6 5
    · exact f416_S4Compression_hV_rows_0_row0_columns6 6
    · exact f416_S4Compression_hV_rows_0_row0_columns6 7
    · exact f416_S4Compression_hV_rows_0_row0_columns7 0
    · exact f416_S4Compression_hV_rows_0_row0_columns7 1
    · exact f416_S4Compression_hV_rows_0_row0_columns7 2
    · exact f416_S4Compression_hV_rows_0_row0_columns7 3
    · exact f416_S4Compression_hV_rows_0_row0_columns7 4
    · exact f416_S4Compression_hV_rows_0_row0_columns7 5
    · exact f416_S4Compression_hV_rows_0_row0_columns7 6
    · exact f416_S4Compression_hV_rows_0_row0_columns7 7
  · change (1 : ℕ) < 1 at hhi
    omega
  · change (2 : ℕ) < 1 at hhi
    omega
  · change (3 : ℕ) < 1 at hhi
    omega
  · change (4 : ℕ) < 1 at hhi
    omega
  · change (5 : ℕ) < 1 at hhi
    omega
  · change (6 : ℕ) < 1 at hhi
    omega
  · change (7 : ℕ) < 1 at hhi
    omega
  · change (8 : ℕ) < 1 at hhi
    omega
  · change (9 : ℕ) < 1 at hhi
    omega

#print axioms f416_S4Compression_hV_rows_0
end TorusLean.BosonFiniteCertificate
