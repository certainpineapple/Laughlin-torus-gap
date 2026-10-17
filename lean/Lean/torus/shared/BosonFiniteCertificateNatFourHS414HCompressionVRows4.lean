import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

private theorem f414_HCompression_hV_rows_4_columns_0 (j : Fin 8) :
    (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 47)=(f414HCompressionLeftProduct) 4 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 47) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 47))
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionLeftProduct) 4 (⟨j.val + 0, by have hj := j.isLt; omega⟩ : Fin 47)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f414_HCompression_hV_rows_4_columns_0

private theorem f414_HCompression_hV_rows_4_columns_1 (j : Fin 8) :
    (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 47)=(f414HCompressionLeftProduct) 4 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 47) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 47))
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionLeftProduct) 4 (⟨j.val + 8, by have hj := j.isLt; omega⟩ : Fin 47)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f414_HCompression_hV_rows_4_columns_1

private theorem f414_HCompression_hV_rows_4_columns_2 (j : Fin 8) :
    (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 47)=(f414HCompressionLeftProduct) 4 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 47) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 47))
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionLeftProduct) 4 (⟨j.val + 16, by have hj := j.isLt; omega⟩ : Fin 47)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f414_HCompression_hV_rows_4_columns_2

private theorem f414_HCompression_hV_rows_4_columns_3 (j : Fin 8) :
    (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 47)=(f414HCompressionLeftProduct) 4 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 47) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 47))
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionLeftProduct) 4 (⟨j.val + 24, by have hj := j.isLt; omega⟩ : Fin 47)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f414_HCompression_hV_rows_4_columns_3

private theorem f414_HCompression_hV_rows_4_columns_4 (j : Fin 8) :
    (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 47)=(f414HCompressionLeftProduct) 4 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 47) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 47))
    (fun (_ : Fin 1) (j : Fin 8) => (f414HCompressionLeftProduct) 4 (⟨j.val + 32, by have hj := j.isLt; omega⟩ : Fin 47)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f414_HCompression_hV_rows_4_columns_4

private theorem f414_HCompression_hV_rows_4_columns_5 (j : Fin 7) :
    (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 47)=(f414HCompressionLeftProduct) 4 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 47) := by
  have h := natFourIntegerEntryCheck_sound
    (fun (_ : Fin 1) (j : Fin 7) => (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) 4 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 47))
    (fun (_ : Fin 1) (j : Fin 7) => (f414HCompressionLeftProduct) 4 (⟨j.val + 40, by have hj := j.isLt; omega⟩ : Fin 47)) (by decide +kernel)
  exact congrFun (congrFun h 0) j

#print axioms f414_HCompression_hV_rows_4_columns_5

theorem f414_HCompression_hV_rows_4 (a : Fin 8) (hlo : 4 ≤ a.val) (hhi : a.val < 5) (b : Fin 47) :
    (f414HCompressionCoordinatesᵀ*f414HCompressionInteger) a b=(f414HCompressionLeftProduct) a b := by
  fin_cases a
  · change 4 ≤ (0 : ℕ) at hlo
    omega
  · change 4 ≤ (1 : ℕ) at hlo
    omega
  · change 4 ≤ (2 : ℕ) at hlo
    omega
  · change 4 ≤ (3 : ℕ) at hlo
    omega
  · fin_cases b
    · exact f414_HCompression_hV_rows_4_columns_0 0
    · exact f414_HCompression_hV_rows_4_columns_0 1
    · exact f414_HCompression_hV_rows_4_columns_0 2
    · exact f414_HCompression_hV_rows_4_columns_0 3
    · exact f414_HCompression_hV_rows_4_columns_0 4
    · exact f414_HCompression_hV_rows_4_columns_0 5
    · exact f414_HCompression_hV_rows_4_columns_0 6
    · exact f414_HCompression_hV_rows_4_columns_0 7
    · exact f414_HCompression_hV_rows_4_columns_1 0
    · exact f414_HCompression_hV_rows_4_columns_1 1
    · exact f414_HCompression_hV_rows_4_columns_1 2
    · exact f414_HCompression_hV_rows_4_columns_1 3
    · exact f414_HCompression_hV_rows_4_columns_1 4
    · exact f414_HCompression_hV_rows_4_columns_1 5
    · exact f414_HCompression_hV_rows_4_columns_1 6
    · exact f414_HCompression_hV_rows_4_columns_1 7
    · exact f414_HCompression_hV_rows_4_columns_2 0
    · exact f414_HCompression_hV_rows_4_columns_2 1
    · exact f414_HCompression_hV_rows_4_columns_2 2
    · exact f414_HCompression_hV_rows_4_columns_2 3
    · exact f414_HCompression_hV_rows_4_columns_2 4
    · exact f414_HCompression_hV_rows_4_columns_2 5
    · exact f414_HCompression_hV_rows_4_columns_2 6
    · exact f414_HCompression_hV_rows_4_columns_2 7
    · exact f414_HCompression_hV_rows_4_columns_3 0
    · exact f414_HCompression_hV_rows_4_columns_3 1
    · exact f414_HCompression_hV_rows_4_columns_3 2
    · exact f414_HCompression_hV_rows_4_columns_3 3
    · exact f414_HCompression_hV_rows_4_columns_3 4
    · exact f414_HCompression_hV_rows_4_columns_3 5
    · exact f414_HCompression_hV_rows_4_columns_3 6
    · exact f414_HCompression_hV_rows_4_columns_3 7
    · exact f414_HCompression_hV_rows_4_columns_4 0
    · exact f414_HCompression_hV_rows_4_columns_4 1
    · exact f414_HCompression_hV_rows_4_columns_4 2
    · exact f414_HCompression_hV_rows_4_columns_4 3
    · exact f414_HCompression_hV_rows_4_columns_4 4
    · exact f414_HCompression_hV_rows_4_columns_4 5
    · exact f414_HCompression_hV_rows_4_columns_4 6
    · exact f414_HCompression_hV_rows_4_columns_4 7
    · exact f414_HCompression_hV_rows_4_columns_5 0
    · exact f414_HCompression_hV_rows_4_columns_5 1
    · exact f414_HCompression_hV_rows_4_columns_5 2
    · exact f414_HCompression_hV_rows_4_columns_5 3
    · exact f414_HCompression_hV_rows_4_columns_5 4
    · exact f414_HCompression_hV_rows_4_columns_5 5
    · exact f414_HCompression_hV_rows_4_columns_5 6
  · change (5 : ℕ) < 5 at hhi
    omega
  · change (6 : ℕ) < 5 at hhi
    omega
  · change (7 : ℕ) < 5 at hhi
    omega

#print axioms f414_HCompression_hV_rows_4
end TorusLean.BosonFiniteCertificate
