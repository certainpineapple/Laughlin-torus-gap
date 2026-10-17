import torus.shared.BosonFiniteCertificateNatFourHS416Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f416_H_source_row_26 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 26) (f416basis b)=f416rawHForm 26 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 26) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 26 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_27_columns0 :
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 0) = f416rawHForm 27 0) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 1) = f416rawHForm 27 1) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 2) = f416rawHForm 27 2) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 3) = f416rawHForm 27 3) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 4) = f416rawHForm 27 4) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 5) = f416rawHForm 27 5) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 6) = f416rawHForm 27 6) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 7) = f416rawHForm 27 7) := by
  decide +kernel

private theorem f416_H_source_row_27_columns1 :
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 8) = f416rawHForm 27 8) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 9) = f416rawHForm 27 9) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 10) = f416rawHForm 27 10) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 11) = f416rawHForm 27 11) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 12) = f416rawHForm 27 12) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 13) = f416rawHForm 27 13) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 14) = f416rawHForm 27 14) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 15) = f416rawHForm 27 15) := by
  decide +kernel

private theorem f416_H_source_row_27_columns2 :
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 16) = f416rawHForm 27 16) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 17) = f416rawHForm 27 17) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 18) = f416rawHForm 27 18) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 19) = f416rawHForm 27 19) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 20) = f416rawHForm 27 20) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 21) = f416rawHForm 27 21) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 22) = f416rawHForm 27 22) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 23) = f416rawHForm 27 23) := by
  decide +kernel

private theorem f416_H_source_row_27_columns3 :
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 24) = f416rawHForm 27 24) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 25) = f416rawHForm 27 25) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 26) = f416rawHForm 27 26) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 27) = f416rawHForm 27 27) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 28) = f416rawHForm 27 28) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 29) = f416rawHForm 27 29) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 30) = f416rawHForm 27 30) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 31) = f416rawHForm 27 31) := by
  decide +kernel

private theorem f416_H_source_row_27_columns4 :
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 32) = f416rawHForm 27 32) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 33) = f416rawHForm 27 33) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 34) = f416rawHForm 27 34) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 35) = f416rawHForm 27 35) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 36) = f416rawHForm 27 36) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 37) = f416rawHForm 27 37) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 38) = f416rawHForm 27 38) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 39) = f416rawHForm 27 39) := by
  decide +kernel

private theorem f416_H_source_row_27_columns5 :
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 40) = f416rawHForm 27 40) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 41) = f416rawHForm 27 41) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 42) = f416rawHForm 27 42) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 43) = f416rawHForm 27 43) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 44) = f416rawHForm 27 44) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 45) = f416rawHForm 27 45) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 46) = f416rawHForm 27 46) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 47) = f416rawHForm 27 47) := by
  decide +kernel

private theorem f416_H_source_row_27_columns6 :
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 48) = f416rawHForm 27 48) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 49) = f416rawHForm 27 49) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 50) = f416rawHForm 27 50) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 51) = f416rawHForm 27 51) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 52) = f416rawHForm 27 52) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 53) = f416rawHForm 27 53) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 54) = f416rawHForm 27 54) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 55) = f416rawHForm 27 55) := by
  decide +kernel

private theorem f416_H_source_row_27_columns7 :
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 56) = f416rawHForm 27 56) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 57) = f416rawHForm 27 57) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 58) = f416rawHForm 27 58) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 59) = f416rawHForm 27 59) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 60) = f416rawHForm 27 60) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 61) = f416rawHForm 27 61) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 62) = f416rawHForm 27 62) ∧
    (natFourHWordFormSparse 16 (f416basis 27) (f416basis 63) = f416rawHForm 27 63) := by
  decide +kernel

private theorem f416_H_source_row_27 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 27) (f416basis b)=f416rawHForm 27 b := by
  intro b
  fin_cases b
  · exact f416_H_source_row_27_columns0.1
  · exact f416_H_source_row_27_columns0.2.1
  · exact f416_H_source_row_27_columns0.2.2.1
  · exact f416_H_source_row_27_columns0.2.2.2.1
  · exact f416_H_source_row_27_columns0.2.2.2.2.1
  · exact f416_H_source_row_27_columns0.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns0.2.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns0.2.2.2.2.2.2.2
  · exact f416_H_source_row_27_columns1.1
  · exact f416_H_source_row_27_columns1.2.1
  · exact f416_H_source_row_27_columns1.2.2.1
  · exact f416_H_source_row_27_columns1.2.2.2.1
  · exact f416_H_source_row_27_columns1.2.2.2.2.1
  · exact f416_H_source_row_27_columns1.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns1.2.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns1.2.2.2.2.2.2.2
  · exact f416_H_source_row_27_columns2.1
  · exact f416_H_source_row_27_columns2.2.1
  · exact f416_H_source_row_27_columns2.2.2.1
  · exact f416_H_source_row_27_columns2.2.2.2.1
  · exact f416_H_source_row_27_columns2.2.2.2.2.1
  · exact f416_H_source_row_27_columns2.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns2.2.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns2.2.2.2.2.2.2.2
  · exact f416_H_source_row_27_columns3.1
  · exact f416_H_source_row_27_columns3.2.1
  · exact f416_H_source_row_27_columns3.2.2.1
  · exact f416_H_source_row_27_columns3.2.2.2.1
  · exact f416_H_source_row_27_columns3.2.2.2.2.1
  · exact f416_H_source_row_27_columns3.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns3.2.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns3.2.2.2.2.2.2.2
  · exact f416_H_source_row_27_columns4.1
  · exact f416_H_source_row_27_columns4.2.1
  · exact f416_H_source_row_27_columns4.2.2.1
  · exact f416_H_source_row_27_columns4.2.2.2.1
  · exact f416_H_source_row_27_columns4.2.2.2.2.1
  · exact f416_H_source_row_27_columns4.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns4.2.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns4.2.2.2.2.2.2.2
  · exact f416_H_source_row_27_columns5.1
  · exact f416_H_source_row_27_columns5.2.1
  · exact f416_H_source_row_27_columns5.2.2.1
  · exact f416_H_source_row_27_columns5.2.2.2.1
  · exact f416_H_source_row_27_columns5.2.2.2.2.1
  · exact f416_H_source_row_27_columns5.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns5.2.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns5.2.2.2.2.2.2.2
  · exact f416_H_source_row_27_columns6.1
  · exact f416_H_source_row_27_columns6.2.1
  · exact f416_H_source_row_27_columns6.2.2.1
  · exact f416_H_source_row_27_columns6.2.2.2.1
  · exact f416_H_source_row_27_columns6.2.2.2.2.1
  · exact f416_H_source_row_27_columns6.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns6.2.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns6.2.2.2.2.2.2.2
  · exact f416_H_source_row_27_columns7.1
  · exact f416_H_source_row_27_columns7.2.1
  · exact f416_H_source_row_27_columns7.2.2.1
  · exact f416_H_source_row_27_columns7.2.2.2.1
  · exact f416_H_source_row_27_columns7.2.2.2.2.1
  · exact f416_H_source_row_27_columns7.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns7.2.2.2.2.2.2.1
  · exact f416_H_source_row_27_columns7.2.2.2.2.2.2.2

theorem f416_H_rows_6_half1 :
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 26) (f416basis b) = f416rawHForm 26 b) ∧
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 27) (f416basis b) = f416rawHForm 27 b) :=
  ⟨f416_H_source_row_26, f416_H_source_row_27⟩

#print axioms f416_H_rows_6_half1
end TorusLean.BosonFiniteCertificate
