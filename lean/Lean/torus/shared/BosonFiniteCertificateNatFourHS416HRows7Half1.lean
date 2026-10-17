import torus.shared.BosonFiniteCertificateNatFourHS416Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f416_H_source_row_30 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 30) (f416basis b)=f416rawHForm 30 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 30) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 30 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_31 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 31) (f416basis b)=f416rawHForm 31 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 31) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 31 b) (by decide +kernel)
  exact h 0

theorem f416_H_rows_7_half1 :
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 30) (f416basis b) = f416rawHForm 30 b) ∧
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 31) (f416basis b) = f416rawHForm 31 b) :=
  ⟨f416_H_source_row_30, f416_H_source_row_31⟩

#print axioms f416_H_rows_7_half1
end TorusLean.BosonFiniteCertificate
