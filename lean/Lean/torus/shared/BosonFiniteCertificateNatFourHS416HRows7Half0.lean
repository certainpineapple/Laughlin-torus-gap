import torus.shared.BosonFiniteCertificateNatFourHS416Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f416_H_source_row_28 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 28) (f416basis b)=f416rawHForm 28 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 28) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 28 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_29 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 29) (f416basis b)=f416rawHForm 29 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 29) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 29 b) (by decide +kernel)
  exact h 0

theorem f416_H_rows_7_half0 :
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 28) (f416basis b) = f416rawHForm 28 b) ∧
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 29) (f416basis b) = f416rawHForm 29 b) :=
  ⟨f416_H_source_row_28, f416_H_source_row_29⟩

#print axioms f416_H_rows_7_half0
end TorusLean.BosonFiniteCertificate
