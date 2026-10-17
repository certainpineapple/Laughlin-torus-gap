import torus.shared.BosonFiniteCertificateNatFourHS416Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f416_H_source_row_22 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 22) (f416basis b)=f416rawHForm 22 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 22) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 22 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_23 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 23) (f416basis b)=f416rawHForm 23 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 23) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 23 b) (by decide +kernel)
  exact h 0

theorem f416_H_rows_5_half1 :
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 22) (f416basis b) = f416rawHForm 22 b) ∧
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 23) (f416basis b) = f416rawHForm 23 b) :=
  ⟨f416_H_source_row_22, f416_H_source_row_23⟩

#print axioms f416_H_rows_5_half1
end TorusLean.BosonFiniteCertificate
