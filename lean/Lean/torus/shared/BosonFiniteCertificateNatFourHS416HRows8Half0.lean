import torus.shared.BosonFiniteCertificateNatFourHS416Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f416_H_source_row_32 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 32) (f416basis b)=f416rawHForm 32 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 32) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 32 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_33 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 33) (f416basis b)=f416rawHForm 33 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 33) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 33 b) (by decide +kernel)
  exact h 0

theorem f416_H_rows_8_half0 :
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 32) (f416basis b) = f416rawHForm 32 b) ∧
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 33) (f416basis b) = f416rawHForm 33 b) :=
  ⟨f416_H_source_row_32, f416_H_source_row_33⟩

#print axioms f416_H_rows_8_half0
end TorusLean.BosonFiniteCertificate
