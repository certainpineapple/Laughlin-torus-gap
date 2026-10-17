import torus.shared.BosonFiniteCertificateNatFourHS416Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f416_H_source_row_18 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 18) (f416basis b)=f416rawHForm 18 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 18) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 18 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_19 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 19) (f416basis b)=f416rawHForm 19 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 19) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 19 b) (by decide +kernel)
  exact h 0

theorem f416_H_rows_4_half1 :
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 18) (f416basis b) = f416rawHForm 18 b) ∧
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 19) (f416basis b) = f416rawHForm 19 b) :=
  ⟨f416_H_source_row_18, f416_H_source_row_19⟩

#print axioms f416_H_rows_4_half1
end TorusLean.BosonFiniteCertificate
