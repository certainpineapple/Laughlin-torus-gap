import torus.shared.BosonFiniteCertificateNatFourHS416Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f416_H_source_row_34 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 34) (f416basis b)=f416rawHForm 34 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 34) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 34 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_35 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 35) (f416basis b)=f416rawHForm 35 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 35) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 35 b) (by decide +kernel)
  exact h 0

theorem f416_H_rows_8_half1 :
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 34) (f416basis b) = f416rawHForm 34 b) ∧
    (∀ b : Fin 64, natFourHWordFormSparse 16 (f416basis 35) (f416basis b) = f416rawHForm 35 b) :=
  ⟨f416_H_source_row_34, f416_H_source_row_35⟩

#print axioms f416_H_rows_8_half1
end TorusLean.BosonFiniteCertificate
