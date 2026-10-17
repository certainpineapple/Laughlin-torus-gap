import torus.shared.BosonFiniteCertificateNatFourRelativeMatrices
import torus.shared.BosonFiniteCertificateNatFourHS400
import torus.shared.BosonFiniteCertificateNatFourHS401
import torus.shared.BosonFiniteCertificateNatFourHS402
import torus.shared.BosonFiniteCertificateNatFourHS403
import torus.shared.BosonFiniteCertificateNatFourHS404
import torus.shared.BosonFiniteCertificateNatFourHS405
import torus.shared.BosonFiniteCertificateNatFourHS406
import torus.shared.BosonFiniteCertificateNatFourHS407
import torus.shared.BosonFiniteCertificateNatFourHS408
import torus.shared.BosonFiniteCertificateNatFourHS409
import torus.shared.BosonFiniteCertificateNatFourHS410
import torus.shared.BosonFiniteCertificateNatFourHS411
import torus.shared.BosonFiniteCertificateNatFourHS412
import torus.shared.BosonFiniteCertificateNatFourHS413
import torus.shared.BosonFiniteCertificateNatFourHS414
import torus.shared.BosonFiniteCertificateNatFourHS415
import torus.shared.BosonFiniteCertificateNatFourHS416

/-! Original relative H/S4 forms, independent of the M4 descendant-average chain. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFourRelativeS4Matrix_source_form (d : Fin 17)
    (x y : Fin (natFourRelativeDimension d) → ℂ) :
    natOccupationInner (natFamilySynthesis (natFourRelativeColumn d) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourRelativeColumn d) y))=
        star x ⬝ᵥ (complexify (natFourRelativeS4Matrix d) *ᵥ y) := by
  fin_cases d
  · change (Fin 1 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f400basis b400relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f400basis b400relative) y)) =
        star x ⬝ᵥ (complexify b400s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f400_actual_relative_S4_form x y
  · change (Fin 0 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f401basis b401relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f401basis b401relative) y)) =
        star x ⬝ᵥ (complexify b401s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f401_actual_relative_S4_form x y
  · change (Fin 1 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f402basis b402relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f402basis b402relative) y)) =
        star x ⬝ᵥ (complexify b402s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f402_actual_relative_S4_form x y
  · change (Fin 1 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f403basis b403relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f403basis b403relative) y)) =
        star x ⬝ᵥ (complexify b403s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f403_actual_relative_S4_form x y
  · change (Fin 2 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f404basis b404relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f404basis b404relative) y)) =
        star x ⬝ᵥ (complexify b404s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f404_actual_relative_S4_form x y
  · change (Fin 1 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f405basis b405relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f405basis b405relative) y)) =
        star x ⬝ᵥ (complexify b405s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f405_actual_relative_S4_form x y
  · change (Fin 3 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f406basis b406relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f406basis b406relative) y)) =
        star x ⬝ᵥ (complexify b406s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f406_actual_relative_S4_form x y
  · change (Fin 2 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f407basis b407relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f407basis b407relative) y)) =
        star x ⬝ᵥ (complexify b407s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f407_actual_relative_S4_form x y
  · change (Fin 4 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f408basis b408relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f408basis b408relative) y)) =
        star x ⬝ᵥ (complexify b408s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f408_actual_relative_S4_form x y
  · change (Fin 3 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f409basis b409relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f409basis b409relative) y)) =
        star x ⬝ᵥ (complexify b409s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f409_actual_relative_S4_form x y
  · change (Fin 5 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f410basis b410relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f410basis b410relative) y)) =
        star x ⬝ᵥ (complexify b410s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f410_actual_relative_S4_form x y
  · change (Fin 4 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f411basis b411relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f411basis b411relative) y)) =
        star x ⬝ᵥ (complexify b411s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f411_actual_relative_S4_form x y
  · change (Fin 7 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f412basis b412relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f412basis b412relative) y)) =
        star x ⬝ᵥ (complexify b412s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f412_actual_relative_S4_form x y
  · change (Fin 5 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f413basis b413relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f413basis b413relative) y)) =
        star x ⬝ᵥ (complexify b413s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f413_actual_relative_S4_form x y
  · change (Fin 8 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f414basis b414relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f414basis b414relative) y)) =
        star x ⬝ᵥ (complexify b414s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f414_actual_relative_S4_form x y
  · change (Fin 7 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f415basis b415relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f415basis b415relative) y)) =
        star x ⬝ᵥ (complexify b415s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f415_actual_relative_S4_form x y
  · change (Fin 10 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f416basis b416relative) x)
      (canonicalNatFourS4 (natFamilySynthesis (natFourColumnFamily f416basis b416relative) y)) =
        star x ⬝ᵥ (complexify b416s *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f416_actual_relative_S4_form x y

theorem natFourRelativeHMatrix_source_form (d : Fin 17)
    (x y : Fin (natFourRelativeDimension d) → ℂ) :
    natOccupationInner (natFamilySynthesis (natFourRelativeColumn d) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourRelativeColumn d) y))=
        star x ⬝ᵥ (complexify (natFourRelativeHMatrix d) *ᵥ y) := by
  fin_cases d
  · change (Fin 1 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f400basis b400relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f400basis b400relative) y)) =
        star x ⬝ᵥ (complexify b400h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f400_actual_relative_H_form x y
  · change (Fin 0 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f401basis b401relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f401basis b401relative) y)) =
        star x ⬝ᵥ (complexify b401h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f401_actual_relative_H_form x y
  · change (Fin 1 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f402basis b402relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f402basis b402relative) y)) =
        star x ⬝ᵥ (complexify b402h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f402_actual_relative_H_form x y
  · change (Fin 1 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f403basis b403relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f403basis b403relative) y)) =
        star x ⬝ᵥ (complexify b403h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f403_actual_relative_H_form x y
  · change (Fin 2 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f404basis b404relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f404basis b404relative) y)) =
        star x ⬝ᵥ (complexify b404h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f404_actual_relative_H_form x y
  · change (Fin 1 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f405basis b405relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f405basis b405relative) y)) =
        star x ⬝ᵥ (complexify b405h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f405_actual_relative_H_form x y
  · change (Fin 3 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f406basis b406relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f406basis b406relative) y)) =
        star x ⬝ᵥ (complexify b406h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f406_actual_relative_H_form x y
  · change (Fin 2 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f407basis b407relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f407basis b407relative) y)) =
        star x ⬝ᵥ (complexify b407h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f407_actual_relative_H_form x y
  · change (Fin 4 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f408basis b408relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f408basis b408relative) y)) =
        star x ⬝ᵥ (complexify b408h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f408_actual_relative_H_form x y
  · change (Fin 3 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f409basis b409relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f409basis b409relative) y)) =
        star x ⬝ᵥ (complexify b409h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f409_actual_relative_H_form x y
  · change (Fin 5 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f410basis b410relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f410basis b410relative) y)) =
        star x ⬝ᵥ (complexify b410h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f410_actual_relative_H_form x y
  · change (Fin 4 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f411basis b411relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f411basis b411relative) y)) =
        star x ⬝ᵥ (complexify b411h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f411_actual_relative_H_form x y
  · change (Fin 7 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f412basis b412relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f412basis b412relative) y)) =
        star x ⬝ᵥ (complexify b412h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f412_actual_relative_H_form x y
  · change (Fin 5 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f413basis b413relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f413basis b413relative) y)) =
        star x ⬝ᵥ (complexify b413h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f413_actual_relative_H_form x y
  · change (Fin 8 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f414basis b414relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f414basis b414relative) y)) =
        star x ⬝ᵥ (complexify b414h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f414_actual_relative_H_form x y
  · change (Fin 7 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f415basis b415relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f415basis b415relative) y)) =
        star x ⬝ᵥ (complexify b415h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f415_actual_relative_H_form x y
  · change (Fin 10 → ℂ) at x y
    change natOccupationInner
      (natFamilySynthesis (natFourColumnFamily f416basis b416relative) x)
      (canonicalPairHamiltonianNat (natFamilySynthesis (natFourColumnFamily f416basis b416relative) y)) =
        star x ⬝ᵥ (complexify b416h *ᵥ y)
    rw [natFourColumnFamily_synthesis,natFourColumnFamily_synthesis]
    exact f416_actual_relative_H_form x y

#print axioms natFourRelativeS4Matrix_source_form
#print axioms natFourRelativeHMatrix_source_form
end TorusLean.BosonFiniteCertificate
