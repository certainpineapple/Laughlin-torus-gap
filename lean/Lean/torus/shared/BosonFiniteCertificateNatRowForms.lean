import torus.shared.BosonFiniteCertificateNatCOMTail
import torus.shared.BosonFiniteCertificateNatOccupationInner
import torus.shared.BosonFiniteCertificateCanonicalFormsCore

/-! The original 138 differential rows and their pair subtraction, acting on
arbitrary natural orbital labels before the genuine occupation form is taken.
Finite-mode transport follows from injective rename and invertible scaling.
The high-descendant conclusion below is a two-sided form identity only. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateAction
open scoped BigOperators

theorem nat_rescale_rename_fin9 (κ : ℕ → ℂ) (κ9 : Fin 9 → ℂ)
    (hκ : ∀ j : Fin 9, κ j.val=κ9 j) (f : Core (Fin 9) ℂ) :
    rescaleHom κ (MvPolynomial.rename Fin.val f)=
      MvPolynomial.rename Fin.val (rescaleHom κ9 f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [rescaleHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f j hf =>
    simp only [map_mul,MvPolynomial.rename_X,rescaleHom_X,hf,map_smul,hκ j]

theorem nat_conjugate_rename_fin9
    (A : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ)
    (B : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ)
    (hAB : ∀ f, A (MvPolynomial.rename Fin.val f)=MvPolynomial.rename Fin.val (B f))
    (f : Core (Fin 9) ℂ) :
    conjugateOperator factorialRootNat factorialRootNat_ne_zero A (MvPolynomial.rename Fin.val f)=
      MvPolynomial.rename Fin.val (conjugateOperator factorialRoot9 factorialRoot9_ne_zero B f) := by
  change rescaleHom factorialRootNat
      (A (rescaleHom (fun j => (factorialRootNat j)⁻¹) (MvPolynomial.rename Fin.val f))) =
    MvPolynomial.rename Fin.val (rescaleHom factorialRoot9
      (B (rescaleHom (fun j => (factorialRoot9 j)⁻¹) f)))
  rw [nat_rescale_rename_fin9 (fun j => (factorialRootNat j)⁻¹)
    (fun j => (factorialRoot9 j)⁻¹) (fun _ => rfl),hAB,
    nat_rescale_rename_fin9 factorialRootNat factorialRoot9 (fun _ => rfl)]

/-- Actual all-core operator intertwining, with all original labels checked. -/
theorem canonicalNatRow_rename (t : ℕ) (row : List ℤ)
    (ht : rowLabelsBounded9 t=true) (f : Core (Fin 9) ℂ) :
    canonicalNatRow t row (MvPolynomial.rename Fin.val f)=
      MvPolynomial.rename Fin.val (canonicalFrozenRow9 t row f) := by
  apply nat_conjugate_rename_fin9
  intro g
  exact (rename_finitePaperRow9 t row ht g).symm

def canonicalNatRowChannelForm {r : ℕ} (rows : Fin r → List ℤ) (t : ℕ)
    (f g : Core ℕ ℂ) : ℂ :=
  ∑ i, (natOccupationInner (canonicalNatRow t (rows i) f) (canonicalNatRow t (rows i) g) -
    natOccupationInner (canonicalNatRow t [rowInteger (rows i) 0] f)
      (canonicalNatRow t [rowInteger (rows i) 0] g))

/-- Each original index occurs once, including the original zero/repeated rows. -/
def canonicalNatOriginalM3Form (f g : Core ℕ ℂ) : ℂ :=
  ∑ t : Fin 4, canonicalNatRowChannelForm
    (fun i : Fin (frozenRowCount t) => ((frozenRows t.val)[i.val]?.getD [])) t.val f g

theorem canonicalNatRowChannelForm_rename {r : ℕ} (rows : Fin r → List ℤ) (t : ℕ)
    (ht : rowLabelsBounded9 t=true) (f g : Core (Fin 9) ℂ) :
    canonicalNatRowChannelForm rows t (MvPolynomial.rename Fin.val f)
      (MvPolynomial.rename Fin.val g)=canonicalRowChannelForm rows t f g := by
  simp only [canonicalNatRowChannelForm,canonicalRowChannelForm,
    canonicalNatRow_rename t _ ht,natOccupationInner_rename_fin9]

theorem canonicalNatOriginalM3Form_rename (f g : Core (Fin 9) ℂ) :
    canonicalNatOriginalM3Form (MvPolynomial.rename Fin.val f)
      (MvPolynomial.rename Fin.val g)=canonicalOriginalM3Form f g := by
  unfold canonicalNatOriginalM3Form canonicalOriginalM3Form
  apply Finset.sum_congr rfl
  intro t _
  exact canonicalNatRowChannelForm_rename _ t.val (frozen_rows_labels_bounded t) f g

/-- The true unlimited-label descendants have zero original-row-minus-pair
cross form above degree eight. No one-sided operator-kernel assertion follows. -/
theorem canonicalNatOriginalM3Form_descendant_tail (d n : ℕ)
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id d) (h : 8<d+n) :
    canonicalNatOriginalM3Form
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] g)=0 := by
  unfold canonicalNatOriginalM3Form canonicalNatRowChannelForm
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro i _
  rw [canonicalNatRow_descendant_tail d n t.val _ f hNf hdf h,
    canonicalNatRow_descendant_tail d n t.val _ g hNg hdg h,sub_self]

#print axioms canonicalNatRow_rename
#print axioms canonicalNatOriginalM3Form_rename
#print axioms canonicalNatOriginalM3Form_descendant_tail
end TorusLean.BosonFiniteCertificate
