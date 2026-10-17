import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact full-COM dual coordinates from the genuine occupation Gram.
T is formed as J Sᵀ G; it is not a separately solved large inverse. The
actual family-to-column identity and complete occupation basis are explicit
inputs. None of these generic identities assert a relative-only family spans
the full four-particle degree sector. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

def natFourCOMDual {n : ℕ} (S G J : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ := J*Sᵀ*G

theorem natFourCOMDual_left {n : ℕ} (S G F J : Matrix (Fin n) (Fin n) ℚ)
    (hGram : Sᵀ*G*S=F) (hJF : J*F=1) : natFourCOMDual S G J*S=1 := by
  calc
    _ = J*(Sᵀ*G*S) := by simp only [natFourCOMDual,Matrix.mul_assoc]
    _ = 1 := by rw [hGram,hJF]

theorem natFourCOMDual_right {n : ℕ} (S G F J : Matrix (Fin n) (Fin n) ℚ)
    (hGram : Sᵀ*G*S=F) (hJF : J*F=1) : S*natFourCOMDual S G J=1 :=
  mul_eq_one_comm.mp (natFourCOMDual_left S G F J hGram hJF)

theorem natFourCOMFamily_synthesis {n : ℕ} (basis : Fin n → List ℕ)
    (w : Fin n → Core ℕ ℂ) (S : Matrix (Fin n) (Fin n) ℚ)
    (hW : ∀ j, w j=natFourWordBlock basis (fun i => complexify S i j)) (x : Fin n → ℂ) :
    natFamilySynthesis w x=natFourWordBlock basis (complexify S *ᵥ x) := by
  have h : w=natFourColumnFamily basis S := funext hW
  rw [h,natFourColumnFamily_synthesis]

theorem natFourCOMFamily_gram {n : ℕ} (basis : Fin n → List ℕ)
    (hinj : Function.Injective (fun a => wordOccupation (basis a)))
    (w : Fin n → Core ℕ ℂ) (S : Matrix (Fin n) (Fin n) ℚ)
    (hW : ∀ j, w j=natFourWordBlock basis (fun i => complexify S i j)) :
    natFamilyGram w=complexify (Sᵀ*natFourWordGram basis*S) := by
  have h : w=natFourColumnFamily basis S := funext hW
  rw [h,natFourColumnFamily_gram basis hinj]

/-- Full true homogeneous occupation completeness, transported through a
proved square COM coordinate change. No finite-span assumption is imposed
on the input polynomial and no relative restriction is silently dropped. -/
theorem natFourCOMFamily_homogeneous_complete {n : ℕ} (D : ℕ) (basis : Fin n → List ℕ)
    (w : Fin n → Core ℕ ℂ) (S T : Matrix (Fin n) (Fin n) ℚ)
    (hW : ∀ j, w j=natFourWordBlock basis (fun i => complexify S i j))
    (hST : S*T=1)
    (hfull : ∀ f : Core ℕ ℂ, f.IsHomogeneous 4 → f.IsWeightedHomogeneous id D →
      ∃ x, natFourWordBlock basis x=f)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id D) :
    ∃ x, natFamilySynthesis w x=f := by
  obtain ⟨v,hv⟩ := hfull f hN hd
  refine ⟨complexify T *ᵥ v,?_⟩
  rw [natFourCOMFamily_synthesis basis w S hW,Matrix.mulVec_mulVec,
    ←complexify_mul_rect,hST,complexify_one_rat,Matrix.one_mulVec,hv]

#print axioms natFourCOMDual_left
#print axioms natFourCOMDual_right
#print axioms natFourCOMFamily_synthesis
#print axioms natFourCOMFamily_gram
#print axioms natFourCOMFamily_homogeneous_complete
end TorusLean.BosonFiniteCertificate
