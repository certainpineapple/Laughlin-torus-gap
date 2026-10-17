import torus.shared.BosonFiniteCertificateNatRowForms
import torus.shared.BosonFiniteCertificateNatPairForms
import torus.shared.BosonFiniteCertificateNatCOMDescendants
import torus.shared.BosonFiniteCertificateNatRelative

/-! Actual natural-label comparison before physical thermal transfer.
Both H factors are the independently defined locally finite Hamiltonian;
COM descendants use the unlimited natural-label raising derivation. The
COM sum here is explicitly finite. No torus single3 is defined by this form. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open scoped BigOperators

def natCOMComparisonWeight (n : ℕ) : ℂ :=
  (2 : ℂ) / ((3 : ℂ)^(n+1) * (n.factorial : ℂ))

def canonicalNatFiniteCOMForm (d : ℕ) (f g : Core ℕ ℂ) : ℂ :=
  ∑ n : Fin (9-d), natCOMComparisonWeight n.val * canonicalNatOriginalM3Form
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n.val] f)
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n.val] g)

def canonicalNatComparisonForm (d : ℕ) (f g : Core ℕ ℂ) : ℂ :=
  natOccupationInner f (canonicalPairHamiltonianNat (canonicalPairHamiltonianNat g)) -
    natOccupationInner f (canonicalPairHamiltonianNat g) -
    canonicalNatFiniteCOMForm d f g +
    (delta : ℂ) * natOccupationInner f (canonicalPairHamiltonianNat g)
end TorusLean.BosonFiniteCertificate
