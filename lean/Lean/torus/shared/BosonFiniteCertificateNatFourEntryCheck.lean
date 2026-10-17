import torus.shared.BosonFiniteCertificateNatFourMatrixCore

/-! An explicit finite Boolean traversal for exact rational entry identities.
Its sole soundness theorem expands both original finite index types. It does
not change any matrix, evaluator, or independently defined source operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
namespace TorusLean.BosonFiniteCertificate

def natFourRationalEntryCheck {m n : ℕ}
    (F M : Fin m → Fin n → ℚ) : Bool :=
  (List.finRange m).all fun a =>
    (List.finRange n).all fun b => decide (F a b=M a b)

theorem natFourRationalEntryCheck_sound {m n : ℕ}
    (F M : Fin m → Fin n → ℚ) (h : natFourRationalEntryCheck F M=true) :
    ∀ a b, F a b=M a b := by
  intro a b
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp h a (List.mem_finRange a)) b (List.mem_finRange b))

#print axioms natFourRationalEntryCheck_sound
end TorusLean.BosonFiniteCertificate
